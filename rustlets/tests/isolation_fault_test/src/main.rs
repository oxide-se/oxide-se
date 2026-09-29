#![deny(unsafe_op_in_unsafe_fn)]
#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};

mod abi_probe;

declare_app!(IsolationFaultRustlet);

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct IsolationFaultRustlet {
    counter: u8,
}

impl Rustlet for IsolationFaultRustlet {
    fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
        let ins = Apdu::new(ctx).ins();
        if ins == 0x5c {
            return Apdu::new(ctx).as_sending().send(&[self.counter]);
        }
        if ins == 0x73 {
            let choice = Apdu::new(ctx).p1();
            self.counter = self.counter.wrapping_add(1);
            ctx.state_bytes_mut()[0] = self.counter;
            let _ = ctx.set_state_len(1);
            let _ = Apdu::new(ctx).as_sending().send(&[0xde, 0xad]);
            if matches!(choice, 5 | 6) {
                raw_svc::<252>(choice as usize, 0, 0);
                return ApduStatus::success();
            }
            return cpu_exception_probe(choice);
        }
        if ins == 0x75 {
            let service = Apdu::new(ctx).p1();
            let case = Apdu::new(ctx).p2();
            return abi_probe::run(ctx, service, case);
        }
        if ins == 0x74 {
            let choice = Apdu::new(ctx).p1();
            let len = Apdu::new(ctx).p2() as usize;
            return apdu_order_probe(ctx, choice, len);
        }
        if ins == 0x72 {
            let choice = Apdu::new(ctx).p1();
            let phase = Apdu::new(ctx).p2();
            for (i, byte) in ctx.data[..255].iter_mut().enumerate() {
                *byte = (i as u8) ^ 0xa5;
            }
            if phase != 0 {
                raw_svc::<7>(0, 0, 0);
                raw_svc::<8>(if phase == 2 { 255 } else { 2 }, 0, 0);
                if phase == 3 {
                    raw_svc::<7>(0, 0, 0); // reset an already staged response
                }
            }
            let len = match choice {
                0 => 256,
                1 => u16::MAX as usize,
                2 => usize::MAX,
                3 => 0,
                4 => 255,
                _ => return ApduStatus::wrong_data(),
            };
            raw_svc::<8>(len, 0, 0);
            return ApduStatus::success();
        }
        if ins == 0x70 {
            let low_stack = Apdu::new(ctx).p1() == 0;
            self.counter = self.counter.wrapping_add(1);
            ctx.state_bytes_mut()[0] = self.counter;
            let _ = ctx.set_state_len(1);
            let _ = Apdu::new(ctx).as_sending().send(&[0xde, 0xad]);
            failed_exception_stacking(low_stack);
        }
        if ins == 0x5f {
            self.counter = self.counter.wrapping_add(1);
            ctx.state_bytes_mut()[0] = self.counter;
            let _ = ctx.set_state_len(1);
            let _ = Apdu::new(ctx).as_sending().send(&[0xde, 0xad]);
            return invalid_execution_state();
        }
        if ins == 0x5e {
            let number = Apdu::new(ctx).p1();
            self.counter = self.counter.wrapping_add(1);
            ctx.state_bytes_mut()[0] = self.counter;
            let _ = ctx.set_state_len(1);
            let _ = Apdu::new(ctx).as_sending().send(&[0xde, 0xad]);
            match number {
                254 => {
                    raw_svc::<254>(0, 0, 0);
                }
                255 => {
                    raw_svc::<255>(0, 0, 0);
                }
                _ => return ApduStatus::wrong_data(),
            }
            // A simple error return to the attacker is not containment.
            return ApduStatus::success();
        }
        if ins == 0x5d {
            let len = Apdu::new(ctx).p1();
            // Stage a changed state and a response, then bypass runtime
            // serialization so the kernel sees the raw adversarial length.
            ctx.state_bytes_mut().fill(0);
            ctx.state_bytes_mut()[0] = self.counter.wrapping_add(1);
            let _ = Apdu::new(ctx).as_sending().send(&[0xde, 0xad]);
            // SAFETY: the initialized length byte precedes the repr(C) byte
            // array in this writable shared context. This deliberately skips
            // set_state_len's validation, as an untrusted application can.
            unsafe { ctx.state_bytes_mut().as_mut_ptr().sub(1).write(len) };
            rustlet_runtime::syscall::runtime::handler_return::trigger(ApduStatus::success())
        }
        if matches!(ins, 0x58 | 0x59) {
            return mapping_probe(ctx, ins);
        }
        if matches!(ins, 0x5a | 0x5b | 0x71) || (0x60..=0x6b).contains(&ins) {
            return integrity_probe(ctx, ins);
        }
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            0x50 => {
                faulting_read(0);
                ApduStatus::success()
            }
            0x51 => {
                faulting_write(0, 0x1122_3344);
                ApduStatus::success()
            }
            0x52 => invalid_instruction(),
            0x53 => execute_shared_buffer(ctx),
            0x54 => unprivileged_entry_svc(),
            // Deliberate unauthorized accesses: the MPU must fault before the
            // Rustlet can read RP2350 entropy or bypass the TRNG health checks.
            0x55 => {
                faulting_read(0x400f_0114);
                ApduStatus::success()
            }
            0x56 => {
                faulting_write(0x400f_0138, 0x0e);
                ApduStatus::success()
            }
            0x57 => {
                let mut bytes = [0; 16];
                let result = rustlet_runtime::RandomData::get_instance(
                    rustlet_runtime::RandomAlgorithm::SecureRandom,
                )
                .and_then(|mut rng| rng.generate_data(&mut bytes));
                if result.is_err() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                apdu.as_sending().send(&bytes)
            }
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}

// Intentionally faulting CPU operations are assembly, not invalid Rust pointer
// accesses. Volatile Rust operations still require non-trapping valid memory.
#[inline(never)]
fn faulting_read(address: usize) -> u32 {
    let value: u32;
    // Deliberate hardware fault: only the diagnostic APDUs above select addresses.
    unsafe {
        core::arch::asm!("ldr r0, [r0]", inout("r0") address => value, options(nostack));
    }
    value
}

#[inline(never)]
fn faulting_write(address: usize, value: u32) {
    // Deliberate hardware fault; no Rust reference or dereference is fabricated.
    unsafe {
        core::arch::asm!("str r1, [r0]", in("r0") address, in("r1") value, options(nostack));
    }
}

#[inline(never)]
fn invalid_instruction() -> ApduStatus {
    unsafe {
        core::arch::asm!(".hword 0xde00", options(noreturn));
    }
}

/// Branch to mapped code with bit zero clear: INVSTATE on Mainline,
/// HardFault on ARMv6-M. If the CPU incorrectly accepts it, return success
/// so the host rejects the result instead of mistaking a timeout for a fault.
#[inline(never)]
fn invalid_execution_state() -> ApduStatus {
    // Deliberate hardware exception; no invalid Rust function pointer is made.
    unsafe {
        core::arch::asm!(
            "adr r0, 2f", "bx r0", ".balign 4", "2:",
            out("r0") _, options(nostack)
        );
    }
    ApduStatus::success()
}

/// The exchange page is data-only, including its previously executable tail.
#[inline(never)]
fn execute_shared_buffer(ctx: &mut RustletCtx) -> ApduStatus {
    ctx.data[..2].copy_from_slice(&[0x70, 0x47]); // bx lr
                                                  // Deliberate NX fault. If isolation fails, the planted BX LR returns with
                                                  // the C caller-clobbered registers declared to the compiler. Data bytes are
                                                  // never represented as a valid Rust function pointer.
    unsafe {
        core::arch::asm!("blx {entry}", entry = in(reg) (ctx.data.as_ptr() as usize | 1), clobber_abi("C"));
    }
    ApduStatus::success()
}

/// SVC 0 issued from user code must not enter the privileged launch path.
#[inline(never)]
fn unprivileged_entry_svc() -> ApduStatus {
    let control: u32;
    unsafe {
        core::arch::asm!("svc #0", "mrs {control}, CONTROL",
            inout("r0") 0u32 => _, control = out(reg) control, options(nostack));
    }
    if control & 3 == 3 {
        ApduStatus::success()
    } else {
        ApduStatus::internal_error()
    }
}

// Exercise phase transitions through raw SVCs, bypassing the safe typestate API.
// Cases: 0 repeated input; 1 output -> input; 2 implicit output -> input;
// 3 input -> output -> input; 4 repeated output; 5 empty input;
// 6 implicit empty output; 7 public runtime wrapper after output.
fn apdu_order_probe(ctx: &mut RustletCtx, choice: u8, len: usize) -> ApduStatus {
    if matches!(choice, 0 | 3 | 5) {
        if raw_svc::<6>(0, 0, 0) != len {
            return ApduStatus::internal_error();
        }
        for byte in &mut ctx.data[..len] {
            *byte ^= 0x5a;
        }
        if raw_svc::<6>(0, 0, 0) != len
            || ctx.data[..len].iter().enumerate().any(|(i, b)| *b != (i as u8 ^ 0x5a))
        {
            return ApduStatus::internal_error();
        }
        if choice == 5 {
            return ApduStatus::success();
        }
    } else {
        ctx.data.fill(0xa5);
    }
    if choice != 2 && choice != 6 {
        raw_svc::<7>(0, 0, 0);
    }
    raw_svc::<8>(len, 0, 0);
    let expected_len = if choice == 4 {
        raw_svc::<7>(0, 0, 0);
        0
    } else {
        len
    };
    if choice != 0 {
        for _ in 0..2 {
            let received = if choice == 7 {
                rustlet_runtime::SEApdu::set_incoming_and_receive(ctx)
            } else {
                raw_svc::<6>(0, 0, 0)
            };
            if received != 0 || !ctx.outgoing_started() || ctx.outgoing_len() != expected_len {
                return ApduStatus::internal_error();
            }
        }
    }
    if ctx.data[..len].iter().enumerate().any(|(i, b)| {
        *b != if matches!(choice, 0 | 3) { i as u8 ^ 0x5a } else { 0xa5 }
    }) {
        return ApduStatus::internal_error();
    }
    ApduStatus::success()
}

/// Raw adversarial ABI calls intentionally bypass the safe application API.
/// Only test images embed this Rustlet. The kernel must distrust these words.
fn raw_svc<const N: u8>(a: usize, b: usize, c: usize) -> usize {
    let result: usize;
    unsafe {
        core::arch::asm!("svc {number}", number = const N,
            inout("r0") a => result, inout("r1") b => _, inout("r2") c => _,
            options(nostack));
    }
    result
}

fn integrity_probe(ctx: &mut RustletCtx, ins: u8) -> ApduStatus {
    use rustlet_runtime::syscall_abi::CRYPTO_RESULT_ERROR_FLAG;
    use rustlet_runtime::{CryptoEcGenerateKeypairParams, CryptoRandomGenerateParams};
    let passed = match ins {
        0x60 => {
            raw_svc::<255>(0, 0, 0);
            true
        }
        0x61 | 0x62 => {
            // The ABI length byte immediately precedes its 244-byte storage.
            // This is an initialized u8 in our writable shared allocation.
            let bytes = ctx.state_bytes_mut().as_mut_ptr();
            unsafe {
                bytes.sub(1).write(if ins == 0x61 { 255 } else { 245 });
            }
            rustlet_runtime::syscall::runtime::handler_return::trigger(ApduStatus::success())
        }
        0x63 => {
            // Deliberately branch to an even address: INVSTATE on Mainline.
            unsafe {
                core::arch::asm!(
                    "adr r0, 2f",
                    "bx r0",
                    ".balign 4",
                    "2: b 2b",
                    options(noreturn)
                );
            }
        }
        0x64 => {
            raw_svc::<8>(256, 0, 0);
            true
        }
        0x71 => {
            let case = Apdu::new(ctx).p1();
            deallocation_probe(ctx, case)
        },
        0x66 => {
            let params = CryptoRandomGenerateParams {
                algorithm: 1,
                output_ptr: core::ptr::null_mut(),
                output_len: 0,
            };
            let address = core::ptr::addr_of!(params) as usize;
            raw_svc::<10>(address + 1, 0, 0) & CRYPTO_RESULT_ERROR_FLAG != 0
        }
        0x67 => {
            let params = CryptoRandomGenerateParams {
                algorithm: 1,
                output_ptr: core::ptr::null_mut(),
                output_len: 0,
            };
            raw_svc::<10>(core::ptr::addr_of!(params) as usize, 0, 0) == 0
        }
        0x68 => {
            let mut output = [0xa5; 80];
            let params = CryptoEcGenerateKeypairParams {
                curve: 1,
                reserved0: 0,
                reserved1: 0,
                reserved2: 0,
                private_key_ptr: output.as_mut_ptr(),
                private_key_capacity: 32,
                public_key_ptr: output.as_mut_ptr(),
                public_key_capacity: 65,
            };
            let result = raw_svc::<13>(core::ptr::addr_of!(params) as usize, 0, 0);
            result & CRYPTO_RESULT_ERROR_FLAG != 0 && output == [0xa5; 80]
        }
        0x69 => {
            let params = CryptoRandomGenerateParams {
                algorithm: 1,
                output_ptr: usize::MAX as *mut u8,
                output_len: 16,
            };
            raw_svc::<10>(core::ptr::addr_of!(params) as usize, 0, 0) & CRYPTO_RESULT_ERROR_FLAG
                != 0
        }
        0x5a => {
            let expected_len = Apdu::new(ctx).p2() as usize;
            let seed = Apdu::new(ctx).p1();
            let apdu = Apdu::new(ctx).as_receiving();
            // Check the complete input, including the former trampoline tail,
            // then return it in place so the host checks the output path too.
            let valid = apdu.data().len() == expected_len
                && apdu
                    .data()
                    .iter()
                    .enumerate()
                    .all(|(i, b)| *b == (i as u8).wrapping_add(seed));
            return if valid {
                apdu.as_sending().send_with(|_| expected_len)
            } else {
                apdu.reject(ApduStatus::internal_error())
            };
        }
        0x5b => {
            // Fill all 256 physical data bytes, not only the 255-byte APDU
            // payload. The adjacent serialization storage must remain intact.
            let version = ctx.version();
            let header = (
                Apdu::new(ctx).ins(),
                Apdu::new(ctx).p1(),
                Apdu::new(ctx).p2(),
            );
            for (i, byte) in ctx.state_bytes_mut().iter_mut().enumerate() {
                *byte = (i as u8) ^ 0xa5;
            }
            if !ctx.set_state_len(244) {
                return ApduStatus::internal_error();
            }
            for (i, byte) in ctx.data.iter_mut().enumerate() {
                *byte = (i as u8) ^ 0x5a;
            }
            let valid = ctx.version() == version
                && (
                    Apdu::new(ctx).ins(),
                    Apdu::new(ctx).p1(),
                    Apdu::new(ctx).p2(),
                ) == header
                && ctx.state_bytes().len() == 244
                && ctx
                    .state_bytes()
                    .iter()
                    .enumerate()
                    .all(|(i, b)| *b == (i as u8) ^ 0xa5)
                && ctx
                    .data
                    .iter()
                    .enumerate()
                    .all(|(i, b)| *b == (i as u8) ^ 0x5a);
            return if valid {
                Apdu::new(ctx).as_sending().send_with(|_| 255)
            } else {
                ApduStatus::internal_error()
            };
        }
        0x6b => true, // cheap return loop for redirect/timer overlap stress
        _ => false,
    };
    if passed {
        ApduStatus::success()
    } else {
        ApduStatus::internal_error()
    }
}

/// Deliberately untrusted input addresses, never converted into Rust references.
fn mapping_probe(ctx: &mut RustletCtx, ins: u8) -> ApduStatus {
    use rustlet_runtime::syscall_abi::{
        CryptoErrorCode, CRYPTO_MAC_DO_FINAL, CRYPTO_RESULT_ERROR_FLAG,
    };
    use rustlet_runtime::{CryptoMacDoFinalParams, CryptoMacOperation, MacAlgorithm};
    let apdu = Apdu::new(ctx).as_receiving();
    let Ok(bytes) = <[u8; 4]>::try_from(apdu.data()) else {
        return apdu.reject(ApduStatus::wrong_data());
    };
    let address = u32::from_le_bytes(bytes) as usize;
    let result = if ins == 0x58 {
        faulting_read(address)
    } else {
        let key = [0u8; 16];
        let mut output = [0xa5u8; 16];
        let params = CryptoMacDoFinalParams {
            algorithm: MacAlgorithm::AesCmac as u8,
            operation: CryptoMacOperation::Compute as u8,
            key_ptr: key.as_ptr(),
            key_len: key.len(),
            input_ptr: address as *const u8,
            input_len: 4,
            expected_tag_ptr: core::ptr::null(),
            expected_tag_len: 0,
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = raw_svc::<CRYPTO_MAC_DO_FINAL>(core::ptr::addr_of!(params) as usize, 0, 0);
        if result == (CRYPTO_RESULT_ERROR_FLAG | CryptoErrorCode::PermissionDenied.word())
            && output != [0xa5; 16]
        {
            return apdu.reject(ApduStatus::internal_error());
        }
        result as u32
    };
    apdu.as_sending().send(&result.to_le_bytes())
}

/// Abandon PSP immediately before SVC. No Rust instruction uses the broken
/// stack: successful containment must resume the saved kernel context instead.
#[inline(never)]
fn failed_exception_stacking(low_stack: bool) -> ! {
    let stack = if low_stack { 8u32 } else { 0xffff_fff8u32 };
    // Deliberate exception-entry fault, not a Rust access through an invalid pointer.
    unsafe {
        core::arch::asm!(
            "mov sp, r0",
            "svc #255",
            "2: b 2b",
            in("r0") stack,
            options(noreturn)
        );
    }
}

/// Check allocator metadata indirectly through live contents and subsequent
/// allocations. Raw assembly accesses avoid Rust aliases across hostile frees.
fn deallocation_probe(ctx: &mut RustletCtx, case: u8) -> bool {
    const SIZE: usize = 32;
    let gate = ctx as *mut RustletCtx as usize;
    let gate_len = rustlet_runtime::APDU_SHARED_REGION_SIZE;
    let gate_case = (9..=11).contains(&case);
    if gate_case {
        ctx.data.fill(0xa5);
        ctx.state_bytes_mut().fill(0x5a);
        if !ctx.set_state_len(244) { return false; }
    }
    // Snapshot only the 12 control bytes; payload canaries avoid a 512-byte copy.
    let control = [faulting_read(gate), faulting_read(gate + 4), faulting_read(gate + 8)];
    let outside_gate = |address: usize, size: usize| {
        address.checked_add(size).is_some_and(|end| end <= gate || address >= gate + gate_len)
    };
    let first = raw_svc::<3>(SIZE, 4, 0);
    let second = raw_svc::<3>(SIZE, 4, 0);
    if first == 0 || second == 0 {
        return false;
    }
    for offset in (0..SIZE).step_by(4) {
        faulting_write(first + offset, 0x1122_3344);
        faulting_write(second + offset, 0x5566_7788);
    }
    let (address, size, align) = match case {
        0 => (first, 1 << 20, 4),  // larger than the heap
        1 => (first, 256, 4),      // ancestor containing live allocations
        2 => (first + 1, SIZE, 4), // misaligned block address
        3 => (first + 8, 8, 4),    // interior of a live block
        4 => (first, 8, 4),        // smaller node inside a full block
        5 => (0, SIZE, 4),
        6 => (usize::MAX - 15, SIZE, 4), // overflowing address range
        7 => (first, SIZE, 3),           // invalid Layout alignment
        8 => {
            raw_svc::<4>(first, SIZE, 4);
            (first, SIZE, 4) // repeated free before any allocation can reuse it
        }
        // Valid aligned Layouts: these must fail heap ownership, not alignment.
        9 => (gate, gate_len, gate_len),
        10 => (gate, 256, 256), // control/serialization half
        11 => (ctx.data.as_mut_ptr() as usize, 256, 256), // APDU half
        _ => return false,
    };
    raw_svc::<4>(address, size, align);
    let third = raw_svc::<3>(SIZE, 4, 0);
    if third == 0 || !outside_gate(third, SIZE) {
        return false;
    }
    let disjoint = |a: usize, b: usize| a.abs_diff(b) >= SIZE;
    let mut valid = disjoint(third, second) && (case == 8 || disjoint(third, first));
    for offset in (0..SIZE).step_by(4) {
        faulting_write(third + offset, 0xaabb_ccdd);
    }
    for offset in (0..SIZE).step_by(4) {
        valid &= faulting_read(second + offset) == 0x5566_7788;
        if case != 8 {
            valid &= faulting_read(first + offset) == 0x1122_3344;
        }
        valid &= faulting_read(third + offset) == 0xaabb_ccdd;
    }
    if case != 8 {
        raw_svc::<4>(first, SIZE, 4);
    }
    raw_svc::<4>(second, SIZE, 4);
    raw_svc::<4>(third, SIZE, 4);
    // Exercise repeated legitimate allocate/free after the rejected operation.
    for _ in 0..8 {
        let block = raw_svc::<3>(SIZE, 4, 0);
        if block == 0 || !outside_gate(block, SIZE) {
            return false;
        }
        faulting_write(block, 0x1234_5678);
        valid &= faulting_read(block) == 0x1234_5678;
        raw_svc::<4>(block, SIZE, 4);
    }
    if gate_case {
        valid &= [faulting_read(gate), faulting_read(gate + 4), faulting_read(gate + 8)] == control;
        valid &= ctx.state_bytes().len() == 244;
        valid &= ctx.state_bytes().iter().all(|byte| *byte == 0x5a);
        valid &= ctx.data.iter().all(|byte| *byte == 0xa5);
    }
    valid
}

/// Raw encodings keep the fixture buildable on Thumb-1: unsupported Mainline
/// instructions deliberately become HardFault on Pico1, never Rust UB.
#[inline(never)]
fn cpu_exception_probe(choice: u8) -> ApduStatus {
    let words = [0u32; 2];
    // SAFETY: diagnostic assembly deliberately traps; no invalid Rust access.
    unsafe {
        match choice {
            0 => core::arch::asm!("udf #0", options(noreturn)),
            1 => core::arch::asm!(".hword 0xc802", inout("r0") (words.as_ptr() as usize + 1) => _, out("r1") _, options(nostack)),
            2 => core::arch::asm!(".hword 0xee10, 0x0f10", out("r0") _, options(nostack)),
            3 => core::arch::asm!(".hword 0xfbb0, 0xf0f1", inout("r0") 1u32 => _, in("r1") 0u32, options(nostack)),
            _ => return ApduStatus::wrong_data(),
        }
    }
    // Returning is a failed probe, not evidence of containment.
    ApduStatus::success()
}
