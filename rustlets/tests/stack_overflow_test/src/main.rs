#![deny(unsafe_op_in_unsafe_fn)]
#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_app!(StackOverflowTestRustlet, 256);

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct StackOverflowTestRustlet;

impl Rustlet for StackOverflowTestRustlet {
    fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            0x00 => apdu.accept(),
            0x52 => {
                touch_stack_guard_gap();
                ApduStatus::success()
            }
            0x54 => {
                touch_flash_outside_app_window();
                ApduStatus::success()
            }
            0x53 => {
                let value = consume_stack(64);
                apdu.as_sending().send(&[value])
            }
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}

#[inline(never)]
fn touch_stack_guard_gap() {
    let local = 0u8;
    let stack_addr = core::ptr::addr_of!(local) as usize;
    let stack_base = stack_addr & !(2048usize - 1);
    let guard_addr = stack_base - 640;

    // Deliberate access outside this allocation: express the faulting store as
    // a CPU instruction instead of a Rust write requiring valid writable memory.
    unsafe {
        core::arch::asm!("strb r1, [r0]", in("r0") guard_addr, in("r1") 0xA5u32, options(nostack));
    }
}

#[inline(never)]
fn touch_flash_outside_app_window() {
    // Deliberate write to read-only flash; expected to terminate this Rustlet.
    unsafe {
        core::arch::asm!("strb r1, [r0]", in("r0") 0x1000_0000usize, in("r1") 0xA5u32, options(nostack));
    }
}

#[inline(never)]
fn consume_stack(depth: usize) -> u8 {
    let mut frame = [0u8; 256];
    for (index, byte) in frame.iter_mut().enumerate() {
        // SAFETY: byte is exclusively borrowed from this initialized frame.
        unsafe { core::ptr::write_volatile(byte, depth.wrapping_add(index) as u8) };
    }

    // SAFETY: the first byte belongs to this live, initialized frame.
    let local = unsafe { core::ptr::read_volatile(frame.as_ptr()) };
    if depth == 0 {
        local
    } else {
        local.wrapping_add(consume_stack(depth - 1))
    }
}
