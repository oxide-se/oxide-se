//! ARMv6-M profile: Thumb-1 entry/return, PMSAv6 MPU and HardFault recovery.
use super::common_arm_m_profile::{
    decode_svc_immediate, ExceptionFrame, RedirectState, TargetAppEntry,
};
pub use super::common_arm_m_profile::{
    disable_interrupts, enable_interrupts, interrupts_restore, interrupts_save_and_disable,
};
use crate::core::mpu::{MpuAccess, MpuError, MpuPrivilege, MpuRegion, MpuRegionConfig, MpuResult};
use crate::core::syscall::{SyscallHandler, SyscallNumber};
use core::arch::global_asm;
use core::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};
use core::sync::atomic::{AtomicBool, Ordering};

const MAX_SYSCALL_COUNT: usize = 256;
const MPU_TYPE: *const u32 = 0xE000_ED90 as *const u32;
const MPU_CTRL: *mut u32 = 0xE000_ED94 as *mut u32;
const MPU_RNR: *mut u32 = 0xE000_ED98 as *mut u32;
const MPU_RBAR: *mut u32 = 0xE000_ED9C as *mut u32;
const MPU_RASR: *mut u32 = 0xE000_EDA0 as *mut u32;

const MPU_CTRL_ENABLE: u32 = 1 << 0;
const MPU_CTRL_PRIVDEFENA: u32 = 1 << 2;
const MPU_RASR_ENABLE: u32 = 1 << 0;
const MPU_RASR_SIZE_SHIFT: u32 = 1;
const MPU_RASR_AP_SHIFT: u32 = 24;
const MPU_RASR_XN: u32 = 1 << 28;

const MPU_AP_NO_ACCESS: u32 = 0b000;
const MPU_AP_PRIVILEGED_RW: u32 = 0b001;
const MPU_AP_PRIVILEGED_RW_UNPRIVILEGED_RW: u32 = 0b011;
const MPU_AP_PRIVILEGED_RO: u32 = 0b101;
const MPU_AP_PRIVILEGED_RO_UNPRIVILEGED_RO: u32 = 0b110;

const MPU_MIN_REGION_SIZE: usize = 32;
const MPU_REGION_COUNT_MASK: u32 = 0xff;
const MPU_REGION_COUNT_SHIFT: u32 = 8;
const ARMV6M_SOFT_MEMFAULT_STATUS: u32 = 1 << 8;
const ARMV6M_SOFT_MEMFAULT_FROM_PSP: u32 = 1 << 9;
const KERNEL_STACK_GUARD_REGION: MpuRegion = 7;
const KERNEL_STACK_GUARD_SIZE: usize = MPU_MIN_REGION_SIZE;
const KERNEL_STATIC_BASE: usize = crate::core::target::FAE_STATIC_BASE;
const APP_GATE_REGION_SIZE: usize = crate::core::isolation::APP_GATE_REGION_SIZE;

static INITIALIZED: AtomicBool = AtomicBool::new(false);
static mut SYSCALL_TABLE: [Option<SyscallHandler>; MAX_SYSCALL_COUNT] = [None; MAX_SYSCALL_COUNT];
static mut PENDING_REDIRECT: Option<RedirectState> = None;
static mut APP_GATE_REGION_STORAGE: [u8; APP_GATE_REGION_SIZE * 2] = [0; APP_GATE_REGION_SIZE * 2];
static mut LAST_SOFT_MEMFAULT_STATUS: u32 = 0;
static mut LAST_SOFT_MEMFAULT_ADDRESS: u32 = 0;
static mut LAST_SOFT_MEMFAULT_STACKED_PC: u32 = 0;
static mut LAST_SOFT_MEMFAULT_STACKED_LR: u32 = 0;
static mut KERNEL_STACK_GUARD_TEST_ACTIVE: u32 = 0;

global_asm!(
    r#"
    .syntax unified
    .arch armv6s-m
    .thumb

    .global oxi_core_resume_isolated_app_ptr
    .type oxi_core_resume_isolated_app_ptr, %function
    .thumb_func
oxi_core_resume_isolated_app_ptr:
    ldr     r0, =oxi_core_armv6m_resume_isolated_app
    movs    r1, #1
    orrs    r0, r1
    bx      lr

    .global oxi_core_periodic_timer_interrupt_handler
    .type oxi_core_periodic_timer_interrupt_handler, %function
    .thumb_func
oxi_core_periodic_timer_interrupt_handler:
    /* C callees preserve r5/r8/r11. Save only our modified registers and LR;
     * every Rust call sees an eight-byte-aligned MSP. Redirect uses 16 bytes. */
    push    {{r4, r6, r7, lr}}
    mov     r6, r9
    mov     r7, r10
    ldr     r0, ={kernel_static_base}
    mov     r9, r0
    mov     r10, r0
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r4, r0
    bl      oxi_core_periodic_timer_interrupt_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_armv6m_svcall_take_redirect
    cmp     r0, #0
    bne     8f
    cmp     r4, #0
    beq     9f
    bl      oxi_core_isolation_resume_rustlet_execution
9:
    add     sp, sp, #16
    mov     r9, r6
    mov     r10, r7
    pop     {{r4, r6, r7}}
    pop     {{r3}}
    mov     lr, r3
    bx      lr
8:
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4, r6, r7}}
    pop     {{r3}}
    mov     lr, r3
    b       oxi_core_armv6m_resume_with_redirect

    .global oxi_core_armv6m_svcall_handler
    .type oxi_core_armv6m_svcall_handler, %function
    .thumb_func
oxi_core_armv6m_svcall_handler:
    mov     r0, lr
    ldr     r1, =0xfffffff9
    cmp     r0, r1
    bne     7f
    mrs     r0, msp
    ldr     r1, [r0, #24]
    ldr     r2, =oxi_core_armv6m_enter_svc_return
    cmp     r1, r2
    bne     7f
    b       oxi_core_armv6m_enter_from_svc
7:

    mov     r0, lr
    movs    r1, #4
    tst     r0, r1
    beq     1f
    mrs     r0, psp
    b       2f
1:
    mrs     r0, msp
2:
    push    {{r4, r6, r7, lr}}
    mov     r4, r0
    mov     r6, r9
    mov     r7, r10
    ldr     r0, ={kernel_static_base}
    mov     r9, r0
    mov     r10, r0
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r0, r4
    ldr     r1, [sp, #12] /* saved EXC_RETURN, before any BL */
    bl      oxi_core_armv6m_svcall_dispatch
    str     r0, [r4, #0]
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_armv6m_svcall_take_redirect
    cmp     r0, #0
    beq     3f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4, r6, r7}}
    pop     {{r3}}
    mov     lr, r3
    b       oxi_core_armv6m_resume_with_redirect
3:
    add     sp, sp, #16
    bl      oxi_core_isolation_resume_rustlet_execution
    mov     r9, r6
    mov     r10, r7
    pop     {{r4, r6, r7}}
    pop     {{r3}}
    mov     lr, r3
    bx      lr

    .global oxi_core_armv6m_hardfault_handler
    .type oxi_core_armv6m_hardfault_handler, %function
    .thumb_func
oxi_core_armv6m_hardfault_handler:
    mov     r0, lr
    movs    r1, #12
    ands    r0, r1
    cmp     r0, #12
    bne     1f
    mrs     r2, psp
    movs    r1, #1
    b       2f
1:
    mrs     r2, msp
    movs    r1, #0
2:
    push    {{r4-r6, lr}}
    mov     r4, r1
    mov     r5, r2
    ldr     r2, ={kernel_static_base}
    mov     r9, r2
    mov     r10, r2
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r1, r4
    mov     r2, r5
    bl      oxi_core_armv6m_hardfault_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_armv6m_svcall_take_redirect
    cmp     r0, #0
    beq     3f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4-r6}}
    pop     {{r3}}
    mov     lr, r3
    b       oxi_core_armv6m_resume_with_redirect
3:
    add     sp, sp, #16
    pop     {{r4-r6}}
    pop     {{r3}}
    mov     lr, r3
    ldr     r0, =oxi_core_armv6m_hardfault_fatal
    movs    r1, #1
    orrs    r0, r1
    bx      r0


    .thumb_func
oxi_core_armv6m_enter_from_svc:
    ldr     r0, [r0, #0]
    push    {{r4-r6, lr}}
    mov     r4, r0
    bl      oxi_core_prepare_app_exception_frame
    mov     r5, r0
    ldr     r6, [r4, #4]
    bl      oxi_core_isolation_enter_rustlet_execution
    msr     PSP, r5
    mov     r9, r6
    mov     r10, r6
    pop     {{r4-r7}}
    add     sp, sp, #32
    movs    r4, #0
    mov     r5, r4
    mov     r6, r4
    mov     r7, r4
    mov     r8, r4
    mov     r11, r4
    movs    r0, #3
    msr     CONTROL, r0
    isb
    ldr     r0, =0xfffffffd
    bx      r0

    .global oxi_core_armv6m_run_isolated_app
    .type oxi_core_armv6m_run_isolated_app, %function
    .thumb_func
oxi_core_armv6m_run_isolated_app:
    push    {{r4-r7, lr}}
    mov     r4, r8
    mov     r5, r9
    mov     r6, r10
    mov     r7, r11
    push    {{r4-r7}}
    sub     sp, sp, #4
    svc     #0
    .global oxi_core_armv6m_enter_svc_return
oxi_core_armv6m_enter_svc_return:
    udf     #0

    .global oxi_core_armv6m_resume_isolated_app
    .type oxi_core_armv6m_resume_isolated_app, %function
    .thumb_func
oxi_core_armv6m_resume_isolated_app:
    mov     r4, r0
    mov     r5, r1
    bl      oxi_core_isolation_resume_cleanup
    mov     r0, r4
    mov     r1, r5
    add     sp, sp, #4
    pop     {{r4-r7}}
    mov     r8, r4
    mov     r9, r5
    mov     r10, r6
    mov     r11, r7
    pop     {{r4-r7, pc}}

    .global oxi_core_armv6m_resume_with_redirect
    .type oxi_core_armv6m_resume_with_redirect, %function
    .thumb_func
oxi_core_armv6m_resume_with_redirect:
    ldr     r3, ={kernel_static_base}
    mov     r9, r3
    mov     r10, r3
    movs    r3, #0
    msr     CONTROL, r3
    isb
    sub     sp, sp, #32
    str     r0, [sp, #0]
    str     r1, [sp, #4]
    str     r3, [sp, #8]
    str     r3, [sp, #12]
    str     r3, [sp, #16]
    str     r3, [sp, #20]
    str     r2, [sp, #24]
    ldr     r0, =0x01000000
    str     r0, [sp, #28]
    ldr     r0, =0xFFFFFFF9
    mov     lr, r0
    bx      lr
"#,
    kernel_static_base = const KERNEL_STATIC_BASE,
);

pub fn syscall_initialize() {
    if initialized() {
        return;
    }

    set_initialized(true);
}

pub fn install_syscall_handler(number: SyscallNumber, handler: SyscallHandler) {
    set_syscall_handler(number, handler);
}

pub fn syscall_table_debug_addr() -> usize {
    core::ptr::addr_of!(SYSCALL_TABLE) as usize
}

pub fn syscall_handler_debug_addr(number: SyscallNumber) -> usize {
    syscall_handler(number)
        .map(|handler| handler as usize)
        .unwrap_or(0)
}

pub fn request_syscall_thread_redirect(pc: usize, r0: usize, r1: usize) {
    set_pending_redirect(Some(RedirectState {
        r0: r0 as u32,
        r1: r1 as u32,
        // Exception-return frames carry Thumb state in xPSR.T; stacked PC
        // itself must remain halfword-aligned.
        pc: (pc & !1) as u32,
    }));
}

/// # Safety
/// Entry, arguments and stack must satisfy the validated AppExecution contract.
pub unsafe fn run_isolated_app(
    entry_pc: usize,
    app_gp: usize,
    arg0: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    stack_top: usize,
) -> Option<crate::core::isolation::AppReturnRegisters> {
    if entry_pc > u32::MAX as usize
        || app_gp > u32::MAX as usize
        || arg0 > u32::MAX as usize
        || arg1 > u32::MAX as usize
        || arg2 > u32::MAX as usize
        || arg3 > u32::MAX as usize
        || stack_top > u32::MAX as usize
        || stack_top < core::mem::size_of::<ExceptionFrame>()
        || !stack_top.is_multiple_of(8)
    {
        return None;
    }

    let entry = TargetAppEntry {
        entry_pc: entry_pc as u32,
        app_gp: app_gp as u32,
        arg0: arg0 as u32,
        arg1: arg1 as u32,
        arg2: arg2 as u32,
        arg3: arg3 as u32,
        stack_top: stack_top as u32,
    };

    let registers = unsafe { oxi_core_armv6m_run_isolated_app(&entry) };
    Some(crate::core::isolation::AppReturnRegisters {
        r0: registers as u32 as usize,
        r1: (registers >> 32) as u32 as usize,
    })
}

pub fn isolated_app_gate_region() -> Option<crate::core::target::AppGateRegion> {
    let base = aligned_app_gate_region() as usize;

    Some(crate::core::target::AppGateRegion {
        base,
        size: APP_GATE_REGION_SIZE,
    })
}

pub fn kernel_stack_guard_initialize() {
    if mpu_region_count() <= KERNEL_STACK_GUARD_REGION {
        return;
    }

    let guard_base = kernel_stack_guard_base();
    let result = mpu_set_region(
        KERNEL_STACK_GUARD_REGION,
        &MpuRegionConfig {
            base_addr: guard_base,
            size: KERNEL_STACK_GUARD_SIZE,
            access: MpuAccess::NoAccess,
            privilege: MpuPrivilege::PrivilegedOnly,
            executable: false,
            disabled_subregions: 0,
        },
    )
    .and_then(|_| mpu_enable());

    if result.is_err() {
        crate::consoleln!(
            "kernel stack guard setup failed: base=0x{:08x} size={}",
            guard_base,
            KERNEL_STACK_GUARD_SIZE
        );
    }
}

/// ARMv6-M has no MSPLIM register.
pub fn kernel_stack_overflow_protection(_stack: crate::core::isolation::AppMemoryWindow) {}

/// ARMv6-M has no PSPLIM register.
pub fn app_stack_overflow_protection(_stack: Option<crate::core::isolation::AppMemoryWindow>) {}

#[inline(never)]
pub fn kernel_stack_guard_test_touch() {
    unsafe {
        write_volatile(addr_of_mut!(KERNEL_STACK_GUARD_TEST_ACTIVE), 1);
        // Deliberate hardware fault; a trapping Rust volatile write would
        // violate its pointer contract before it could test the MPU.
        core::arch::asm!("strb r1, [r0]", in("r0") kernel_stack_guard_base(), in("r1") 0x5au32, options(nostack));
        write_volatile(addr_of_mut!(KERNEL_STACK_GUARD_TEST_ACTIVE), 0);
    }
    crate::consoleln!("kernel stack guard test did not fault");
    crate::core::shutdown(1)
}

#[inline(never)]
pub fn kernel_ram_execute_never_test_touch() -> bool {
    if crate::core::target::kernel_ram_execute_never_windows()
        .iter()
        .all(Option::is_none)
    {
        return false;
    }

    #[repr(align(4))]
    struct RamCode([u16; 1]);

    static mut RAM_CODE: RamCode = RamCode([0]);

    // Invariant: this test runs in kernel phase, after MPU initialization, so
    // region 6 must carry the privileged RAM-XN mapping where the target
    // declares one. Executing this RAM-resident `BX LR` must fault.
    let addr = unsafe { addr_of_mut!(RAM_CODE.0) as usize | 1 };
    unsafe {
        write_volatile((addr & !1) as *mut u16, 0x4770);
        mpu_sync();
    }
    // Deliberate NX fault. No Rust function pointer is fabricated from data.
    // The planted BX LR can return only if protection is ineffective.
    unsafe {
        core::arch::asm!("blx {entry}", entry = in(reg) addr, clobber_abi("C"));
    }
    true
}

pub fn last_mem_manage_fault() -> Option<crate::core::isolation::MemoryFaultInfo> {
    let status = unsafe { read_volatile(addr_of!(LAST_SOFT_MEMFAULT_STATUS)) };
    if status == 0 {
        return None;
    }

    let address = unsafe { read_volatile(addr_of!(LAST_SOFT_MEMFAULT_ADDRESS)) };
    let stacked_pc = unsafe { read_volatile(addr_of!(LAST_SOFT_MEMFAULT_STACKED_PC)) };
    let stacked_lr = unsafe { read_volatile(addr_of!(LAST_SOFT_MEMFAULT_STACKED_LR)) };
    Some(crate::core::isolation::MemoryFaultInfo {
        status,
        address: if address == 0 {
            None
        } else {
            Some(address as usize)
        },
        hfsr: 0,
        cfsr: 0,
        mmfar: None,
        bfar: None,
        stacked_pc: if stacked_pc == 0 {
            None
        } else {
            Some(stacked_pc as usize)
        },
        stacked_lr: if stacked_lr == 0 {
            None
        } else {
            Some(stacked_lr as usize)
        },
    })
}

pub fn mpu_enable() -> MpuResult<()> {
    if mpu_region_count() == 0 {
        return Err(MpuError::Unsupported);
    }

    program_kernel_nx_regions()?;

    unsafe {
        write_volatile(MPU_CTRL, MPU_CTRL_ENABLE | MPU_CTRL_PRIVDEFENA);
        mpu_sync();
    }
    Ok(())
}

fn program_kernel_nx_regions() -> MpuResult<()> {
    super::common_arm_m_profile::program_kernel_nx_regions(
        &super::kernel_ram_execute_never_windows(),
        mpu_region_count(),
        mpu_set_region,
    )
}

pub fn mpu_disable() -> MpuResult<()> {
    if mpu_region_count() == 0 {
        return Err(MpuError::Unsupported);
    }

    unsafe {
        write_volatile(MPU_CTRL, 0);
        mpu_sync();
    }
    Ok(())
}

pub fn mpu_set_region(region: MpuRegion, config: &MpuRegionConfig) -> MpuResult<()> {
    validate_region(region)?;
    validate_region_config(config)?;

    let region_size_encoding = encode_region_size(config.size)?;
    let access_bits = encode_access_bits(config.access, config.privilege);

    let mut rasr = MPU_RASR_ENABLE | (region_size_encoding << MPU_RASR_SIZE_SHIFT);
    rasr |= access_bits << MPU_RASR_AP_SHIFT;
    rasr |= u32::from(config.disabled_subregions) << 8;

    if !config.executable {
        rasr |= MPU_RASR_XN;
    }

    // RNR selects the bank subsequently accessed through RBAR/RASR. Keep
    // that selector stable if the periodic interrupt also updates the MPU.
    let primask = interrupts_save_and_disable();
    unsafe {
        write_volatile(MPU_RNR, region as u32);
        write_volatile(MPU_RBAR, config.base_addr as u32);
        write_volatile(MPU_RASR, rasr);
        mpu_sync();
    }
    interrupts_restore(primask);
    Ok(())
}

pub fn mpu_unset_region(region: MpuRegion) -> MpuResult<()> {
    validate_region(region)?;

    let primask = interrupts_save_and_disable();
    unsafe {
        write_volatile(MPU_RNR, region as u32);
        write_volatile(MPU_RBAR, 0);
        write_volatile(MPU_RASR, 0);
        mpu_sync();
    }
    interrupts_restore(primask);
    Ok(())
}

pub fn protect_kernel_nx(enabled: bool) {
    let unset_kernel_nx_regions = || -> MpuResult<()> {
        for window in crate::core::target::kernel_ram_execute_never_windows()
            .iter()
            .flatten()
        {
            if mpu_region_count() > window.region {
                mpu_unset_region(window.region)?;
            }
        }
        Ok(())
    };
    let result = if enabled {
        program_kernel_nx_regions()
    } else {
        unset_kernel_nx_regions()
    };

    if result.is_err() {
        crate::consoleln!("kernel NX update failed: enabled={}", enabled);
    }
}

#[inline(always)]
pub unsafe fn mpu_set_region_executable_unchecked(region: MpuRegion, executable: bool) {
    // SAFETY: the caller validated the active region; IRQ masking keeps RNR stable.
    let primask = interrupts_save_and_disable();
    unsafe { write_volatile(MPU_RNR, region as u32) };
    let mut rasr = unsafe { read_volatile(MPU_RASR) };
    if executable {
        rasr &= !MPU_RASR_XN;
    } else {
        rasr |= MPU_RASR_XN;
    }
    unsafe { write_volatile(MPU_RASR, rasr) };
    mpu_sync();
    interrupts_restore(primask);
}

fn initialized() -> bool {
    INITIALIZED.load(Ordering::Relaxed)
}

fn set_initialized(value: bool) {
    INITIALIZED.store(value, Ordering::Relaxed);
}

fn syscall_handler(number: SyscallNumber) -> Option<SyscallHandler> {
    unsafe {
        let table = addr_of!(SYSCALL_TABLE) as *const Option<SyscallHandler>;
        read_volatile(table.add(number as usize))
    }
}

fn set_syscall_handler(number: SyscallNumber, handler: SyscallHandler) {
    unsafe {
        let table = addr_of_mut!(SYSCALL_TABLE) as *mut Option<SyscallHandler>;
        write_volatile(table.add(number as usize), Some(handler));
    }
}

fn pending_redirect() -> Option<RedirectState> {
    unsafe { read_volatile(addr_of!(PENDING_REDIRECT)) }
}

fn set_pending_redirect(redirect: Option<RedirectState>) {
    unsafe {
        write_volatile(addr_of_mut!(PENDING_REDIRECT), redirect);
    }
}

fn set_soft_memfault(status: u32, address: Option<u32>, frame: Option<&ExceptionFrame>) {
    let stacked_pc = frame.map(|frame| frame.pc).unwrap_or(0);
    let stacked_lr = frame.map(|frame| frame.lr).unwrap_or(0);
    unsafe {
        write_volatile(addr_of_mut!(LAST_SOFT_MEMFAULT_STATUS), status);
        write_volatile(
            addr_of_mut!(LAST_SOFT_MEMFAULT_ADDRESS),
            address.unwrap_or(0),
        );
        write_volatile(addr_of_mut!(LAST_SOFT_MEMFAULT_STACKED_PC), stacked_pc);
        write_volatile(addr_of_mut!(LAST_SOFT_MEMFAULT_STACKED_LR), stacked_lr);
    }
}

fn aligned_app_gate_region() -> *mut u8 {
    let base =
        addr_of_mut!(APP_GATE_REGION_STORAGE) as *mut [u8; APP_GATE_REGION_SIZE * 2] as usize;
    let aligned = (base + (APP_GATE_REGION_SIZE - 1)) & !(APP_GATE_REGION_SIZE - 1);
    aligned as *mut u8
}

/// Assembly-only entry with a caller-provided exception/redirect buffer.
///
/// # Safety
/// The exception veneer must supply the correctly aligned, live ABI frame or
/// output buffer, exclusively writable for redirect output. A nullable fault
/// frame may be null only on paths that explicitly handle an incomplete frame.
/// The veneer must establish the exception origin and preserve the owner-core
/// execution protocol before calling Rust.
#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_armv6m_svcall_dispatch(
    frame: *const ExceptionFrame,
    exc_return: u32,
) -> u32 {
    let frame = unsafe { &*frame };
    // SAFETY: the exception veneer supplies a frame from an executed SVC.
    let syscall_number = unsafe { decode_svc_immediate(frame.pc as usize) };
    let handler = syscall_handler(syscall_number);

    let Some(handler) = handler else {
        return super::common_arm_m_profile::reject_unknown_syscall(
            syscall_number,
            exc_return,
            frame.xpsr,
        );
    };

    unsafe {
        handler(
            frame.r0 as usize,
            frame.r1 as usize,
            frame.r2 as usize,
            frame.r3 as usize,
        ) as u32
    }
}

/// Assembly-only entry with a caller-provided exception/redirect buffer.
///
/// # Safety
/// The exception veneer must supply the correctly aligned, live ABI frame or
/// output buffer, exclusively writable for redirect output. A nullable fault
/// frame may be null only on paths that explicitly handle an incomplete frame.
/// The veneer must establish the exception origin and preserve the owner-core
/// execution protocol before calling Rust.
#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_armv6m_svcall_take_redirect(out: *mut RedirectState) -> u32 {
    let pending = pending_redirect();
    let Some(redirect) = pending else {
        return 0;
    };

    set_pending_redirect(None);
    unsafe { *out = redirect };

    1
}

/// Records an ARMv6-M HardFault without dereferencing its unproven frame.
///
/// # Safety
/// The exception veneer must establish the owner-core kernel execution phase
/// and supply the saved fault origin. The raw frame argument is ignored and
/// need not point to a complete or readable hardware frame. Recovery requires
/// the existing active-call context; this function is not a user entry point.
#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_armv6m_hardfault_dispatch(
    entered_kernel_from_rustlet: u32,
    used_psp: u32,
    _frame: *const ExceptionFrame,
) {
    let mut status = ARMV6M_SOFT_MEMFAULT_STATUS;
    if used_psp != 0 {
        status |= ARMV6M_SOFT_MEMFAULT_FROM_PSP;
    }
    // ARMv6-M has no stacking-error status to prove that this frame completed.
    // Preserve fault origin, but report PC/LR as unavailable instead of reading
    // a potentially invalid PSP after a stack-overflow HardFault.
    set_soft_memfault(status, None, None);

    // ARMv6-M has no MemManage exception. A HardFault raised while the
    // isolation phase is Rustlet is the target backend's recoverable MPU-fault
    // path; other HardFaults remain fatal kernel/porting failures.
    let control: u32;
    // SAFETY: CONTROL retains the interrupted Thread privilege indication.
    unsafe {
        core::arch::asm!("mrs {}, CONTROL", out(reg) control, options(nomem, nostack, preserves_flags));
    }
    if entered_kernel_from_rustlet == 0
        || used_psp == 0
        || control & 1 == 0
        || !crate::core::isolation::app_call_active()
    {
        oxi_core_armv6m_hardfault_fatal();
    }

    crate::core::isolation::handle_memory_fault();
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_armv6m_hardfault_fatal() -> ! {
    if kernel_stack_guard_test_active() {
        crate::consoleln!("kernel ARMv6-M HardFault: kernel stack overflow suspected");
        crate::core::shutdown(1);
    }

    if let Some(info) = last_mem_manage_fault() {
        let stacked_pc = info.stacked_pc.unwrap_or(0);
        let stacked_lr = info.stacked_lr.unwrap_or(0);
        crate::consoleln!(
            "fatal ARMv6-M HardFault: status=0x{:08x} hfsr=0x{:08x} cfsr=0x{:08x} mmfar=0x{:08x} bfar=0x{:08x} pc=0x{:08x} lr=0x{:08x}",
            info.status,
            info.hfsr,
            info.cfsr,
            info.mmfar.unwrap_or(0),
            info.bfar.unwrap_or(0),
            stacked_pc,
            stacked_lr
        );
    } else {
        crate::consoleln!("fatal ARMv6-M HardFault");
    }
    crate::core::shutdown(1)
}

fn mpu_region_count() -> u8 {
    unsafe { ((read_volatile(MPU_TYPE) >> MPU_REGION_COUNT_SHIFT) & MPU_REGION_COUNT_MASK) as u8 }
}

fn validate_region(region: MpuRegion) -> MpuResult<()> {
    if mpu_region_count() == 0 {
        return Err(MpuError::Unsupported);
    }
    if region >= mpu_region_count() {
        return Err(MpuError::InvalidRegion);
    }
    Ok(())
}

fn validate_region_config(config: &MpuRegionConfig) -> MpuResult<()> {
    if config.disabled_subregions != 0 && config.size < 256 {
        return Err(MpuError::InvalidSize);
    }
    if config.base_addr == 0 {
        return Err(MpuError::InvalidAddress);
    }
    if config.size < MPU_MIN_REGION_SIZE || !config.size.is_power_of_two() {
        return Err(MpuError::InvalidSize);
    }
    if config.base_addr % config.size != 0 {
        return Err(MpuError::UnalignedAddress);
    }
    Ok(())
}

fn encode_region_size(size: usize) -> MpuResult<u32> {
    if size < MPU_MIN_REGION_SIZE || !size.is_power_of_two() {
        return Err(MpuError::InvalidSize);
    }
    Ok(size.trailing_zeros() - 1)
}

fn encode_access_bits(access: MpuAccess, privilege: MpuPrivilege) -> u32 {
    match (access, privilege) {
        (MpuAccess::NoAccess, _) => MPU_AP_NO_ACCESS,
        (MpuAccess::ReadOnly, MpuPrivilege::PrivilegedOnly) => MPU_AP_PRIVILEGED_RO,
        (MpuAccess::ReadOnly, MpuPrivilege::Unprivileged) => MPU_AP_PRIVILEGED_RO_UNPRIVILEGED_RO,
        (MpuAccess::ReadWrite, MpuPrivilege::PrivilegedOnly) => MPU_AP_PRIVILEGED_RW,
        (MpuAccess::ReadWrite, MpuPrivilege::Unprivileged) => MPU_AP_PRIVILEGED_RW_UNPRIVILEGED_RW,
    }
}

fn kernel_stack_guard_base() -> usize {
    crate::core::target::kernel_stack_guard_window()
        .map(|(base, _)| base)
        .unwrap_or(0)
}

fn kernel_stack_guard_test_active() -> bool {
    unsafe { read_volatile(addr_of!(KERNEL_STACK_GUARD_TEST_ACTIVE)) != 0 }
}

#[inline(always)]
fn mpu_sync() {
    super::common_arm_m_profile::synchronize();
}

unsafe extern "C" {
    fn oxi_core_armv6m_run_isolated_app(entry: *const TargetAppEntry) -> u64;
}
