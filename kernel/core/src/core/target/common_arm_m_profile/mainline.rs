//! Exception entry/return shared by ARMv7-M and ARMv8-M Mainline.
//! ARMv6-M keeps its own instruction sequences and HardFault recovery path.
use super::{decode_svc_immediate, ExceptionFrame, RedirectState, TargetAppEntry};
use crate::core::syscall::{SyscallHandler, SyscallNumber};
use core::arch::global_asm;
use core::ptr::{addr_of, addr_of_mut, read_volatile, write_volatile};
use core::sync::atomic::{AtomicBool, Ordering};

const SCB_SHCSR: *mut u32 = 0xE000_ED24 as *mut u32;
const SCB_CFSR: *mut u32 = 0xE000_ED28 as *mut u32;
const SCB_DFSR: *mut u32 = 0xE000_ED30 as *mut u32;
const SCB_HFSR: *mut u32 = 0xE000_ED2C as *mut u32;
const SCB_MMFAR: *const u32 = 0xE000_ED34 as *const u32;
const SCB_BFAR: *const u32 = 0xE000_ED38 as *const u32;
const MAX_SYSCALL_COUNT: usize = 256;
const SCB_SHCSR_MEMFAULTENA: u32 = 1 << 16;
const SCB_SHCSR_BUSFAULTENA: u32 = 1 << 17;
const SCB_SHCSR_USGFAULTENA: u32 = 1 << 18;
const SCB_CFSR_MEMFAULT_MASK: u32 = 0xff;
const SCB_CFSR_USAGEFAULT_MASK: u32 = 0xffff_0000;
// Do not inspect incomplete frames or frames rejected during exception return.
const INCOMPLETE_FRAME: u32 = (0x38 << 8) | 0x38 | (1 << 20) | (1 << 18);
const SCB_CFSR_MMARVALID: u32 = 1 << 7;
const SCB_CFSR_BFARVALID: u32 = 1 << 15;

const KERNEL_STATIC_BASE: usize = crate::core::target::FAE_STATIC_BASE;
const APP_GATE_REGION_SIZE: usize = crate::core::isolation::APP_GATE_REGION_SIZE;

#[derive(Clone, Copy)]
struct MemManageFaultState {
    status: u32,
    address: u32,
    hfsr: u32,
    cfsr: u32,
    mmfar: u32,
    bfar: u32,
    stacked_pc: u32,
    stacked_lr: u32,
}

static INITIALIZED: AtomicBool = AtomicBool::new(false);
static mut SYSCALL_TABLE: [Option<SyscallHandler>; MAX_SYSCALL_COUNT] = [None; MAX_SYSCALL_COUNT];
static mut APP_GATE_REGION_STORAGE: [u8; APP_GATE_REGION_SIZE * 2] = [0; APP_GATE_REGION_SIZE * 2];
static mut PENDING_REDIRECT: Option<RedirectState> = None;
static mut LAST_MEM_MANAGE_STATUS: u32 = 0;
static mut LAST_MEM_MANAGE_ADDRESS: u32 = 0;
static mut LAST_MEM_MANAGE_HFSR: u32 = 0;
static mut LAST_MEM_MANAGE_CFSR: u32 = 0;
static mut LAST_MEM_MANAGE_MMFAR: u32 = 0;
static mut LAST_MEM_MANAGE_BFAR: u32 = 0;
static mut LAST_MEM_MANAGE_STACKED_PC: u32 = 0;
static mut LAST_MEM_MANAGE_STACKED_LR: u32 = 0;

global_asm!(
    r#"
    .syntax unified
    .thumb

    .global oxi_core_svcall_handler_ptr
    .type oxi_core_svcall_handler_ptr, %function
    .thumb_func
oxi_core_svcall_handler_ptr:
    adr     r0, oxi_core_svcall_handler
    orr.w   r0, r0, #1
    bx      lr

    .global oxi_core_resume_isolated_app_ptr
    .type oxi_core_resume_isolated_app_ptr, %function
    .thumb_func
oxi_core_resume_isolated_app_ptr:
    adr     r0, oxi_core_resume_isolated_app
    orr.w   r0, r0, #1
    bx      lr

    .global oxi_core_mem_manage_handler_ptr
    .type oxi_core_mem_manage_handler_ptr, %function
    .thumb_func
oxi_core_mem_manage_handler_ptr:
    adr     r0, oxi_core_mem_manage_handler
    orr.w   r0, r0, #1
    bx      lr

    .global oxi_core_usage_fault_handler_ptr
    .type oxi_core_usage_fault_handler_ptr, %function
    .thumb_func
oxi_core_usage_fault_handler_ptr:
    adr     r0, oxi_core_usage_fault_handler
    orr.w   r0, r0, #1
    bx      lr

    .global oxi_core_periodic_timer_interrupt_handler
    .type oxi_core_periodic_timer_interrupt_handler, %function
    .global oxi_core_periodic_timer_interrupt_handler_ptr
    .type oxi_core_periodic_timer_interrupt_handler_ptr, %function
    .thumb_func
oxi_core_periodic_timer_interrupt_handler_ptr:
    adr     r0, oxi_core_periodic_timer_interrupt_handler
    orr.w   r0, r0, #1
    bx      lr

    .thumb_func
oxi_core_periodic_timer_interrupt_handler:
    /* C callees preserve the remaining registers. Keep MSP aligned. */
    push    {{r4, r6, r7, lr}}
    mov     r6, r9
    mov     r7, r10
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r4, r0
    bl      oxi_core_periodic_timer_interrupt_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    bne     8f
    cmp     r4, #0
    beq     9f
    bl      oxi_core_isolation_resume_rustlet_execution
9:
    add     sp, sp, #16
    mov     r9, r6
    mov     r10, r7
    pop     {{r4, r6, r7, lr}}
    bx      lr
8:
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    mov     r9, r6
    mov     r10, r7
    pop     {{r4, r6, r7, lr}}
    b       oxi_core_resume_with_redirect

    .global oxi_core_svcall_handler
    .type oxi_core_svcall_handler, %function
    .thumb_func
oxi_core_svcall_handler:
    mov     r0, lr
    ldr     r1, =0xfffffff9
    cmp     r0, r1
    bne     7f
    mrs     r0, msp
    ldr     r1, [r0, #24]
    ldr     r2, =oxi_core_enter_svc_return
    cmp     r1, r2
    bne     7f
    b       oxi_core_enter_from_svc
7:

    tst     lr, #4
    ite     eq
    mrseq   r0, msp
    mrsne   r0, psp
    push    {{r4, r6, r7, lr}}
    mov     r4, r0
    mov     r6, r9
    mov     r7, r10
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r0, r4
    ldr     r1, [sp, #12] /* saved EXC_RETURN, before any BL */
    bl      oxi_core_svcall_dispatch
    str     r0, [r4, #0]
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    beq     1f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4, r6, r7, lr}}
    b       oxi_core_resume_with_redirect
1:
    bl      oxi_core_isolation_resume_rustlet_execution
    mov     r9, r6
    mov     r10, r7
    add     sp, sp, #16
    pop     {{r4, r6, r7, lr}}
    bx      lr

    .thumb_func
oxi_core_enter_from_svc:
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

    .global oxi_core_run_isolated_app
    .type oxi_core_run_isolated_app, %function
    .thumb_func
oxi_core_run_isolated_app:
    push    {{r4-r11, lr}}
    sub     sp, sp, #4
    svc     #0
    .global oxi_core_enter_svc_return
oxi_core_enter_svc_return:
    udf     #0

    .global oxi_core_resume_isolated_app
    .type oxi_core_resume_isolated_app, %function
    .thumb_func
oxi_core_resume_isolated_app:
    mov     r4, r0
    mov     r5, r1
    bl      oxi_core_isolation_resume_cleanup
    mov     r0, r4
    mov     r1, r5
    add     sp, sp, #4
    pop     {{r4-r11, pc}}

    .global oxi_core_mem_manage_handler
    .type oxi_core_mem_manage_handler, %function
    .thumb_func
oxi_core_mem_manage_handler:
    tst     lr, #4
    ite     eq
    mrseq   r4, msp
    mrsne   r4, psp
    mov     r5, lr
    /* Fault paths either terminate or restore the saved kernel context;
     * they never resume these application callee-saved registers. */
    push    {{r4-r6, lr}}
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r1, r4
    mov     r2, r5
    bl      oxi_core_mem_manage_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    beq     2f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    b       oxi_core_resume_with_redirect
2:
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    bl      oxi_core_mem_manage_fatal

    .global oxi_core_hardfault_handler
    .type oxi_core_hardfault_handler, %function
    .thumb_func
oxi_core_hardfault_handler:
    /* Native vectors forward only unprivileged Thread/PSP origins here.
     * Preserve the saved kernel MSP; never inspect or reset the failed PSP. */
    mrs     r4, psp
    mov     r5, lr
    push    {{r4-r6, lr}}
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r1, r4
    mov     r2, r5
    bl      oxi_core_hardfault_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    beq     2f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    b       oxi_core_resume_with_redirect
2:
    bl      oxi_core_hardfault_fatal

    .global oxi_core_usage_fault_handler
    .type oxi_core_usage_fault_handler, %function
    .thumb_func
oxi_core_usage_fault_handler:
    tst     lr, #4
    ite     eq
    mrseq   r4, msp
    mrsne   r4, psp
    mov     r5, lr
    /* Fault paths either terminate or restore the saved kernel context;
     * they never resume these application callee-saved registers. */
    push    {{r4-r6, lr}}
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r1, r4
    mov     r2, r5
    bl      oxi_core_usage_fault_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    beq     3f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    b       oxi_core_resume_with_redirect
3:
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    bl      oxi_core_usage_fault_fatal

    .global oxi_core_bus_fault_handler
    .type oxi_core_bus_fault_handler, %function
    .thumb_func
oxi_core_bus_fault_handler:
    tst     lr, #4
    ite     eq
    mrseq   r4, msp
    mrsne   r4, psp
    mov     r5, lr
    /* Fault paths either terminate or restore the saved kernel context;
     * they never resume these application callee-saved registers. */
    push    {{r4-r6, lr}}
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    bl      oxi_core_isolation_enter_kernel_execution
    mov     r1, r4
    mov     r2, r5
    bl      oxi_core_bus_fault_dispatch
    sub     sp, sp, #16
    mov     r0, sp
    bl      oxi_core_svcall_take_redirect
    cmp     r0, #0
    beq     3f
    ldr     r0, [sp, #0]
    ldr     r1, [sp, #4]
    ldr     r2, [sp, #8]
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    b       oxi_core_resume_with_redirect
3:
    add     sp, sp, #16
    pop     {{r4-r6, lr}}
    bl      oxi_core_bus_fault_fatal

    .global oxi_core_resume_with_redirect
    .type oxi_core_resume_with_redirect, %function
    .thumb_func
oxi_core_resume_with_redirect:
    ldr     r9, ={kernel_static_base}
    mov     r10, r9
    movs    r3, #0
    msr     control, r3
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
    ldr     lr, =0xFFFFFFF9
    bx      lr
"#,
    kernel_static_base = const KERNEL_STATIC_BASE,
);

pub fn syscall_initialize() {
    if initialized() {
        return;
    }

    set_initialized(true);
    unsafe {
        initialize_boot_exception_forwarding();
    }
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

    let registers = unsafe { oxi_core_run_isolated_app(&entry) };
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

pub fn last_mem_manage_fault() -> Option<crate::core::isolation::MemoryFaultInfo> {
    let fault = mem_manage_fault_state();
    if fault.status == 0 {
        return None;
    }

    let address = if fault.status & SCB_CFSR_MMARVALID != 0 {
        Some(fault.address as usize)
    } else {
        None
    };

    Some(crate::core::isolation::MemoryFaultInfo {
        status: fault.status,
        address,
        hfsr: fault.hfsr,
        cfsr: fault.cfsr,
        mmfar: if fault.cfsr & SCB_CFSR_MMARVALID != 0 {
            Some(fault.mmfar as usize)
        } else {
            None
        },
        bfar: if fault.cfsr & SCB_CFSR_BFARVALID != 0 {
            Some(fault.bfar as usize)
        } else {
            None
        },
        stacked_pc: if fault.stacked_pc == 0 {
            None
        } else {
            Some(fault.stacked_pc as usize)
        },
        stacked_lr: if fault.stacked_lr == 0 {
            None
        } else {
            Some(fault.stacked_lr as usize)
        },
    })
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
unsafe extern "C" fn oxi_core_svcall_dispatch(
    frame: *const ExceptionFrame,
    exc_return: u32,
) -> u32 {
    let frame = unsafe { &*frame };
    // SAFETY: the exception veneer supplies a frame from an executed SVC.
    let syscall_number = unsafe { decode_svc_immediate(frame.pc as usize) };
    let handler = syscall_handler(syscall_number);

    let Some(handler) = handler else {
        return super::reject_unknown_syscall(syscall_number, exc_return, frame.xpsr);
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

/// Capture fault state before clearing sticky flags, without trusting a failed PSP.
///
/// # Safety
/// Called only by exception veneers with the hardware EXC_RETURN and selected
/// hardware frame. The veneer establishes kernel execution before this call.
unsafe fn dispatch_fault(
    kind: &str,
    origin: u32,
    frame: *const ExceptionFrame,
    exc_return: u32,
    mask: u32,
) {
    let cfsr = unsafe { read_volatile(SCB_CFSR) };
    let hfsr = unsafe { read_volatile(SCB_HFSR) };
    let (stacked_pc, stacked_lr) = unsafe { fault_frame_registers(frame, cfsr, exc_return) };
    let mmfar = if cfsr & SCB_CFSR_MMARVALID != 0 {
        unsafe { read_volatile(SCB_MMFAR) }
    } else {
        0
    };
    let bfar = if cfsr & SCB_CFSR_BFARVALID != 0 {
        unsafe { read_volatile(SCB_BFAR) }
    } else {
        0
    };
    set_mem_manage_fault_state(MemManageFaultState {
        status: if cfsr == 0 { hfsr } else { cfsr & mask },
        address: mmfar,
        hfsr,
        cfsr,
        mmfar,
        bfar,
        stacked_pc,
        stacked_lr,
    });
    if origin == 0 && cfsr & SCB_CFSR_MMARVALID != 0 && kernel_stack_guard_contains(mmfar as usize)
    {
        crate::consoleln!("kernel MemManage: kernel stack overflow suspected hfsr=0x{:08x} cfsr=0x{:08x} mmfar=0x{:08x} pc=0x{:08x} lr=0x{:08x}", hfsr, cfsr, mmfar, stacked_pc, stacked_lr);
        crate::core::shutdown(1);
    }
    let control: u32;
    // SAFETY: CONTROL preserves the interrupted Thread privilege state.
    unsafe {
        core::arch::asm!("mrs {}, CONTROL", out(reg) control, options(nomem, nostack, preserves_flags));
    }
    let dfsr = unsafe { read_volatile(SCB_DFSR) };
    let breakpoint = crate::core::target::fault_policy::recoverable_breakpoint(
        origin != 0,
        crate::core::isolation::app_call_active(),
        exc_return,
        control,
        cfsr,
        hfsr,
        dfsr,
    );
    if !crate::core::target::fault_policy::recoverable(
        origin != 0,
        crate::core::isolation::app_call_active(),
        exc_return,
        control,
        cfsr,
        hfsr,
        cfg!(oxide_se_target_has_stack_limits),
    ) && !breakpoint
    {
        #[cfg(any(oxide_se_trace_semihosting, oxide_se_trace_jtag))]
        trace_fault_origin(kind, origin, exc_return);
        fault_fatal(kind);
    }
    // W1C only captured flags after attribution. Abandon PSP, including a failed
    // unstack operation, and redirect through the saved kernel return context.
    unsafe {
        write_volatile(SCB_CFSR, cfsr);
        write_volatile(SCB_HFSR, hfsr);
        if breakpoint {
            write_volatile(SCB_DFSR, dfsr);
        }
    }
    crate::core::isolation::handle_memory_fault();
}

#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_mem_manage_dispatch(
    origin: u32,
    frame: *const ExceptionFrame,
    exc_return: u32,
) {
    // SAFETY: forwarded directly from the matching exception veneer.
    unsafe {
        dispatch_fault(
            "MemManage",
            origin,
            frame,
            exc_return,
            SCB_CFSR_MEMFAULT_MASK,
        )
    };
}

#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_usage_fault_dispatch(
    origin: u32,
    frame: *const ExceptionFrame,
    exc_return: u32,
) {
    // SAFETY: forwarded directly from the matching exception veneer.
    unsafe {
        dispatch_fault(
            "UsageFault",
            origin,
            frame,
            exc_return,
            SCB_CFSR_USAGEFAULT_MASK,
        )
    };
}

#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_bus_fault_dispatch(
    origin: u32,
    frame: *const ExceptionFrame,
    exc_return: u32,
) {
    // SAFETY: forwarded directly from the matching exception veneer.
    unsafe { dispatch_fault("BusFault", origin, frame, exc_return, 0xff00) };
}

#[unsafe(no_mangle)]
unsafe extern "C" fn oxi_core_hardfault_dispatch(
    origin: u32,
    _frame: *const ExceptionFrame,
    exc_return: u32,
) {
    // SAFETY: escalation can invalidate the frame; omit its diagnostics entirely.
    unsafe { dispatch_fault("HardFault", origin, core::ptr::null(), exc_return, u32::MAX) };
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_mem_manage_fatal() -> ! {
    fault_fatal("MemManage")
}
#[unsafe(no_mangle)]
extern "C" fn oxi_core_usage_fault_fatal() -> ! {
    fault_fatal("UsageFault")
}
#[unsafe(no_mangle)]
extern "C" fn oxi_core_bus_fault_fatal() -> ! {
    fault_fatal("BusFault")
}
#[unsafe(no_mangle)]
extern "C" fn oxi_core_hardfault_fatal() -> ! {
    fault_fatal("HardFault")
}

fn fault_fatal(kind: &str) -> ! {
    if let Some(info) = last_mem_manage_fault() {
        crate::consoleln!("fatal {}: status=0x{:08x} hfsr=0x{:08x} cfsr=0x{:08x} mmfar=0x{:08x} bfar=0x{:08x} pc=0x{:08x} lr=0x{:08x}",
            kind, info.status, info.hfsr, info.cfsr, info.mmfar.unwrap_or(0), info.bfar.unwrap_or(0), info.stacked_pc.unwrap_or(0), info.stacked_lr.unwrap_or(0));
    } else {
        crate::consoleln!("fatal {}", kind);
    }
    crate::core::shutdown(1)
}

/// Describe the interrupted execution without reading its exception frame.
#[cfg(any(oxide_se_trace_semihosting, oxide_se_trace_jtag))]
#[cold]
#[inline(never)]
fn trace_fault_origin(kind: &str, rustlet_phase: u32, exc_return: u32) {
    let control: u32;
    // SAFETY: this runs in the exception handler before changing CONTROL.
    unsafe {
        core::arch::asm!("mrs {}, CONTROL", out(reg) control, options(nomem, nostack, preserves_flags));
    }
    let origin = if rustlet_phase != 0 && exc_return & 12 == 12 && control & 1 != 0 {
        "rustlet"
    } else {
        "kernel/transition"
    };
    crate::consoleln!(
        "fault entry: {} origin={} exc_return=0x{:08x} control=0x{:08x}",
        kind,
        origin,
        exc_return,
        control
    );
}

/// # Safety
/// With no stacking error, frame must identify the complete basic hardware
/// frame. Extended FP frames are not inspected. With a stacking
/// error the pointer need not be dereferenceable and is never accessed.
unsafe fn fault_frame_registers(
    frame: *const ExceptionFrame,
    cfsr: u32,
    exc_return: u32,
) -> (u32, u32) {
    if cfsr & INCOMPLETE_FRAME != 0
        || !matches!(exc_return, 0xffff_fff1 | 0xffff_fff9 | 0xffff_fffd)
        || frame.is_null()
    {
        return (0, 0);
    }
    // SAFETY: successful exception stacking initialized these two words. Raw
    // reads avoid lending a Rust reference into potentially faulting user data.
    unsafe {
        (
            read_volatile(addr_of!((*frame).pc)),
            read_volatile(addr_of!((*frame).lr)),
        )
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
unsafe extern "C" fn oxi_core_svcall_take_redirect(out: *mut RedirectState) -> u32 {
    let pending = pending_redirect();
    let Some(redirect) = pending else {
        return 0;
    };

    set_pending_redirect(None);
    unsafe { *out = redirect };

    1
}

unsafe fn initialize_boot_exception_forwarding() {
    let Some(boot_abi) = crate::core::target::boot_abi_region() else {
        return;
    };

    // SAFETY: the board layout reserves these writable boot ABI words;
    // each forwarded symbol implements the corresponding exception ABI.
    unsafe {
        write_volatile(
            boot_abi.svc_forward as *mut u32,
            oxi_core_svcall_handler_ptr() as usize as u32,
        );
        write_volatile(
            boot_abi.memmanage_forward as *mut u32,
            oxi_core_mem_manage_handler_ptr() as usize as u32,
        );
        write_volatile(
            boot_abi.usagefault_forward as *mut u32,
            oxi_core_usage_fault_handler_ptr() as usize as u32,
        );
        write_volatile(
            boot_abi.periodic_timer_forward as *mut u32,
            oxi_core_periodic_timer_interrupt_handler_ptr() as usize as u32,
        );
        write_volatile(
            SCB_SHCSR,
            read_volatile(SCB_SHCSR)
                | SCB_SHCSR_MEMFAULTENA
                | SCB_SHCSR_BUSFAULTENA
                | SCB_SHCSR_USGFAULTENA,
        );
        // A hardware divide by zero must not silently return zero. Normal
        // unaligned byte-buffer access remains supported by the existing ABI.
        let ccr = 0xe000_ed14 as *mut u32;
        write_volatile(ccr, read_volatile(ccr) | (1 << 4));
        core::arch::asm!("dsb", "isb", options(nostack, preserves_flags));
    }
}

fn aligned_app_gate_region() -> *mut u8 {
    let base =
        addr_of_mut!(APP_GATE_REGION_STORAGE) as *mut [u8; APP_GATE_REGION_SIZE * 2] as usize;
    let aligned = (base + (APP_GATE_REGION_SIZE - 1)) & !(APP_GATE_REGION_SIZE - 1);
    aligned as *mut u8
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

fn mem_manage_fault_state() -> MemManageFaultState {
    let status = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_STATUS)) };
    let address = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_ADDRESS)) };
    let hfsr = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_HFSR)) };
    let cfsr = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_CFSR)) };
    let mmfar = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_MMFAR)) };
    let bfar = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_BFAR)) };
    let stacked_pc = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_STACKED_PC)) };
    let stacked_lr = unsafe { read_volatile(addr_of!(LAST_MEM_MANAGE_STACKED_LR)) };
    MemManageFaultState {
        status,
        address,
        hfsr,
        cfsr,
        mmfar,
        bfar,
        stacked_pc,
        stacked_lr,
    }
}

fn set_mem_manage_fault_state(fault: MemManageFaultState) {
    unsafe {
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_STATUS), fault.status);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_ADDRESS), fault.address);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_HFSR), fault.hfsr);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_CFSR), fault.cfsr);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_MMFAR), fault.mmfar);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_BFAR), fault.bfar);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_STACKED_PC), fault.stacked_pc);
        write_volatile(addr_of_mut!(LAST_MEM_MANAGE_STACKED_LR), fault.stacked_lr);
    }
}

fn kernel_stack_guard_contains(address: usize) -> bool {
    let Some((base, size)) = crate::core::target::kernel_stack_guard_window() else {
        return false;
    };

    address >= base && address < base + size
}
unsafe extern "C" {
    fn oxi_core_svcall_handler_ptr() -> *const ();
    fn oxi_core_run_isolated_app(entry: *const TargetAppEntry) -> u64;
    fn oxi_core_mem_manage_handler_ptr() -> *const ();
    fn oxi_core_usage_fault_handler_ptr() -> *const ();
    fn oxi_core_periodic_timer_interrupt_handler_ptr() -> *const ();
}
