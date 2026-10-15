//! Hardware fault injection, compiled only into the opt-in integrity module.

/// Force a UsageFault to escalate, or restore normal configurable handlers.
/// This diagnostic does not modify MPU permissions or application memory.
pub(super) fn set_escalation(enabled: bool) -> bool {
    #[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
    {
        let shcsr = 0xe000_ed24 as *mut u32;
        // SAFETY: privileged test-image access to the architectural register.
        unsafe {
            let current = core::ptr::read_volatile(shcsr);
            core::ptr::write_volatile(shcsr, if enabled { current & !(1 << 18) } else { current | (1 << 18) });
            core::arch::asm!("dsb", "isb", options(nostack, preserves_flags));
        }
        true
    }
    #[cfg(not(all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
    { let _ = enabled; false }
}

/// Install the deliberate exception-return corrupter only in this test image.
pub(super) fn initialize() {
    #[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
    oxi_core::core::syscall::install_handler(252, corrupt_exception_return);
}

/// # Safety
/// Called from the SVC veneer with its live, basic PSP frame. This test-only
/// hook never runs outside an active Rustlet call and accepts no user pointer.
#[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
unsafe extern "C" fn corrupt_exception_return(choice: usize, _: usize, _: usize, _: usize) -> usize {
    if !oxi_core::core::isolation::app_call_active() { return 0; }
    let psp: usize;
    // SAFETY: invoked by the diagnostic SVC with a successfully stacked frame.
    unsafe {
        core::arch::asm!("mrs {}, PSP", out(reg) psp, options(nomem, nostack, preserves_flags));
        match choice {
            5 => core::arch::asm!("msr PSP, {}", in(reg) 0x2001_0000usize, options(nomem, nostack, preserves_flags)),
            6 => {
                // IPSR != 0 is inconsistent with return to Thread mode.
                let xpsr = (psp + 28) as *mut u32;
                core::ptr::write_volatile(xpsr, core::ptr::read_volatile(xpsr) | 1);
            }
            _ => {},
        }
    }
    0
}
