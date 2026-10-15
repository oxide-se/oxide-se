//! Diagnostic-only real SysTick injection. No timing estimates or production APDU.
#[cfg(all(oxide_se_redirect_probe, target_arch = "arm"))]
mod enabled {
    use core::sync::atomic::{AtomicU32, Ordering::Relaxed};
    static POINT: AtomicU32 = AtomicU32::new(0);
    static FIRED: AtomicU32 = AtomicU32::new(0);
    static DELIVERED: AtomicU32 = AtomicU32::new(0);
    static WAITING: AtomicU32 = AtomicU32::new(0);
    static NESTED: AtomicU32 = AtomicU32::new(0);
    static PUBLISHED: AtomicU32 = AtomicU32::new(0);
    static CONSUMED: AtomicU32 = AtomicU32::new(0);
    static ORIGIN: AtomicU32 = AtomicU32::new(0);
    static OBSERVING: AtomicU32 = AtomicU32::new(0);
    pub fn arm(point: u32) -> bool {
        if !(1..=5).contains(&point) {
            return false;
        }
        for value in [
            &FIRED, &DELIVERED, &WAITING, &NESTED, &PUBLISHED, &CONSUMED, &ORIGIN,
        ] {
            value.store(0, Relaxed);
        }
        OBSERVING.store(1, Relaxed);
        // SVC priority 128, SysTick priority 0: force actual SVC preemption.
        // HardFault and an active SysTick defer the injected tick architecturally.
        unsafe {
            core::ptr::write_volatile(0xe000_ed1f as *mut u8, 128);
            core::ptr::write_volatile(0xe000_ed23 as *mut u8, 0);
        }
        POINT.store(point, Relaxed);
        true
    }
    pub fn checkpoint(point: u32) {
        if POINT.load(Relaxed) != point {
            return;
        }
        POINT.store(0, Relaxed);
        crate::core::target::with_interrupts_masked(|| {
            FIRED.store(1, Relaxed);
            WAITING.store(1, Relaxed);
            let ipsr: u32;
            unsafe {
                core::arch::asm!("mrs {}, IPSR", out(reg) ipsr, options(nomem, nostack));
                core::ptr::write_volatile(0xe000_ed04 as *mut u32, 1 << 26);
                core::arch::asm!("dsb", "isb", "nop", "nop", options(nostack));
            }
            ORIGIN.store(ipsr, Relaxed);
        });
        unsafe {
            core::arch::asm!("isb", "nop", "nop", options(nostack));
        }
    }
    pub fn tick() -> bool {
        if WAITING.load(Relaxed) == 0 {
            return false;
        }
        WAITING.store(0, Relaxed);
        DELIVERED.store(DELIVERED.load(Relaxed) + 1, Relaxed);
        // Force a late watchdog decision after the return is committed. It
        // must not publish another continuation or retire the invocation twice.
        crate::core::apdu_watchdog::diagnostic_expire();
        assert!(
            !crate::core::isolation::watchdog_tick(),
            "late watchdog replaced committed return"
        );
        true // keep NULL protocol work out of the injected diagnostic tick
    }
    pub fn nested() {
        if OBSERVING.load(Relaxed) != 0 {
            NESTED.store(NESTED.load(Relaxed) + 1, Relaxed);
        }
    }
    pub fn published() {
        if OBSERVING.load(Relaxed) != 0 {
            PUBLISHED.store(PUBLISHED.load(Relaxed) + 1, Relaxed);
        }
    }
    pub fn consumed() {
        if OBSERVING.load(Relaxed) != 0 {
            CONSUMED.store(CONSUMED.load(Relaxed) + 1, Relaxed);
        }
    }
    pub fn report() -> [u32; 6] {
        OBSERVING.store(0, Relaxed);
        unsafe {
            core::ptr::write_volatile(0xe000_ed1f as *mut u8, 0);
            core::ptr::write_volatile(0xe000_ed23 as *mut u8, 255);
        }
        [
            FIRED.load(Relaxed),
            DELIVERED.load(Relaxed),
            NESTED.load(Relaxed),
            PUBLISHED.load(Relaxed),
            CONSUMED.load(Relaxed),
            ORIGIN.load(Relaxed),
        ]
    }
}
#[cfg(all(oxide_se_redirect_probe, target_arch = "arm"))]
pub use enabled::*;
#[cfg(not(all(oxide_se_redirect_probe, target_arch = "arm")))]
mod disabled {
    pub fn arm(_: u32) -> bool {
        false
    }
    pub fn report() -> [u32; 6] {
        [0; 6]
    }
    #[inline(always)]
    pub fn checkpoint(_: u32) {}
    #[inline(always)]
    pub fn tick() -> bool {
        false
    }
    #[inline(always)]
    pub fn nested() {}
    #[inline(always)]
    pub fn published() {}
    #[inline(always)]
    pub fn consumed() {}
}
#[cfg(not(all(oxide_se_redirect_probe, target_arch = "arm")))]
pub use disabled::*;
