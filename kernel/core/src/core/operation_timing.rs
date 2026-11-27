//! Kernel-owned anticipation of opaque crypto/flash work, independent of caller identity.
//! Estimates feed NULL anticipation and APDU watchdog admission, not a certified WCET.
use core::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Copy, Debug)]
pub enum Operation {
    Aes(usize),
    Hash(usize),
    Random(usize),
    P256,
    FlashProgram,
    FlashErase,
}

mod pico1;
mod pico2;
// (base microseconds, microseconds per effective byte, minimum/maximum work).
struct MeasuredProfile {
    core_hz: u32,
    aes: (u32, u32, u32, u32),
    hash: (u32, u32, u32, u32),
    random: (u32, u32, u32, u32),
    p256: (u32, u32, u32, u32),
    flash_program: (u32, u32, u32, u32),
    flash_erase: (u32, u32, u32, u32),
}
impl MeasuredProfile {
    fn terms(&self, operation: Operation) -> ((u32, u32, u32, u32), usize) {
        match operation {
            Operation::Aes(n) => (self.aes, n),
            Operation::Hash(n) => (self.hash, n),
            Operation::Random(n) => (self.random, n),
            Operation::P256 => (self.p256, 0),
            Operation::FlashProgram => (self.flash_program, 0),
            Operation::FlashErase => (self.flash_erase, 0),
        }
    }
    fn projected(&self, operation: Operation, hz: u32) -> Option<u32> {
        if hz != self.core_hz {
            return None;
        }
        let (b, n) = self.terms(operation);
        Some(
            (b.0 as u64)
                .saturating_add((b.1 as u64).saturating_mul(n as u64))
                .min(u32::MAX as u64) as u32,
        )
    }
    fn estimate(&self, operation: Operation, hz: u32) -> Option<u32> {
        let (b, n) = self.terms(operation);
        if n < b.2 as usize || n > b.3 as usize {
            return None;
        }
        self.projected(operation, hz)
    }
}

static BEFORE: AtomicUsize = AtomicUsize::new(0);
pub type BeforeOperation = fn(u32) -> bool;

/// Installed once at firmware boot. No hook means no APDU transport exists yet.
pub fn install(handler: BeforeOperation) {
    BEFORE.store(handler as usize, Ordering::Release);
}

/// False means the transport could not reserve time; do not start the operation.
// SVC-PERF: svc=all; replay=all; see docs/kernel.developer.guide.md#svc-performance-maintenance.
pub fn before(operation: Operation) -> bool {
    let address = BEFORE.load(Ordering::Acquire);
    if address == 0 {
        return true;
    }
    // SAFETY: only install publishes a function with this exact signature.
    let handler: BeforeOperation = unsafe { core::mem::transmute(address) };
    handler(estimate_us(operation, crate::core::target::core_clock_hz()))
}

/// Hardware measurements override the initial table only for their board/clock.
/// Outside the measured size range, use the larger of the extrapolated envelope
/// and the initial estimate (never drop the budget at the range boundary).
/// CPU costs in the initial table scale with the configured
/// clock; flash/entropy waits do not. Hardware qualification must cover each
/// device/voltage/temperature and backend. An estimate >= one NULL interval
/// requests an immediate NULL if the separate APDU watchdog still admits it.
// SVC-PERF: svc=all; replay=all; see docs/kernel.developer.guide.md#svc-performance-maintenance.
pub fn estimate_us(operation: Operation, hz: u32) -> u32 {
    let measured = if cfg!(oxide_se_board_raspi_pico) {
        pico1::PROFILE.as_ref()
    } else if cfg!(oxide_se_board_raspi_pico2) {
        pico2::PROFILE.as_ref()
    } else {
        None
    };
    if let Some(us) = measured.and_then(|p| p.estimate(operation, hz)) {
        return us;
    }
    let (cycles, fixed_us) = match operation {
        Operation::Aes(bytes) => (
            20_000u64.saturating_add((bytes as u64).saturating_mul(600)),
            0,
        ),
        Operation::Hash(bytes) => (
            20_000u64.saturating_add((bytes as u64).saturating_mul(300)),
            0,
        ),
        Operation::Random(bytes) => (
            0,
            20_000u64.saturating_add((bytes as u64).saturating_mul(200)),
        ),
        // Fallback for unprofiled boards/clocks, not a proven upper bound.
        Operation::P256 => (60_000_000, 0),
        Operation::FlashProgram => (0, 10_000),
        Operation::FlashErase => (0, 400_000),
    };
    let cpu_us = cycles.saturating_mul(1_000_000).div_ceil(hz.max(1) as u64);
    let initial = cpu_us.saturating_add(fixed_us).min(u32::MAX as u64) as u32;
    if let Some(projected) = measured.and_then(|p| p.projected(operation, hz)) {
        return initial.max(projected);
    }
    initial
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn measured_profile_only_applies_to_its_clock_and_measured_range() {
        let p = MeasuredProfile {
            core_hz: 150_000_000,
            aes: (10, 2, 16, 1024),
            hash: (10, 2, 16, 1024),
            random: (10, 2, 16, 1024),
            p256: (123, 0, 0, 0),
            flash_program: (23, 0, 0, 0),
            flash_erase: (45, 0, 0, 0),
        };
        assert_eq!(p.estimate(Operation::Aes(16), 150_000_000), Some(42));
        assert_eq!(p.estimate(Operation::Aes(0), 150_000_000), None);
        assert_eq!(p.estimate(Operation::Aes(1025), 150_000_000), None);
        assert_eq!(p.estimate(Operation::P256, 12_000_000), None);
        assert_eq!(p.estimate(Operation::P256, 150_000_000), Some(123));
    }
    #[test]
    fn budgets_scale_with_work_and_clock_without_wrapping() {
        assert!(
            estimate_us(Operation::Aes(256), 12_000_000)
                > estimate_us(Operation::Aes(16), 12_000_000)
        );
        assert!(
            estimate_us(Operation::P256, 12_000_000) > estimate_us(Operation::P256, 150_000_000)
        );
        assert_eq!(
            estimate_us(Operation::FlashErase, 12_000_000),
            estimate_us(Operation::FlashErase, 150_000_000)
        );
        assert_eq!(estimate_us(Operation::Hash(usize::MAX), 1), u32::MAX);
    }
}
