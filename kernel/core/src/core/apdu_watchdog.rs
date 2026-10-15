//! One non-renewable monotonic deadline for the entire physical APDU.
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

pub const TIMEOUT_US: u32 = 10_000_000;
static ACTIVE: AtomicBool = AtomicBool::new(false);
static DEADLINE: AtomicU32 = AtomicU32::new(0);
static REFUSED: AtomicBool = AtomicBool::new(false);
static STANDALONE: AtomicBool = AtomicBool::new(false);

fn ticks(us: u32) -> u32 {
    (us as u64 * super::target::monotonic_hz() as u64)
        .div_ceil(1_000_000)
        .min(i32::MAX as u64) as u32
}
fn due(now: u32, deadline: u32, ahead: u32) -> bool {
    now.wrapping_sub(deadline) as i32 >= 0 || deadline.wrapping_sub(now) <= ahead
}

/// Called once when the physical command header has arrived, never on data RX
/// or on entry into an application or delegated Security Domain.
pub fn begin() {
    super::target::with_interrupts_masked(|| {
        DEADLINE.store(
            super::target::monotonic_ticks().wrapping_add(ticks(TIMEOUT_US)),
            Ordering::Relaxed,
        );
        REFUSED.store(false, Ordering::Relaxed);
        ACTIVE.store(true, Ordering::Release);
    });
}
pub fn end() {
    ACTIVE.store(false, Ordering::Release);
}
/// Preserve the previous startup protection for calls made before any APDU
/// exists. Only those standalone calls own a per-invocation deadline.
pub(crate) fn enter_invocation() {
    let standalone = !ACTIVE.load(Ordering::Acquire);
    if standalone {
        begin();
    }
    STANDALONE.store(standalone, Ordering::Release);
}
pub(crate) fn leave_invocation() {
    if STANDALONE.load(Ordering::Acquire) {
        end();
        STANDALONE.store(false, Ordering::Release);
    }
}
pub(crate) fn expired() -> bool {
    ACTIVE.load(Ordering::Acquire)
        && (REFUSED.load(Ordering::Relaxed)
            || due(
                super::target::monotonic_ticks(),
                DEADLINE.load(Ordering::Relaxed),
                0,
            ))
}
/// Called by the shared NULL/operation preflight. Only record the refusal here:
/// the SVC dispatcher terminates after all handler-owned borrows are released.
pub fn admit_operation(estimated_with_margin_us: u32) -> bool {
    if !super::isolation::app_call_active() || !ACTIVE.load(Ordering::Acquire) {
        return true;
    }
    if REFUSED.load(Ordering::Relaxed)
        || due(
            super::target::monotonic_ticks(),
            DEADLINE.load(Ordering::Relaxed),
            ticks(estimated_with_margin_us),
        )
    {
        REFUSED.store(true, Ordering::Release);
        false
    } else {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn deadline_includes_svc_time_and_does_not_renew_with_io_or_invocations() {
        let header = 123;
        let deadline = header + 10_000_000;
        assert!(!due(header, deadline, 5_303_499));
        // A second P-256 call cannot fit, even though no SysTick ran in the first.
        assert!(due(header + 5_283_499, deadline, 5_303_499));
        // Delaying reception or changing SD/app invocation grants no fresh time.
        assert!(due(header + 9_999_000, deadline, 20_000));
        assert!(due(deadline, deadline, 0));
        assert!(due(deadline + 1, deadline, 0));
    }
    #[test]
    fn deadline_wrap_and_exact_fit_are_rejected() {
        let deadline = u32::MAX.wrapping_add(100);
        assert!(!due(u32::MAX - 50, deadline, 149));
        assert!(due(u32::MAX - 50, deadline, 150));
        assert!(due(99, deadline, 0));
        assert!(due(100, deadline, 0));
    }
}

/// Test-only late expiry, independent of host speed or measured SVC budgets.
#[cfg(all(oxide_se_redirect_probe, target_arch = "arm"))]
pub(crate) fn diagnostic_expire() {
    REFUSED.store(true, Ordering::Release);
}
