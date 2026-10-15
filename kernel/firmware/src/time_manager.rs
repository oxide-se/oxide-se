//! T=0 NULL deadlines belong to the physical transport, not a Rustlet invocation.
//! SysTick checks elapsed hardware time; operation preflight checks both deadlines.
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use core::time::Duration;

const TIMER_PERIOD: Duration = Duration::from_millis(100);
const NULL_PERIOD_US: u32 = 500_000;
const OPERATION_MARGIN_US: u32 = 20_000;
const NULL_PROCEDURE_BYTE: u8 = 0x60;

static OPEN: AtomicBool = AtomicBool::new(false);
static DEADLINE: AtomicU32 = AtomicU32::new(0);
static NULL_BYTES_SENT: AtomicU32 = AtomicU32::new(0);
static ANTICIPATED_NULLS: AtomicU32 = AtomicU32::new(0);

#[derive(Clone, Copy, Default)]
struct Window {
    open: bool,
    deadline: u32,
}
impl Window {
    fn open(&mut self, now: u32, period: u32) {
        self.open = true;
        self.deadline = now.wrapping_add(period);
    }
    fn due(&self, now: u32, ahead: u32) -> bool {
        self.open
            && (now.wrapping_sub(self.deadline) as i32 >= 0
                || self.deadline.wrapping_sub(now) <= ahead)
    }
    fn service(
        &mut self,
        now: impl Fn() -> u32,
        period: u32,
        ahead: u32,
        send: impl FnOnce() -> bool,
    ) -> Result<bool, ()> {
        if !self.due(now(), ahead) {
            return Ok(false);
        }
        if !send() {
            return Err(());
        }
        // Only actual UART acceptance renews the deadline; never reset on failure.
        self.deadline = now().wrapping_add(period);
        Ok(true)
    }
}

// Test transports run concurrently on the host. Keep their timing state local.
#[cfg(test)]
std::thread_local! { static TEST_WINDOW: core::cell::Cell<Window> = const { core::cell::Cell::new(Window { open: false, deadline: 0 }) }; }

fn with_window<R>(run: impl FnOnce(&mut Window) -> R) -> R {
    #[cfg(test)]
    {
        TEST_WINDOW.with(|cell| {
            let mut w = cell.get();
            let result = run(&mut w);
            cell.set(w);
            result
        })
    }
    #[cfg(not(test))]
    {
        crate::core::target::with_interrupts_masked(|| {
            let mut w = Window {
                open: OPEN.load(Ordering::Relaxed),
                deadline: DEADLINE.load(Ordering::Relaxed),
            };
            let result = run(&mut w);
            DEADLINE.store(w.deadline, Ordering::Relaxed);
            OPEN.store(w.open, Ordering::Relaxed);
            result
        })
    }
}

#[cfg(test)]
pub(crate) fn test_window_open() -> bool {
    with_window(|w| w.open)
}

pub(crate) fn initialize() {
    OPEN.store(false, Ordering::Relaxed);
    NULL_BYTES_SENT.store(0, Ordering::Relaxed);
    ANTICIPATED_NULLS.store(0, Ordering::Relaxed);
    crate::core::target::monotonic_initialize();
    crate::core::operation_timing::install(before_blocking_operation);
    crate::core::timer::set_periodic_handler(periodic_tick, TIMER_PERIOD)
        .expect("periodic kernel time services are unavailable");
}

#[cfg(oxide_se_kernel_app_module = "timer-test")]
pub(crate) fn null_bytes_sent() -> u32 {
    NULL_BYTES_SENT.load(Ordering::Acquire)
}
#[cfg(oxide_se_kernel_app_module = "timer-test")]
pub(crate) fn anticipated_nulls() -> u32 {
    ANTICIPATED_NULLS.load(Ordering::Acquire)
}

fn ticks_for_us(us: u32) -> u32 {
    ((us as u64 * crate::core::target::monotonic_hz() as u64).div_ceil(1_000_000))
        .min(i32::MAX as u64) as u32
}

/// Transport has finished receiving the currently expected bytes (header or data).
/// This is not called by SVC entry/exit or internal SDDISPATCH messages.
pub(crate) fn transport_processing_started() {
    with_window(|w| {
        w.open(
            crate::core::target::monotonic_ticks(),
            ticks_for_us(NULL_PERIOD_US),
        )
    });
}

/// Close before an incoming-data ACK, outgoing procedure byte, payload or status.
/// Preparing output, returning from a Rustlet, wrapping and committing do not close it.
pub(crate) fn before_response_byte() {
    with_window(|w| {
        w.open = false;
        #[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
        PROFILING.store(false, Ordering::Relaxed);
    });
}

#[cfg(oxide_se_kernel_app_module = "timer-test")]
static FORCE_PREFLIGHT: AtomicBool = AtomicBool::new(false);
#[cfg(oxide_se_kernel_app_module = "timer-test")]
pub(crate) fn diagnostic_force_preflight(enable: bool) {
    FORCE_PREFLIGHT.store(enable, Ordering::Relaxed);
}

/// Allocation-free preflight; UART backpressure is retried for at most 10 ms.
/// Failure leaves the deadline pending and prevents starting the opaque operation.
fn before_blocking_operation(estimated_us: u32) -> bool {
    #[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
    if PROFILING.load(Ordering::Relaxed) {
        return true;
    }
    #[cfg(oxide_se_kernel_app_module = "timer-test")]
    let estimated_us = if FORCE_PREFLIGHT.load(Ordering::Relaxed) {
        NULL_PERIOD_US
    } else {
        estimated_us
    };
    let start = crate::core::target::monotonic_ticks();
    loop {
        if !crate::core::apdu_watchdog::admit_operation(
            estimated_us.saturating_add(OPERATION_MARGIN_US),
        ) {
            return false;
        }
        if service_null(estimated_us.saturating_add(OPERATION_MARGIN_US), true).is_ok() {
            return true;
        }
        // A full UART FIFO must drain before opaque work starts. Bound this
        // transport-only retry; never hold the timing-state IRQ mask while waiting.
        if crate::core::target::monotonic_ticks().wrapping_sub(start) >= ticks_for_us(10_000) {
            return false;
        }
        core::hint::spin_loop();
    }
}

fn service_null(ahead_us: u32, anticipated: bool) -> Result<bool, ()> {
    // Serialize due-check, UART write and renewal with the timer and transport.
    // Never block or access a Rustlet/registry borrow under this IRQ mask.
    with_window(|window| {
        if !window.open {
            return Ok(false);
        }
        let sent = window.service(
            crate::core::target::monotonic_ticks,
            ticks_for_us(NULL_PERIOD_US),
            ticks_for_us(ahead_us),
            || crate::core::serial::try_send_byte(NULL_PROCEDURE_BYTE),
        )?;
        if sent {
            NULL_BYTES_SENT.store(
                NULL_BYTES_SENT.load(Ordering::Relaxed).saturating_add(1),
                Ordering::Relaxed,
            );
            if anticipated {
                ANTICIPATED_NULLS.store(
                    ANTICIPATED_NULLS.load(Ordering::Relaxed).saturating_add(1),
                    Ordering::Relaxed,
                );
            }
        }
        Ok(sent)
    })
}

fn periodic_tick() {
    if crate::core::isolation::watchdog_tick() {
        return;
    }
    #[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
    let suspended = PROFILING.load(Ordering::Relaxed);
    #[cfg(not(any(test, oxide_se_kernel_app_module = "svc-profile")))]
    let suspended = false;
    if !suspended {
        let _ = service_null(0, false);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn profiling_requires_open_transport_and_restores_on_error() {
        with_window(|w| w.open = false);
        assert!(profile_begin().is_none());
        with_window(|w| w.open(0, 500));
        let attempt = || -> Result<(), ()> {
            let _guard = profile_begin().unwrap();
            assert!(profile_begin().is_none());
            assert!(before_blocking_operation(u32::MAX));
            Err(())
        };
        assert!(attempt().is_err());
        // Keep an overdue automatic NULL suppressed through response setup.
        assert!(PROFILING.load(Ordering::Relaxed));
        before_response_byte();
        assert!(!PROFILING.load(Ordering::Relaxed));
    }

    #[test]
    fn elapsed_time_not_callback_count_controls_nulls() {
        let mut w = Window::default();
        w.open(100, 1000);
        for _ in 0..1000 {
            assert_eq!(
                w.service(|| 101, 1000, 0, || panic!("early NULL")),
                Ok(false)
            );
        }
        assert_eq!(w.service(|| 5100, 1000, 0, || true), Ok(true));
        assert_eq!(w.deadline, 6100); // one byte, no burst to catch up missed ticks
    }
    #[test]
    fn anticipation_and_timer_share_one_deadline() {
        let mut w = Window::default();
        w.open(0, 1000);
        assert_eq!(w.service(|| 800, 1000, 199, || panic!()), Ok(false));
        assert_eq!(w.service(|| 800, 1000, 200, || true), Ok(true));
        assert_eq!(
            w.service(|| 1000, 1000, 0, || panic!("double NULL")),
            Ok(false)
        );
        assert_eq!(w.service(|| 1800, 1000, 0, || true), Ok(true));
    }
    #[test]
    fn failed_send_does_not_renew_and_success_uses_actual_send_time() {
        let mut w = Window::default();
        w.open(0, 1000);
        assert_eq!(w.service(|| 900, 1000, 200, || false), Err(()));
        assert_eq!(w.deadline, 1000);
        let now = core::cell::Cell::new(900);
        assert_eq!(
            w.service(
                || now.get(),
                1000,
                200,
                || {
                    now.set(910);
                    true
                }
            ),
            Ok(true)
        );
        assert_eq!(w.deadline, 1910);
    }
    #[test]
    fn oversized_operation_gets_one_null_without_requiring_it_to_fit() {
        let mut w = Window::default();
        w.open(0, 500_000);
        let sent = core::cell::Cell::new(0);
        assert_eq!(
            w.service(
                || 100,
                500_000,
                5_000_000,
                || {
                    sent.set(sent.get() + 1);
                    true
                }
            ),
            Ok(true)
        );
        assert_eq!(sent.get(), 1);
        assert_eq!(w.deadline, 500_100);
        // No callback runs during the indivisible operation. A real response
        // closes the transport window even though the deadline has elapsed.
        w.open = false;
        assert_eq!(
            w.service(|| 5_000_100, 500_000, 0, || panic!("late NULL in response")),
            Ok(false)
        );
    }

    #[test]
    fn closed_transport_forbids_nulls_even_for_long_operations() {
        let mut w = Window::default();
        for time in [0, 5000, u32::MAX] {
            assert_eq!(
                w.service(|| time, 1000, i32::MAX as u32, || panic!()),
                Ok(false)
            );
        }
        w.open(10, 1000);
        w.open = false; // ACK/data transfer or real response begins
        assert_eq!(w.service(|| 9000, 1000, 1000, || panic!()), Ok(false));
        w.open(9001, 1000); // all incoming data received
        assert_eq!(w.service(|| 9500, 1000, 501, || true), Ok(true));
    }
    #[test]
    fn deadlines_work_across_counter_wrap() {
        let mut w = Window::default();
        w.open(u32::MAX - 499, 1000);
        assert_eq!(w.deadline, 500);
        assert!(!w.due(u32::MAX, 499));
        assert!(w.due(u32::MAX, 501));
        assert!(!w.due(499, 0));
        assert!(w.due(500, 0));
    }
}

// Private diagnostic capability; unavailable in production configurations.
#[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
static PROFILING: AtomicBool = AtomicBool::new(false);
#[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
pub(crate) struct ProfileGuard;
#[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
impl Drop for ProfileGuard {
    fn drop(&mut self) {
        // An opaque sample may overrun the NULL deadline. Keep suppression
        // until the transport starts the real response, including error SWs;
        // restoring here could race a pending SysTick and emit a 51st NULL.
        with_window(|w| {
            if !w.open {
                PROFILING.store(false, Ordering::Relaxed);
            }
        });
    }
}
#[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
pub(crate) fn profile_begin() -> Option<ProfileGuard> {
    with_window(|w| {
        if !w.open || PROFILING.load(Ordering::Relaxed) {
            return None;
        }
        PROFILING.store(true, Ordering::Relaxed);
        Some(ProfileGuard)
    })
}
#[cfg(any(test, oxide_se_kernel_app_module = "svc-profile"))]
pub(crate) fn profile_send_null() -> bool {
    if !PROFILING.load(Ordering::Relaxed) {
        return false;
    }
    let start = crate::core::target::monotonic_ticks();
    loop {
        match service_null(NULL_PERIOD_US, false) {
            Ok(sent) => return sent,
            Err(()) => {}
        }
        if crate::core::target::monotonic_ticks().wrapping_sub(start) >= ticks_for_us(10_000) {
            return false;
        }
    }
}
