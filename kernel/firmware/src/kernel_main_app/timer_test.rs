use super::{ApduFilter, KernelAppModule};
use crate::apdu_manager::ApduStatus;
use rustlet_runtime::SEApdu;

const INS_KERNEL_TIMER: u8 = 0x0a;

pub(crate) struct Module;

impl KernelAppModule for Module {
    fn initialize() {}
}

pub(crate) const APDU_FILTER: ApduFilter = ApduFilter {
    matches: matches,
    process: process,
};

fn matches(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == INS_KERNEL_TIMER
}

/// P1=1 waits twelve ticks; P1=2 waits 3.6 seconds of hardware time.
fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    let available = apdu.set_outgoing();
    if available < 12 {
        return ApduStatus::wrong_length();
    }

    if apdu.p1() == 3 {
        // A hardware clock must advance even while no SysTick can be serviced.
        // Exercise the real crypto preflight under the same exclusion as SVC.
        let (elapsed, ticks, nulls) = crate::core::target::with_interrupts_masked(|| {
            let start = crate::core::target::monotonic_ticks();
            let hz = crate::core::target::monotonic_hz();
            let ticks = crate::core::timer::interrupt_counts().0;
            while crate::core::target::monotonic_ticks().wrapping_sub(start) < hz / 5 {
                core::hint::spin_loop();
            }
            let before = crate::time_manager::anticipated_nulls();
            crate::time_manager::diagnostic_force_preflight(true);
            let key = crate::core::crypto::AesKey::from_bytes(&[0; 16]).unwrap();
            let result = crate::core::crypto::aes_ecb_encrypt_in_place(&key, &mut [0; 16]);
            crate::time_manager::diagnostic_force_preflight(false);
            if result.is_err() {
                return (0, 1, 0);
            }
            let elapsed = (crate::core::target::monotonic_ticks().wrapping_sub(start) as u64
                * 1_000_000
                / hz as u64) as u32;
            (
                elapsed,
                crate::core::timer::interrupt_counts().0.wrapping_sub(ticks),
                crate::time_manager::anticipated_nulls().wrapping_sub(before),
            )
        });
        for (i, value) in [elapsed, ticks, nulls].iter().enumerate() {
            apdu.buffer_mut()[i * 4..i * 4 + 4].copy_from_slice(&value.to_be_bytes());
        }
        apdu.set_outgoing_length(12);
        return ApduStatus::success();
    }
    if apdu.p1() == 8 {
        // Consume almost all of the shared APDU budget after UNWRAP. WRAP's
        // first opaque crypto call must fault, not receive a fresh SD budget.
        let start = crate::core::target::monotonic_ticks();
        let duration = (crate::core::target::monotonic_hz() as u64 * 93 / 10) as u32;
        while crate::core::target::monotonic_ticks().wrapping_sub(start) < duration {
            core::hint::spin_loop();
        }
        crate::time_manager::diagnostic_force_preflight(true);
    }
    if matches!(apdu.p1(), 4 | 5 | 6 | 8) {
        if !matches!(apdu.p1(), 5 | 8) {
            crate::time_manager::diagnostic_force_preflight(apdu.p1() == 4);
        }
        // Deterministic bytes include procedure/status lookalikes. Any NULL
        // incorrectly inserted into response data breaks the host comparison.
        apdu.buffer_mut()[..12]
            .copy_from_slice(&[0x60, 0x90, 0, 0x61, 0x60, 0x90, 0, 0x61, 1, 2, 3, 4]);
        apdu.set_outgoing_length(12);
        return ApduStatus::success();
    }

    if apdu.p1() == 2 {
        let start = crate::core::target::monotonic_ticks();
        let duration = (crate::core::target::monotonic_hz() as u64 * 36 / 10) as u32;
        while crate::core::target::monotonic_ticks().wrapping_sub(start) < duration {
            core::hint::spin_loop();
        }
    }

    let wait_ticks = match apdu.p1() {
        0 => 0,
        1 => 12,
        2 => 0,
        _ => return ApduStatus::incorrect_p1_p2(),
    };
    if wait_ticks != 0 {
        let start = crate::core::timer::interrupt_counts().0;
        while crate::core::timer::interrupt_counts()
            .0
            .saturating_sub(start)
            < wait_ticks
        {
            core::hint::spin_loop();
        }
    }

    let (top, bottom) = crate::core::timer::interrupt_counts();
    let top = top.to_be_bytes();
    let bottom = bottom.to_be_bytes();
    let nulls = crate::time_manager::null_bytes_sent().to_be_bytes();
    apdu.buffer_mut()[..4].copy_from_slice(&top);
    apdu.buffer_mut()[4..8].copy_from_slice(&bottom);
    apdu.buffer_mut()[8..12].copy_from_slice(&nulls);
    apdu.set_outgoing_length(12);
    ApduStatus::success()
}
