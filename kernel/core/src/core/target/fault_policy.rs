//! Pure classification of Mainline CPU faults; no interrupted-stack reads.
#![forbid(unsafe_code)]

pub(super) const ADDRESS_VALID: u32 = (1 << 7) | (1 << 15);
pub(super) const STACK_FAULTS: u32 = (1 << 3) | (1 << 4) | (1 << 11) | (1 << 12) | (1 << 20);
// Imprecise bus errors cannot establish which execution phase issued the write.
// Lazy FP faults and extended frames need a separate FP-context ownership model.
pub(super) const SYNCHRONOUS_FAULTS: u32 = (1 << 0)
    | (1 << 1)
    | (1 << 8)
    | (1 << 9)
    | (1 << 16)
    | (1 << 17)
    | (1 << 18)
    | (1 << 19)
    | (1 << 24)
    | (1 << 25);
pub(super) const FORCED: u32 = 1 << 30;

/// Only discard an attributable, unprivileged basic-frame Thread/PSP context.
/// Never resume the failed instruction or retry a failed unstack operation.
/// Cross-security-state returns are outside this runtime ownership contract.
pub(super) fn recoverable(
    rustlet_phase: bool,
    active: bool,
    exc_return: u32,
    control: u32,
    cfsr: u32,
    hfsr: u32,
    stack_limits: bool,
) -> bool {
    let causes = cfsr & !ADDRESS_VALID;
    rustlet_phase
        && active
        && exc_return == 0xffff_fffd
        && control & 1 != 0
        && causes != 0
        && causes & !(STACK_FAULTS | SYNCHRONOUS_FAULTS) == 0
        && hfsr & !FORCED == 0
        && (stack_limits || causes & (1 << 20) == 0)
}

/// A standalone BKPT without a debugger can escalate through DEBUGEVT.
/// Other debug events (external halt, watchpoint, vector catch) prove no origin.
pub(super) fn recoverable_breakpoint(
    rustlet_phase: bool,
    active: bool,
    exc_return: u32,
    control: u32,
    cfsr: u32,
    hfsr: u32,
    dfsr: u32,
) -> bool {
    rustlet_phase
        && active
        && exc_return == 0xffff_fffd
        && control & 1 != 0
        && cfsr == 0
        && hfsr == (1 << 31)
        && dfsr == (1 << 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn synchronous_and_stack_causes_recover_directly_and_after_escalation() {
        // Architectural causes, independent of the implementation's masks:
        // IACCVIOL, DACCVIOL, MUNSTKERR, MSTKERR, IBUSERR, PRECISERR,
        // UNSTKERR, STKERR, UNDEFINSTR, INVSTATE, INVPC, NOCP, STKOF,
        // UNALIGNED and DIVBYZERO.
        for bit in [0, 1, 3, 4, 8, 9, 11, 12, 16, 17, 18, 19, 20, 24, 25] {
            let cause = 1 << bit;
            for hfsr in [0, FORCED] {
                assert!(recoverable(
                    true,
                    true,
                    0xffff_fffd,
                    3,
                    cause | ADDRESS_VALID,
                    hfsr,
                    true
                ));
            }
        }
    }

    #[test]
    fn only_a_standalone_rustlet_breakpoint_is_recoverable() {
        assert!(recoverable_breakpoint(
            true,
            true,
            0xffff_fffd,
            3,
            0,
            1 << 31,
            2
        ));
        assert!(!recoverable_breakpoint(
            false,
            true,
            0xffff_fffd,
            3,
            0,
            1 << 31,
            2
        ));
        assert!(!recoverable_breakpoint(
            true,
            true,
            0xffff_fff1,
            3,
            0,
            1 << 31,
            2
        ));
        assert!(!recoverable_breakpoint(
            true,
            true,
            0xffff_fffd,
            3,
            0,
            1 << 31,
            10
        ));
        assert!(!recoverable_breakpoint(
            true,
            true,
            0xffff_fffd,
            3,
            1,
            1 << 31,
            2
        ));
    }

    #[test]
    fn kernel_nested_extended_and_ambiguous_faults_remain_fatal() {
        let valid = 1 << 17;
        assert!(!recoverable(false, true, 0xffff_fffd, 3, valid, 0, true));
        assert!(!recoverable(true, false, 0xffff_fffd, 3, valid, 0, true));
        assert!(!recoverable(true, true, 0xffff_fffd, 0, valid, 0, true));
        for exc in [
            0xffff_fff1,
            0xffff_fff9,
            0xffff_ffed,
            0xffff_ffbd,
            0,
            0xffff_ffff,
        ] {
            assert!(!recoverable(true, true, exc, 3, valid, 0, true));
        }
        for cause in [0, ADDRESS_VALID, 1 << 5, 1 << 10, 1 << 13, 1 << 31] {
            assert!(!recoverable(true, true, 0xffff_fffd, 3, cause, 0, true));
        }
        for hfsr in [1 << 1, 1 << 31, FORCED | (1 << 1)] {
            assert!(!recoverable(true, true, 0xffff_fffd, 3, valid, hfsr, true));
        }
        assert!(!recoverable(true, true, 0xffff_fffd, 3, 1 << 20, 0, false));
        assert!(!recoverable(
            true,
            true,
            0xffff_fffd,
            3,
            valid | (1 << 10),
            0,
            true
        ));
    }
}
