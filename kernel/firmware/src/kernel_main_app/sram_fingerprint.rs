//! Experimental SRAM repeatability probe. Never enabled by default.
use super::{ApduFilter, KernelAppModule};
use crate::apdu_manager::ApduStatus;
#[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
use crate::selected_app;
use rustlet_runtime::SEApdu;

#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
const LEN: usize = 1020;
#[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
const ENROLLED_MASK: u16 = 0xdf02;
#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
const BASE: usize = 0x2004_0000;
// Exactly one physical SRAM4 word every four interleaved system words.
#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
const STRIDE: usize = 16;

pub(crate) struct Module;
impl KernelAppModule for Module {
    fn initialize() {}
}
pub(crate) const APDU_FILTER: ApduFilter = ApduFilter { matches, process };
fn matches(apdu: &dyn SEApdu) -> bool {
    apdu.cla() == 0x80 && (0xb0..=0xb2).contains(&apdu.ins())
}
#[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
fn sample_byte(index: usize) -> u8 {
    // Read physical power-up bytes, not a Rust uninitialized allocation.
    let address = BASE + (index / 4) * STRIDE;
    let word = unsafe { core::ptr::read_volatile(address as *const u32) };
    word.to_le_bytes()[index % 4]
}
#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn merge(reference: u8, previous: u8, current: u8) -> u8 {
    previous | (reference ^ current)
}
fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    if !cfg!(oxide_se_board_raspi_pico2) {
        return ApduStatus::conditions_not_satisfied();
    }
    if apdu.ins() == 0xb2 { return read_mask(apdu); }
    enrolled_experiment(apdu)
}

fn read_mask(apdu: &mut dyn SEApdu) -> ApduStatus {
    if apdu.p1() > 3 || apdu.p2() != 0 || !apdu.incoming_data().is_empty() {
        return ApduStatus::wrong_data();
    }
    if apdu.set_outgoing() != 255 { return ApduStatus::correct_length(255); }
    #[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
    {
        let Some(mask) = selected_app::probe_data(ENROLLED_MASK) else {
            return ApduStatus::conditions_not_satisfied();
        };
        let Some(fragment) = mask_fragment(&mask, apdu.p1()) else {
            return ApduStatus::conditions_not_satisfied();
        };
        apdu.buffer_mut()[..255].copy_from_slice(fragment);
        apdu.set_outgoing_length(255);
        return ApduStatus::success();
    }
    #[cfg(not(all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
    ApduStatus::conditions_not_satisfied()
}

#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn mask_fragment(mask: &[u8], fragment: u8) -> Option<&[u8]> {
    if mask.len() != LEN || fragment > 3 { return None; }
    let start = usize::from(fragment) * 255;
    Some(&mask[start..start + 255])
}

/// One initial observation followed by exactly `cycles` power cuts.
/// The pre-cut pattern is an experimental condition, not the reference.
#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn acquire_cycles(
    reference: &mut [u8],
    mask: &mut [u8],
    cycles: u32,
    mut sample: impl FnMut(usize) -> u8,
    mut power_cycle: impl FnMut(u8) -> bool,
) -> bool {
    for (i, byte) in reference.iter_mut().enumerate() {
        *byte = sample(i);
    }
    mask.fill(0);
    for cycle in 0..cycles {
        if !power_cycle(if cycle.is_multiple_of(2) { 0 } else { 0xff }) {
            return false;
        }
        for (i, unstable) in mask.iter_mut().enumerate() {
            *unstable = merge(reference[i], *unstable, sample(i));
        }
    }
    true
}

fn valid_enrolled_parameters(ins: u8, p1: u8, p2: u8) -> bool {
    p1 != 0 && p2 != 0 && (ins == 0xb0 || (ins == 0xb1 && p1 % 2 == 1))
}

fn enrolled_experiment(apdu: &mut dyn SEApdu) -> ApduStatus {
    if !valid_enrolled_parameters(apdu.ins(), apdu.p1(), apdu.p2())
        || !apdu.incoming_data().is_empty() {
        return ApduStatus::wrong_data();
    }
    // Reject wrong Le before a long acquisition or a persistent write.
    let le = apdu.set_outgoing();
    let expected = if apdu.ins() == 0xb0 { 4 } else { 255 };
    if (if le == 0 { 256 } else { le }) != expected {
        return ApduStatus::correct_length(expected);
    }
    #[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
    { return power_cycle::enrolled(apdu); }
    #[cfg(not(all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
    ApduStatus::conditions_not_satisfied()
}

/// Freeze the first requested zero-mask positions in increasing byte and bit order.
#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn selected_positions(mask: &[u8], positions: &mut [u32]) -> bool {
    let mut count = 0;
    for (index, byte) in mask.iter().enumerate() {
        for bit in 0..8 {
            if byte & (1 << bit) == 0 {
                if count == positions.len() { return true; }
                positions[count] = (index * 8 + bit) as u32;
                count += 1;
            }
        }
    }
    count == positions.len()
}

#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn vote_sample(positions: &[u32], votes: &mut [u8], mut sample: impl FnMut(usize) -> u8) {
    for (&position, ones) in positions.iter().zip(votes.iter_mut()) {
        *ones += (sample(position as usize / 8) >> (position % 8)) & 1;
    }
}

#[cfg(any(test, all(target_arch = "arm", oxide_se_board_raspi_pico2)))]
fn pack_majority(votes: &[u8], cycles: u8, output: &mut [u8]) {
    output.fill(0);
    for (i, ones) in votes.iter().enumerate() {
        output[i / 8] |= u8::from(*ones > cycles / 2) << (i % 8);
    }
}

// Hardware access stays private to this opt-in privileged experiment.
#[cfg(all(target_arch = "arm", oxide_se_board_raspi_pico2))]
#[path = "sram_fingerprint/power_cycle.rs"]
mod power_cycle;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn mask_fragments_cover_exactly_the_persisted_mask() {
        let mask: [u8; LEN] = core::array::from_fn(|i| (i / 255) as u8);
        let mut combined = std::vec::Vec::new();
        for page in 0..4 {
            let fragment = mask_fragment(&mask, page).unwrap();
            assert_eq!(fragment, &[page; 255]);
            combined.extend_from_slice(fragment);
        }
        assert_eq!(combined, mask);
        assert!(mask_fragment(&mask, 4).is_none());
        assert!(mask_fragment(&mask[..1019], 0).is_none());
        assert!(mask_fragment(&[0; 32768], 0).is_none());
    }
    #[test]
    fn frozen_positions_and_majority_preserve_order_despite_noisy_samples() {
        let mut positions = [0; 3];
        assert!(selected_positions(&[0b1111_0010], &mut positions));
        assert_eq!(positions, [0, 2, 3]);
        let mut votes = [0; 3];
        for sample in [0b1101, 0b0100, 0b1001] { vote_sample(&positions, &mut votes, |_| sample); }
        let mut out = [255];
        pack_majority(&votes, 3, &mut out);
        assert_eq!(out, [7]);
        assert!(!selected_positions(&[255], &mut positions));
        let mut votes = [0];
        for _ in 0..255 { vote_sample(&[0], &mut votes, |_| 1); }
        assert_eq!(votes, [255]);
    }
    #[test]
    fn enrollment_and_reconstruction_parameters_are_distinct() {
        assert!(valid_enrolled_parameters(0xb0, 2, 255));
        assert!(valid_enrolled_parameters(0xb1, 255, 1));
        assert!(!valid_enrolled_parameters(0xb1, 2, 1));
        assert!(!valid_enrolled_parameters(0xb0, 0, 1));
        assert!(!valid_enrolled_parameters(0xb1, 1, 0));
        assert!(!valid_enrolled_parameters(0xb3, 1, 1));
    }
    #[test]
    fn enrollment_cycle_counter_does_not_truncate_at_255() {
        let (mut reference, mut mask) = ([0], [0]);
        let mut cuts = 0u32;
        assert!(acquire_cycles(&mut reference, &mut mask, 255 * 256,
            |_| 0, |_| { cuts += 1; true }));
        assert_eq!(cuts, 65280);
    }
    #[test]
    fn ten_cycles_use_one_fixed_reference_and_alternate_preloads() {
        use core::cell::Cell;
        let cycle = Cell::new(0usize);
        let samples = [0x55, 0x54, 0x55, 0x57, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55];
        let mut reference = [0; 1];
        let mut mask = [0xff; 1];
        assert!(acquire_cycles(&mut reference, &mut mask, 10,
            |_| samples[cycle.get()],
            |pattern| {
                assert_eq!(pattern, if cycle.get().is_multiple_of(2) { 0 } else { 255 });
                cycle.set(cycle.get() + 1);
                true
            }));
        assert_eq!(cycle.get(), 10);
        assert_eq!(reference, [0x55]);
        assert_eq!(mask, [3]);
    }
    #[test]
    fn failed_power_cycle_stops_without_reading_unpowered_ram() {
        let mut reference = [0];
        let mut mask = [0];
        let mut reads = 0;
        assert!(!acquire_cycles(&mut reference, &mut mask, 10,
            |_| { reads += 1; 7 }, |_| false));
        assert_eq!(reads, 1);
    }
    #[test]
    fn changes_never_cancel_and_sample_stays_in_bank() {
        let first = merge(0b1010, 0, 0b1000);
        assert_eq!(merge(0b1010, first, 0b1010), 0b0010);
        assert_eq!(BASE + (LEN / 4 - 1) * STRIDE, 0x2004_0fe0);
    }
}
