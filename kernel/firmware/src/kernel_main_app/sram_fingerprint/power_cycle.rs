//! RP2350-only SRAM1 power switching for the opt-in measurement module.
use super::*;
use crate::kernel_cell::KernelCell;

// SAFETY: only the privileged APDU owner core runs this opt-in experiment.
// One guard covers the physical scratch, power switch and cycle counter.
static EXPERIMENT: KernelCell<()> = unsafe { KernelCell::new(()) };

const SCRATCH: usize = 0x2002_0000;
// Reconstruction still tracks 2040 positions and vote counters. These buffers
// fit within the already authorized scratch range independently of mask size.
const WORKSPACE_LEN: usize = 2040 * core::mem::size_of::<u32>();
const COUNTERS_LEN: usize = 2040;
const STATE: usize = 0x4010_0038;
const PASSWORD: u32 = 0x5afe_0000;
const CHANGING_OR_WAITING: u32 = 0x3000;
const REQUEST_ERRORS: u32 = 0x0500;
const DEMCR: usize = 0xe000_edfc;
const DWT_CTRL: usize = 0xe000_1000;
const CYCCNT: usize = 0xe000_1004;
const CYCLES_PER_MS: u32 = 150_000;

fn read(address: usize) -> u32 {
    // SAFETY: callers supply aligned RP2350 MMIO addresses in Secure kernel mode.
    unsafe { core::ptr::read_volatile(address as *const u32) }
}
fn write(address: usize, value: u32) {
    // SAFETY: private callers own the experiment's registers and physical words.
    unsafe { core::ptr::write_volatile(address as *mut u32, value) }
}

struct Clock { demcr: u32, control: u32 }
impl Clock {
    fn start() -> Option<Self> {
        let clock = Self { demcr: read(DEMCR), control: read(DWT_CTRL) };
        write(DEMCR, clock.demcr | (1 << 24));
        write(DWT_CTRL, clock.control | 1);
        let start = read(CYCCNT);
        for _ in 0..100 {
            if read(CYCCNT) != start { return Some(clock); }
        }
        None
    }
    fn delay_ms(&self, ms: u32) {
        let start = read(CYCCNT);
        // Interrupts stay enabled, including the T=0 NULL-byte timer.
        while read(CYCCNT).wrapping_sub(start) < ms * CYCLES_PER_MS {
            core::hint::spin_loop();
        }
    }
    fn cycle(&self, pattern: u8, off_ms: u32) -> bool {
        let value = u32::from_le_bytes([pattern; 4]);
        for i in 0..LEN / 4 { write(BASE + i * STRIDE, value); }
        // SAFETY: complete all writes before switching the exclusively owned domain.
        unsafe { core::arch::asm!("dsb sy", options(nostack, preserves_flags)); }
        if !self.state(true) { let _ = self.state(false); return false; }
        self.delay_ms(off_ms);
        let on = self.state(false);
        // SAFETY: domain is not accessed by the caller unless power-on succeeded.
        unsafe { core::arch::asm!("dsb sy", options(nostack, preserves_flags)); }
        on
    }
    fn state(&self, off: bool) -> bool {
        // P0.0 <-> P0.1: SRAM1 only. SRAM0, XIP and SWCORE remain powered.
        write(STATE, PASSWORD | 0x100 | (u32::from(off) << 4));
        let start = read(CYCCNT);
        loop {
            let state = read(STATE);
            if state & REQUEST_ERRORS != 0 { return false; }
            if state & CHANGING_OR_WAITING == 0 && state & 15 == u32::from(off) {
                return true;
            }
            if read(CYCCNT).wrapping_sub(start) >= 100 * CYCLES_PER_MS { return false; }
        }
    }
}
impl Drop for Clock {
    fn drop(&mut self) {
        write(DWT_CTRL, self.control);
        write(DEMCR, self.demcr);
    }
}

pub(super) fn memory_available() -> bool {
    read(STATE) & (CHANGING_OR_WAITING | 15) == 0
}

/// Enroll a persistent mask or reconstruct its first 2040 selected positions.
pub(super) fn enrolled(apdu: &mut dyn SEApdu) -> ApduStatus {
    let Some(_experiment) = EXPERIMENT.try_borrow_mut() else {
        return ApduStatus::conditions_not_satisfied();
    };
    if crate::core::target::kernel_heap_end().is_none_or(|end| end > 0x2001_0000)
        || !memory_available() { return ApduStatus::conditions_not_satisfied(); }
    let Some(clock) = Clock::start() else { return ApduStatus::conditions_not_satisfied(); };
    // SAFETY: the opt-in module exclusively owns these buffers outside kernel RAM.
    let (reference, mask) = unsafe {
        core::ptr::write_bytes(SCRATCH as *mut u8, 0, WORKSPACE_LEN + COUNTERS_LEN);
        core::slice::from_raw_parts_mut(SCRATCH as *mut u8, WORKSPACE_LEN + COUNTERS_LEN).split_at_mut(WORKSPACE_LEN)
    };
    let status = if apdu.ins() == 0xb0 {
        enroll_mask(apdu, &clock, &mut reference[..LEN], &mut mask[..LEN])
    } else {
        reconstruct(apdu, &clock, reference, mask)
    };
    crate::core::secure_zero(reference);
    crate::core::secure_zero(mask);
    status
}

fn enroll_mask(apdu: &mut dyn SEApdu, clock: &Clock, reference: &mut [u8], mask: &mut [u8]) -> ApduStatus {
    if !acquire_cycles(reference, mask, u32::from(apdu.p1()) * 256, sample_byte,
        |pattern| clock.cycle(pattern, u32::from(apdu.p2()))) {
        return ApduStatus::conditions_not_satisfied();
    }
    // Publish only after every cut and comparison succeeded. The writer stages
    // the DATA pages then commits one BOSS, preserving the old mask on failure.
    if let Err(error) = selected_app::write_registry_data_objects(selected_app::root_security_domain_instance_aid(),
        &[(ENROLLED_MASK, LEN)], |_, i| mask[i]) {
        return error.status();
    }
    let count: u32 = mask.iter().map(|b| b.count_zeros()).sum();
    let _ = apdu.set_outgoing();
    apdu.buffer_mut()[..4].copy_from_slice(&count.to_be_bytes());
    apdu.set_outgoing_length(4);
    ApduStatus::success()
}

fn reconstruct(apdu: &mut dyn SEApdu, clock: &Clock, workspace: &mut [u8], counters: &mut [u8]) -> ApduStatus {
    let Some(mask) = selected_app::probe_data(ENROLLED_MASK) else {
        return ApduStatus::conditions_not_satisfied();
    };
    if mask.len() != LEN { return ApduStatus::conditions_not_satisfied(); }
    // SAFETY: scratch is word-aligned, exclusively borrowed and initialized;
    // every u32 bit pattern is valid. No additional allocation or kernel stack.
    let (_, positions, _) = unsafe { workspace.align_to_mut::<u32>() };
    let positions = &mut positions[..2040];
    if !selected_positions(&mask, positions) { return ApduStatus::conditions_not_satisfied(); }
    let votes = &mut counters[..2040];
    for cycle in 0..apdu.p1() {
        let pattern = if cycle.is_multiple_of(2) { 0 } else { 255 };
        if !clock.cycle(pattern, u32::from(apdu.p2())) { return ApduStatus::conditions_not_satisfied(); }
        vote_sample(positions, votes, sample_byte);
    }
    let _ = apdu.set_outgoing();
    pack_majority(votes, apdu.p1(), &mut apdu.buffer_mut()[..255]);
    apdu.set_outgoing_length(255);
    ApduStatus::success()
}
