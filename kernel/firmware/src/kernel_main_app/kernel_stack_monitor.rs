//! Kernel-stack watermark: raw accesses are confined to the linker-owned stack.
use super::{ApduFilter, KernelAppModule};
use crate::apdu_layer::ApduCommand;
use crate::apdu_manager::ApduStatus;
use rustlet_runtime::SEApdu;
use core::sync::atomic::{AtomicUsize, Ordering};

const STACK_MAGIC: u32 = 0x600D_FACE;
const INS_GET_DATA: u8 = 0xca;
const STACK_HIGH_WATERMARK_TAG: u16 = 0xdf71;

unsafe extern "C" {
    static __StackLimit: u8;
    static __StackTop: u8;
}

pub(crate) struct Module;

impl KernelAppModule for Module {
    fn initialize() {
        let start = stack_start();
        let current = current_msp() & !core::mem::align_of::<u32>().saturating_sub(1);

        // MSP is sampled in this frame, before any painting. Never paint live
        // frames or accept a linker/entry mismatch as a writable memory range.
        assert!(start.is_multiple_of(4) && start <= current && current <= stack_top());
        let mut cursor = start;
        while cursor + core::mem::size_of::<u32>() <= current {
            // SAFETY: aligned words below this frame's MSP belong to the
            // inactive kernel stack. No reference is formed to live frames.
            unsafe {
                core::ptr::write_volatile(cursor as *mut u32, STACK_MAGIC);
            }
            cursor += core::mem::size_of::<u32>();
        }
        // The initial live frame was never painted. Remember its boundary so
        // no scan reads it or uninitialized padding above the painted prefix.
        LAST_HIGH_WATERMARK_BYTES.store(stack_top() - current, Ordering::Relaxed);
    }
}

pub(crate) const APDU_FILTER: ApduFilter = ApduFilter {
    matches: matches_apdu,
    process: process_apdu,
};

pub(crate) fn preserves_clear_apdu_session(command: &ApduCommand) -> bool {
    command.ins() == INS_GET_DATA
        && u16::from_be_bytes([command.p1(), command.p2()]) == STACK_HIGH_WATERMARK_TAG
}

pub(crate) fn record_after_apdu() {
    let untouched = untouched_magic_bytes();
    let total = stack_top().saturating_sub(stack_start());
    LAST_HIGH_WATERMARK_BYTES.store(total.saturating_sub(untouched), Ordering::Relaxed);
}

fn matches_apdu(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == INS_GET_DATA
        && u16::from_be_bytes([apdu.p1(), apdu.p2()]) == STACK_HIGH_WATERMARK_TAG
}

fn process_apdu(apdu: &mut dyn SEApdu) -> ApduStatus {
    let high_watermark = high_watermark_bytes() as u32;
    let _ = apdu.set_outgoing();
    apdu.buffer_mut()[..4].copy_from_slice(&high_watermark.to_be_bytes());
    apdu.set_outgoing_length(4);
    ApduStatus::success()
}

fn high_watermark_bytes() -> usize {
    LAST_HIGH_WATERMARK_BYTES.load(Ordering::Relaxed)
}

fn untouched_magic_bytes() -> usize {
    let mut cursor = stack_start();
    // A watermark can only grow. Everything below the previous boundary was
    // initialized by painting; scanning above it cannot reveal a new maximum.
    let end = stack_top() - LAST_HIGH_WATERMARK_BYTES.load(Ordering::Relaxed);
    while cursor + core::mem::size_of::<u32>() <= end {
        // SAFETY: startup painted this aligned stack range; volatile reads
        // observe the watermark without borrowing storage used by stack frames.
        let word = unsafe { core::ptr::read_volatile(cursor as *const u32) };
        if word != STACK_MAGIC {
            break;
        }
        cursor += core::mem::size_of::<u32>();
    }
    cursor.saturating_sub(stack_start())
}

fn stack_start() -> usize {
    core::ptr::addr_of!(__StackLimit) as usize
}

fn stack_top() -> usize {
    core::ptr::addr_of!(__StackTop) as usize
}

fn current_msp() -> usize {
    let value: usize;
    // SAFETY: reading MSP has no memory or privilege side effects.
    unsafe {
        core::arch::asm!("mrs {value}, msp", value = out(reg) value, options(nomem, nostack, preserves_flags));
    }
    value
}

static LAST_HIGH_WATERMARK_BYTES: AtomicUsize = AtomicUsize::new(0);
