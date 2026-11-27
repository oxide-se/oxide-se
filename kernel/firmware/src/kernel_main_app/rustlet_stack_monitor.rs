//! Measures only a suspended Rustlet stack owned by the loader.
use super::{ApduFilter, KernelAppModule};
use crate::apdu_layer::ApduCommand;
use crate::apdu_manager::ApduStatus;
use crate::core::isolation::AppMemoryWindow;
use rustlet_runtime::SEApdu;
use core::sync::atomic::{AtomicUsize, Ordering};

const STACK_MAGIC: u32 = 0x600D_FACE;
const INS_GET_DATA: u8 = 0xca;
const STACK_HIGH_WATERMARK_TAG: u16 = 0xdf72;

pub(crate) struct Module;

impl KernelAppModule for Module {
    fn initialize() {
        MAX_HIGH_WATERMARK_BYTES.store(0, Ordering::Relaxed);
    }
}

pub(crate) const APDU_FILTER: ApduFilter = ApduFilter {
    matches: matches_apdu,
    process: process_apdu,
};

/// # Safety
/// The complete window must be writable, initialized, exclusively owned by the
/// loader and inactive. No live Rustlet frame or reference may survive here.
pub(crate) unsafe fn before_rustlet(stack: AppMemoryWindow) {
    let mut cursor = aligned_start(stack);
    let end = aligned_end(stack);
    while cursor + core::mem::size_of::<u32>() <= end {
        // SAFETY: the caller owns this inactive, bounded, aligned stack word.
        unsafe {
            core::ptr::write_volatile(cursor as *mut u32, STACK_MAGIC);
        }
        cursor += core::mem::size_of::<u32>();
    }
}

/// # Safety
/// The window must be the initialized allocation passed to before_rustlet;
/// execution has stopped and the loader retains it until this observer returns.
pub(crate) unsafe fn after_rustlet(stack: AppMemoryWindow) {
    let start = aligned_start(stack);
    let end = aligned_end(stack);
    let mut cursor = start;
    while cursor + core::mem::size_of::<u32>() <= end {
        // SAFETY: the caller retains the initialized, suspended stack.
        let word = unsafe { core::ptr::read_volatile(cursor as *const u32) };
        if word != STACK_MAGIC {
            break;
        }
        cursor += core::mem::size_of::<u32>();
    }
    let high_watermark = end.saturating_sub(cursor);
    // Only the serialized loader writes this maximum; ARMv6-M needs no RMW.
    let previous = MAX_HIGH_WATERMARK_BYTES.load(Ordering::Relaxed);
    MAX_HIGH_WATERMARK_BYTES.store(previous.max(high_watermark), Ordering::Relaxed);
}

pub(crate) fn preserves_clear_apdu_session(command: &ApduCommand) -> bool {
    command.ins() == INS_GET_DATA
        && u16::from_be_bytes([command.p1(), command.p2()]) == STACK_HIGH_WATERMARK_TAG
}

fn matches_apdu(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == INS_GET_DATA
        && u16::from_be_bytes([apdu.p1(), apdu.p2()]) == STACK_HIGH_WATERMARK_TAG
}

fn process_apdu(apdu: &mut dyn SEApdu) -> ApduStatus {
    let high_watermark = MAX_HIGH_WATERMARK_BYTES.load(Ordering::Relaxed) as u32;
    let _ = apdu.set_outgoing();
    apdu.buffer_mut()[..4].copy_from_slice(&high_watermark.to_be_bytes());
    apdu.set_outgoing_length(4);
    ApduStatus::success()
}

fn aligned_start(stack: AppMemoryWindow) -> usize {
    let align = core::mem::align_of::<u32>();
    (stack.start.checked_add(align - 1).expect("stack alignment overflow")) & !(align - 1)
}

fn aligned_end(stack: AppMemoryWindow) -> usize {
    stack.start.checked_add(stack.len).expect("stack range overflow") & !(core::mem::align_of::<u32>() - 1)
}

static MAX_HIGH_WATERMARK_BYTES: AtomicUsize = AtomicUsize::new(0);
