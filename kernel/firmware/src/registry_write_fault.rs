//! Write/erase prefix fault injection, compiled only into registry-test images.
//! After a cut, all publication writes are blocked until reset. The diagnostic
//! APDU may acknowledge the injection; its RAM result is never recovery evidence.
use crate::kernel_cell::KernelCell;
use crate::{core::flash, object_registry_persistence::REGISTRY_BLOCK_MAGIC};
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

const DISARMED: usize = usize::MAX;
const MAX_PAGE: usize = 256;
static CUT: AtomicUsize = AtomicUsize::new(DISARMED);
static BOSS_ONLY: AtomicBool = AtomicBool::new(false);
static ERASE: AtomicBool = AtomicBool::new(false);
static ERASE_COUNT: AtomicUsize = AtomicUsize::new(0);
// SAFETY: registry diagnostics run only on the owner core, outside IRQs. The
// checked guard prevents a nested erase from aliasing the resident scratch.
static ERASE_IMAGE: KernelCell<[u8; 4096]> = unsafe { KernelCell::new([0; 4096]) };
static HIT: AtomicBool = AtomicBool::new(false);

pub(crate) fn arm(cut: usize, mode: u8) -> bool {
    if HIT.load(Ordering::Relaxed)
        || flash::logical_page_size() != MAX_PAGE
        || mode > 2
        || (mode == 2 && (flash::erase_sector_size() != 4096 || cut > 4096))
    {
        return false;
    }
    BOSS_ONLY.store(mode == 1, Ordering::Relaxed);
    ERASE.store(mode == 2, Ordering::Relaxed);
    CUT.store(cut, Ordering::Relaxed);
    true
}

pub(crate) fn hit() -> bool {
    HIT.load(Ordering::Relaxed)
}

/// Write a prefix of the selected block, leaving the remaining flash erased.
/// Returning None delegates the unchanged write to the normal backend.
pub(crate) fn write(offset: usize, block: &[u8]) -> Option<bool> {
    if hit() {
        return Some(false);
    }
    let cut = CUT.load(Ordering::Relaxed);
    if cut == DISARMED
        || ERASE.load(Ordering::Relaxed)
        || (BOSS_ONLY.load(Ordering::Relaxed)
            && block.get(..4) != Some(REGISTRY_BLOCK_MAGIC.to_le_bytes().as_slice()))
    {
        return None;
    }
    // Reject an invalid test point instead of silently running without a cut.
    if cut > block.len() {
        return Some(false);
    }
    let page_size = flash::logical_page_size();
    let start = flash::persistence_area().start + offset;
    let mut page = [0xFF; MAX_PAGE];
    for base in (0..cut).step_by(page_size) {
        page.fill(0xFF);
        let count = (cut - base).min(page_size);
        page[..count].copy_from_slice(&block[base..base + count]);
        if flash::write_page(start + base, &page[..page_size]).is_err() {
            return Some(false);
        }
    }
    HIT.store(true, Ordering::Relaxed);
    Some(false)
}

/// Count completed recycling erases, independently of injection hits.
pub(crate) fn erase_count() -> usize {
    ERASE_COUNT.load(Ordering::Relaxed)
}

pub(crate) fn record_completed_erase() {
    // Registry mutation has one kernel caller; no atomic RMW is needed (or
    // available on ARMv6-M).
    ERASE_COUNT.store(erase_count().saturating_add(1), Ordering::Relaxed);
}

/// Model a torn erase as an erased prefix followed by the original sector bytes.
/// The backend completes a real erase then restores the suffix before the host
/// resets the CPU. This tests recovery from that durable image, not electrical
/// interruption of a flash erase. Only the allocator's unprotected sectors enter.
pub(crate) fn erase(address: usize) -> Option<bool> {
    if hit() {
        return Some(false);
    }
    let cut = CUT.load(Ordering::Relaxed);
    if cut == DISARMED || !ERASE.load(Ordering::Relaxed) {
        return None;
    }
    let area = flash::persistence_area();
    let end = area
        .page_count
        .checked_mul(flash::logical_page_size())
        .and_then(|len| area.start.checked_add(len));
    if cut > 4096
        || !address.is_multiple_of(4096)
        || address < area.start
        || address
            .checked_add(4096)
            .zip(end)
            .is_none_or(|(stop, end)| stop > end)
    {
        return Some(false);
    }
    // Single-threaded diagnostic; reserve scratch outside the kernel stack.
    let mut image = ERASE_IMAGE.borrow_mut();
    let result = (|| {
        for (offset, byte) in image.iter_mut().enumerate() {
            // SAFETY: address is a complete, mapped sector selected by the allocator.
            *byte = unsafe { core::ptr::read_volatile((address + offset) as *const u8) };
        }
        image[..cut].fill(0xff);
        if flash::erase_sector(address).is_err() {
            return Some(false);
        }
        record_completed_erase();
        for (index, page) in image.chunks_exact(MAX_PAGE).enumerate() {
            if flash::write_page(address + index * MAX_PAGE, page).is_err() {
                return Some(false);
            }
        }
        HIT.store(true, Ordering::Relaxed);
        Some(false)
    })();
    // Diagnostic snapshots may contain registry secrets. Retire them on both
    // successful injection and backend failure, before releasing the loan.
    crate::core::secure_zero(&mut *image);
    result
}
