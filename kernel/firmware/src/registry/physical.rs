//! Trusted physical flash boundary for registry storage.
//!
//! Geometry is exposed by area/page/sector queries. Successful program/erase
//! returns are assumed durable and visible; no flush or atomic write is used.
//! Programming follows byte order. Interruption resets volatile state and leaves
//! flash as it stands. Returned verification errors preserve the backend result,
//! not a promise that the target bytes are unchanged. Mapped reads are exposed
//! by `read_area` without introducing a copy.
//! Re-exports deliberately preserve the exact backend checks and error values.
pub(crate) use oxi_core::core::flash::{erase_sector_size, logical_page_size};

/// The last two erase sectors of the core persistence area hold the BOSS journal.
pub(crate) fn persistence_area() -> oxi_core::core::flash::FlashPersistenceArea {
    let mut area = oxi_core::core::flash::persistence_area();
    let page = logical_page_size();
    let sector = erase_sector_size();
    if page == 0 || sector == 0 || !sector.is_multiple_of(page) {
        area.page_count = 0;
        return area;
    }
    area.page_count = area.page_count.saturating_sub(2 * sector / page);
    area
}

pub(crate) fn journal_area() -> Option<(usize, usize)> {
    let area = oxi_core::core::flash::persistence_area();
    let sector = erase_sector_size();
    let page = logical_page_size();
    let bytes = area.page_count.checked_mul(page)?;
    if sector == 0 || page == 0 || bytes < 3 * sector {
        return None;
    }
    Some((area.start + bytes - 2 * sector, sector))
}

/// Borrow the mapped persistence area; no buffer copy or flash operation.
pub(crate) fn read_area() -> Option<&'static [u8]> {
    let area = persistence_area();
    let page_size = logical_page_size();
    let len = area.page_count.checked_mul(page_size)?;
    if len == 0 {
        return None;
    }
    Some(unsafe { core::slice::from_raw_parts(area.start as *const u8, len) })
}

/// Diagnostic snapshot read, preserving the original volatile byte access.
///
/// # Safety
/// The caller must supply a readable mapped flash address.
#[cfg(oxide_se_kernel_app_module = "registry-test")]
pub(crate) unsafe fn read_byte_volatile(address: usize) -> u8 {
    unsafe { core::ptr::read_volatile(address as *const u8) }
}

/// Every owner write invalidates overlapping block validation before touching flash.
pub(crate) fn program_page(address: usize, bytes: &[u8]) -> oxi_core::core::flash::FlashResult<()> {
    // No programming/recycling (including an in-progress LOAD) after uncertainty.
    super::storage::require_writable()
        .map_err(|_| oxi_core::core::flash::FlashError::CorruptedState)?;
    super::header_auth::invalidate(address, bytes.len());
    oxi_core::core::flash::write_page(address, bytes)
}
pub(crate) fn erase_sector(address: usize) -> oxi_core::core::flash::FlashResult<()> {
    // No programming/recycling (including an in-progress LOAD) after uncertainty.
    super::storage::require_writable()
        .map_err(|_| oxi_core::core::flash::FlashError::CorruptedState)?;
    super::header_auth::invalidate(address, erase_sector_size());
    oxi_core::core::flash::erase_sector(address)
}

/// Checked mapped read within the two physical journal sectors.
pub(crate) fn read_journal(address: usize, len: usize) -> Option<&'static [u8]> {
    let (base, sector) = journal_area()?;
    if address < base || address.checked_add(len)? > base.checked_add(sector.checked_mul(2)?)? {
        return None;
    }
    // SAFETY: the configured journal consists of two mapped flash sectors;
    // the checked span lies wholly inside them. No mutable reference is formed.
    Some(unsafe { core::slice::from_raw_parts(address as *const u8, len) })
}
