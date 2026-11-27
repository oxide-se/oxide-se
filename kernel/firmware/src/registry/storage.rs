//! Registry flash access, initialization and reusable-span allocation.
//!
//! Extraction preserves write/erase order and error behavior. Callers supply
//! protected ranges; transaction ownership and recovery policy remain above this
//! layer. No atomic flash write or additional flush is introduced.

use super::format as registry_persistence;
use super::state::PERSISTENCE_RUNTIME_STATE;
#[cfg(oxide_se_kernel_app_module = "registry-test")]
use super::write_fault as registry_write_fault;
use crate::kernel_cell::KernelCell;
use crate::registry::objects::{RegistryError, RegistryResult};

pub(crate) const PERSISTENCE_PAGE_BUFFER_SIZE: usize = 4096;

// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static PERSISTENCE_PAGE_BUFFER: KernelCell<[u8; PERSISTENCE_PAGE_BUFFER_SIZE]> =
    unsafe { KernelCell::new([0xFF; PERSISTENCE_PAGE_BUFFER_SIZE]) };

// Volatile only: reset must retry initialization while the durable marker is absent.
static AREA_PREPARED: KernelCell<bool> = unsafe { KernelCell::new(false) };

// A returned write/erase error may already have made a complete BOSS durable.
// Do not permit a second publication using stale RAM before reset/recovery.
static WRITE_UNCERTAIN: KernelCell<bool> = unsafe { KernelCell::new(false) };
pub(crate) fn require_writable() -> RegistryResult {
    if *WRITE_UNCERTAIN.borrow() {
        Err(RegistryError::Persistence)
    } else {
        Ok(())
    }
}
#[cfg(test)]
pub(crate) fn reset_freeze_for_test() {
    *WRITE_UNCERTAIN.borrow_mut() = false;
}

pub(crate) fn freeze() {
    *WRITE_UNCERTAIN.borrow_mut() = true;
}

pub(crate) fn write_persistence_area_marker_page() -> bool {
    let mut page_guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    let page = &mut *page_guard;
    let page_size = crate::registry::physical::logical_page_size();
    if page_size == 0 || page_size > page.len() {
        return false;
    }
    page.fill(0xFF);
    if registry_persistence::write_persistence_area_marker(page).is_err() {
        return false;
    }
    crate::registry::physical::program_page(
        crate::registry::physical::persistence_area().start,
        &page[..page_size],
    )
    .is_ok()
}

pub(crate) fn write_persistent_block(offset: usize, block: &[u8]) -> RegistryResult {
    require_writable()?;
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Program);
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    if let Some(result) = registry_write_fault::write(offset, block) {
        if !result {
            freeze();
        }
        return result.then_some(()).ok_or(RegistryError::Persistence);
    }
    let area = crate::registry::physical::persistence_area();
    let page_size = crate::registry::physical::logical_page_size();
    if page_size == 0 || !block.len().is_multiple_of(page_size) {
        return Err(RegistryError::Persistence);
    }
    let mut written = 0usize;
    while written < block.len() {
        // Invariant: `write_page` only programs 1 bits to 0 bits. Sector erase,
        // when needed, has already been performed by `reserve_persistent_span`.
        if crate::registry::physical::program_page(
            area.start + offset + written,
            &block[written..written + page_size],
        )
        .is_err()
        {
            freeze();
            return Err(RegistryError::Persistence);
        }
        written += page_size;
    }
    Ok(())
}

pub(crate) fn ensure_persistence_area_initialized(area_bytes: &[u8], page_size: usize) -> bool {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::InitializeArea);
    if *AREA_PREPARED.borrow() || registry_persistence::has_persistence_area_marker(area_bytes) {
        return true;
    }
    let area = crate::registry::physical::persistence_area();
    let erase_sector_size = crate::registry::physical::erase_sector_size();
    let Some(area_len) = area.page_count.checked_mul(page_size) else {
        return false;
    };
    if erase_sector_size == 0
        || !erase_sector_size.is_multiple_of(page_size)
        || !area.start.is_multiple_of(erase_sector_size)
        || area_len % erase_sector_size != 0
    {
        return false;
    }
    let mut sector_offset = 0usize;
    while sector_offset < area_len {
        if crate::registry::physical::erase_sector(area.start + sector_offset).is_err() {
            return false;
        }
        sector_offset += erase_sector_size;
    }
    if super::journal::initialize().is_err() {
        freeze();
        return false;
    }
    *AREA_PREPARED.borrow_mut() = true;
    true
}

pub(crate) fn reserve_persistent_span(
    area_bytes: &[u8],
    page_size: usize,
    required_len: usize,
    protected: &super::pages::Pages,
) -> RegistryResult<usize> {
    reserve_persistent_span_sized(area_bytes, page_size, |_| Some(required_len), protected)
}

pub(crate) fn reserve_persistent_span_sized(
    area_bytes: &[u8],
    page_size: usize,
    required_at: impl Fn(usize) -> Option<usize>,
    protected: &super::pages::Pages,
) -> RegistryResult<usize> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Allocate);
    require_writable()?;
    let erase_sector_size = crate::registry::physical::erase_sector_size();
    let (append_offset, search_start) = {
        let state = PERSISTENCE_RUNTIME_STATE.borrow();
        let after_boss = state
            .latest_registry
            .map(|boss| boss.offset.saturating_add(boss.total_len))
            .unwrap_or(page_size);
        (state.append_offset, after_boss)
    };
    let append_span = match required_at(append_offset) {
        Some(required_len) => registry_persistence::erased_span_at(
            area_bytes,
            page_size,
            required_len,
            append_offset,
            protected,
        )
        .map_err(|_| RegistryError::Persistence)?,
        None => None,
    };
    let span = match append_span {
        Some(span) => span,
        None => registry_persistence::find_reusable_span_sized_from(
            area_bytes,
            page_size,
            erase_sector_size,
            search_start,
            &required_at,
            protected,
        )
        .map_err(|_| RegistryError::Persistence)?
        .ok_or(RegistryError::Capacity)?,
    };
    if span.needs_erase() {
        neutralize_persistent_span(area_bytes, page_size, span)?;
        if !erase_reusable_span(span) {
            freeze();
            return Err(RegistryError::Persistence);
        }
    }
    let mut state_guard = PERSISTENCE_RUNTIME_STATE.borrow_mut();
    let state = &mut *state_guard;
    state.append_offset = span.offset.saturating_add(span.total_len);
    // Reservation owns pages immediately, including unprogrammed payloads.
    protected.reserve(registry_persistence::PersistentRange::new(
        span.offset,
        span.total_len,
    ))?;
    Ok(span.offset)
}

fn neutralize_persistent_span(
    area: &[u8],
    page_size: usize,
    span: registry_persistence::ReusableSpan,
) -> RegistryResult {
    // Reservation precedes encoding the new block, so the existing page buffer
    // can be reused without an additional allocation or stack-sized page copy.
    let mut guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    neutralize_with_program(
        area,
        page_size,
        span,
        &mut guard[..page_size],
        |offset, page| {
            let address = crate::registry::physical::persistence_area().start + offset;
            crate::registry::physical::program_page(address, page)
                .map_err(|_| RegistryError::Persistence)
        },
    )
}

fn neutralize_with_program(
    area: &[u8],
    page_size: usize,
    span: registry_persistence::ReusableSpan,
    page: &mut [u8],
    mut program: impl FnMut(usize, &[u8]) -> RegistryResult,
) -> RegistryResult {
    let result =
        registry_persistence::neutralize_recycled_blocks(area, page_size, span, |offset| {
            page.copy_from_slice(&area[offset..offset + page_size]);
            page[..4].fill(0);
            program(offset, page)?;
            // Confirm durable readback before retiring the enclosing header.
            if area[offset..offset + page_size] != *page {
                return Err(RegistryError::Persistence);
            }
            Ok(())
        });
    oxi_core::core::secure_zero(page);
    // Invariant: any neutralization error may follow physical effects. Freeze
    // before returning so allocation, publication and cleanup cannot reuse them
    // until reset/recovery, including when programming succeeded but readback failed.
    result.inspect_err(|_| freeze())
}

fn erase_reusable_span(span: registry_persistence::ReusableSpan) -> bool {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Erase);
    let area = crate::registry::physical::persistence_area();
    let erase_sector_size = crate::registry::physical::erase_sector_size();
    if !span.needs_erase()
        || erase_sector_size == 0
        || !span.erase_len.is_multiple_of(erase_sector_size)
        || !span.erase_offset.is_multiple_of(erase_sector_size)
    {
        return !span.needs_erase();
    }
    let mut offset = 0usize;
    while offset < span.erase_len {
        // Invariant: the allocator only returns erasable sector runs that do
        // not overlap the latest valid BOSS or any object reachable from it.
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        if let Some(result) = registry_write_fault::erase(area.start + span.erase_offset + offset) {
            return result;
        }
        if crate::registry::physical::erase_sector(area.start + span.erase_offset + offset).is_err()
        {
            return false;
        }
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        registry_write_fault::record_completed_erase();
        offset += erase_sector_size;
    }
    true
}

pub(crate) fn persistent_registry_area_bytes() -> Option<&'static [u8]> {
    super::physical::read_area()
}

#[cfg(test)]
mod neutralization_tests {
    use super::*;

    #[test]
    fn neutralization_program_and_readback_errors_freeze_before_cleanup() {
        const PAGE: usize = 256;
        // Run with the registry host suite's single-threaded global-state policy.
        struct Reset;
        impl Drop for Reset {
            fn drop(&mut self) {
                reset_freeze_for_test();
            }
        }
        let _reset = Reset;
        for program_error in [true, false] {
            reset_freeze_for_test();
            let mut area = [0xff; PAGE * 2];
            registry_persistence::encode_object_block(
                registry_persistence::PACKAGE_BLOCK_MAGIC,
                &[0x5a; PAGE],
                PAGE,
                &mut area,
            )
            .unwrap();
            let span = registry_persistence::ReusableSpan {
                offset: 0,
                total_len: PAGE,
                erase_offset: 0,
                erase_len: PAGE * 2,
            };
            let mut scratch = [0xff; PAGE];
            let mut calls = 0;
            let result = neutralize_with_program(&area, PAGE, span, &mut scratch, |_, bytes| {
                calls += 1;
                assert_eq!(&bytes[..4], &[0; 4]);
                // Ok without the requested update exercises the additional
                // readback check independently of the backend's error return.
                if program_error {
                    Err(RegistryError::Persistence)
                } else {
                    Ok(())
                }
            });
            assert_eq!(result, Err(RegistryError::Persistence));
            assert_eq!(calls, 1);
            assert!(scratch.iter().all(|byte| *byte == 0));
            assert!(require_writable().is_err());
            // Frozen cleanup must retain possibly affected reservations.
            let pages = super::super::pages::Pages::new();
            pages.reset(PAGE, area.len()).unwrap();
            let range = registry_persistence::PersistentRange::new(0, PAGE);
            pages.reserve(range).unwrap();
            super::super::retention::release_unattached(&pages, range).unwrap();
            assert!(registry_persistence::Protection::overlaps(&pages, range));
            assert!(write_persistent_block(0, &scratch).is_err());
        }
    }

    #[test]
    fn empty_neutralization_keeps_registry_writable() {
        reset_freeze_for_test();
        let area = [0xff; 256];
        let span = registry_persistence::ReusableSpan {
            offset: 0,
            total_len: 256,
            erase_offset: 0,
            erase_len: 256,
        };
        let mut scratch = [0xaa; 256];
        neutralize_with_program(&area, 256, span, &mut scratch, |_, _| {
            panic!("erased flash needs no neutralization")
        })
        .unwrap();
        assert!(require_writable().is_ok());
        assert!(scratch.iter().all(|byte| *byte == 0));
    }
}
