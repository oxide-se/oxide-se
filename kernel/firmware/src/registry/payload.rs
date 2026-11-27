//! Physical payload preparation before registry publication.
//!
//! GP authority, block sequencing, expected hash and FAE checks remain in the
//! caller. A completed payload is not a committed registry object. All calls
//! are serialized; callers must attach prepared references synchronously before
//! any subsequent allocation can recycle their storage. Reset discards RAM.

use super::format as registry_persistence;

use super::state::{
    dynamic_package_load_in_progress, DYNAMIC_LOAD_CONTEXT, OBJECT_REGISTRY, USED_PAGES,
};
use super::storage::{
    persistent_registry_area_bytes, reserve_persistent_span, reserve_persistent_span_sized,
    write_persistent_block, PERSISTENCE_PAGE_BUFFER, PERSISTENCE_PAGE_BUFFER_SIZE,
};
use crate::registry::objects::{RegistryError, RegistryResult};
use sha2::{Digest, Sha256};

/// Physical cursor, copied with the GP context until an append is accepted.
/// Fields stay crate-visible during the interface migration.
#[derive(Clone, Copy)]
pub(crate) struct PayloadPreparation {
    pub(crate) expected_size: usize,
    pub(crate) reserved_offset: usize,
    pub(crate) block_total_len: usize,
    pub(crate) bytes_received: usize,
    pub(crate) current_page_index: usize,
    pub(crate) current_page_dirty: bool,
}

/// Validated on-flash payload, not yet a published registry reference.
pub(crate) struct PreparedPayload {
    bytes: &'static [u8],
}

impl PreparedPayload {
    /// Consume immediately in the serialized registry attachment path.
    pub(crate) fn into_bytes(self) -> &'static [u8] {
        self.bytes
    }
}

/// Reserve a package block with the existing address-dependent MPU padding.
/// Stages the header in the shared page; does not publish or write that page yet.
pub(crate) fn prepare_payload(expected_size: usize) -> RegistryResult<PayloadPreparation> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::PrepareLoad);
    let Some(area_bytes) = persistent_registry_area_bytes() else {
        return Err(RegistryError::Persistence);
    };
    let page_size = crate::registry::physical::logical_page_size();
    if page_size == 0 || page_size > PERSISTENCE_PAGE_BUFFER_SIZE {
        return Err(RegistryError::Persistence);
    }
    let Ok(block_total_len) = registry_persistence::object_block_total_len(
        registry_persistence::PACKAGE_BLOCK_MAGIC,
        expected_size,
        page_size,
    ) else {
        return Err(RegistryError::InvalidData);
    };

    let protected_ranges = &USED_PAGES;
    let Some(_protected_len) =
        build_current_persistence_protection(area_bytes, page_size, protected_ranges)
    else {
        return Err(RegistryError::Persistence);
    };
    // Reserve against the actual candidate address, including a possible
    // excluded prefix. Never erase a speculative oversized reservation.
    let padding_at = |offset: usize| {
        let address = (area_bytes.as_ptr() as usize).checked_add(offset)?;
        oxi_core::core::mpu_cover::mpu_cover_require_padding_for(address, block_total_len)
            .ok()
            .filter(|padding| {
                padding.before.is_multiple_of(page_size) && padding.after.is_multiple_of(page_size)
            })
    };
    let reservation_offset = reserve_persistent_span_sized(
        area_bytes,
        page_size,
        |offset| {
            let padding = padding_at(offset)?;
            block_total_len
                .checked_add(padding.before)?
                .checked_add(padding.after)
        },
        protected_ranges,
    )?;
    let Some(padding) = padding_at(reservation_offset) else {
        return Err(RegistryError::Persistence);
    };
    if padding.before != 0 {
        super::retention::release_unattached(
            protected_ranges,
            registry_persistence::PersistentRange::new(reservation_offset, padding.before),
        )?;
    }
    protected_ranges.retain(registry_persistence::PersistentRange::new(
        reservation_offset + padding.before,
        block_total_len + padding.after,
    ))?;
    let reserved_offset = reservation_offset + padding.before;
    let block_total_len = block_total_len + padding.after;

    let mut page_guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    let page = &mut *page_guard;
    page.fill(0xFF);
    // The C0DE header is staged as soon as the span is reserved, but no BOSS
    // block points to it until final LOAD validates size/hash and seals the CMAC.
    write_u32_le_local(&mut page[0..4], registry_persistence::PACKAGE_BLOCK_MAGIC);
    write_u32_le_local(&mut page[4..8], block_total_len as u32);
    write_u32_le_local(&mut page[8..12], expected_size as u32);
    page[12..16].fill(0xff);
    Ok(PayloadPreparation {
        expected_size,
        reserved_offset,
        block_total_len,
        bytes_received: 0,
        current_page_index: 0,
        current_page_dirty: true,
    })
}

/// Finish CMAC and validate the physical block after the caller's size/hash/FAE
/// checks. Does not clear the active reservation or mutate registry membership.
pub(crate) fn finalize_payload(
    context: PayloadPreparation,
    area_bytes: &[u8],
    page_size: usize,
    page: &mut [u8; PERSISTENCE_PAGE_BUFFER_SIZE],
) -> RegistryResult<PreparedPayload> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::FinalizeLoad);
    if context.current_page_dirty && !flush_dynamic_load_page(&context, page_size, page) {
        return Err(RegistryError::Persistence);
    }
    seal_stored_block(
        context.reserved_offset,
        context.block_total_len,
        area_bytes,
        &mut page[..page_size],
    )?;
    let area_bytes = persistent_registry_area_bytes().ok_or(RegistryError::Persistence)?;
    let block = registry_persistence::decode_object_block_at(
        area_bytes,
        context.reserved_offset,
        page_size,
    )
    .map_err(|_| RegistryError::Persistence)?;
    if block.magic != registry_persistence::PACKAGE_BLOCK_MAGIC
        || block.payload.len() != context.expected_size
    {
        return Err(RegistryError::Persistence);
    }
    Ok(PreparedPayload {
        bytes: block.payload,
    })
}

/// Release an unattached package reservation without erasing its bytes.
pub(crate) fn discard_prepared_payload(payload: PayloadPreparation) {
    // A failed journal publication can already refer to this LOAD.
    if super::storage::require_writable().is_err() {
        return;
    }
    #[cfg(test)]
    let _ = payload;
    #[cfg(not(test))]
    super::retention::fatal(super::retention::release_unattached(
        &USED_PAGES,
        registry_persistence::PersistentRange::new(
            payload.reserved_offset,
            payload.block_total_len,
        ),
    ));
}
/// Abandonment releases the active volatile reservation.
pub(crate) fn abandon_payload() {
    if let Some(load) = DYNAMIC_LOAD_CONTEXT.replace(None) {
        discard_prepared_payload(load.payload);
    }
}

/// Exclusive responsibility for one unattached Data block. No Copy/Clone or raw
/// reference accessor: attachment consumes the token. Dropping it releases only
/// the RAM reservation, never flash; a frozen registry retains it conservatively.
#[must_use = "attach the reservation or drop it before leaving its transaction scope"]
pub(crate) struct DataReservation {
    range: Option<registry_persistence::PersistentRange>,
    data: Option<super::data_crypto::DataRef>,
}

impl DataReservation {
    pub(crate) fn attach<const N: usize>(
        mut self,
        registry: &mut super::objects::Registry<N>,
        parent: rustlet_runtime::Aid,
        aid: rustlet_runtime::Aid,
    ) -> RegistryResult {
        // upsert returns an error only before replacing the image entry.
        registry.upsert_flash_data_object(
            parent,
            aid,
            self.data.ok_or(RegistryError::InvalidState)?,
        )?;
        self.range = None; // The image now owns the reference, including on later rollback.
        Ok(())
    }
}

impl Drop for DataReservation {
    fn drop(&mut self) {
        if let Some(range) = self.range.take() {
            super::retention::fatal(super::retention::release_unattached(&USED_PAGES, range));
        }
    }
}

/// Prepare one Data block inside the caller's transaction scope. The producer
/// must be deterministic and must not mutate registry or flash. Attach or drop
/// the returned token before preparing the next member or closing the scope.
pub(crate) fn prepare_data_payload(
    len: usize,
    mut byte: impl FnMut(usize) -> u8,
) -> RegistryResult<DataReservation> {
    if dynamic_package_load_in_progress() {
        return Err(RegistryError::InvalidState);
    }
    let Some(area) = persistent_registry_area_bytes() else {
        return Err(RegistryError::Persistence);
    };
    let page_size = crate::registry::physical::logical_page_size();
    if page_size != 256 {
        return Err(RegistryError::Persistence);
    }
    OBJECT_REGISTRY.borrow_mut().before_change(None)?;
    let protected = &USED_PAGES;
    build_current_persistence_protection(area, page_size, protected)
        .ok_or(RegistryError::Persistence)?;
    let Ok(total) = registry_persistence::object_block_total_len(
        registry_persistence::ENCRYPTED_DATA_MAGIC,
        len,
        page_size,
    ) else {
        return Err(RegistryError::Persistence);
    };
    let offset = reserve_persistent_span(area, page_size, total, protected)?;
    let mut reservation = DataReservation {
        range: Some(registry_persistence::PersistentRange::new(offset, total)),
        data: None,
    };
    let data = (|| {
        let mut header = [0xffu8; 32];
        let mut iv = super::data_crypto::prepare_header(offset, len, &mut header)
            .map_err(|_| RegistryError::Persistence)?;
        let cipher_end = 32 + len.div_ceil(16) * 16;
        let mut page = [0xffu8; 256];
        // No LOAD is active: retain the first page in existing shared scratch
        // until the CMAC is known, avoiding a second page program.
        let mut first_guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
        let first_page = &mut first_guard[..page_size];
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        let _stream = super::write_fault::stream(total).ok_or(RegistryError::Persistence)?;
        for start in (0..total).step_by(page_size) {
            page.fill(0xff);
            for (i, slot) in page.iter_mut().enumerate() {
                let pos = start + i;
                *slot = match pos {
                    0..32 => header[pos],
                    p if p < 32 + len => byte(p - 32),
                    _ => 0xff,
                };
            }
            let body_start = if start == 0 { 32 } else { 0 };
            let encrypt_end = cipher_end.saturating_sub(start).min(page_size);
            if encrypt_end > body_start {
                super::data_crypto::encrypt(&mut iv, &mut page[body_start..encrypt_end])
                    .map_err(|_| RegistryError::Persistence)?;
            }
            if start == 0 {
                first_page.copy_from_slice(&page);
            } else {
                write_persistent_block(offset + start, &page)?;
            }
        }
        let tag = super::header_auth::tag_split(
            offset,
            &first_page[..16],
            &first_page[32..],
            &area[offset + page_size..offset + total],
        )
        .map_err(|_| RegistryError::Persistence)?;
        first_page[16..32].copy_from_slice(&tag);
        write_persistent_block(offset, first_page)?;
        drop(first_guard);
        super::header_auth::remember_publication(offset);
        super::data_crypto::DataRef::from_structural(area, offset, page_size)
            .map_err(|_| RegistryError::Persistence)
    })()?;
    reservation.data = Some(data);
    Ok(reservation)
}

/// Append sequential bytes. Advance the accepted byte count only on success.
/// The caller checks size and protocol sequencing and abandons on failure.
pub(crate) fn append_payload(
    context: &mut PayloadPreparation,
    page_size: usize,
    page: &mut [u8; PERSISTENCE_PAGE_BUFFER_SIZE],
    data: &[u8],
) -> bool {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::AppendLoad);
    let mut written = 0usize;
    while written < data.len() {
        let absolute_payload_offset =
            registry_persistence::OBJECT_BLOCK_HEADER_LEN + context.bytes_received + written;
        // Invariant: LOAD bytes are written after the persistent object header.
        // The FAE image therefore remains contiguous when later exposed as the
        // decoded C0DE payload.
        let page_index = absolute_payload_offset / page_size;
        if page_index != context.current_page_index {
            if context.current_page_dirty && !flush_dynamic_load_page(context, page_size, page) {
                return false;
            }
            // Invariant: LOAD offsets are sequential; moving to another page
            // can only advance, never skip backwards or create a gap.
            if page_index < context.current_page_index {
                return false;
            }
            context.current_page_index = page_index;
            context.current_page_dirty = false;
            page.fill(0xFF);
        }

        let offset_in_page = absolute_payload_offset % page_size;
        let available = page_size - offset_in_page;
        let take = available.min(data.len() - written);
        page[offset_in_page..offset_in_page + take].copy_from_slice(&data[written..written + take]);
        context.current_page_dirty = true;
        written += take;

        if offset_in_page + take == page_size {
            if !flush_dynamic_load_page(context, page_size, page) {
                return false;
            }
            context.current_page_index += 1;
            context.current_page_dirty = false;
            page.fill(0xFF);
        }
    }
    context.bytes_received += data.len();
    true
}

/// The body is immutable and verified by the backend before the tag is written.
/// Compute LOAD CRC32 directly from XIP, then authenticate the header and reuse
/// the caller's page buffer to program its previously erased CRC/tag fields.
fn seal_stored_block(offset: usize, total: usize, area: &[u8], page: &mut [u8]) -> RegistryResult {
    let block = area
        .get(
            offset
                ..offset
                    .checked_add(total)
                    .ok_or(RegistryError::Persistence)?,
        )
        .ok_or(RegistryError::Persistence)?;
    if block.len() < page.len() || page.len() < 32 {
        return Err(RegistryError::Persistence);
    }
    page.copy_from_slice(&block[..page.len()]);
    let crc = super::format::crc32_body(&block[32..]);
    page[12..16].copy_from_slice(&crc.to_le_bytes());
    let tag = super::header_auth::tag(offset, &page[..16], &[])
        .map_err(|_| RegistryError::Persistence)?;
    page[16..32].copy_from_slice(&tag);
    write_persistent_block(offset, page)?;
    super::header_auth::remember_publication(offset);
    Ok(())
}

pub(crate) fn update_sha256_from_payload_region(
    context: &PayloadPreparation,
    area_bytes: &[u8],
    current_page: &[u8; PERSISTENCE_PAGE_BUFFER_SIZE],
    start: usize,
    len: usize,
    hasher: &mut Sha256,
) {
    let page_size = crate::registry::physical::logical_page_size();
    let mut offset = 0usize;
    while offset < len {
        let absolute = start + offset;
        let page_index = absolute / page_size;
        let offset_in_page = absolute % page_size;
        let take = (page_size - offset_in_page).min(len - offset);
        if page_index == context.current_page_index {
            hasher.update(&current_page[offset_in_page..offset_in_page + take]);
        } else {
            let start = context.reserved_offset + absolute;
            hasher.update(&area_bytes[start..start + take]);
        }
        offset += take;
    }
}

fn flush_dynamic_load_page(
    context: &PayloadPreparation,
    page_size: usize,
    page: &[u8; PERSISTENCE_PAGE_BUFFER_SIZE],
) -> bool {
    write_dynamic_load_page(
        context.reserved_offset,
        context.current_page_index,
        page_size,
        page,
    )
}

fn write_dynamic_load_page(
    reserved_offset: usize,
    page_index: usize,
    page_size: usize,
    page: &[u8; PERSISTENCE_PAGE_BUFFER_SIZE],
) -> bool {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Program);
    let area = crate::registry::physical::persistence_area();
    let Some(page_offset) = page_index.checked_mul(page_size) else {
        return false;
    };
    let Some(offset) = reserved_offset.checked_add(page_offset) else {
        return false;
    };
    crate::registry::physical::program_page(area.start + offset, &page[..page_size]).is_ok()
}

pub(crate) fn build_current_persistence_protection(
    area_bytes: &[u8],
    page_size: usize,
    protected: &super::pages::Pages,
) -> Option<usize> {
    build_persistence_protection_for(&OBJECT_REGISTRY.borrow(), area_bytes, page_size, protected)
}

pub(super) fn build_persistence_protection_for<const N: usize>(
    registry: &super::objects::Registry<N>,
    area: &[u8],
    page: usize,
    pages: &super::pages::Pages,
) -> Option<usize> {
    super::publication::ensure_protection(registry, area, page, pages).ok()?;
    Some(0)
}

fn write_u32_le_local(out: &mut [u8], value: u32) {
    out.copy_from_slice(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fragments_preserve_header_and_advance_only_the_payload_cursor() {
        let mut context = PayloadPreparation {
            expected_size: 5,
            reserved_offset: 256,
            block_total_len: 256,
            bytes_received: 0,
            current_page_index: 0,
            current_page_dirty: true,
        };
        let mut page = [0xff; PERSISTENCE_PAGE_BUFFER_SIZE];
        let header = [0x42; registry_persistence::OBJECT_BLOCK_HEADER_LEN];
        page[..header.len()].copy_from_slice(&header);
        assert!(append_payload(&mut context, 256, &mut page, &[1, 2]));
        assert_eq!(context.bytes_received, 2);
        assert!(append_payload(&mut context, 256, &mut page, &[]));
        assert_eq!(context.bytes_received, 2);
        assert!(append_payload(&mut context, 256, &mut page, &[3, 4, 5]));
        assert_eq!(context.bytes_received, 5);
        assert_eq!(&page[..header.len()], &header);
        assert_eq!(&page[header.len()..header.len() + 5], &[1, 2, 3, 4, 5]);
        assert!(page[header.len() + 5..].iter().all(|&b| b == 0xff));
        assert_eq!(context.current_page_index, 0);
        assert!(context.current_page_dirty);
    }

    #[test]
    fn data_reservation_cleanup_and_attachment_transfer() {
        use super::super::{format::Protection, objects::Registry, storage};
        use rustlet_runtime::Aid;
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        storage::reset_freeze_for_test();
        USED_PAGES.reset(256, 4096).unwrap();
        USED_PAGES.set_depth(1);
        let range = registry_persistence::PersistentRange::new(0, 256);
        USED_PAGES.reserve(range).unwrap();
        drop(DataReservation {
            range: Some(range),
            data: None,
        });
        assert!(!USED_PAGES.overlaps(range));

        USED_PAGES.reserve(range).unwrap();
        storage::freeze();
        drop(DataReservation {
            range: Some(range),
            data: None,
        });
        assert!(USED_PAGES.overlaps(range));
        storage::reset_freeze_for_test();
        USED_PAGES.release(range).unwrap();

        let mut area = alloc::vec![0xff; 256];
        registry_persistence::encode_object_block(
            registry_persistence::ENCRYPTED_DATA_MAGIC,
            b"payload",
            256,
            &mut area,
        )
        .unwrap();
        let data = super::super::data_crypto::DataRef::from_structural(
            alloc::boxed::Box::leak(area.into_boxed_slice()),
            0,
            256,
        )
        .unwrap();
        let parent = Aid::from_array([1]);
        let aid = Aid::from_array([2]);
        USED_PAGES.reserve(range).unwrap();
        let mut full = Registry::<0>::new();
        assert_eq!(
            DataReservation {
                range: Some(range),
                data: Some(data)
            }
            .attach(&mut full, parent, aid),
            Err(RegistryError::Capacity)
        );
        assert!(!USED_PAGES.overlaps(range));

        USED_PAGES.reserve(range).unwrap();
        let mut registry = Registry::<1>::new();
        DataReservation {
            range: Some(range),
            data: Some(data),
        }
        .attach(&mut registry, parent, aid)
        .unwrap();
        assert!(USED_PAGES.overlaps(range));
        assert!(registry.find_data_object(&parent, &aid).is_some());
        USED_PAGES.finish_scope(1, false);
        assert!(!USED_PAGES.overlaps(range));
        USED_PAGES.invalidate();
    }
}

/// Stop streaming while retaining the reservation for synchronous attachment.
/// The caller must attach it or discard_prepared_payload on failure.
pub(crate) fn complete_payload() {
    DYNAMIC_LOAD_CONTEXT.set(None);
}
