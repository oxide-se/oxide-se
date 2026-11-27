//! Private diagnostic access to the normal persistent registry (not raw flash).
#![forbid(unsafe_code)]
use super::{ApduFilter, KernelAppModule};
use crate::{apdu_manager::ApduStatus, selected_app};
use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use rustlet_runtime::{Aid, SEApdu};

const TEST_BYTES: usize = 64 * 1024;
// Keep the diagnostic's 64 KiB of object space plus two journal sectors.
const RESERVED_BYTES: usize = TEST_BYTES + 8 * 1024;
const CHILD: Aid = Aid::from_array([0xf0, 0x52, 1]);
const GRANDCHILD: Aid = Aid::from_array([0xf0, 0x52, 2]);
static READY: AtomicBool = AtomicBool::new(false);

pub(crate) struct Module;
impl KernelAppModule for Module {
    fn initialize() {
        // Bound disposable flash, not RAM or MPU regions, to reach recycling
        // in a short campaign. Reserve before normal registry initialization.
        let area = crate::core::target::flash_persistence_area();
        let total = area
            .page_count
            .saturating_mul(crate::core::flash::logical_page_size());
        let ready = crate::core::flash::logical_page_size() == 256
            && crate::core::flash::erase_sector_size() == 4096
            && total > RESERVED_BYTES
            && crate::core::flash::reserve_persistence_tail(total - RESERVED_BYTES).is_ok();
        READY.store(ready, Ordering::Relaxed);
    }
}

pub(crate) const APDU_FILTER: ApduFilter = ApduFilter { matches, process };

fn matches(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == 0xa0
}

static LAST_TICKS: AtomicU32 = AtomicU32::new(0);

fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    if apdu.p1() == 0xf9 {
        let Some(used) = crate::core::kernel_heap_allocated_bytes() else {
            return ApduStatus::conditions_not_satisfied();
        };
        let (_, available, _, _) = crate::core::kernel_heap_debug_window();
        let (_, metadata) = crate::core::kernel_heap_metadata_debug_window();
        let values = [
            used,
            available,
            metadata,
            core::mem::size_of::<crate::registry::objects::Registry<63>>(),
            crate::registry::read().len(),
        ];
        let _ = apdu.set_outgoing();
        for (i, value) in values.iter().enumerate() {
            apdu.buffer_mut()[4 * i..4 * i + 4].copy_from_slice(&(*value as u32).to_be_bytes());
        }
        apdu.set_outgoing_length(20);
        return ApduStatus::success();
    }
    if apdu.p1() == 0xf3 {
        crate::registry::perf::clear();
        return ApduStatus::success();
    }
    if apdu.p1() == 0xf8 {
        let start = apdu.p2() as usize * 7;
        if start >= crate::registry::perf::COUNT {
            return ApduStatus::wrong_data();
        }
        let count = (crate::registry::perf::COUNT - start).min(7);
        let _ = apdu.set_outgoing();
        for i in 0..count {
            let sample = crate::registry::perf::sample(start + i).unwrap();
            encode_perf_sample(sample, &mut apdu.buffer_mut()[i * 28..i * 28 + 28]);
        }
        apdu.set_outgoing_length(count * 28);
        return ApduStatus::success();
    }
    if apdu.p1() == 0xf2 {
        let Some(sample) = crate::registry::perf::sample(apdu.p2() as usize) else {
            return ApduStatus::wrong_data();
        };
        let _ = apdu.set_outgoing();
        encode_perf_sample(sample, &mut apdu.buffer_mut()[..28]);
        apdu.set_outgoing_length(28);
        return ApduStatus::success();
    }
    if apdu.p1() == 0xf0 {
        let start = oxi_core::core::target::monotonic_ticks();
        let overhead = oxi_core::core::target::monotonic_ticks().wrapping_sub(start);
        let values = [
            LAST_TICKS.load(Ordering::Relaxed),
            oxi_core::core::target::monotonic_hz(),
            oxi_core::core::target::core_clock_hz(),
            overhead,
        ];
        let _ = apdu.set_outgoing();
        for (i, value) in values.iter().enumerate() {
            apdu.buffer_mut()[i * 4..i * 4 + 4].copy_from_slice(&value.to_be_bytes());
        }
        apdu.set_outgoing_length(16);
        return ApduStatus::success();
    }
    let start = oxi_core::core::target::monotonic_ticks();
    let status = if apdu.p1() == 0xf1 {
        if storage_codec_probe().is_ok() {
            ApduStatus::success()
        } else {
            ApduStatus::memory_failure()
        }
    } else {
        process_inner(apdu)
    };
    LAST_TICKS.store(
        oxi_core::core::target::monotonic_ticks().wrapping_sub(start),
        Ordering::Relaxed,
    );
    status
}

fn process_inner(apdu: &mut dyn SEApdu) -> ApduStatus {
    if !READY.load(Ordering::Relaxed) {
        return ApduStatus::conditions_not_satisfied();
    }
    let parent = selected_app::root_security_domain_instance_aid();
    let tag = 0xd000 | u16::from(apdu.p2());
    match apdu.p1() {
        0xf4 => match fill_erased_noise() {
            Ok(count) => {
                let _ = apdu.set_outgoing();
                apdu.buffer_mut()[..4].copy_from_slice(&count.to_be_bytes());
                apdu.set_outgoing_length(4);
                ApduStatus::success()
            }
            Err(error) => error.status(),
        },
        0xf5 => selected_app::registry_result_status(transaction_probe(apdu.p2())),
        0xfa => selected_app::registry_result_status(capacity_probe()),
        0xfb => selected_app::registry_result_status(data_pair_probe()),
        0xf6 => {
            apdu.set_incoming_and_receive();
            let Ok(bytes) = <[u8; 4]>::try_from(apdu.incoming_data()) else {
                return ApduStatus::wrong_data();
            };
            let len = u32::from_be_bytes(bytes) as usize;
            if len > 16 * 1024 {
                return ApduStatus::wrong_data();
            }
            selected_app::registry_result_status(selected_app::write_registry_data_objects(
                parent,
                &[(tag, len)],
                |_, i| (i % 251) as u8,
            ))
        }
        0xf7 => {
            apdu.set_incoming_and_receive();
            let Ok(bytes) = <[u8; 8]>::try_from(apdu.incoming_data()) else {
                return ApduStatus::wrong_data();
            };
            let start = u32::from_be_bytes(bytes[..4].try_into().unwrap()) as usize;
            let len = u32::from_be_bytes(bytes[4..].try_into().unwrap()) as usize;
            if len > 244 {
                return ApduStatus::wrong_data();
            }
            let _ = apdu.set_outgoing();
            match selected_app::load_registry_data_object_range(
                &parent,
                tag,
                start,
                &mut apdu.buffer_mut()[..len],
            ) {
                Ok(len) => {
                    apdu.set_outgoing_length(len);
                    ApduStatus::success()
                }
                Err(error) => error.status(),
            }
        }
        0 => {
            let _ = apdu.set_outgoing();
            apdu.buffer_mut()[..4].copy_from_slice(&(TEST_BYTES as u32).to_be_bytes());
            apdu.buffer_mut()[4..8].copy_from_slice(
                &(selected_app::registry_write_fault::erase_count() as u32).to_be_bytes(),
            );
            apdu.set_outgoing_length(8);
            ApduStatus::success()
        }
        1 => {
            apdu.set_incoming_and_receive();
            selected_app::registry_result_status(selected_app::upsert_registry_data_object(
                parent,
                tag,
                apdu.incoming_data(),
            ))
        }
        2 => {
            let _ = apdu.set_outgoing();
            match selected_app::load_registry_data_object(&parent, tag, apdu.buffer_mut()) {
                Ok(len) => {
                    // Return directly from shared storage, without chunk copies.
                    apdu.set_outgoing_length(len);
                    ApduStatus::success()
                }
                Err(error) => error.status(),
            }
        }
        3 => {
            let aid = rustlet_runtime::Aid::from_array([
                b'D',
                b'A',
                b'T',
                b'A',
                (tag >> 8) as u8,
                tag as u8,
            ]);
            match selected_app::delete_visible_managed_object_under_authority(parent, &aid, false) {
                Ok(()) => ApduStatus::success(),
                Err(error) => error.status(),
            }
        }
        4 => {
            apdu.set_incoming_and_receive();
            let data = apdu.incoming_data();
            if data.len() != 2 || apdu.p2() > 2 {
                return ApduStatus::wrong_data();
            }
            let cut = u16::from_le_bytes([data[0], data[1]]) as usize;
            if selected_app::registry_write_fault::arm(cut, apdu.p2()) {
                ApduStatus::success()
            } else {
                ApduStatus::conditions_not_satisfied()
            }
        }
        5 => {
            let _ = apdu.set_outgoing();
            apdu.buffer_mut()[0] = u8::from(selected_app::registry_write_fault::hit());
            apdu.set_outgoing_length(1);
            ApduStatus::success()
        }
        6 => {
            let backend = selected_app::SecurityDomainObjectBackend::NullSecurityDomain;
            selected_app::registry_result_status(selected_app::registry_operation(|| {
                selected_app::upsert_security_domain_state_object(
                    parent, parent, CHILD, backend, [0; 3], b"child",
                )?;
                selected_app::upsert_security_domain_state_object(
                    CHILD,
                    parent,
                    GRANDCHILD,
                    backend,
                    [0; 3],
                    b"grandchild",
                )?;
                selected_app::upsert_registry_data_object(CHILD, 0xd081, b"child-data")?;
                selected_app::upsert_registry_data_object(GRANDCHILD, 0xd082, b"grandchild-data")
            }))
        }
        7 => {
            let mut buffer = [0u8; 32];
            let child = selected_app::read_security_domain_state_by_aid(&CHILD, &mut buffer)
                == Some(5)
                && &buffer[..5] == b"child";
            let grandchild =
                selected_app::read_security_domain_state_by_aid(&GRANDCHILD, &mut buffer)
                    == Some(10)
                    && &buffer[..10] == b"grandchild";
            let child_data = selected_app::load_registry_data_object(&CHILD, 0xd081, &mut buffer)
                == Ok(10)
                && &buffer[..10] == b"child-data";
            let grandchild_data =
                selected_app::load_registry_data_object(&GRANDCHILD, 0xd082, &mut buffer) == Ok(15)
                    && &buffer[..15] == b"grandchild-data";
            let _ = apdu.set_outgoing();
            apdu.buffer_mut()[..4].copy_from_slice(&[
                presence(&CHILD, child),
                presence(&GRANDCHILD, grandchild),
                presence(
                    &Aid::from_array([b'D', b'A', b'T', b'A', 0xd0, 0x81]),
                    child_data,
                ),
                presence(
                    &Aid::from_array([b'D', b'A', b'T', b'A', 0xd0, 0x82]),
                    grandchild_data,
                ),
            ]);
            apdu.set_outgoing_length(4);
            ApduStatus::success()
        }
        8 => {
            match selected_app::delete_visible_managed_object_under_authority(
                parent,
                &CHILD,
                apdu.p2() == 1,
            ) {
                Ok(()) => ApduStatus::success(),
                Err(error) => error.status(),
            }
        }
        9 => selected_app::registry_result_status(selected_app::registry_operation(|| {
            selected_app::upsert_security_domain_state_object(
                parent,
                parent,
                CHILD,
                selected_app::SecurityDomainObjectBackend::KernelSecurityDomain,
                [0x80, 0, 0],
                &[],
            )?;
            for usage in [
                crate::security_domain::Scp03KeyUsage::Enc,
                crate::security_domain::Scp03KeyUsage::Mac,
            ] {
                selected_app::upsert_scp03_key_object(CHILD, 1, 3, usage, &[usage.as_byte(); 16])?;
            }
            Ok(())
        })),
        10 => selected_app::install_kernel_side_security_domain_instance(
            selected_app::SecurityDomainObjectBackend::KernelSecurityDomain,
            CHILD,
            parent,
            GRANDCHILD,
            &[0x80, 0, 0],
        ),
        11 => {
            let mut key = [0; 16];
            let mut result = [0u8; 3];
            result[0] = u8::from(
                selected_app::find_managed_object_kind_by_aid(&GRANDCHILD)
                    == Some(selected_app::ManagedObjectKind::SecurityDomain),
            );
            for (index, usage) in [
                crate::security_domain::Scp03KeyUsage::Enc,
                crate::security_domain::Scp03KeyUsage::Mac,
            ]
            .into_iter()
            .enumerate()
            {
                result[index + 1] = u8::from(
                    selected_app::load_scp03_key_material(&GRANDCHILD, 1, 3, usage, &mut key)
                        == Some(16)
                        && key == [usage.as_byte(); 16],
                );
            }
            crate::core::secure_zero(&mut key);
            apdu.set_outgoing();
            apdu.buffer_mut()[..3].copy_from_slice(&result);
            apdu.set_outgoing_length(3);
            ApduStatus::success()
        }
        12 | 14 => {
            // Exercise the ordinary hook entry with a registry mutation already
            // staged, under the same savepoint rule as GP management dispatch.
            let inject = apdu.p1() == 14;
            let mode = apdu.p2();
            let operation = match selected_app::RegistryOperationScope::begin(true) {
                Ok(scope) => scope,
                Err(error) => return error.status(),
            };
            let status = match selected_app::upsert_registry_data_object(parent, 0xd0f0, &[mode]) {
                Err(error) => error.status(),
                Ok(()) => {
                    match selected_app::security_domain_get_data(0xef00 | u16::from(mode), &mut [])
                    {
                        Ok(_) => ApduStatus::success(),
                        Err(status) => status,
                    }
                }
            };
            operation.finish(status.sw1 == 0x90 && status.sw2 == 0);
            if inject && !selected_app::registry_write_fault::arm(0, 1) {
                return ApduStatus::conditions_not_satisfied();
            }
            status
        }
        _ => ApduStatus::wrong_data(),
    }
}

// Distinguish absence from a surviving object with corrupt/unexpected content.
fn presence(aid: &Aid, valid: bool) -> u8 {
    if valid {
        1
    } else if selected_app::find_managed_object_kind_by_aid(aid).is_none() {
        0
    } else {
        2
    }
}

// Exercise the real get_puf-derived header CMAC and independent body CRC.
fn storage_codec_probe() -> Result<(), crate::registry::format::PersistenceFormatError> {
    use crate::registry::format as f;
    let mut block = [0xff; 256];
    f::encode_object_block(f::DATA_BLOCK_MAGIC, b"header probe", 256, &mut block)?;
    if f::decode_object_block_at(&block, 0, 256)?.payload != b"header probe" {
        return Err(f::PersistenceFormatError::Authentication);
    }
    block[32] ^= 1;
    if f::decode_object_block_at(&block, 0, 256).is_ok() {
        return Err(f::PersistenceFormatError::Authentication);
    }
    block[32] ^= 1;
    block[8] ^= 1;
    if f::decode_object_block_at(&block, 0, 256).is_ok() {
        return Err(f::PersistenceFormatError::Authentication);
    }
    Ok(())
}

/// Fill only unprotected erased pages. Never overwrite any live or rollback
/// block, including its all-FF padding. No erase is performed by this fixture.
fn fill_erased_noise() -> crate::registry::objects::RegistryResult<u32> {
    use crate::registry::objects::RegistryError;
    use crate::registry::{format, payload, physical, state, storage};
    let area = storage::persistent_registry_area_bytes().ok_or(RegistryError::Persistence)?;
    let protected = &state::USED_PAGES;
    let _count = payload::build_current_persistence_protection(area, 256, protected)
        .ok_or(RegistryError::Persistence)?;
    let mut page = [0u8; 256];
    let mut filled = 0u32;
    for offset in (256..area.len()).step_by(256) {
        let range = format::PersistentRange::new(offset, 256);
        if format::Protection::overlaps(protected, range)
            || area[offset..offset + 256].iter().any(|b| *b != 0xff)
        {
            continue;
        }
        for (i, byte) in page.iter_mut().enumerate() {
            *byte = ((offset / 256 * 73 + i * 29 + i / 7) % 251) as u8;
        }
        if (offset / 256).is_multiple_of(2) {
            page[..4].copy_from_slice(&format::DATA_BLOCK_MAGIC.to_le_bytes());
            page[4..8].copy_from_slice(&u32::MAX.to_le_bytes());
        }
        physical::program_page(physical::persistence_area().start + offset, &page)
            .map_err(|_| RegistryError::Persistence)?;
        filled += 1;
    }
    Ok(filled)
}

struct PerfObserver;
impl crate::registry::savepoint::RollbackObserver for PerfObserver {
    fn before_rollback(_: &crate::registry::savepoint::RollbackView) {}
    fn after_rollback(_: crate::registry::savepoint::InvalidatedSlots) {}
}
// Exercise the full ten-page BOSS and all six rollback roots on real flash.
// The enclosing local scope restores the original registry before returning.
fn capacity_probe() -> crate::registry::objects::RegistryResult {
    use crate::registry::{self, objects::RegistryError, savepoint::OperationScope};
    let parent = selected_app::root_security_domain_instance_aid();
    let outer = OperationScope::<PerfObserver>::begin(true)?;
    let aid = |id| Aid::from_array([0xf1, 0x63, id]);
    let mut id = 0u8;
    while registry::read().len() < 63 {
        registry::edit().upsert_data_object(parent, aid(id), &[id])?;
        id += 1;
    }
    if id == 0 {
        return Err(RegistryError::InvalidState);
    }
    if registry::edit().upsert_data_object(parent, aid(id), &[id]) != Err(RegistryError::Capacity) {
        return Err(RegistryError::InvalidState);
    }
    let a = OperationScope::<PerfObserver>::begin(true)?;
    let b = OperationScope::<PerfObserver>::begin(true)?;
    let c = OperationScope::<PerfObserver>::begin(true)?;
    let d = OperationScope::<PerfObserver>::begin(true)?;
    if OperationScope::<PerfObserver>::begin(true).is_ok() {
        return Err(RegistryError::InvalidState);
    }
    registry::edit().upsert_data_object(parent, aid(0), b"changed")?;
    d.rollback();
    if registry::read().len() != 63 {
        return Err(RegistryError::InvalidState);
    }
    let mut byte = [0xff];
    let view = registry::read();
    let object = view
        .find_data_object(&parent, &aid(0))
        .ok_or(RegistryError::NotFound)?;
    if object.read_range(0, &mut byte)? != 1 || byte != [0] {
        return Err(RegistryError::InvalidData);
    }
    drop(view);
    c.accept();
    b.accept();
    a.accept();
    outer.rollback();
    Ok(())
}

// Exercise real encrypted preparations inside nested scopes, including failure
// of B after A was attached. The enclosing scope rolls back all test objects.
fn data_pair_probe() -> crate::registry::objects::RegistryResult {
    use crate::registry::{objects::RegistryError, savepoint::OperationScope};
    let parent = selected_app::root_security_domain_instance_aid();
    let scope = OperationScope::<PerfObserver>::begin(true)?;
    let result = (|| {
        let write = |objects: &[(u16, usize)], values: &[&[u8]]| {
            selected_app::write_registry_data_objects(parent, objects, |which, i| values[which][i])
        };
        let check = |tag, expected: &[u8]| {
            let mut out = [0; 16];
            let n = selected_app::load_registry_data_object(&parent, tag, &mut out)?;
            if &out[..n] == expected { Ok(()) } else { Err(RegistryError::InvalidData) }
        };
        write(&[(0xd0f8, 3), (0xd0f9, 3)], &[b"old", b"two"])?;
        // The second size is rejected before asking the producer for its bytes.
        if write(&[(0xd0f8, 3), (0xd0f9, usize::MAX)], &[b"new", b""]).is_ok() {
            return Err(RegistryError::InvalidData);
        }
        check(0xd0f8, b"old")?;
        check(0xd0f9, b"two")?;
        // Only member 1 changes: preserve the original producer index.
        write(&[(0xd0f8, 3), (0xd0f9, 3)], &[b"old", b"new"])?;
        check(0xd0f8, b"old")?;
        check(0xd0f9, b"new")?;
        // Repeated tags retain sequential last-writer semantics.
        write(&[(0xd0f8, 3), (0xd0f8, 3)], &[b"one", b"end"])?;
        check(0xd0f8, b"end")?;
        write(&[(0xd0f8, 3), (0xd0f9, 3)], &[b"end", b"new"])?;
        Ok(())
    })();
    scope.rollback();
    result
}

fn transaction_probe(mode: u8) -> crate::registry::objects::RegistryResult {
    use crate::registry::objects::RegistryError;
    use crate::registry::{self, savepoint::OperationScope, transaction};
    if mode > 2 {
        return Err(RegistryError::InvalidData);
    }
    let parent = selected_app::root_security_domain_instance_aid();
    let aid = Aid::from_array([b'D', b'A', b'T', b'A', 0xd0, 0xfe]);
    // The external APDU already owns the transaction.
    let scope = OperationScope::<PerfObserver>::begin(true)?;
    if let Err(error) = registry::edit().upsert_data_object(parent, aid, b"transaction benchmark") {
        scope.rollback();
        transaction::request_abort();
        return Err(error);
    }
    if mode == 1 {
        scope.rollback();
    } else {
        scope.accept();
    }
    if mode == 0 {
        transaction::request_abort();
    }
    // The dispatcher performs commit/rollback before the response is emitted.
    Ok(())
}

fn encode_perf_sample(sample: crate::registry::perf::Sample, out: &mut [u8]) {
    out[..4].copy_from_slice(&sample.calls.to_be_bytes());
    out[4..12].copy_from_slice(&sample.total.to_be_bytes());
    out[12..16].copy_from_slice(&sample.min.to_be_bytes());
    out[16..20].copy_from_slice(&sample.max.to_be_bytes());
    out[20..24].copy_from_slice(&sample.last.to_be_bytes());
    out[24..28].copy_from_slice(&oxi_core::core::target::monotonic_hz().to_be_bytes());
}
