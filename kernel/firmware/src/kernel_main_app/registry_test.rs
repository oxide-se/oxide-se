//! Private diagnostic access to the normal persistent registry (not raw flash).
#![forbid(unsafe_code)]
use core::sync::atomic::{AtomicBool, Ordering};
use super::{ApduFilter, KernelAppModule};
use crate::{apdu_manager::ApduStatus, selected_app};
use rustlet_runtime::{Aid, SEApdu};

const TEST_BYTES: usize = 64 * 1024;
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
            && total > TEST_BYTES
            && crate::core::flash::reserve_persistence_tail(total - TEST_BYTES).is_ok();
        READY.store(ready, Ordering::Relaxed);
    }
}

pub(crate) const APDU_FILTER: ApduFilter = ApduFilter { matches, process };

fn matches(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == 0xa0
}

fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    if !READY.load(Ordering::Relaxed) {
        return ApduStatus::conditions_not_satisfied();
    }
    let parent = selected_app::root_security_domain_instance_aid();
    let tag = 0xd000 | u16::from(apdu.p2());
    match apdu.p1() {
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
            let child = selected_app::find_security_domain_state_by_aid(&CHILD).as_deref()
                == Some(b"child".as_slice());
            let grandchild = selected_app::find_security_domain_state_by_aid(&GRANDCHILD).as_deref()
                == Some(b"grandchild".as_slice());
            let mut buffer = [0u8; 32];
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
            let operation = selected_app::RegistryOperationScope::begin(true);
            let status = match selected_app::upsert_registry_data_object(parent, 0xd0f0, &[mode]) {
                Err(error) => error.status(),
                Ok(()) => match selected_app::security_domain_get_data(0xef00 | u16::from(mode), &mut []) {
                    Ok(_) => ApduStatus::success(),
                    Err(status) => status,
                },
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
