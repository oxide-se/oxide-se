//! Opt-in audit probes. Synthetic inputs never contain production secrets.
#![deny(unsafe_code)]
#[allow(unsafe_code)]
mod cpu_fault_probe;
use super::{ApduFilter, KernelAppModule};
use crate::{apdu_manager::ApduStatus, object_registry_persistence as persistence};
use rustlet_runtime::SEApdu;

pub(crate) struct Module;
impl KernelAppModule for Module {
    fn initialize() { cpu_fault_probe::initialize(); }
}
pub(crate) const APDU_FILTER: ApduFilter = ApduFilter { matches, process };
fn matches(apdu: &dyn SEApdu) -> bool {
    apdu.ins() == 0xa1
}
fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    if apdu.p1() == 7 {
        return if cpu_fault_probe::set_escalation(apdu.p2() != 0) {
            ApduStatus::success()
        } else { ApduStatus::wrong_data() };
    }
    if apdu.p1() == 6 {
        let Some(fault) = oxi_core::core::target::last_mem_manage_fault() else {
            return ApduStatus::referenced_data_not_found();
        };
        apdu.set_outgoing();
        let out = apdu.buffer_mut();
        out[0..4].copy_from_slice(&fault.status.to_le_bytes());
        out[4..8].copy_from_slice(&fault.cfsr.to_le_bytes());
        out[8..12].copy_from_slice(&fault.hfsr.to_le_bytes());
        apdu.set_outgoing_length(12);
        return ApduStatus::success();
    }
    if apdu.p1() == 5 {
        apdu.set_incoming_and_receive();
        let bytes = apdu.incoming_data();
        if bytes.is_empty() || bytes.len() > 16 { return ApduStatus::wrong_data(); }
        let aid = rustlet_runtime::Aid::new(bytes);
        apdu.set_outgoing();
        let Some(len) = crate::selected_app::integrity_package_mapping(&aid, apdu.buffer_mut()) else {
            return ApduStatus::referenced_data_not_found();
        };
        apdu.set_outgoing_length(len);
        return ApduStatus::success();
    }

    let result = match apdu.p1() {
        0 => scanner_probe(true),
        1 => crate::fae_runtime::integrity_mapping_probe(),
        2 => crate::fae_runtime::integrity_descriptor_probe(),
        3 => key_storage_probe(),
        4 => scanner_probe(false),
        _ => return ApduStatus::wrong_data(),
    };
    apdu.set_outgoing();
    apdu.buffer_mut()[0] = u8::from(result);
    apdu.set_outgoing_length(1);
    ApduStatus::success()
}

fn scanner_probe(interrupt_outer: bool) -> bool {
    const PAGE: usize = 256;
    // Heap scratch avoids increasing the kernel stack with flash-sized arrays.
    let mut area = alloc::vec![0xff; PAGE * 6];
    let mut payload = alloc::vec![0xff; PAGE * 3];
    let setup = (|| {
        persistence::encode_registry_block(1, &[], PAGE, &mut area[..PAGE]).ok()?;
        persistence::encode_registry_block(
            999,
            &[],
            PAGE,
            &mut payload[PAGE - persistence::OBJECT_BLOCK_HEADER_LEN..],
        )
        .ok()?;
        let len = persistence::encode_object_block(
            persistence::PACKAGE_BLOCK_MAGIC,
            &payload,
            PAGE,
            &mut area[PAGE..],
        )
        .ok()?;
        let before = persistence::find_latest_registry_block(&area, PAGE).ok()??;
        if before.mutation_counter != 1 {
            return None;
        }
        if interrupt_outer {
            area[PAGE + len - persistence::BLOCK_CRC_LEN..PAGE + len].fill(0xff);
        }
        let after = persistence::find_latest_registry_block(&area, PAGE).ok()??;
        Some(after.mutation_counter == 1)
    })();
    setup == Some(true)
}

fn key_storage_probe() -> bool {
    use crate::object_registry::{KeyObjectState, KeyObjectType, ObjectRegistry};
    use rustlet_runtime::Aid;
    let mut registry: ObjectRegistry<1> = ObjectRegistry::new();
    let marker = [0xc7; 16];
    if registry
        .upsert_key_object(
            Aid::new(b"owner"),
            Aid::new(b"key"),
            KeyObjectType::Scp03Static,
            KeyObjectState::Active,
            1,
            3,
            1,
            &marker,
        )
        .is_err()
    {
        return false;
    }
    let mut out = [0; 64];
    let Some(object) = registry.entries().next() else {
        return false;
    };
    let Ok((_, len)) = persistence::encode_registry_object_payload(object, &mut out) else {
        return false;
    };
    // A passing result requires a representation that does not expose the marker.
    !out[..len]
        .windows(marker.len())
        .any(|window| window == marker)
}
