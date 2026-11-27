//! Opt-in audit probes. Synthetic inputs never contain production secrets.
#![deny(unsafe_code)]
#[allow(unsafe_code)]
mod cpu_fault_probe;
use super::{ApduFilter, KernelAppModule};
use crate::{apdu_manager::ApduStatus, registry::format as persistence};
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
    if apdu.p1() == 3 {
        let Some(report) = crate::selected_app::integrity_key_storage(apdu.p2()) else {
            return ApduStatus::conditions_not_satisfied();
        };
        apdu.set_outgoing();
        apdu.buffer_mut()[..report.len()].copy_from_slice(&report);
        apdu.set_outgoing_length(report.len());
        return ApduStatus::success();
    }
    if apdu.p1() == 8 {
        return if oxi_core::core::redirect_probe::arm(apdu.p2() as u32) {
            ApduStatus::success()
        } else { ApduStatus::wrong_data() };
    }
    if apdu.p1() == 9 {
        let report = oxi_core::core::redirect_probe::report();
        apdu.set_outgoing();
        for (i, value) in report.iter().enumerate() {
            apdu.buffer_mut()[i*4..i*4+4].copy_from_slice(&value.to_le_bytes());
        }
        apdu.set_outgoing_length(24);
        return ApduStatus::success();
    }
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
        persistence::encode_registry_block_at(
            PAGE * 3,
            999,
            &[],
            PAGE,
            &mut payload[PAGE - persistence::OBJECT_BLOCK_HEADER_LEN..],
        )
        .ok()?;
        let _len = persistence::encode_object_block_at(
            PAGE,
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
            area[PAGE + 16..PAGE + 32].fill(0xff);
        }
        let after = persistence::find_latest_registry_block(&area, PAGE).ok()??;
        Some(after.mutation_counter == 1)
    })();
    setup == Some(true)
}
