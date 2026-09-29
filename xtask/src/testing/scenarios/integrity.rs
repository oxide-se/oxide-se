//! Skeleton for the adversarial kernel-integrity campaign.
//!
//! Finding identifiers below distinguish the Markdown report (F1..F5) from
//! the HTML report (F-01..F-10). Their numbering is not interchangeable.
//! SD key-authority, registry-provenance, package-boundary, shared-gate and
//! serialized-state-length checks run on target.
//! Remaining probes are placeholders.
//! Incomplete coverage always returns an error, even when implemented checks pass.

use super::*;

/// Run independent audit regressions on Pico1/QEMU or Pico2/OpenOCD.
///
/// Implementation must use the existing target-session abstraction, preserve
/// destructive-operation authorization, and never classify a known security
/// failure as a passing regression merely because it was expected.
pub(crate) fn run_kernel_integrity_test(
    ctx: &TestContext,
    board: &str,
) -> Result<(), Box<dyn Error>> {
    // TODO: Validate board/backend support and prepare the diagnostic image.
    // Use prepare_apdu_session and TargetSession rather than launching QEMU,
    // OpenOCD or serial processes here. Check build/connection/ATR failures
    // separately from a failure reached after successful probe setup.

    // TODO: Collect per-case results and continue independent cases after a
    // timeout or kernel halt. Use bounded response deadlines and a fresh boot
    // for destructive probes. Preserve flash only for explicit recovery cases;
    // reset alone must not contaminate the next case with a forged registry.
    // Require a subsequent unrelated APDU before reboot when testing liveness:
    // a successful reboot is not evidence that the original call was contained.

    type Probe = fn(&TestContext, &str) -> Result<TestReport, Box<dyn Error>>;
    let implemented: &[(&str, Probe)] = &[
        ("F1 / F-01 (single-SD coverage)", test_sd_key_authority),
        ("F-05 (mixed SD branches)", test_session_authority_binding),
        (
            "F5 (ABI pointers and descriptors)",
            test_abi_pointer_and_descriptor_validation,
        ),
        (
            "F2 (scanner and interrupted LOAD recovery)",
            test_registry_candidate_provenance,
        ),
        (
            "F3 / F-02 (package boundaries)",
            test_package_mapping_boundaries,
        ),
        (
            "F-04 (shared page and entry gate)",
            test_shared_page_and_entry_gate,
        ),
        (
            "F4 / F-03 (serialized state length)",
            test_state_slice_integrity,
        ),
        ("F4 / F-03 (unknown SVC)", test_unknown_svc_integrity),
        ("F4 / F-03 (APDU output)", test_output_apdu_integrity),
        ("F4 / F-03 (APDU ordering)", test_apdu_order_integrity),
        (
            "F-06 / F-03 (invalid deallocation)",
            test_invalid_deallocation,
        ),
        ("F4 / F-03 (CPU exceptions)", test_cpu_exception_integrity),
        ("F4 / F-03 (exception stacking)", test_stack_entry_integrity),
        (
            "F4 / F-03 (invalid execution state)",
            test_invalid_state_integrity,
        ),
    ];
    let mut passed = 0;
    let mut failed = 0;
    for &(finding, probe) in implemented {
        match probe(ctx, board) {
            Ok(report) if report.failed == 0 => {
                eprintln!(
                    "kernel_integrity: {finding}: PASS ({} checks)",
                    report.total
                );
                passed += 1;
            }
            Ok(report) => {
                eprintln!(
                    "kernel_integrity: {finding}: FAIL ({}/{} checks)\n{}\n{}",
                    report.failed, report.total, report.stdout, report.stderr
                );
                failed += 1;
            }
            Err(error) => {
                eprintln!("kernel_integrity: {finding}: ERROR: {error}");
                failed += 1;
            }
        }
    }

    // These functions are deliberately empty. Calling one is not a passed test.
    type PendingProbe = fn(&TestContext, &str);
    let probes: &[(&str, PendingProbe)] = &[
        ("F-07", test_key_storage_representation),
        ("F-08", test_redirect_interleavings),
        ("F-09", test_random_service_boundaries),
        ("F-10", test_deployment_management_policy),
        (
            "Publication / SD rollback",
            test_publication_and_sd_rollback,
        ),
    ];
    for &(finding, probe) in probes {
        probe(ctx, board);
        eprintln!("kernel_integrity: {finding}: NOT IMPLEMENTED");
    }

    // TODO: Emit a per-finding summary with evidence level, passed/failed checks,
    // infrastructure errors and unimplemented coverage. Return a failing result
    // for violated invariants or incomplete required coverage. Do not publish
    // stack baselines or claim performance/entropy/race guarantees from this run.
    eprintln!(
        "KERNEL-INTEGRITY-INCOMPLETE board={board} passed={passed} failed={failed} unimplemented={}",
        probes.len()
    );
    Err(format!(
        "kernel_integrity: {passed} passed groups, {failed} failed groups, {} unimplemented groups; F1 multi-SD coverage remains pending",
        probes.len()
    )
    .into())
}

/// Exercise the existing on-target SD key-authority regression fixtures.
fn test_sd_key_authority(ctx: &TestContext, board: &str) -> Result<TestReport, Box<dyn Error>> {
    // Force delegated SCP03: successful secure-channel authentication must use
    // SDDISPATCH and Rustlet key loading, never the native kernel SCP03 path.
    // The existing scenario also checks PermissionDenied AND unchanged output
    // from ordinary SD/application process_apdu, then repeats the denial after
    // an application panic and SD reselection, without rebooting the target.
    // Uses function `process_apdu` from files `rustlets/complete_security_domain/src/main.rs`
    // and `rustlets/tests/minimal_valid_test/src/main.rs` for the denial probes.
    // Uses function `run_rustlet_security_domain_test_for_board` from file `xtask/src/testing/scenarios/gp.rs`.
    // TODO: Add distinct keyed SDs to verify exact key ownership and authority
    // retirement across SD-to-SD switching and a fault inside SDDISPATCH itself.
    // The existing application-panic check does not cover an SD dispatch fault.
    let sd_ctx =
        ctx.with_config("configs/config_rustlet_security_domain_delegated_scp03_test.toml");
    run_rustlet_security_domain_test_for_board(&sd_ctx, LayoutImageFormat::Elf, board)
}

/// Keep scanner evidence separate from recovery through the public LOAD path.
fn test_registry_candidate_provenance(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let registry_ctx = ctx.with_config("configs/config_registry_integrity_test.toml");
    let mut target =
        testing::target::prepare_apdu_session(&registry_ctx, board, LayoutImageFormat::Elf, true)?;
    const TAG: u16 = 0xDF01;
    const MARKER: &[u8] = b"registry-provenance-before-load";
    const CATEGORIES: [u8; 3] = [0x80, 0x40, 0x20];
    let mut baseline = Vec::new();
    let mut report = TestReport::passed(0);

    target.boot(
        "integrity registry setup",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            // P1=4 is the same nested BOSS with an intact outer C0DE CRC.
            // Uses function `scanner_probe` from file `kernel/firmware/src/kernel_main_app/integrity_test.rs`.
            expect_response(
                client.exchange(&CommandBuilder::gp_command(0xA1, 4, 0, &[], 1))?,
                &[1],
                (0x90, 0x00),
                "F2 scanner valid-container control",
            )?;
            report.total += 1;
            let response = client.exchange(&CommandBuilder::gp_command(0xA1, 0, 0, &[], 1))?;
            expect_response(
                response.clone(),
                &response.data,
                (0x90, 0x00),
                "F2 scanner interrupted-container probe",
            )?;
            if response.data != [0] && response.data != [1] {
                return Err("F2 scanner returned an invalid diagnostic payload".into());
            }
            report.total += 1;
            if response.data == [0] {
                report.failed += 1;
                eprintln!("kernel_integrity: F2 scanner: FAIL (previous BOSS not preserved)");
            } else {
                eprintln!("kernel_integrity: F2 scanner: PASS");
            }
            // Publish an instance and data absent from the predeployment manifest.
            // A boot which silently replays the manifest cannot pass these checks.
            expect_status(
                client.exchange(&CommandBuilder::install(
                    crate_rustlet_minimal_valid_test_aid(),
                ))?,
                (0x90, 0x00),
                "F2 install baseline instance",
            )?;
            expect_status(
                client.exchange(&CommandBuilder::gp_store_data_with_tag(TAG, MARKER))?,
                (0x90, 0x00),
                "F2 store baseline marker",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::gp_get_data(TAG, MARKER.len() as u8))?,
                MARKER,
                (0x90, 0x00),
                "F2 read baseline marker",
            )?;
            report.total += 3;
            for category in CATEGORIES {
                let response =
                    client.exchange(&CommandBuilder::gp_get_status(category, false, &[]))?;
                // A category can be empty (notably ISD for NullSecurityDomain).
                // Preserve that response too; recovery must reproduce it exactly.
                if response.status != (0x90, 0x00)
                    && !(response.status == (0x6A, 0x88) && response.data.is_empty())
                {
                    return Err(format!(
                        "F2 baseline GET STATUS {category:02X}: unexpected {:?}",
                        response.status
                    )
                    .into());
                }
                baseline.push(response);
                report.total += 1;
            }
            begin_interrupted_registry_load(client, false)?;
            Ok(())
        },
    )?;

    // No reflash between boots. First establish that benign interrupted LOADs
    // preserve the published graph, then repeat with an empty, high-counter BOSS.
    for forged in [false, true] {
        let phase = if forged {
            "integrity registry forged recovery"
        } else {
            "integrity registry control recovery"
        };
        target.reboot(phase, APDU_RESPONSE_TIMEOUT, |client| {
            let label = if forged { "forged" } else { "control" };
            let marker = client.exchange(&CommandBuilder::gp_get_data(TAG, MARKER.len() as u8))?;
            let mut intact = marker.status == (0x90, 0x00) && marker.data == MARKER;
            if !intact {
                eprintln!("kernel_integrity: F2 {label}: persisted marker lost or changed (status={:02X?}, data={:02X?})", marker.status, marker.data);
            }
            for (category, expected) in CATEGORIES.into_iter().zip(&baseline) {
                let observed = client.exchange(&CommandBuilder::gp_get_status(category, false, &[]))?;
                if observed != *expected {
                    eprintln!("kernel_integrity: F2 {label}: GET STATUS {category:02X} changed: expected {expected:02X?}, observed {observed:02X?}");
                    intact = false;
                }
            }
            report.total += 1;
            if intact {
                eprintln!("kernel_integrity: F2 {label} LOAD/reboot: PASS (marker and registry listings preserved)");
            } else {
                report.failed += 1;
                eprintln!("kernel_integrity: F2 {label} LOAD/reboot: FAIL (marker or registry listings changed)");
            }
            if !forged {
                if !intact {
                    return Err("F2 benign recovery control failed; forged recovery was not attempted".into());
                }
                begin_interrupted_registry_load(client, true)?;
            }
            Ok(())
        })?;
    }
    Ok(report)
}

/// Write two complete flash pages, but never finalize or publish the package.
fn begin_interrupted_registry_load(
    client: &mut ApduClient,
    forged: bool,
) -> Result<(), Box<dyn Error>> {
    let payload = registry_load_payload(forged);
    let hash = Sha256::digest(&payload);
    expect_status(
        client.exchange(&CommandBuilder::gp_install_for_load(
            crate_rustlet_getting_started_test_aid(),
            root_security_domain_aid(),
            payload.len() as u32,
            &hash,
        ))?,
        (0x90, 0x00),
        "F2 INSTALL for interrupted LOAD",
    )?;
    let encoded = apdu_tool::gp::encode_load_file_data_block(&payload)?;
    let tlv_len = encoded.len() - payload.len();
    // The 12-byte C0DE header puts the embedded BOSS at flash offset 256.
    // Sending 512 payload bytes flushes its entire page, including its CRC,
    // while the outer C0DE CRC and the last 256 payload bytes remain unwritten.
    // No APDU may follow here: management commands can cancel an active LOAD.
    for (number, chunk) in encoded[..tlv_len + 512].chunks(128).enumerate() {
        expect_status(
            client.exchange(&CommandBuilder::gp_load_block(number as u8, false, chunk))?,
            (0x90, 0x00),
            "F2 non-final LOAD block",
        )?;
    }
    Ok(())
}

/// An empty BOSS is a valid format fixture, not executable FAE code.
fn registry_load_payload(forged: bool) -> Vec<u8> {
    const PAGE: usize = 256; // Logical flash page on both Pico targets.
    let mut payload = vec![0xFF; PAGE * 3];
    if forged {
        let boss = &mut payload[PAGE - 12..PAGE * 2 - 12];
        boss[..4].copy_from_slice(&0x600D_B055u32.to_le_bytes());
        boss[4..8].copy_from_slice(&(PAGE as u32).to_le_bytes());
        boss[8..12].copy_from_slice(&999u32.to_le_bytes());
        boss[12..16].copy_from_slice(&0u32.to_le_bytes());
        let crc = registry_crc64(&boss[..PAGE - 8]);
        boss[PAGE - 8..].copy_from_slice(&crc.to_le_bytes());
    }
    payload
}

// CRC64/ECMA-182, matching the persistent format, not the FAE CRC32.
fn registry_crc64(bytes: &[u8]) -> u64 {
    let mut crc = 0u64;
    for &byte in bytes {
        crc ^= u64::from(byte) << 56;
        for _ in 0..8 {
            crc = (crc << 1)
                ^ if crc >> 63 != 0 {
                    0x42F0_E1EB_A9EA_3693
                } else {
                    0
                };
        }
    }
    crc
}

/// Exercise the actual dynamic C0DE placement, not just synthetic geometry.
fn test_package_mapping_boundaries(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::Management;
    let board = board_spec(board)?;
    let mapping_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&mapping_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&mapping_ctx, board, LayoutImageFormat::Elf, true)?;
    let mut total = target.boot(
        "integrity mapping ownership",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            // Uses integrity_mapping_probe in firmware/fae_runtime.rs for a separate
            // geometry check. The following Rustlet accesses provide CPU evidence.
            expect_response(
                client.exchange(&CommandBuilder::gp_command(0xa1, 1, 0, &[], 1))?,
                &[1],
                (0x90, 0),
                "F3 planner geometry",
            )?;
            let mut management = Management::open(client, false)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            mapping_marker(client, 0xdf31, &MAPPING_BEFORE)?;
            management.load(client, aid, &payload)?;
            mapping_marker(client, 0xdf32, &MAPPING_AFTER)?;
            let mut checks = mapping_checks(client, true)?;
            let before = mapping_erase_count(client)?;
            for iteration in 0..192u16 {
                if iteration % 32 == 0 {
                    eprintln!(
                        "integrity-mapping: recycling replacement {}/192",
                        iteration + 1
                    );
                }
                let bytes = [iteration as u8; 128];
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 1, 32, &bytes, 0))?,
                    (0x90, 0),
                    "F3 pressure publication",
                )?;
            }
            let after = mapping_erase_count(client)?;
            if after <= before {
                return Err("F3 did not observe successful sector recycling".into());
            }
            eprintln!(
                "integrity-mapping: observed {} recycled sectors",
                after - before
            );
            checks += mapping_checks(client, false)?;
            Ok(management.total + checks + 197)
        },
    )?;
    total += target.reboot(
        "integrity mapping after recycling",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let checks = mapping_checks(client, false)?;
            let mut management = Management::open(client, false)?;
            management.command(
                client,
                apdu_tool::gp::delete_aid_with_related(aid, true)?,
                (0x90, 0),
                "F3 delete instance sharing the package AID",
            )?;
            // The fixture intentionally shares one AID between package and
            // instance. Registry lookup resolves the instance first; delete
            // and verify both objects explicitly before reloading the code.
            expect_status(
                client.exchange(&CommandBuilder::gp_get_status(0x40, false, aid))?,
                (0x6a, 0x88),
                "F3 deleted instance absent",
            )?;
            management.command(
                client,
                CommandBuilder::gp_delete_aid(aid),
                (0x90, 0),
                "F3 delete package after instance",
            )?;
            expect_status(
                client.exchange(&CommandBuilder::gp_get_status(0x20, false, aid))?,
                (0x6a, 0x88),
                "F3 deleted package absent",
            )?;
            mapping_marker(client, 0xdf31, &MAPPING_BEFORE)?;
            management.load(client, aid, &payload)?;
            mapping_marker(client, 0xdf32, &MAPPING_AFTER)?;
            Ok(checks + management.total + mapping_checks(client, false)? + 4)
        },
    )?;
    total += target.reboot(
        "integrity mapping reloaded package durable",
        APDU_RESPONSE_TIMEOUT,
        |client| mapping_checks(client, false),
    )?;
    Ok(TestReport::passed(total))
}

const MAPPING_BEFORE: [u8; 4] = [0xc1, 0x13, 0x57, 0x9b];
const MAPPING_AFTER: [u8; 4] = [0xc2, 0x24, 0x68, 0xac];

fn mapping_marker(client: &mut ApduClient, tag: u16, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    expect_status(
        client.exchange(&CommandBuilder::gp_store_data_with_tag(tag, bytes))?,
        (0x90, 0),
        "F3 root-owned marker",
    )
}

fn mapping_erase_count(client: &mut ApduClient) -> Result<u32, Box<dyn Error>> {
    let response = client.exchange(&CommandBuilder::gp_command(0xa0, 0, 0, &[], 8))?;
    if response.status != (0x90, 0) {
        return Err(format!(
            "F3 bounded persistence information: unexpected status {:02x?}",
            response.status
        )
        .into());
    }
    if response.data.len() != 8 || u32::from_be_bytes(response.data[..4].try_into()?) != 64 * 1024 {
        return Err("F3 requires the bounded disposable registry fixture".into());
    }
    Ok(u32::from_be_bytes(response.data[4..8].try_into()?))
}

fn mapping_checks(client: &mut ApduClient, initial: bool) -> Result<usize, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let aid = crate_rustlet_isolation_fault_test_aid();
    let response = client.exchange(&CommandBuilder::gp_command(0xa1, 5, 0, aid, 32))?;
    if response.status != (0x90, 0) {
        return Err(format!(
            "F3 current package ownership: unexpected status {:02x?}",
            response.status
        )
        .into());
    }
    if response.data.len() != 32 {
        return Err("F3 truncated ownership diagnostic".into());
    }
    let words: Vec<u32> = response
        .data
        .chunks_exact(4)
        .map(|b| u32::from_le_bytes(b.try_into().unwrap()))
        .collect();
    let (start, len, fae, fae_len) = (words[0], words[1], words[2], words[3]);
    let end = start.checked_add(len).ok_or("F3 overflowing extent")?;
    if start % 256 != 0
        || len == 0
        || len % 256 != 0
        || fae != start + 12
        || fae.checked_add(fae_len).is_none_or(|last| last > end - 8)
        || words[6] != u32::from_le_bytes(MAPPING_BEFORE)
        || words[7] != u32::from_le_bytes(MAPPING_AFTER)
        || words[4..6].iter().any(|a| *a >= start && *a < end)
    {
        return Err("F3 inconsistent package/foreign-owner extents".into());
    }
    if initial && (words[4] >= start || words[5] < end || (start % 2048 == 0 && end % 2048 == 0)) {
        return Err(
            "F3 fixture must surround a package with a boundary inside an old 2-KiB window".into(),
        );
    }
    eprintln!("integrity-mapping: C0DE {start:#010x}..{end:#010x}, FAE {fae_len} bytes, markers {:#010x}/{:#010x}",words[4],words[5]);
    let mut checks = 1;
    for (tag, bytes) in [(0xdf31, MAPPING_BEFORE), (0xdf32, MAPPING_AFTER)] {
        expect_response(
            client.exchange(&CommandBuilder::gp_get_data(tag, 4))?,
            &bytes,
            (0x90, 0),
            "F3 foreign marker intact",
        )?;
        checks += 1;
    }
    let mut management = Management::open(client, false)?;
    management.install(client, aid)?;
    select(client, aid)?;
    checks += 1;
    // Uses faulting_read in isolation_fault_test: hardware reads of owned
    // header/code/trailer must succeed, including the explicitly accepted header.
    for address in [start, fae, end - 4] {
        let response = client.exchange(&CommandBuilder::gp_command(
            0x58,
            0,
            0,
            &address.to_le_bytes(),
            4,
        ))?;
        if response.status != (0x90, 0) {
            return Err(format!(
                "F3 owned direct read: unexpected status {:02x?}",
                response.status
            )
            .into());
        }
        if response.data.len() != 4
            || (address == start && response.data != 0x600d_c0deu32.to_le_bytes())
        {
            return Err("F3 owned direct read returned unexpected bytes".into());
        }
        checks += 1;
    }
    // CMAC consumes exactly four bytes. Positive control distinguishes range
    // rejection from an unavailable service; denied requests must leave output intact.
    for (address, result) in [
        (fae, 16),
        (start, 0x8000_0005),
        (fae + fae_len, 0x8000_0005),
        (start - 4, 0x8000_0005),
        (end, 0x8000_0005),
        (words[4], 0x8000_0005),
        (words[5], 0x8000_0005),
    ] {
        expect_response(
            client.exchange(&CommandBuilder::gp_command(
                0x59,
                0,
                0,
                &address.to_le_bytes(),
                4,
            ))?,
            &u32::to_le_bytes(result),
            (0x90, 0),
            "F3 syscall source range",
        )?;
        checks += 1;
    }
    for address in [start - 4, end, words[4], words[5]] {
        management.install(client, aid)?;
        select(client, aid)?;
        expect_status(
            client.exchange(&CommandBuilder::gp_command(
                0x58,
                0,
                0,
                &address.to_le_bytes(),
                4,
            ))?,
            (0x6f, 1),
            "F3 foreign direct read must fault",
        )?;
        // Prove containment before any reboot, with an unrelated application.
        select(client, crate_rustlet_minimal_valid_test_aid())?;
        expect_status(
            client.exchange(&CommandBuilder::process_no_data(0))?,
            (0x90, 0),
            "F3 unrelated Rustlet remains live",
        )?;
        checks += 4;
    }
    Ok(checks + management.total)
}

/// Check rejection, output scrubbing and persistent-state rollback on target.
pub(crate) fn test_state_slice_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    test_rejected_call_integrity(ctx, board, RejectedCall::StateLength)
}

pub(crate) fn test_unknown_svc_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    test_rejected_call_integrity(ctx, board, RejectedCall::UnknownSvc)
}

pub(crate) fn test_invalid_state_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    test_rejected_call_integrity(ctx, board, RejectedCall::InvalidState)
}

pub(crate) fn test_stack_entry_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    test_rejected_call_integrity(ctx, board, RejectedCall::StackEntry)
}

/// Exercise actual instruction faults and configurable-fault escalation.
pub(crate) fn test_cpu_exception_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    test_rejected_call_integrity(ctx, board, RejectedCall::CpuException)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RejectedCall {
    StateLength,
    UnknownSvc,
    InvalidState,
    StackEntry,
    CpuException,
}

// These probes must preserve the same committed state and contain staged output.
fn test_rejected_call_integrity(
    ctx: &TestContext,
    board: &str,
    probe: RejectedCall,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let expected_fault_status = if board == "raspi-pico1" {
        0x300u32
    } else {
        1 << 17
    };
    let board = board_spec(board)?;
    let (label, ins, values, status): (&str, u8, &[u8], (u8, u8)) = match probe {
        RejectedCall::StateLength => (
            "integrity serialized state length",
            0x5d,
            &[245, 255],
            (0x67, 0),
        ),
        RejectedCall::UnknownSvc => ("integrity unknown SVC", 0x5e, &[254, 255], (0x6f, 0)),
        RejectedCall::CpuException => (
            "integrity CPU exceptions",
            0x73,
            &[0, 1, 2, 3, 4, 5, 6],
            (0x6f, 1),
        ),
        RejectedCall::StackEntry => ("integrity exception stacking", 0x70, &[0, 1], (0x6f, 1)),
        RejectedCall::InvalidState => (
            "integrity invalid execution state",
            0x5f,
            &[0, 0],
            (0x6f, 1),
        ),
    };
    let state_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&state_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&state_ctx, board, LayoutImageFormat::Elf, true)?;
    let mut total = target.boot(label, APDU_RESPONSE_TIMEOUT, |client| {
        let mut management = Management::open(client, false)?;
        management.install(client, crate_rustlet_minimal_valid_test_aid())?;
        management.load(client, aid, &payload)?;
        management.install(client, aid)?;
        select(client, aid)?;
        let mut checks = 1;
        // A 244-byte state must not be rejected. The fixture serializes its
        // counter in byte zero; postcard accepts the remaining trailing bytes.
        expect_response(
            client.exchange(&CommandBuilder::gp_command(0x5d, 244, 0, &[], 2))?,
            &[0xde, 0xad],
            (0x90, 0),
            "F4 valid state capacity",
        )?;
        // The raw HandlerReturn deliberately bypasses runtime destruction.
        // Reload the fixture before inspecting durable state, rather than
        // consulting its abandoned in-memory instance.
        select(client, crate_rustlet_minimal_valid_test_aid())?;
        select(client, aid)?;
        checks += 3;
        for &value in values {
            eprintln!("integrity rejected-call: INS={ins:02x} case={value}");
            let escalated = probe == RejectedCall::CpuException && value == 4;
            if probe == RejectedCall::CpuException && value >= 4 && board.env_name != "raspi-pico2"
            {
                continue;
            }
            if escalated {
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa1, 7, 1, &[], 0))?,
                    (0x90, 0),
                    "force UsageFault escalation",
                )?;
                checks += 1;
            }
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x5c, 1))?,
                &[1],
                (0x90, 0),
                "F4 previously committed state",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::gp_command(
                    ins,
                    if escalated { 0 } else { value },
                    0,
                    &[],
                    2,
                ))?,
                // Unknown SVC aborts staged output before the outgoing
                // procedure byte. State-length rejection scrubs the bytes
                // before the normal completion path emits the response.
                if probe == RejectedCall::StateLength {
                    &[0, 0]
                } else {
                    &[]
                },
                status,
                "F4 hostile call rejected without response leakage",
            )?;
            if probe == RejectedCall::CpuException {
                let cause: u32 = if expected_fault_status == 0x300 {
                    0
                } else {
                    match value {
                        0 | 4 => 1 << 16,
                        1 => 1 << 24,
                        2 => 1 << 19,
                        3 => 1 << 25,
                        5 => 1 << 3,
                        6 => 1 << 18,
                        _ => unreachable!(),
                    }
                };
                let mut expected = [0u8; 12];
                expected[..4]
                    .copy_from_slice(&(if cause == 0 { 0x300u32 } else { cause }).to_le_bytes());
                expected[4..8].copy_from_slice(&cause.to_le_bytes());
                expected[8..]
                    .copy_from_slice(&(if escalated { 1u32 << 30 } else { 0 }).to_le_bytes());
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0xa1, 6, 0, &[], 12))?,
                    &expected,
                    (0x90, 0),
                    "CPU exception exact hardware cause",
                )?;
                checks += 1;
                if escalated {
                    expect_status(
                        client.exchange(&CommandBuilder::gp_command(0xa1, 7, 0, &[], 0))?,
                        (0x90, 0),
                        "restore UsageFault handler",
                    )?;
                    checks += 1;
                }
            }
            if probe == RejectedCall::InvalidState || probe == RejectedCall::StackEntry {
                // Read before another Rustlet entry can replace diagnostics.
                let mut expected = [0u8; 12];
                expected[..4].copy_from_slice(&expected_fault_status.to_le_bytes());
                if probe == RejectedCall::StackEntry && expected_fault_status != 0x300 {
                    let cause: u32 = if value == 0 { 1 << 20 } else { 1 << 4 };
                    expected[..4].copy_from_slice(&cause.to_le_bytes());
                    expected[4..8].copy_from_slice(&cause.to_le_bytes());
                    // Pico2 reports STKOF for a low SP and MSTKERR for
                    // exception entry onto an MPU-inaccessible high SP.
                    // Both enabled fault handlers run without escalation.
                } else if expected_fault_status != 0x300 {
                    expected[4..8].copy_from_slice(&(1u32 << 17).to_le_bytes());
                }
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0xa1, 6, 0, &[], 12))?,
                    &expected,
                    (0x90, 0),
                    "F4 correct hardware fault cause",
                )?;
                checks += 1;
            }
            select(client, crate_rustlet_minimal_valid_test_aid())?;
            expect_status(
                client.exchange(&CommandBuilder::process_no_data(0))?,
                (0x90, 0),
                "F4 unrelated APDU survives without reboot",
            )?;
            select(client, aid)?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x5c, 1))?,
                &[1],
                (0x90, 0),
                "F4 rejected state never replaces committed counter",
            )?;
            checks += 6;
        }
        Ok(management.total + checks)
    })?;
    total += target.reboot(
        "integrity rejected state remains absent after reboot",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            select(client, aid)?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x5c, 1))?,
                &[1],
                (0x90, 0),
                "F4 durable state after rejected call",
            )?;
            Ok(2)
        },
    )?;
    Ok(TestReport::passed(total))
}

pub(crate) fn test_apdu_order_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let board = board_spec(board)?;
    let probe_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&probe_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&probe_ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot(
        "integrity APDU call ordering",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, false)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            management.load(client, aid, &payload)?;
            management.install(client, aid)?;
            select(client, aid)?;
            let mut checks = 1;
            for choice in 0..8 {
                let lengths: &[u8] = match choice {
                    0 | 3 => &[1, 255],
                    4 => &[2],
                    5 | 6 => &[0],
                    _ => &[0, 2, 255],
                };
                for &len in lengths {
                    let incoming = matches!(choice, 0 | 3);
                    let input: Vec<u8> = if incoming {
                        (0..len).collect()
                    } else {
                        Vec::new()
                    };
                    let output_len = if choice == 4 { 0 } else { len };
                    let expected: Vec<u8> = (0..output_len)
                        .map(|i| if incoming { i ^ 0x5a } else { 0xa5 })
                        .collect();
                    expect_response(
                        client.exchange(&CommandBuilder::gp_command(
                            0x74, choice, len, &input, output_len,
                        ))?,
                        &expected,
                        (0x90, 0),
                        &format!("APDU order case {choice}, length {len}"),
                    )?;
                    select(client, crate_rustlet_minimal_valid_test_aid())?;
                    expect_status(
                        client.exchange(&CommandBuilder::process_no_data(0))?,
                        (0x90, 0),
                        "APDU order: unrelated command remains live without reboot",
                    )?;
                    select(client, aid)?;
                    checks += 4;
                }
            }
            Ok(management.total + checks)
        },
    )?;
    Ok(TestReport::passed(total))
}

pub(crate) fn test_abi_pointer_and_descriptor_validation(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let board = board_spec(board)?;
    let probe_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&probe_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&probe_ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot(
        "integrity ABI pointers and descriptors",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_response(
                client.exchange(&CommandBuilder::gp_command(0xa1, 2, 0, &[], 1))?,
                &[1],
                (0x90, 0),
                "F5 descriptor validation and positive controls",
            )?;
            let mut management = Management::open(client, false)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            management.load(client, aid, &payload)?;
            management.install(client, aid)?;
            select(client, aid)?;
            let mut checks = 2;
            // Every record-bearing SVC, each buffer role, and legal alias/empty cases.
            for (service, count) in (9..=16).map(|s| (s, 4)).chain([(0, 39), (1, 7)]) {
                for case in 0..count {
                    expect_response(
                        client.exchange(&CommandBuilder::gp_command(
                            0x75,
                            service,
                            case,
                            &[],
                            0,
                        ))?,
                        &[],
                        (0x90, 0),
                        &format!("F5 ABI service {service}, case {case}"),
                    )?;
                    select(client, crate_rustlet_minimal_valid_test_aid())?;
                    expect_status(
                        client.exchange(&CommandBuilder::process_no_data(0))?,
                        (0x90, 0),
                        "F5 next unrelated APDU survives without reboot",
                    )?;
                    select(client, aid)?;
                    checks += 4;
                }
            }
            Ok(management.total + checks)
        },
    )?;
    Ok(TestReport::passed(total))
}

pub(crate) fn test_shared_page_and_entry_gate(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let board = board_spec(board)?;
    let gate_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&gate_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&gate_ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot("integrity shared gate", APDU_RESPONSE_TIMEOUT, |client| {
        let mut management = Management::open(client, false)?;
        management.install(client, crate_rustlet_minimal_valid_test_aid())?;
        management.load(client, aid, &payload)?;
        management.install(client, aid)?;
        select(client, aid)?;
        let mut checks = 1;
        for seed in [0u8, 0x55, 0xa5, 0xff] {
            // Cross the historical +502 trampoline boundary, then exercise
            // the maximum short APDU and a short command after a full buffer.
            for len in [246u8, 247, 255, 1] {
                let bytes: Vec<_> = (0..len).map(|i| i.wrapping_add(seed)).collect();
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0x5a, seed, len, &bytes, len))?,
                    &bytes,
                    (0x90, 0),
                    "F-04 full input/output remains intact",
                )?;
                checks += 1;
            }
        }
        let expected: Vec<_> = (0..255u8).map(|i| i ^ 0x5a).collect();
        expect_response(
            client.exchange(&CommandBuilder::gp_command(0x5b, 0x35, 0xca, &[], 255))?,
            &expected,
            (0x90, 0),
            "F-04 physical buffer preserves adjacent control/state",
        )?;
        expect_status(
            client.exchange(&CommandBuilder::process_no_data(0x54))?,
            (0x90, 0),
            "F-04 user SVC 0 preserves unprivileged execution",
        )?;
        expect_status(
            client.exchange(&CommandBuilder::process_no_data(0x53))?,
            (0x6f, 1),
            "F-04 shared page execution must fault",
        )?;
        select(client, crate_rustlet_minimal_valid_test_aid())?;
        expect_status(
            client.exchange(&CommandBuilder::process_no_data(0))?,
            (0x90, 0),
            "F-04 unrelated Rustlet remains live without reboot",
        )?;
        checks += 5;
        Ok(management.total + checks)
    })?;
    Ok(TestReport::passed(total))
}

pub(crate) fn test_session_authority_binding(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let ctx = ctx.with_config("configs/config_sd_authority_integrity_test.toml");
    super::sd_authority::run(&ctx, board)
}

pub(crate) fn test_output_apdu_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let board = board_spec(board)?;
    let probe_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&probe_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&probe_ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot(
        "integrity APDU output lengths",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, false)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            management.load(client, aid, &payload)?;
            management.install(client, aid)?;
            select(client, aid)?;
            let mut checks = 1;
            for phase in 0..4 {
                for choice in 0..5 {
                    let len = match choice {
                        3 => 0,
                        4 => 255,
                        _ => match phase {
                            1 => 2,
                            2 => 255,
                            _ => 0,
                        },
                    };
                    let expected: Vec<u8> = (0..len).map(|i| i ^ 0xa5).collect();
                    expect_response(
                        client.exchange(&CommandBuilder::gp_command(
                            0x72,
                            choice,
                            phase,
                            &[],
                            len,
                        ))?,
                        &expected,
                        (0x90, 0),
                        &format!("APDU output phase {phase}, length case {choice}"),
                    )?;
                    select(client, crate_rustlet_minimal_valid_test_aid())?;
                    expect_status(
                        client.exchange(&CommandBuilder::process_no_data(0))?,
                        (0x90, 0),
                        "APDU output: next application remains live without reboot",
                    )?;
                    select(client, aid)?;
                    checks += 4;
                }
            }
            Ok(management.total + checks)
        },
    )?;
    Ok(TestReport::passed(total))
}

pub(crate) fn test_invalid_deallocation(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    use super::dynamic::{select, Management};
    let board = board_spec(board)?;
    let probe_ctx = ctx.with_config("configs/config_mapping_integrity_test.toml");
    let payload = build_dynamic_load_payload(&probe_ctx.build, board, "isolation_fault_test")?;
    let aid = crate_rustlet_isolation_fault_test_aid();
    let mut target =
        testing::target::prepare_apdu_session(&probe_ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot(
        "integrity hostile deallocation",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, false)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            management.load(client, aid, &payload)?;
            management.install(client, aid)?;
            select(client, aid)?;
            let mut checks = 1;
            for case in 0..12 {
                // Repeat within the same selection to detect accumulating damage.
                for _ in 0..2 {
                    expect_response(
                        client.exchange(&CommandBuilder::gp_command(0x71, case, 0, &[], 0))?,
                        &[],
                        (0x90, 0),
                        &format!("DEALLOC case {case}: live blocks and allocator intact"),
                    )?;
                    checks += 1;
                }
                select(client, crate_rustlet_minimal_valid_test_aid())?;
                expect_status(
                    client.exchange(&CommandBuilder::process_no_data(0))?,
                    (0x90, 0),
                    "DEALLOC unrelated application remains live",
                )?;
                select(client, aid)?;
                checks += 3;
            }
            Ok(management.total + checks)
        },
    )?;
    Ok(TestReport::passed(total))
}

fn test_key_storage_representation(_ctx: &TestContext, _board: &str) {
    // TODO: F-07: test the stored representation of synthetic keys. Report clear
    // storage as an exposure/hardening result, not a demonstrated cross-domain
    // read. Never log or return real key material through diagnostic helpers.
    // Will use function `key_storage_probe` from file `kernel/firmware/src/kernel_main_app/integrity_test.rs`.
}

fn test_redirect_interleavings(_ctx: &TestContext, _board: &str) {
    // TODO: F-08: stress return/fault/watchdog transitions and add controlled
    // interrupt injection at the redirect boundary. Repeated normal returns
    // alone cannot close the suspected race; report that coverage limitation.
    // Will use function `integrity_probe` from file `rustlets/tests/isolation_fault_test/src/main.rs`.
    // Will use function `run_rustlet_watchdog_test_for_board` from file `xtask/src/testing/scenarios/rustlets.rs`.
}

fn test_random_service_boundaries(_ctx: &TestContext, _board: &str) {
    // TODO: F-09: exercise random-service success/error handling and forbidden
    // TRNG register access with liveness checks. Reuse driver/DRBG negative tests
    // where applicable. Random-looking output is not an entropy qualification;
    // distinguish QEMU, simulated-register tests and physical Pico2 observations.
    // Will use function `process_apdu` from file `rustlets/tests/isolation_fault_test/src/main.rs`.
    // Will use function `run_kernel_crypto_test_for_board` from file `xtask/src/testing/scenarios/kernel.rs`.
}

fn test_deployment_management_policy(_ctx: &TestContext, _board: &str) {
    // TODO: F-10: verify the intentional open-development posture and a separate
    // authenticated configuration that rejects clear management. Never infer
    // production suitability merely from the diagnostic image's successful boot.
    // Will use function `process_apdu` from file `rustlets/tests/isolation_fault_test/src/main.rs`.
    // Will use function `run_noscp_test_for_board` from file `xtask/src/testing/scenarios/gp.rs`.
    // Will use function `run_single_scp03_test_for_board` from file `xtask/src/testing/scenarios/gp.rs`.
}

fn test_publication_and_sd_rollback(_ctx: &TestContext, _board: &str) {
    // TODO: Publication failures and resident-SD rollback: reuse registry fault
    // and sd_transaction campaigns, including normal rejection, crash retirement,
    // response publication failure and reboot recovery. Preserve their failures
    // in the aggregate report instead of stopping before subsequent campaigns.
    // Will use function `process` from file `kernel/firmware/src/kernel_main_app/integrity_test.rs`.
    // Will use function `run_kernel_registry_test_for_board` from file `xtask/src/testing/scenarios/kernel.rs`.
    // Will use function `run` from file `xtask/src/testing/scenarios/sd_transaction.rs`.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_boss_fixture_has_valid_crc_and_page_alignment() {
        assert_eq!(registry_crc64(b"123456789"), 0x6C40_DF5F_0B49_7347);
        let payload = registry_load_payload(true);
        let boss = &payload[244..500];
        assert_eq!(
            u32::from_le_bytes(boss[..4].try_into().unwrap()),
            0x600D_B055
        );
        assert_eq!(u32::from_le_bytes(boss[4..8].try_into().unwrap()), 256);
        assert_eq!(u32::from_le_bytes(boss[8..12].try_into().unwrap()), 999);
        assert_eq!(&boss[12..16], &[0; 4]);
        assert_eq!(
            registry_crc64(&boss[..248]),
            u64::from_le_bytes(boss[248..].try_into().unwrap())
        );
        assert!(registry_load_payload(false)
            .iter()
            .all(|&byte| byte == 0xFF));
    }
}
