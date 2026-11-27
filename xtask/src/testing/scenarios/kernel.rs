//! kernel scenario operations and assertions, shared by individual tests and campaigns.
use super::*;

/// Runs the low-level core-test firmware under QEMU and parses its text report.
///
/// This predates the APDU-driven GP/Rustlet campaigns and remains useful for
/// checking board bring-up, allocator basics, and target support without
/// booting the full GP kernel.
pub(crate) fn run_core_test_with_context(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    testing::target::run_core(ctx, board, "qemu", "kernel-core", |output| {
        let stdout = String::from_utf8(output.stdout).map_err(|_| "qemu stdout was not utf-8")?;
        let stderr = String::from_utf8(output.stderr).map_err(|_| "qemu stderr was not utf-8")?;
        let summary = parse_core_test_output(&stdout, &stderr)?;

        if !output.status.success() {
            return Err(format!(
                "qemu test process failed on {} with status {}\nstdout:\n{}\nstderr:\n{}",
                board.env_name, output.status, stdout, stderr
            )
            .into());
        }

        if summary.failed != 0 {
            return Err(format!("embedded tests failed on {}", board.env_name).into());
        }

        Ok(summary)
    })
}

/// Runs the core-test stack-guard firmware under QEMU or on physical Pico2.
///
/// The test intentionally triggers the guard path and succeeds only when QEMU
/// reports the expected guard diagnostic, making it a focused regression for
/// kernel stack protection. OpenOCD instead checks STKOF at UsageFault entry
/// and the boot-configured MSPLIM, without relying on console output.
pub(crate) fn run_kernel_stack_guard_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<(), Box<dyn Error>> {
    let board = board_spec(board)?;
    let owned_ctx = ctx.with_fault("OXIDE_SE_KERNEL_STACK_GUARD_TEST");
    let ctx = &owned_ctx;

    if ctx.openocd().is_some() {
        if board.env_name != "raspi-pico2" {
            return Err("hardware stack guard observation is supported only on Pico2".into());
        }
        build_firmware(
            &ctx.build,
            FirmwareKind::CoreTest,
            None,
            board.env_name,
            "hardware",
        )?;
        return testing::openocd::run_stack_guard(
            ctx,
            board,
            &firmware_elf_path(FirmwareKind::CoreTest)?,
        );
    }

    testing::target::run_core(
        ctx,
        board,
        "qemu-kernel-stack-guard",
        "kernel-stack-guard",
        |output| {
            let stdout =
                String::from_utf8(output.stdout).map_err(|_| "qemu stdout was not utf-8")?;
            let stderr =
                String::from_utf8(output.stderr).map_err(|_| "qemu stderr was not utf-8")?;
            let combined = format!("{stdout}\n{stderr}");

            if board.env_name == "raspi-pico1" {
                if output.status.success()
                    || !combined.contains("kernel fatal: BKPT #0 (exit_code=1)")
                {
                    return Err(format!(
                        "Pico1 fatal fault did not reach the terminal breakpoint: {}\n{combined}",
                        output.status
                    )
                    .into());
                }
                eprintln!(
                    "KERNEL-FATAL-EVIDENCE board=raspi-pico1 terminal=BKPT0 status={}",
                    output.status
                );
            }

            let expected_m_profile = "kernel MemManage: kernel stack overflow suspected";
            let expected_armv6m = "kernel ARMv6-M HardFault: kernel stack overflow suspected";
            if !combined.contains(expected_m_profile) && !combined.contains(expected_armv6m) {
                return Err(format!(
            "kernel stack guard test did not report the expected fault\nstdout:\n{stdout}\nstderr:\n{stderr}"
        )
        .into());
            }

            Ok(())
        },
    )
}

/// Runs the core-test RAM execute-never firmware under QEMU.
///
/// The embedded test attempts to branch to a RAM-resident `BX LR` instruction
/// while the kernel is active. A passing target must fault before returning,
/// proving that kernel-phase RAM-XN is actually enforced by the MPU.
pub(crate) fn run_kernel_ram_nx_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<(), Box<dyn Error>> {
    let board = board_spec(board)?;
    if ctx.openocd().is_some() {
        if board.env_name != "raspi-pico2" {
            return Err("hardware RAM NX observation is supported only on Pico2".into());
        }
        let ctx = ctx.with_fault("OXIDE_SE_KERNEL_RAM_NX_TEST");
        build_firmware(
            &ctx.build,
            FirmwareKind::CoreTest,
            None,
            board.env_name,
            "hardware",
        )?;
        return testing::openocd::run_ram_nx(
            &ctx,
            board,
            &firmware_elf_path(FirmwareKind::CoreTest)?,
        );
    }
    if !kernel_ram_nx_qemu_supported(board) {
        return Err(format!(
            "kernel RAM NX QEMU regression is currently validated only on boards with a clean RAM-NX fault path; {} is unsupported",
            board.env_name
        )
        .into());
    }

    let owned_ctx = ctx.with_fault("OXIDE_SE_KERNEL_RAM_NX_TEST");
    let ctx = &owned_ctx;

    testing::target::run_core(
        ctx,
        board,
        "qemu-kernel-ram-nx",
        "kernel-ram-nx",
        |output| {
            let stdout =
                String::from_utf8(output.stdout).map_err(|_| "qemu stdout was not utf-8")?;
            let stderr =
                String::from_utf8(output.stderr).map_err(|_| "qemu stderr was not utf-8")?;
            let combined = format!("{stdout}\n{stderr}");

            if combined.contains("TEST-UNSUPPORTED kernel-ram-nx") {
                return Err(format!(
                    "kernel RAM NX test is unsupported on {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                    board.env_name
                )
                .into());
            }

            if combined.contains("TEST-FAIL kernel-ram-nx ram-execution-returned")
                || combined.contains("kernel RAM NX test did not fault")
            {
                return Err(format!(
            "kernel RAM NX test returned from RAM execution\nstdout:\n{stdout}\nstderr:\n{stderr}",
        )
                .into());
            }

            let expected_m_profile = "fatal MemManage";
            let expected_armv6m = "fatal ARMv6-M HardFault";
            if !combined.contains(expected_m_profile) && !combined.contains(expected_armv6m) {
                return Err(format!(
            "kernel RAM NX test did not report the expected fault\nstdout:\n{stdout}\nstderr:\n{stderr}"
        )
        .into());
            }

            Ok(())
        },
    )
}

/// Validates ping and response lengths 0, 16, 32, ..., 240, 255 bytes.
///
/// Its dedicated manifest selects only the `ping` module, so it isolates the
/// APDU transport and kernel main loop from Rustlet loading and GP management.
/// Nonempty patterns exercise both direct Le-driven output and case-4 echo
/// with one GET RESPONSE, including payload bytes resembling T=0 status/NULL.
pub(crate) fn run_kernel_ping_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let test_result = testing::target::run_apdu(
        ctx,
        board,
        LayoutImageFormat::Elf,
        "kernel-ping",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let payload = [0x12, 0x34, 0x56, 0x78];
            let response = client.exchange(&CommandBuilder::kernel_ping(&payload))?;
            expect_response(response, &payload, (0x90, 0x00), "kernel ping")?;
            let mut command = CommandBuilder::kernel_ping(&[]);
            command.p1 = 2;
            expect_response(
                client.exchange(&command)?,
                &[],
                (0x90, 0x00),
                "kernel ping empty",
            )?;
            for len in (16..=240).step_by(16).chain(std::iter::once(255)) {
                let expected: Vec<u8> = (0..len).map(|index| index as u8).collect();
                let label = format!("kernel ping direct Le={len}");
                eprintln!("kernel-ping: {label}");
                command.p1 = 1;
                command.le = len as u8;
                expect_response(client.exchange(&command)?, &expected, (0x90, 0x00), &label)?;
                let label = format!("kernel ping GET RESPONSE length={len}");
                eprintln!("kernel-ping: {label}");
                expect_response(
                    client.exchange(&CommandBuilder::kernel_ping(&expected))?,
                    &expected,
                    (0x90, 0x00),
                    &label,
                )?;
            }
            Ok(())
        },
    );
    test_result?;

    Ok(TestReport::passed(34))
}

/// Exercises the kernel T=0 transport edge cases on the selected backend.
///
/// The scenario checks ATR delivery, no-data status handling, case-3 ingress,
/// case-2 egress, and case-4 in/out behavior without involving Rustlets.
pub(crate) fn run_kernel_t0_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let test_result = testing::target::run_apdu(
        ctx,
        board,
        LayoutImageFormat::Elf,
        "kernel-t0",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            eprintln!("kernel-t0: empty");
            expect_status(
                client.exchange(&CommandBuilder::process_no_data(0x00))?,
                (0x90, 0x00),
                "kernel_main_app empty",
            )?;

            eprintln!("kernel-t0: inbound");
            expect_status(
                client.exchange(&CommandBuilder::process_with_data(
                    0x02,
                    &[0x00, 0x01, 0x02, 0x03],
                ))?,
                (0x90, 0x00),
                "kernel_main_app inbound",
            )?;

            eprintln!("kernel-t0: outbound with 6C retry");
            let response = client.exchange(&CommandBuilder::process_no_data_with_le(0x04, 0x02))?;
            expect_response(
                response,
                &[0x00, 0x01, 0x02],
                (0x90, 0x00),
                "kernel_main_app outbound",
            )?;

            eprintln!("kernel-t0: in/out");
            let response = client.exchange(&CommandBuilder::process_with_data_and_le(
                0x06,
                &[0x00, 0x01, 0x02, 0x03],
                0x04,
            ))?;
            expect_response(
                response,
                &[0x03, 0x02, 0x01, 0x00],
                (0x90, 0x00),
                "kernel_main_app in/out",
            )?;

            Ok(())
        },
    );
    test_result?;

    Ok(TestReport::passed(4))
}

/// Verifies periodic SysTick delivery and the explicit top/bottom-half boundary.
pub(crate) fn run_kernel_timer_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    testing::target::run_apdu(
        ctx,
        board,
        LayoutImageFormat::Elf,
        "kernel-timer",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let first = client.exchange(&CommandBuilder::kernel_timer(0))?;
            let (first_top, first_bottom, first_nulls) = timer_counters(first)?;

            let second = client.exchange(&CommandBuilder::kernel_timer(1))?;
            let (second_top, second_bottom, second_nulls) = timer_counters(second)?;
            let elapsed_ticks = second_top.wrapping_sub(first_top);
            eprintln!(
                "kernel-timer: period=100ms top={first_top}->{second_top} bottom={first_bottom}->{second_bottom} null={first_nulls}->{second_nulls}"
            );
            if elapsed_ticks < 3 {
                return Err(format!(
                    "periodic timer advanced only {elapsed_ticks} times during the observation window"
                )
                .into());
            }
            if second_bottom.wrapping_sub(first_bottom) < 3 {
                return Err("bottom-half marker was not reached periodically".into());
            }
            if second_top.abs_diff(second_bottom) > 1 {
                return Err(format!(
                    "top/bottom-half counters diverged: top={second_top}, bottom={second_bottom}"
                )
                .into());
            }
            if second_nulls <= first_nulls {
                return Err("delayed APDU emitted no periodic T=0 NULL byte".into());
            }
            Ok(())
        },
    )?;
    Ok(TestReport::passed(3))
}

/// Verifies 500 ms hardware-time deadlines while a T=0 command is processing.
/// The 3.6-second hardware-time observation includes polling latency: a
/// successful write renews from actual time, not the previous tick deadline.
pub(crate) fn run_kernel_null_byte_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    testing::target::run_apdu(
        ctx,
        board,
        LayoutImageFormat::Elf,
        "kernel-null-byte",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let before = client.exchange(&CommandBuilder::kernel_timer(0))?;
            let (before_top, _, before_nulls) = timer_counters(before)?;
            let (after, wire_nulls) = null_exchange(client, &CommandBuilder::kernel_timer(2))?;
            let (after_top, _, after_nulls) = timer_counters(after)?;
            let elapsed_ticks = after_top.wrapping_sub(before_top);
            let emitted_nulls = after_nulls.wrapping_sub(before_nulls);
            eprintln!(
                "kernel-null-byte: period=500ms ticks={elapsed_ticks} nulls={before_nulls}->{after_nulls}"
            );
            if wire_nulls != emitted_nulls as usize {
                return Err(
                    format!("NULL counter={emitted_nulls} differs from wire={wire_nulls}").into(),
                );
            }
            if !(5..=7).contains(&emitted_nulls) {
                return Err(format!(
                    "expected 5..=7 periodic T=0 NULL bytes (500 ms + polling latency), observed {emitted_nulls}"
                )
                .into());
            }
            Ok(())
        },
    )?;
    Ok(TestReport::passed(2))
}

fn timer_counters(response: T0Response) -> Result<(u32, u32, u32), Box<dyn Error>> {
    if response.status != (0x90, 0x00) || response.data.len() != 12 {
        return Err(format!(
            "kernel timer counter response malformed: len={}, status={:02X}{:02X}",
            response.data.len(),
            response.status.0,
            response.status.1
        )
        .into());
    }
    Ok((
        u32::from_be_bytes(response.data[..4].try_into().unwrap()),
        u32::from_be_bytes(response.data[4..8].try_into().unwrap()),
        u32::from_be_bytes(response.data[8..12].try_into().unwrap()),
    ))
}

/// Exercise normal registry APIs and recovery with write/erase fault injection.
/// Only the first boot programs the image; every later boot restores flash state.
pub(crate) fn run_kernel_registry_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<usize, Box<dyn Error>> {
    let board = board_spec(board)?;
    if let Ok(path) = std::env::var("OXIDE_REGISTRY_PERF_CSV") {
        let perf_ctx = ctx.with_config("configs/config_registry_perf_test.toml");
        let payload = build_dynamic_load_payload(&perf_ctx.build, board, "minimal_valid_test")?;
        let mut target =
            testing::target::prepare_apdu_session(&perf_ctx, board, LayoutImageFormat::Elf, true)?;
        return run_registry_performance(&mut target, &path, &payload);
    }
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    // 17 + 17 * 244 = 4165 payload bytes. Each 244-byte object plus
    // persistence header/CRC spans two 256-byte logical pages.
    let mut expected: Vec<Vec<u8>> = (0..18usize)
        .map(|id| {
            (0..if id == 0 { 17 } else { 244 })
                .map(|offset| ((id * 53 + offset * 7 + offset / 13) & 255) as u8)
                .collect()
        })
        .collect();
    let mut total = 0;
    for boot in 0..3 {
        let label = format!("kernel-registry-boot-{boot}");
        let mut scenario = |client: &mut ApduClient| {
            if boot == 0 {
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 0xfb, 0, &[], 0))?,
                    &[],
                    (0x90, 0),
                    "Data pair scope, rollback and repeated tags",
                )?;
                total += 1;
                let missing = CommandBuilder::gp_command(0xa0, 2, 0, &[], 17);
                expect_response(
                    client.exchange(&missing)?,
                    &[],
                    (0x6a, 0x88),
                    "registry starts empty",
                )?;
                total += 1;
                for (id, data) in expected.iter().enumerate() {
                    eprintln!("kernel-registry: write object {id}, {} bytes", data.len());
                    let write = CommandBuilder::gp_command(0xa0, 1, id as u8, data, 0);
                    expect_response(client.exchange(&write)?, &[], (0x90, 0), "registry write")?;
                    total += 1;
                }
            }
            for (id, data) in expected.iter().enumerate() {
                eprintln!(
                    "kernel-registry: boot {boot}, read object {id}, {} bytes",
                    data.len()
                );
                total += read_registry_object(client, id as u8, data)?;
            }
            if boot == 1 {
                // Exact threshold: 32-byte header and AES-aligned body, no trailer.
                for size in [223usize, 224, 225] {
                    expected[0] = (0..size).map(|i| (i * 7 + size) as u8).collect();
                    expect_status(
                        client.exchange(&CommandBuilder::gp_command(
                            0xa0,
                            1,
                            0,
                            &expected[0],
                            0,
                        ))?,
                        (0x90, 0),
                        "whole-block CMAC page threshold",
                    )?;
                    total += 1 + read_registry_object(client, 0, &expected[0])?;
                }
                // Replace one multi-page object with a shorter, different value.
                expected[1] = (0..31).map(|i| 0xe3u8.wrapping_sub(i * 3)).collect();
                let data = &expected[1];
                let write = CommandBuilder::gp_command(0xa0, 1, 1, data, 0);
                expect_response(
                    client.exchange(&write)?,
                    &[],
                    (0x90, 0),
                    "registry replacement",
                )?;
                total += 1 + read_registry_object(client, 1, data)?;
            }
            Ok(())
        };
        if boot == 0 {
            target.boot(&label, APDU_RESPONSE_TIMEOUT, &mut scenario)?;
        } else {
            target.reboot(&label, APDU_RESPONSE_TIMEOUT, &mut scenario)?;
        }
    }
    total += run_registry_write_faults(&mut target, &expected)?;
    total += run_registry_cumulative_faults(&mut target, &expected)?;
    total += run_registry_erase_faults(&mut target, &expected)?;
    total += run_registry_sd_install_fault(&mut target)?;
    Ok(total)
}

/// A failed final BOSS must retain neither the new SD nor one of its inherited keys.
fn run_registry_sd_install_fault(
    target: &mut testing::target::TargetSession<'_>,
) -> Result<usize, Box<dyn Error>> {
    let inspect = |client: &mut ApduClient, present: bool| {
        expect_response(
            client.exchange(&CommandBuilder::gp_command(0xa0, 11, 0, &[], 3))?,
            &[u8::from(present); 3],
            (0x90, 0),
            "SD and inherited keys form one graph",
        )
    };
    target.reboot(
        "registry SD inheritance publication failure",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            // The preceding recycling fixture fills most slots. Release three
            // unrelated DATA objects so this case reaches publication, not capacity.
            for tag in [0, 1, 3] {
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 3, tag, &[], 0))?,
                    (0x90, 0),
                    "reserve slots for SD inheritance fixture",
                )?;
            }
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 9, 0, &[], 0))?,
                (0x90, 0),
                "seed inheritance source",
            )?;
            inspect(client, false)?;
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 4, 1, &[0, 0], 0))?,
                (0x90, 0),
                "arm final BOSS failure",
            )?;
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 10, 0, &[], 0))?,
                (0x65, 0x81),
                "SD installation publication rejected",
            )?;
            inspect(client, false)
        },
    )?;
    target.reboot(
        "registry SD inheritance recovery",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            inspect(client, false)?;
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 10, 0, &[], 0))?,
                (0x90, 0),
                "SD installation after failed publication",
            )?;
            inspect(client, true)
        },
    )?;
    target.reboot(
        "registry SD inheritance durable",
        APDU_RESPONSE_TIMEOUT,
        |client| inspect(client, true),
    )?;
    Ok(12)
}

/// The injected write prefix is durable; RAM is discarded at the next boot.
fn run_registry_write_faults(
    target: &mut testing::target::TargetSession<'_>,
    expected: &[Vec<u8>],
) -> Result<usize, Box<dyn Error>> {
    let mut total = 0;
    // Object 2 spans two pages; the registry of 18 objects is also multi-page.
    for delete in [false, true] {
        for cut in [0u16, 1, 15, 16, 17, 31, 32, 33, 255, 256, 511] {
            let label = format!("registry-cut delete={delete} bytes={cut}");
            target.reboot(&label, APDU_RESPONSE_TIMEOUT, |client| {
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(
                        0xa0,
                        4,
                        u8::from(delete),
                        &cut.to_le_bytes(),
                        0,
                    ))?,
                    (0x90, 0),
                    "arm registry prefix cut",
                )?;
                let command = if delete {
                    CommandBuilder::gp_command(0xa0, 3, 2, &[], 0)
                } else {
                    CommandBuilder::gp_command(0xa0, 1, 2, &[0xC7; 244], 0)
                };
                expect_status(
                    client.exchange(&command)?,
                    (0x65, 0x81),
                    "injected persistence failure",
                )?;
                // Failure must preserve the old RAM view even before reboot.
                read_registry_object(client, 2, &expected[2])?;
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 5, 0, &[], 1))?,
                    &[1],
                    (0x90, 0),
                    "cut actually reached",
                )?;
                Ok(())
            })?;
            total += 4;
            for recovery in 0..2 {
                target.reboot(
                    "registry repeated recovery",
                    APDU_RESPONSE_TIMEOUT,
                    |client| {
                        for (id, data) in expected.iter().enumerate() {
                            total += read_registry_object(client, id as u8, data)?;
                        }
                        if recovery == 0 {
                            // A new publication after recovery must preserve the old
                            // object graph, not revive the interrupted RAM mutation.
                            expect_status(
                                client.exchange(&CommandBuilder::gp_command(
                                    0xa0,
                                    1,
                                    31,
                                    b"recovery-sentinel",
                                    0,
                                ))?,
                                (0x90, 0),
                                "publication after recovery",
                            )?;
                            total += 1;
                        } else {
                            total += read_registry_object(client, 31, b"recovery-sentinel")?;
                        }
                        Ok(())
                    },
                )?;
            }
        }
    }
    target.reboot(
        "registry commit deletion",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 3, 2, &[], 0))?,
                (0x90, 0),
                "commit deletion",
            )
        },
    )?;
    total += 1;
    for _ in 0..3 {
        target.reboot(
            "registry deletion remains durable",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 2, 2, &[], 1))?,
                    (0x6a, 0x88),
                    "deleted object absent",
                )?;
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 3, 2, &[], 0))?,
                    (0x6a, 0x88),
                    "repeated delete leaves object absent",
                )?;
                for (id, data) in expected.iter().enumerate().filter(|(id, _)| *id != 2) {
                    total += read_registry_object(client, id as u8, data)?;
                }
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(
                        0xa0,
                        1,
                        31,
                        b"after-delete",
                        0,
                    ))?,
                    (0x90, 0),
                    "publication after deletion",
                )?;
                total += 3;
                Ok(())
            },
        )?;
    }
    Ok(total)
}

/// Check the entire surviving graph, including an unrelated committed object.
fn registry_survivors(
    client: &mut ApduClient,
    expected: &[Vec<u8>],
) -> Result<usize, Box<dyn Error>> {
    let mut total = 0;
    for (id, data) in expected.iter().enumerate().filter(|(id, _)| *id != 2) {
        total += read_registry_object(client, id as u8, data)?;
    }
    expect_status(
        client.exchange(&CommandBuilder::gp_command(0xa0, 2, 2, &[], 1))?,
        (0x6a, 0x88),
        "old deletion remains absent",
    )?;
    total += 1 + read_registry_object(client, 31, b"after-delete")?;
    Ok(total)
}

fn registry_tree(client: &mut ApduClient, present: bool) -> Result<(), Box<dyn Error>> {
    expect_response(
        client.exchange(&CommandBuilder::gp_command(0xa0, 7, 0, &[], 4))?,
        &[u8::from(present); 4],
        (0x90, 0),
        "complete SD subtree",
    )
}

fn run_registry_cumulative_faults(
    target: &mut testing::target::TargetSession<'_>,
    expected: &[Vec<u8>],
) -> Result<usize, Box<dyn Error>> {
    let mut total = 0;
    target.reboot(
        "registry cumulative fixture",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 6, 0, &[], 0))?,
                (0x90, 0),
                "create SD subtree",
            )?;
            registry_tree(client, true)?;
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 8, 0, &[], 0))?,
                (0x69, 0x85),
                "non-cumulative deletion rejected",
            )?;
            registry_tree(client, true)
        },
    )?;
    total += 4;
    for cut in [0u16, 1, 15, 16, 17, 31, 32, 33, 255, 256, 511] {
        target.reboot(
            &format!("registry cumulative BOSS cut={cut}"),
            APDU_RESPONSE_TIMEOUT,
            |client| {
                registry_tree(client, true)?;
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(
                        0xa0,
                        4,
                        1,
                        &cut.to_le_bytes(),
                        0,
                    ))?,
                    (0x90, 0),
                    "arm cumulative BOSS cut",
                )?;
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 8, 1, &[], 0))?,
                    (0x65, 0x81),
                    "cumulative delete persistence failure",
                )?;
                expect_response(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 5, 0, &[], 1))?,
                    &[1],
                    (0x90, 0),
                    "cumulative cut reached",
                )?;
                registry_tree(client, true)
            },
        )?;
        total += 5;
        for _ in 0..2 {
            target.reboot(
                "registry cumulative repeated recovery",
                APDU_RESPONSE_TIMEOUT,
                |client| {
                    registry_tree(client, true)?;
                    total += 1 + registry_survivors(client, expected)?;
                    // Publish another snapshot after recovery; no descendant may
                    // disappear through stale deletion state on the next reboot.
                    expect_status(
                        client.exchange(&CommandBuilder::gp_command(
                            0xa0,
                            1,
                            31,
                            b"after-delete",
                            0,
                        ))?,
                        (0x90, 0),
                        "publish after cumulative recovery",
                    )?;
                    total += 1;
                    Ok(())
                },
            )?;
        }
    }
    target.reboot(
        "registry commit cumulative deletion",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 8, 1, &[], 0))?,
                (0x90, 0),
                "commit full subtree deletion",
            )
        },
    )?;
    total += 1;
    for _ in 0..3 {
        target.reboot(
            "registry durable cumulative deletion",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                registry_tree(client, false)?;
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 8, 1, &[], 0))?,
                    (0x6a, 0x88),
                    "repeated subtree deletion stays absent",
                )?;
                total += 2 + registry_survivors(client, expected)?;
                Ok(())
            },
        )?;
    }
    Ok(total)
}

fn run_registry_erase_faults(
    target: &mut testing::target::TargetSession<'_>,
    expected: &[Vec<u8>],
) -> Result<usize, Box<dyn Error>> {
    let mut total = 0;
    let mut committed = vec![0x35; 244];
    target.reboot(
        "registry pressure fixture",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let info = client.exchange(&CommandBuilder::gp_command(0xa0, 0, 0, &[], 8))?;
            if info.status != (0x90, 0)
                || info.data.len() != 8
                || u32::from_be_bytes(info.data[..4].try_into()?) != 65536
            {
                return Err("registry pressure test requires its bounded 64-KiB area".into());
            }
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 1, 32, &committed, 0))?,
                (0x90, 0),
                "pressure object",
            )
        },
    )?;
    total += 2;
    for cut in [0u16, 1, 255, 256, 2048, 4095, 4096] {
        target.reboot(
            &format!("registry erase prefix={cut}"),
            APDU_RESPONSE_TIMEOUT,
            |client| {
                total += read_registry_object(client, 32, &committed)?;
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(
                        0xa0,
                        4,
                        2,
                        &cut.to_le_bytes(),
                        0,
                    ))?,
                    (0x90, 0),
                    "arm erase cut",
                )?;
                total += 1;
                for attempt in 0..256 {
                    let next: Vec<u8> = committed.iter().map(|b| b.wrapping_add(1)).collect();
                    let replacement =
                        client.exchange(&CommandBuilder::gp_command(0xa0, 1, 32, &next, 0))?;
                    let hit = client.exchange(&CommandBuilder::gp_command(0xa0, 5, 0, &[], 1))?;
                    total += 2;
                    if hit.status != (0x90, 0) || hit.data.len() != 1 || hit.data[0] > 1 {
                        return Err("malformed erase injection state".into());
                    }
                    expect_status(
                        replacement,
                        if hit.data == [1] {
                            (0x65, 0x81)
                        } else {
                            (0x90, 0)
                        },
                        "pressure replacement outcome",
                    )?;
                    if hit.data == [1] {
                        read_registry_object(client, 32, &committed)?;
                        total += 1;
                        eprintln!(
                            "registry-erase: prefix={cut} reached after {} replacements",
                            attempt + 1
                        );
                        return Ok(());
                    }
                    committed = next;
                }
                Err("recycling was not reached under bounded pressure".into())
            },
        )?;
        for recovery in 0..2 {
            target.reboot(
                "registry erase repeated recovery",
                APDU_RESPONSE_TIMEOUT,
                |client| {
                    total += registry_survivors(client, expected)?;
                    total += read_registry_object(client, 32, &committed)?;
                    if recovery == 0 {
                        let next: Vec<u8> = committed.iter().map(|b| b.wrapping_add(3)).collect();
                        expect_status(
                            client.exchange(&CommandBuilder::gp_command(0xa0, 1, 32, &next, 0))?,
                            (0x90, 0),
                            "resume writes after torn erase",
                        )?;
                        committed = next;
                        total += 1;
                    }
                    Ok(())
                },
            )?;
        }
    }
    // Exercise successful recycling too, with every final value verified after
    // reset, rather than inferring recycling from the number of writes alone.
    target.reboot(
        "registry sustained recycling",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            for iteration in 0..192 {
                if iteration % 32 == 0 {
                    eprintln!("registry-recycle: replacement {}/192", iteration + 1);
                }
                let next: Vec<u8> = committed.iter().map(|b| b.wrapping_add(1)).collect();
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 1, 32, &next, 0))?,
                    (0x90, 0),
                    "recycle replacement",
                )?;
                committed = next;
                total += 1;
            }
            let info = client.exchange(&CommandBuilder::gp_command(0xa0, 0, 0, &[], 8))?;
            if info.status != (0x90, 0)
                || info.data.len() != 8
                || u32::from_be_bytes(info.data[4..8].try_into()?) < 2
            {
                return Err("successful sector recycling was not observed".into());
            }
            eprintln!(
                "registry-recycle: {} sectors erased",
                u32::from_be_bytes(info.data[4..8].try_into()?)
            );
            total += 1;
            Ok(())
        },
    )?;
    for _ in 0..3 {
        target.reboot(
            "registry recycled graph remains durable",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                total += registry_survivors(client, expected)?;
                total += read_registry_object(client, 32, &committed)?;
                Ok(())
            },
        )?;
    }
    Ok(total)
}

/// Compares the complete object in a single response, including after reset.
fn read_registry_object(
    client: &mut ApduClient,
    id: u8,
    data: &[u8],
) -> Result<usize, Box<dyn Error>> {
    let read = CommandBuilder::gp_command(0xa0, 2, id, &[], data.len() as u8);
    expect_response(
        client.exchange(&read)?,
        data,
        (0x90, 0),
        &format!("registry object {id}"),
    )?;
    Ok(1)
}

pub(crate) fn run_kernel_flash_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<(), Box<dyn Error>> {
    let board = board_spec(board)?;
    let layout = read_target_memory_layout(board)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let prefix = |marker| {
        [
            0x52, 0x4c, 0x4f, 0x53, 0x46, 0x4c, 0x53, 0x48, marker, 0x8e, 16, 0, 0xa5, 0xff, 0xff,
            0xff,
        ]
    };
    target.boot("kernel-flash-write-A5", APDU_RESPONSE_TIMEOUT, |client| {
        let info = client.exchange(&CommandBuilder::process_no_data_with_le(0x8e, 12))?;
        let start = layout
            .flash_base
            .checked_add(layout.flash_size)
            .and_then(|end| end.checked_sub(4096))
            .ok_or("invalid flash layout")?;
        let mut expected = Vec::new();
        expected.extend_from_slice(&(u32::try_from(start)?).to_le_bytes());
        expected.extend_from_slice(&16u32.to_le_bytes());
        expected.extend_from_slice(&256u32.to_le_bytes());
        expect_response(info, &expected, (0x90, 0), "diagnostic block geometry")?;
        eprintln!("kernel-flash: reserved block 0x{start:08X}, 4096 bytes; write A5");
        let mut write = CommandBuilder::process_no_data_with_le(0x8e, 16);
        write.p1 = 1;
        write.p2 = 0xa5;
        expect_response(
            client.exchange(&write)?,
            &prefix(0xa5),
            (0x90, 0),
            "write/read A5",
        )
    })?;
    target.reboot(
        "kernel-flash-read-A5-write-5A",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut read = CommandBuilder::process_no_data_with_le(0x8e, 16);
            read.p1 = 2;
            expect_response(
                client.exchange(&read)?,
                &prefix(0xa5),
                (0x90, 0),
                "A5 retained after complete boot",
            )?;
            let mut write = CommandBuilder::process_no_data_with_le(0x8e, 16);
            write.p1 = 1;
            write.p2 = 0x5a;
            expect_response(
                client.exchange(&write)?,
                &prefix(0x5a),
                (0x90, 0),
                "erase/rewrite 5A",
            )
        },
    )?;
    target.reboot("kernel-flash-read-5A", APDU_RESPONSE_TIMEOUT, |client| {
        let mut read = CommandBuilder::process_no_data_with_le(0x8e, 16);
        read.p1 = 2;
        expect_response(
            client.exchange(&read)?,
            &prefix(0x5a),
            (0x90, 0),
            "5A retained after complete boot",
        )
    })
}

/// Exercises kernel-local crypto APIs on the selected backend without entering a Rustlet.
///
/// The scenario runs through the same kernel-owned APDU plumbing as
/// `test kernel_t0`, but the handlers call `oxi_core::core::crypto` directly.
/// This keeps runtime syscalls and Rustlet isolation out of the diagnostic
/// path when debugging target-specific crypto behavior.
pub(crate) fn run_kernel_crypto_test_for_board(
    ctx: &TestContext,
    board: &str,
    bench: Option<&KernelCryptoBench>,
) -> Result<TestReport, Box<dyn Error>> {
    const AES128_NIST_CIPHERTEXT: [u8; 16] = [
        0x76, 0x49, 0xab, 0xac, 0x81, 0x19, 0xb2, 0x46, 0xce, 0xe9, 0x8e, 0x9b, 0x12, 0xe9, 0x19,
        0x7d,
    ];

    let board = board_spec(board)?;
    let test_result = testing::target::run_apdu(
        ctx,
        board,
        LayoutImageFormat::Elf,
        "kernel-crypto",
        if bench.is_some() {
            KERNEL_CRYPTO_BENCH_TIMEOUT
        } else {
            APDU_RESPONSE_TIMEOUT
        },
        |client| {
            if let Some(bench) = bench {
                return run_kernel_crypto_bench(client, board.env_name, bench);
            }

            eprintln!("kernel-crypto: random");
            let random = client.exchange(&CommandBuilder::process_no_data_with_le(0x80, 0x10))?;
            if random.status != (0x90, 0x00) || random.data.len() != 16 {
                return Err(format!(
                "kernel crypto random: expected 16 bytes and status 9000, got data {:02X?} and status {:02X?}",
                random.data, random.status
            )
            .into());
            }

            // Exercise separate requests, partial SHA-256 blocks and idle gaps.
            // This detects repeats/stalls, not cryptographic unpredictability.
            let mut seen = std::collections::HashSet::new();
            for index in 0..16 {
                if index % 4 == 0 {
                    std::thread::sleep(Duration::from_millis(10));
                }
                let len = [16, 31, 32, 33, 255][index % 5];
                let mut command = CommandBuilder::process_no_data_with_le(0x85, len);
                command.p1 = len;
                let start = Instant::now();
                let response = client.exchange(&command)?;
                if response.status != (0x90, 0)
                    || response.data.len() != usize::from(len)
                    || response.data.iter().all(|b| *b == 0)
                    || !seen.insert(response.data.clone())
                {
                    return Err(format!("RNG request {index} failed or repeated").into());
                }
                println!(
                    "KERNEL-RNG-TIMING request={index} bytes={len} apdu_elapsed_us={}",
                    start.elapsed().as_micros()
                );
            }

            eprintln!("kernel-crypto: AES-128 CBC");
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x82, 0x10))?,
                &AES128_NIST_CIPHERTEXT,
                (0x90, 0x00),
                "kernel crypto AES-128 CBC",
            )?;

            eprintln!("kernel-crypto: P-256 keygen");
            let start = Instant::now();
            let p256 = exchange_kernel_crypto(
                client,
                &CommandBuilder::process_no_data_with_le(0x84, 0x41),
            )?;
            println!(
                "KERNEL-CRYPTO-TIMING board={} op=p256_generate_keypair apdu_elapsed_ms={}",
                board.env_name,
                start.elapsed().as_millis()
            );
            if p256.status != (0x90, 0x00) || p256.data.len() != 65 || p256.data[0] != 0x04 {
                return Err(format!(
                "kernel crypto P-256 keygen: expected uncompressed public key and status 9000, got data {:02X?} and status {:02X?}",
                p256.data, p256.status
            )
            .into());
            }

            Ok(())
        },
    );
    test_result?;

    Ok(TestReport::passed(if bench.is_some() { 1 } else { 19 }))
}

fn exchange_kernel_crypto(
    client: &mut ApduClient,
    command: &OwnedT0Command,
) -> Result<T0Response, Box<dyn Error>> {
    let mut command = command.clone();
    if matches!(
        command.ins,
        0x84 | KernelCryptoBench::INS_P256_GENERATE_KEYPAIR
    ) {
        command.p1 = 1;
        command.lc = 1;
        command.data = vec![0];
    }
    // Key generation keeps its case-4 coverage, with the complete result
    // retrieved from the shared APDU buffer in one GET RESPONSE.
    client.exchange(&command)
}

pub(crate) fn run_kernel_crypto_bench(
    client: &mut ApduClient,
    board: &str,
    bench: &KernelCryptoBench,
) -> Result<(), Box<dyn Error>> {
    eprintln!("kernel-crypto-bench: {}", bench.op_name());
    let command = bench.command();
    let start = Instant::now();
    let response = exchange_kernel_crypto(client, &command)?;
    let elapsed = start.elapsed();
    bench.verify_response(&response)?;
    println!(
        "KERNEL-CRYPTO-BENCH board={} op={} elapsed_ms={} data={}",
        board,
        bench.op_name(),
        elapsed.as_millis(),
        hex_bytes_upper(&response.data)
    );
    Ok(())
}

/// Enrollment and reconstruction plumbing, not PUF qualification.
pub(crate) fn run_sram_fingerprint_test(
    ctx: &TestContext,
    board: &str,
) -> Result<usize, Box<dyn Error>> {
    if board != "raspi-pico2" || ctx.openocd().is_none() {
        return Err("sram_fingerprint requires physical Pico2/OpenOCD".into());
    }
    let board = board_spec(board)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let command = |ins, p1, p2, le| CommandBuilder::gp_command(ins, p1, p2, &[], le);
    let mut saved_mask = Vec::new();
    target.boot_sram_probe("sram-enroll", APDU_RESPONSE_TIMEOUT, |client| {
        expect_status(
            client.exchange(&command(0xb1, 3, 1, 255))?,
            (0x69, 0x85),
            "not enrolled",
        )?;
        expect_status(
            client.exchange(&command(0xb2, 0, 0, 255))?,
            (0x69, 0x85),
            "missing mask",
        )?;
        for (ins, p1, p2, le) in [
            (0xb0, 0, 1, 4),
            (0xb1, 2, 1, 255),
            (0xb1, 1, 0, 255),
            (0xb2, 4, 0, 255),
            (0xb2, 0, 1, 255),
        ] {
            expect_status(
                client.exchange(&command(ins, p1, p2, le))?,
                (0x6a, 0x80),
                "invalid parameters",
            )?;
        }
        for ins in 0xb3..=0xb5 {
            expect_status(
                client.exchange(&command(ins, 0, 0, 0))?,
                (0x6d, 0),
                "removed command",
            )?;
        }
        let response = client.exchange(&command(0xb0, 2, 1, 4))?;
        if response.status != (0x90, 0)
            || response.data.len() != 4
            || u32::from_be_bytes(response.data[..4].try_into()?) < 2040
        {
            return Err("enrollment did not retain enough positions".into());
        }
        let count = u32::from_be_bytes(response.data[..4].try_into()?);
        for page in 0..4 {
            let part = client.exchange(&command(0xb2, page, 0, 255))?;
            if part.status != (0x90, 0) || part.data.len() != 255 {
                return Err("invalid mask fragment".into());
            }
            saved_mask.extend_from_slice(&part.data);
        }
        if saved_mask.iter().map(|b| b.count_zeros()).sum::<u32>() != count {
            return Err("mask fragments disagree with enrollment count".into());
        }
        for votes in [1, 15, 255] {
            let response = client.exchange(&command(0xb1, votes, 1, 255))?;
            if response.status != (0x90, 0) || response.data.len() != 255 {
                return Err("invalid fingerprint response".into());
            }
        }
        Ok(())
    })?;
    for _ in 0..3 {
        target.boot_sram_probe("sram-mask-restored", APDU_RESPONSE_TIMEOUT, |client| {
            let response = client.exchange(&command(0xb1, 15, 1, 255))?;
            if response.status != (0x90, 0) || response.data.len() != 255 {
                return Err("persisted mask could not reconstruct after reset".into());
            }
            for page in 0..4 {
                let start = usize::from(page) * 255;
                expect_response(
                    client.exchange(&command(0xb2, page, 0, 255))?,
                    &saved_mask[start..start + 255],
                    (0x90, 0),
                    "mask fragment restored",
                )?;
            }
            // A noisy fingerprint is not a registry persistence failure.
            Ok(())
        })?;
    }
    Ok(33)
}

/// Keep privileged failures distinct from recoverable Rustlet failures.
pub(crate) fn run_kernel_cpu_fatal_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<(), Box<dyn Error>> {
    let board = board_spec(board)?;
    for (flag, cause) in [
        ("OXIDE_SE_KERNEL_FAULT_UDF", 1 << 16),
        ("OXIDE_SE_KERNEL_FAULT_UNALIGNED", 1 << 24),
        ("OXIDE_SE_KERNEL_FAULT_NOCP", 1 << 19),
        ("OXIDE_SE_KERNEL_FAULT_DIVZERO", 1 << 25),
        ("OXIDE_SE_KERNEL_FAULT_BUS", (1 << 9) | (1 << 15)),
        ("OXIDE_SE_KERNEL_FAULT_UNSTACK", 1 << 11),
        ("OXIDE_SE_KERNEL_FAULT_INVPC", 1 << 18),
    ] {
        if board.env_name == "raspi-pico1"
            && matches!(
                flag,
                "OXIDE_SE_KERNEL_FAULT_BUS"
                    | "OXIDE_SE_KERNEL_FAULT_UNSTACK"
                    | "OXIDE_SE_KERNEL_FAULT_INVPC"
            )
        {
            continue;
        }
        let fault_ctx = ctx.with_fault(flag);
        if ctx.openocd().is_some() {
            if board.env_name != "raspi-pico2" {
                return Err("kernel CPU fault hardware controls require Pico2".into());
            }
            build_firmware(
                &fault_ctx.build,
                FirmwareKind::CoreTest,
                None,
                board.env_name,
                "hardware",
            )?;
            testing::openocd::run_cpu_fatal(
                &fault_ctx,
                board,
                &firmware_elf_path(FirmwareKind::CoreTest)?,
                cause,
            )?;
        } else {
            if board.env_name != "raspi-pico1" {
                return Err("kernel CPU fault QEMU controls require Pico1".into());
            }
            testing::target::run_core(
                &fault_ctx,
                board,
                "qemu-kernel-cpu-fault",
                "kernel-cpu-fault",
                |output| {
                    let text = format!(
                        "{}\n{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    );
                    if output.status.success()
                        || !text.contains("fatal ARMv6-M HardFault:")
                        || !text.contains("kernel fatal: BKPT #0")
                        || text.contains("instruction-returned")
                    {
                        return Err(format!(
                            "kernel CPU fault did not halt through HardFault: {text}"
                        )
                        .into());
                    }
                    Ok(())
                },
            )?;
        }
        eprintln!(
            "KERNEL-CPU-FATAL-EVIDENCE board={} case={flag} PASS",
            board.env_name
        );
    }
    Ok(())
}

/// Observe NULLs on the actual T=0 wire, not only the firmware counter.
pub(crate) fn run_null_integrity(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let total = target.boot("NULL anticipation", APDU_RESPONSE_TIMEOUT, |client| {
        let (response, sent) = null_exchange(client, &CommandBuilder::kernel_timer(3))?;
        let (us, ticks, anticipated) = timer_counters(response)?;
        if !(200_000..1_000_000).contains(&us) || ticks != 0 || anticipated != 1 || sent != 1 {
            return Err(format!("monotonic/crypto preflight: us={us} ticks={ticks} anticipated={anticipated} wire={sent}").into());
        }
        let marker = [0x60, 0x90, 0, 0x61, 0x60, 0x90, 0, 0x61, 1, 2, 3, 4];
        expect_response(client.exchange(&CommandBuilder::kernel_timer(4))?, &marker, (0x90, 0), "enable diagnostic anticipation")?;
        // Actual erase/program, confined to flash-probe's reserved sector.
        let mut write = CommandBuilder::process_no_data_with_le(0x8e, 16);
        write.p1 = 1; write.p2 = 0xA5;
        let (response, sent) = null_exchange(client, &write)?;
        expect_response(response, &[0x52,0x4c,0x4f,0x53,0x46,0x4c,0x53,0x48,0xa5,0x8e,16,0,0xa5,0xff,0xff,0xff], (0x90,0), "flash anticipation payload intact")?;
        if sent < 2 { return Err("flash erase/program emitted fewer than two anticipated NULLs".into()); }
        expect_response(client.exchange(&CommandBuilder::kernel_timer(6))?, &marker, (0x90, 0), "disable diagnostic anticipation")?;
        // Delegated SCP03: response crypto is executed by a Rustlet SD with no
        // transport pointer. Enable forced preflight only inside the command,
        // after UNWRAP, so observed NULLs must come from WRAP/commit afterwards.
        expect_response(client.exchange(&CommandBuilder::select(complete_security_domain_instance_aid()))?, complete_security_domain_select_fci(), (0x90,0), "select delegated SD")?;
        let profile = HostScp03Profile::S16;
        let keys = exchange_scp03_initialize_update(client, profile, profile.challenge(),
            &SCP03_TEST_ENC_KEY, &SCP03_TEST_MAC_KEY, 1, 3, "NULL delegated SD")?;
        let (authenticate, mut command_chain) = CommandBuilder::scp03_external_authenticate(0x33,
            &keys.host_cryptogram, &keys.session_mac_key, profile.mac_len())?;
        expect_status(client.exchange(&authenticate)?, (0x90,0), "NULL delegated authenticate")?;
        let mut response_chain = command_chain;
        let mut command_counter = 0;
        let mut response_counter = 0;
        for mode in [4, 5, 6] {
            let mut command = CommandBuilder::kernel_timer(mode);
            command.le = 32; // 16 encrypted bytes plus the S16 R-MAC.
            let protected = scp03_encrypt_command_data(command,
                &keys.session_enc_key, &keys.session_mac_key, &mut command_chain, &mut command_counter, profile.mac_len())?;
            let (response, sent) = null_exchange(client, &protected)?;
            let response = parse_protected_response(response, "NULL SD wrap")?;
            let mut mac_input = response.encrypted_data.clone(); mac_input.extend_from_slice(&[0x90, 0]);
            let mac = host_chained_truncated_aes_cmac(&keys.session_rmac_key, &mut response_chain, &mac_input, profile.mac_len())?;
            let iv = host_scp03_encryption_iv(&keys.session_enc_key, &mut response_counter, 0x02)?;
            let plain = host_aes_cbc_decrypt(&keys.session_enc_key, &iv, &response.encrypted_data, HostCbcPadding::Iso9797M2)?;
            if response.status != (0x90,0) || response.mac != mac || plain != marker {
                return Err("NULL corrupted SD protected response or session chaining".into());
            }
            if mode != 6 && sent == 0 { return Err("SD wrap emitted no anticipated NULL after application return".into()); }
            eprintln!("NULL delegated mode={mode} wire={sent}: authenticated response intact");
        }
        if ctx.openocd().is_none() {
            eprintln!("NULL integrity: SKIP measured-budget SD WRAP watchdog on QEMU; wire integrity and anticipation checks passed");
            return Ok(12);
        }
        // The same SD is re-entered for WRAP after a long kernel handler.
        // Its expired/insufficient APDU budget must be a terminal fault.
        let mut command = CommandBuilder::kernel_timer(8);
        command.le = 32;
        let protected = scp03_encrypt_command_data(command,
            &keys.session_enc_key, &keys.session_mac_key, &mut command_chain,
            &mut command_counter, profile.mac_len())?;
        let started = Instant::now();
        expect_status(client.exchange(&protected)?, (0x6f, 0), "SD WRAP shares the APDU watchdog deadline")?;
        eprintln!("Watchdog delegated WRAP: terminal fault after {:.3}s", started.elapsed().as_secs_f64());
        expect_response(client.exchange(&CommandBuilder::select(complete_security_domain_instance_aid()))?, complete_security_domain_select_fci(), (0x90,0), "reselect SD after watchdog fault")?;
        expect_response(client.exchange(&CommandBuilder::kernel_timer(6))?, &marker, (0x90,0), "transport and SD live after watchdog fault")?;
        Ok(15)
    })?;
    Ok(TestReport::passed(total))
}

fn null_exchange(
    client: &mut ApduClient,
    command: &OwnedT0Command,
) -> Result<(T0Response, usize), Box<dyn Error>> {
    let mut nulls = 0;
    let response = client
        .protocol
        .exchange_with_progress(command.as_borrowed(), || nulls += 1)?;
    Ok((response, nulls))
}

/// Fixed workload, same diagnostic image and timer query before/after.
fn run_registry_performance(
    target: &mut testing::target::TargetSession<'_>,
    path: &str,
    load_payload: &DynamicLoadPayload,
) -> Result<usize, Box<dyn Error>> {
    if std::env::var_os("OXIDE_REGISTRY_STATE_PROFILE").is_some() {
        return run_registry_state_profile(target, path);
    }
    use std::io::Write;
    let mut file = std::fs::File::create(path)?;
    let mut intrinsic = std::fs::File::create(format!("{path}.intrinsic.csv"))?;
    writeln!(intrinsic, "boot,repeat,case,useful_bytes,metric,calls,total_ticks,min_ticks,max_ticks,last_ticks,timer_hz")?;
    writeln!(file, "boot,repeat,operation,useful_bytes,host_ns,device_ticks,timer_hz,cpu_hz,timer_overhead_ticks")?;
    let sizes = [0usize, 17, 219, 220, 221, 223, 224, 225, 236, 237, 244];
    let short = std::env::var_os("OXIDE_REGISTRY_PERF_SHORT").is_some();
    let mut total = 0;
    for boot in 0..if short { 1 } else { 3 } {
        let mut scenario = |client: &mut ApduClient| {
            record_registry_metrics(client, &mut intrinsic, boot, 0, "boot_recovery", 0)?;
            if boot == 0 {
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 0xfa, 0, &[], 0))?,
                    (0x90, 0),
                    "63 entries, six nested scopes and full BOSS rollback",
                )?;
                record_registry_metrics(
                    client,
                    &mut intrinsic,
                    boot,
                    0,
                    "capacity_63_rollback",
                    2528,
                )?;
            }
            if boot != 0 {
                for (id, size) in sizes.iter().copied().enumerate() {
                    let expected: Vec<u8> = (0..size).map(|i| (i as u8).wrapping_add(4)).collect();
                    read_registry_object(client, id as u8, &expected)?;
                    record_registry_metrics(
                        client,
                        &mut intrinsic,
                        boot,
                        0,
                        "first_read_after_reboot",
                        size,
                    )?;
                }
            }
            expect_status(
                client.exchange(&CommandBuilder::gp_command(0xa0, 0xf1, 0, &[], 0))?,
                (0x90, 0),
                "PUF storage codec hardware probe",
            )?;
            for repeat in 0..if short { 2 } else { 5 } {
                for (id, size) in sizes.iter().copied().enumerate() {
                    let data: Vec<u8> = (0..size).map(|i| (i as u8).wrapping_add(repeat)).collect();
                    for (operation, p1) in [("write", 1), ("read", 2), ("read_hot", 2)] {
                        let command = CommandBuilder::gp_command(
                            0xa0,
                            p1,
                            id as u8,
                            if p1 == 1 { &data } else { &[] },
                            if p1 == 2 { size as u8 } else { 0 },
                        );
                        let start = std::time::Instant::now();
                        let response = client.exchange(&command)?;
                        let elapsed = start.elapsed().as_nanos();
                        expect_response(
                            response,
                            if p1 == 2 { &data } else { &[] },
                            (0x90, 0),
                            "performance operation",
                        )?;
                        let timing =
                            client.exchange(&CommandBuilder::gp_command(0xa0, 0xf0, 0, &[], 16))?;
                        if timing.status != (0x90, 0) || timing.data.len() != 16 {
                            return Err("invalid timer report".into());
                        }
                        let v: Vec<u32> = timing
                            .data
                            .chunks_exact(4)
                            .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
                            .collect();
                        writeln!(
                            file,
                            "{boot},{repeat},{operation},{size},{elapsed},{},{},{},{}",
                            v[0], v[1], v[2], v[3]
                        )?;
                        let case = if p1 == 1 {
                            if boot == 0 && repeat == 0 {
                                "create"
                            } else {
                                "replace"
                            }
                        } else {
                            operation
                        };
                        record_registry_metrics(client, &mut intrinsic, boot, repeat, case, size)?;
                        total += 1;
                    }
                }
            }
            if short {
                file.flush()?;
                intrinsic.flush()?;
                return Ok(());
            }
            for repeat in 0..5 {
                for (mode, case) in [
                    (0, "rollback"),
                    (1, "savepoint_rollback"),
                    (2, "savepoint_accept_commit"),
                ] {
                    expect_status(
                        client.exchange(&CommandBuilder::gp_command(0xa0, 0xf5, mode, &[], 0))?,
                        (0x90, 0),
                        case,
                    )?;
                    record_registry_metrics(client, &mut intrinsic, boot, repeat, case, 21)?;
                }
                expect_status(
                    client.exchange(&CommandBuilder::gp_command(0xa0, 3, 0xfe, &[], 0))?,
                    (0x90, 0),
                    "delete committed fixture",
                )?;
                record_registry_metrics(client, &mut intrinsic, boot, repeat, "delete", 21)?;
            }
            file.flush()?;
            intrinsic.flush()?;
            Ok(())
        };
        if boot == 0 {
            target.boot("registry perf cold", APDU_RESPONSE_TIMEOUT, &mut scenario)?;
        } else {
            target.reboot("registry perf reboot", APDU_RESPONSE_TIMEOUT, &mut scenario)?;
        }
    }
    if short {
        return Ok(total);
    }
    target.reboot(
        "registry LOAD performance",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            record_registry_metrics(client, &mut intrinsic, 3, 0, "before_load_recovery", 0)?;
            let aid = crate_rustlet_minimal_valid_test_aid();
            let mut management = dynamic::Management::open(client, false)?;
            for repeat in 0..3 {
                management.load(client, aid, load_payload)?;
                record_registry_metrics(
                    client,
                    &mut intrinsic,
                    3,
                    repeat,
                    "load_package",
                    load_payload.fae.len(),
                )?;
                if repeat != 2 {
                    management.command(
                        client,
                        CommandBuilder::gp_delete_aid(aid),
                        (0x90, 0),
                        "delete LOAD fixture",
                    )?;
                    record_registry_metrics(
                        client,
                        &mut intrinsic,
                        3,
                        repeat,
                        "delete_package",
                        load_payload.fae.len(),
                    )?;
                }
            }
            Ok(())
        },
    )?;
    let mut large_size = None;
    let mut large_rejections = 0usize;
    target.reboot("registry large data", APDU_RESPONSE_TIMEOUT, |client| {
        record_registry_metrics(client, &mut intrinsic, 3, 0, "large_fixture_recovery", 0)?;
        expect_get_status_record(
            &client.exchange(&CommandBuilder::gp_get_status(
                0x20,
                false,
                crate_rustlet_minimal_valid_test_aid(),
            ))?,
            crate_rustlet_minimal_valid_test_aid(),
            false,
            "LOAD package recovered",
        )?;
        for repeat in 0..3 {
            for size in [223usize, 224, 225, 4095, 4096, 4097, 8191, 8192, 8193] {
                let response = client.exchange(&CommandBuilder::gp_command(
                    0xa0, 0xf6, 31, &(size as u32).to_be_bytes(), 0))?;
                if response.status == (0x6a, 0x84) {
                    large_rejections += 1;
                    record_registry_metrics(client, &mut intrinsic, 3, repeat, "large_capacity_rejection", size)?;
                    eprintln!("registry large capacity rejection: repeat={repeat} requested={size} retained={large_size:?}");
                    if let Some(previous) = large_size {
                        for start in (0..previous).step_by(244) { read_performance_range(client, 31, previous, start, 244)?; }
                        read_performance_range(client, 31, previous, previous, 1)?;
                        record_registry_metrics(client, &mut intrinsic, 3, repeat, "read_after_rejected_write", previous)?;
                    }
                    continue;
                }
                expect_status(response, (0x90, 0), "large data write")?;
                large_size = Some(size);
                record_registry_metrics(client, &mut intrinsic, 3, repeat, "large_write", size)?;
                for start in [0, 15, 16, 223, 224, 255, 256, size.saturating_sub(1), size] {
                    if start > size {
                        continue;
                    }
                    read_performance_range(client, 31, size, start, 33)?;
                    record_registry_metrics(
                        client,
                        &mut intrinsic,
                        3,
                        repeat,
                        "partial_read",
                        size,
                    )?;
                }
                for start in (0..size).step_by(244) {
                    read_performance_range(client, 31, size, start, 244)?;
                }
                record_registry_metrics(
                    client,
                    &mut intrinsic,
                    3,
                    repeat,
                    "streamed_full_read",
                    size,
                )?;
            }
        }
        Ok(())
    })?;
    let large_size = large_size.ok_or("no large-data fixture could be created")?;
    eprintln!("registry large observations: capacity_rejections={large_rejections}; final_size={large_size}");
    target.reboot("registry populate noise", APDU_RESPONSE_TIMEOUT, |client| {
        record_registry_metrics(client, &mut intrinsic, 3, 0, "before_noise_recovery", 0)?;
        let noise = client.exchange(&CommandBuilder::gp_command(0xa0, 0xf4, 0, &[], 4))?;
        if noise.status != (0x90, 0) || noise.data.len() != 4 { return Err("noise fixture failed".into()); }
        let pages = u32::from_be_bytes(noise.data[..].try_into().unwrap());
        if pages == 0 { return Err("noise fixture did not fill any erased page".into()); }
        eprintln!("registry perf noise: {pages} pages filled, alternating junk and hostile length headers");
        Ok(())
    })?;
    for boot in 4..7 {
        target.reboot("registry noise recovery", APDU_RESPONSE_TIMEOUT, |client| {
            record_registry_metrics(client, &mut intrinsic, boot, 0, "noise_recovery", 0)?;
            for start in (0..large_size).step_by(244) {
                read_performance_range(client, 31, large_size, start, 244)?;
            }
            record_registry_metrics(
                client,
                &mut intrinsic,
                boot,
                0,
                "noise_large_read",
                large_size,
            )?;
            for (id, size) in sizes.iter().copied().enumerate() {
                let expected: Vec<u8> = (0..size).map(|i| (i as u8).wrapping_add(4)).collect();
                read_registry_object(client, id as u8, &expected)?;
                record_registry_metrics(client, &mut intrinsic, boot, 0, "noise_first_read", size)?;
            }
            Ok(())
        })?;
    }
    let mut retained = Vec::new();
    target.reboot("registry live capacity", APDU_RESPONSE_TIMEOUT, |client| {
        record_registry_metrics(client, &mut intrinsic, 7, 0, "before_capacity_recovery", 0)?;
        for (index, size) in [16384usize, 16384, 8192, 4096, 2048, 1024]
            .into_iter()
            .enumerate()
        {
            let id = 40 + index as u8;
            let response = client.exchange(&CommandBuilder::gp_command(
                0xa0,
                0xf6,
                id,
                &(size as u32).to_be_bytes(),
                0,
            ))?;
            let success = response.status == (0x90, 0);
            if !success && response.status != (0x6a, 0x84) {
                return Err(format!("unexpected capacity status {:?}", response.status).into());
            }
            record_registry_metrics(
                client,
                &mut intrinsic,
                7,
                index as u8,
                if success {
                    "capacity_write"
                } else {
                    "capacity_rejection"
                },
                size,
            )?;
            if success {
                retained.push((id, size));
            }
            eprintln!("registry live capacity: id={id} bytes={size} accepted={success}");
        }
        Ok(())
    })?;
    for boot in 8..11 {
        target.reboot(
            "registry near-full recovery",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                record_registry_metrics(client, &mut intrinsic, boot, 0, "near_full_recovery", 0)?;
                for &(id, size) in &retained {
                    for start in (0..size).step_by(244) {
                        read_performance_range(client, id, size, start, 244)?;
                    }
                    record_registry_metrics(
                        client,
                        &mut intrinsic,
                        boot,
                        0,
                        "near_full_read",
                        size,
                    )?;
                }
                Ok(())
            },
        )?;
    }
    intrinsic.flush()?;
    Ok(total)
}

/// Replays existing diagnostic commands, including against archived pre-change ELFs.
/// Measures SD state reads and key extraction separately from Data benchmarks.
fn run_registry_state_profile(
    target: &mut testing::target::TargetSession<'_>,
    path: &str,
) -> Result<usize, Box<dyn Error>> {
    use std::io::Write;
    let mut file = std::fs::File::create(path)?;
    let mut intrinsic = std::fs::File::create(format!("{path}.intrinsic.csv"))?;
    writeln!(file, "boot,repeat,operation,device_ticks,timer_hz")?;
    writeln!(intrinsic, "boot,repeat,case,useful_bytes,metric,calls,total_ticks,min_ticks,max_ticks,last_ticks,timer_hz")?;
    let mut count = 0;
    for boot in 0..3 {
        let mut scenario = |client: &mut ApduClient| {
            record_registry_metrics(client, &mut intrinsic, boot, 0, "state_key_recovery", 0)?;
            let mut measure =
                |p1, p2, expected: &[u8], label: &str, repeat| -> Result<(), Box<dyn Error>> {
                    expect_response(
                        client.exchange(&CommandBuilder::gp_command(
                            0xa0,
                            p1,
                            p2,
                            &[],
                            expected.len() as u8,
                        ))?,
                        expected,
                        (0x90, 0),
                        label,
                    )?;
                    let timing =
                        client.exchange(&CommandBuilder::gp_command(0xa0, 0xf0, 0, &[], 16))?;
                    if timing.status != (0x90, 0) || timing.data.len() != 16 {
                        return Err("invalid state/key timing".into());
                    }
                    let ticks = u32::from_be_bytes(timing.data[..4].try_into()?);
                    let hz = u32::from_be_bytes(timing.data[4..8].try_into()?);
                    writeln!(file, "{boot},{repeat},{label},{ticks},{hz}")?;
                    record_registry_metrics(client, &mut intrinsic, boot, repeat, label, 0)?;
                    count += 1;
                    Ok(())
                };
            if boot == 0 {
                measure(6, 0, &[], "create_two_sd_and_data", 0)?;
                for repeat in 0..5 {
                    measure(7, 0, &[1; 4], "read_two_sd_and_data", repeat)?;
                }
                measure(8, 1, &[], "delete_sd_graph", 0)?;
                measure(9, 0, &[], "create_sd_and_two_keys", 0)?;
                measure(10, 0, &[], "install_sd_inherit_keys", 0)?;
            }
            for repeat in 0..5 {
                measure(11, 0, &[1; 3], "read_two_keys", repeat)?;
            }
            file.flush()?;
            intrinsic.flush()?;
            Ok(())
        };
        if boot == 0 {
            target.boot(
                "registry state/key cold",
                APDU_RESPONSE_TIMEOUT,
                &mut scenario,
            )?;
        } else {
            target.reboot(
                "registry state/key reboot",
                APDU_RESPONSE_TIMEOUT,
                &mut scenario,
            )?;
        }
    }
    Ok(count)
}

const REGISTRY_METRICS: [&str; 23] = [
    "recovery",
    "scan",
    "decode_boss",
    "decode_object",
    "allocate",
    "program",
    "erase",
    "publish",
    "prepare_object",
    "prepare_load",
    "append_load",
    "finalize_load",
    "begin_transaction",
    "commit",
    "rollback",
    "savepoint",
    "accept_savepoint",
    "rollback_savepoint",
    "write_data",
    "read_data",
    "delete",
    "stage_data",
    "initialize_area",
];
fn record_registry_metrics(
    client: &mut ApduClient,
    file: &mut std::fs::File,
    boot: usize,
    repeat: u8,
    case: &str,
    useful: usize,
) -> Result<(), Box<dyn Error>> {
    use std::io::Write;
    for group in 0..REGISTRY_METRICS.len().div_ceil(7) {
        let count = (REGISTRY_METRICS.len() - group * 7).min(7);
        let response = client.exchange(&CommandBuilder::gp_command(
            0xa0,
            0xf8,
            group as u8,
            &[],
            (count * 28) as u8,
        ))?;
        if response.status != (0x90, 0) || response.data.len() != count * 28 {
            return Err("invalid registry intrinsic timing report".into());
        }
        for (index, b) in response.data.chunks_exact(28).enumerate() {
            let name = REGISTRY_METRICS[group * 7 + index];
            let calls = u32::from_be_bytes(b[..4].try_into().unwrap());
            if calls == 0 {
                continue;
            }
            let total = u64::from_be_bytes(b[4..12].try_into().unwrap());
            let v: Vec<u32> = b[12..]
                .chunks_exact(4)
                .map(|x| u32::from_be_bytes(x.try_into().unwrap()))
                .collect();
            writeln!(
                file,
                "{boot},{repeat},{case},{useful},{name},{calls},{total},{},{},{},{}",
                v[0], v[1], v[2], v[3]
            )?;
        }
    }
    // Cumulative stack watermark for this boot; sampled outside all timed work.
    let stack = client.exchange(&CommandBuilder::gp_command(0xca, 0xdf, 0x71, &[], 4))?;
    if stack.status != (0x90, 0) || stack.data.len() != 4 {
        return Err("missing kernel stack watermark".into());
    }
    let peak = u32::from_be_bytes(stack.data[..].try_into().unwrap());
    let heap = client.exchange(&CommandBuilder::gp_command(0xa0, 0xf9, 0, &[], 20))?;
    if heap.status != (0x90, 0) || heap.data.len() != 20 {
        return Err("missing registry RAM report".into());
    }
    let fields: Vec<u32> = heap
        .data
        .chunks_exact(4)
        .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
        .collect();
    let path = std::env::var("OXIDE_REGISTRY_PERF_CSV")?;
    let mut memory = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(format!("{path}.memory.csv"))?;
    if memory.metadata()?.len() == 0 {
        writeln!(
            memory,
            "boot,repeat,case,useful_bytes,boot_stack_peak_bytes,heap_live_bytes,heap_capacity_bytes,heap_metadata_bytes,registry_control_bytes,live_entries"
        )?;
    }
    writeln!(
        memory,
        "{boot},{repeat},{case},{useful},{peak},{},{},{},{},{}",
        fields[0], fields[1], fields[2], fields[3], fields[4]
    )?;
    expect_status(
        client.exchange(&CommandBuilder::gp_command(0xa0, 0xf3, 0, &[], 0))?,
        (0x90, 0),
        "reset timing counters",
    )?;
    Ok(())
}

fn read_performance_range(
    client: &mut ApduClient,
    id: u8,
    size: usize,
    start: usize,
    len: usize,
) -> Result<(), Box<dyn Error>> {
    let mut request = [0u8; 8];
    request[..4].copy_from_slice(&(start as u32).to_be_bytes());
    request[4..].copy_from_slice(&(len as u32).to_be_bytes());
    let response = client.exchange(&CommandBuilder::gp_command(
        0xa0, 0xf7, id, &request, len as u8,
    ))?;
    let expected: Vec<u8> = (start..size.min(start + len))
        .map(|i| (i % 251) as u8)
        .collect();
    expect_response(response, &expected, (0x90, 0), "bounded data read")
}
