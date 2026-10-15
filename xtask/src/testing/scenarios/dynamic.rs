//! Dynamic packages only: reject unfinished, corrupt or incompatible LOADs,
//! then exercise persisted state and memory faults on clear and SCP03 images.
use super::*;

#[derive(Clone, Copy, Debug)]
enum IncompatibleFooter {
    Cpu,
    Abi,
}

/// Preserve the executable body and all other metadata, including a valid CRC.
/// Negative fixtures bypass the CLI validator so the target must reject them.
fn incompatible_payload(
    source: &DynamicLoadPayload,
    kind: IncompatibleFooter,
) -> Result<DynamicLoadPayload, Box<dyn Error>> {
    let metadata = apdu_tool::fae::validate(&source.fae)?;
    let len = source.fae.len();
    let (offset, descriptor) = match kind {
        IncompatibleFooter::Cpu => {
            // Thumb-v6M and Thumb-v7M are distinct FAE ISA subgroups. Pick the
            // other subgroup, which is well-formed but incompatible with this image.
            let subgroup = if (metadata.isa >> 16) & 0xff == 3 {
                2
            } else {
                3
            };
            (len - 8, (metadata.isa & !0x00ff_0000) | (subgroup << 16))
        }
        IncompatibleFooter::Abi => (len - 12, 0xFACA_DE16u32),
    };
    rewrite_footer_word(source, len - offset, descriptor)
}

fn with_stack_size(
    source: &DynamicLoadPayload,
    bytes: u32,
) -> Result<DynamicLoadPayload, Box<dyn Error>> {
    apdu_tool::fae::validate(&source.fae)?;
    if !bytes.is_multiple_of(32) || bytes / 32 > u16::MAX as u32 {
        return Err("stack fixture must fit the FAE 32-byte units".into());
    }
    let offset = source.fae.len() - 28;
    let requirements = u32::from_le_bytes(source.fae[offset..offset + 4].try_into()?);
    rewrite_footer_word(source, 28, (requirements & 0xffff_0000) | (bytes / 32))
}

fn rewrite_footer_word(
    source: &DynamicLoadPayload,
    distance: usize,
    descriptor: u32,
) -> Result<DynamicLoadPayload, Box<dyn Error>> {
    let mut fae = source.fae.clone();
    let len = fae.len();
    let offset = len
        .checked_sub(distance)
        .ok_or("truncated footer fixture")?;
    fae[offset..offset + 4].copy_from_slice(&descriptor.to_le_bytes());
    let crc_offset = len - 20;
    fae[crc_offset..crc_offset + 4].fill(0);
    // FAE 1.0 uses reflected CRC-32 with its own field treated as zero.
    let mut crc = 0xffff_ffffu32;
    for byte in &fae {
        crc ^= u32::from(*byte);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xedb8_8320 & 0u32.wrapping_sub(crc & 1));
        }
    }
    fae[crc_offset..crc_offset + 4].copy_from_slice(&(!crc).to_le_bytes());
    let hash = Sha256::digest(&fae).to_vec();
    Ok(DynamicLoadPayload { fae, hash })
}

pub(super) struct Management {
    session: Option<HostScp03Session>,
    pub(super) total: usize,
}

impl Management {
    pub(super) fn open(client: &mut ApduClient, protected: bool) -> Result<Self, Box<dyn Error>> {
        let session = if protected {
            Some(open_host_scp03_session(
                client,
                HostScp03Profile::S8,
                1,
                3,
                &SCP03_TEST_ENC_KEY,
                &SCP03_TEST_MAC_KEY,
                "dyn-rustlet SCP03",
            )?)
        } else {
            None
        };
        Ok(Self { session, total: 0 })
    }

    pub(super) fn command(
        &mut self,
        client: &mut ApduClient,
        command: OwnedT0Command,
        expected: (u8, u8),
        label: &str,
    ) -> Result<(), Box<dyn Error>> {
        expect_status(self.exchange(client, command, label)?, expected, label)
    }

    fn exchange(
        &mut self,
        client: &mut ApduClient,
        command: OwnedT0Command,
        label: &str,
    ) -> Result<T0Response, Box<dyn Error>> {
        eprintln!("{label}");
        let command = if let Some(session) = &mut self.session {
            scp03_encrypt_command_data(
                command,
                &session.session_enc_key,
                &session.session_mac_key,
                &mut session.command_mac_chain,
                &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?
        } else {
            command
        };
        let response = client.exchange(&command)?;
        self.total += 1;
        Ok(response)
    }

    fn present(&mut self, client: &mut ApduClient, aid: &[u8]) -> Result<(), Box<dyn Error>> {
        let label = "dyn-rustlet package present after reboot";
        let response = self.exchange(
            client,
            CommandBuilder::gp_get_status(0x20, false, aid),
            label,
        )?;
        expect_get_status_record(&response, aid, false, label)
    }

    fn begin(
        &mut self,
        client: &mut ApduClient,
        aid: &[u8],
        payload: &DynamicLoadPayload,
        bad_hash: bool,
    ) -> Result<(), Box<dyn Error>> {
        let mut hash = payload.hash.clone();
        if bad_hash {
            hash[0] ^= 1;
        }
        self.command(
            client,
            CommandBuilder::gp_install_for_load(
                aid,
                root_security_domain_aid(),
                payload.fae.len() as u32,
                &hash,
            ),
            (0x90, 0),
            "dyn-rustlet INSTALL [for load]",
        )
    }

    fn fragments(
        &mut self,
        client: &mut ApduClient,
        payload: &DynamicLoadPayload,
        partial: bool,
        final_status: (u8, u8),
    ) -> Result<(), Box<dyn Error>> {
        let encoded = apdu_tool::gp::encode_load_file_data_block(&payload.fae)?;
        // Bound clear and protected traffic alike for the physical UART FIFO.
        let chunks: Vec<_> = encoded.chunks(128).collect();
        if chunks.len() < 3 || chunks.len() > 256 {
            return Err("dynamic fixture must span 3..=256 LOAD blocks".into());
        }
        let count = if partial {
            chunks.len() / 2
        } else {
            chunks.len()
        };
        for (index, chunk) in chunks.iter().take(count).enumerate() {
            let last = index + 1 == chunks.len();
            self.command(
                client,
                CommandBuilder::gp_load_block(index as u8, last, chunk),
                if last { final_status } else { (0x90, 0) },
                &format!("dyn-rustlet LOAD {index} last={last}"),
            )?;
        }
        Ok(())
    }

    pub(super) fn load(
        &mut self,
        client: &mut ApduClient,
        aid: &[u8],
        payload: &DynamicLoadPayload,
    ) -> Result<(), Box<dyn Error>> {
        self.begin(client, aid, payload, false)?;
        self.fragments(client, payload, false, (0x90, 0))
    }

    fn absent(&mut self, client: &mut ApduClient, aid: &[u8]) -> Result<(), Box<dyn Error>> {
        self.command(
            client,
            CommandBuilder::gp_get_status(0x20, false, aid),
            (0x6A, 0x88),
            "dyn-rustlet package absent from GET STATUS",
        )
    }

    pub(super) fn install(
        &mut self,
        client: &mut ApduClient,
        aid: &[u8],
    ) -> Result<(), Box<dyn Error>> {
        self.command(
            client,
            CommandBuilder::install(aid),
            (0x90, 0),
            "dyn-rustlet INSTALL instance",
        )
    }
}

pub(super) fn select(client: &mut ApduClient, aid: &[u8]) -> Result<(), Box<dyn Error>> {
    expect_status(
        client.exchange(&CommandBuilder::select(aid))?,
        (0x90, 0),
        "dyn-rustlet SELECT",
    )
}

fn counter(client: &mut ApduClient, expected: u8) -> Result<usize, Box<dyn Error>> {
    select(client, crate_rustlet_state_test_aid())?;
    expect_response(
        client.exchange(&CommandBuilder::process_no_data_with_le(0x10, 1))?,
        &[expected],
        (0x90, 0),
        "dyn-rustlet persisted counter",
    )?;
    Ok(2)
}

pub(crate) fn run_dynamic_rustlet_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let mut total = 0;
    for (config, protected) in [
        ("configs/config_devkit.toml", false),
        ("configs/config_dyn_rustlet_scp03.toml", true),
    ] {
        total += run_with_build_config(ctx, config, |ctx| run_profile(ctx, board, protected))?;
    }
    Ok(TestReport::passed(total))
}

fn run_profile(ctx: &TestContext, board: &str, protected: bool) -> Result<usize, Box<dyn Error>> {
    eprintln!(
        "dyn-rustlet: profile={} board={board}",
        if protected { "SCP03" } else { "devkit" }
    );
    let board = board_spec(board)?;
    let minimal = build_dynamic_load_payload(&ctx.build, board, "minimal_valid_test")?;
    let basic = build_dynamic_load_payload(&ctx.build, board, "getting_started_test")?;
    let state = build_dynamic_load_payload(&ctx.build, board, "state_test")?;
    let fault = build_dynamic_load_payload(&ctx.build, board, "isolation_fault_test")?;
    let minimal = with_stack_size(&minimal, 4096)?;
    let basic = with_stack_size(&basic, 1536)?;
    let state = with_stack_size(&state, 3072)?;
    let zero_stack = with_stack_size(&state, 0)?;
    let minimum_stack = with_stack_size(&state, 32)?;
    let minimum_aid = &[0xF0, 0x53, 0x54, 0x41, 0x43, 1];
    let zero_aid = &[0xF0, 0x53, 0x54, 0x41, 0x43, 0];
    let unavailable_stack = with_stack_size(&state, u16::MAX as u32 * 32)?;
    let unavailable_aid = &[0xF0, 0x53, 0x54, 0x41, 0x43, 0x4B];
    let wrong_cpu = incompatible_payload(&state, IncompatibleFooter::Cpu)?;
    let wrong_abi = incompatible_payload(&fault, IncompatibleFooter::Abi)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let mut total = target.boot(
        "dyn-rustlet basic and interrupted LOAD",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, protected)?;
            management.absent(client, crate_rustlet_minimal_valid_test_aid())?;
            management.load(client, crate_rustlet_minimal_valid_test_aid(), &minimal)?;
            management.install(client, crate_rustlet_minimal_valid_test_aid())?;
            select(client, crate_rustlet_minimal_valid_test_aid())?;
            let basic_total =
                run_minimal_valid_post_select_apdus(client, "dyn-rustlet minimal", false)?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x08, 1))?,
                &[0x80],
                (0x90, 0),
                "dyn-rustlet stack frame larger than 2048 bytes",
            )?;
            management.load(client, crate_rustlet_getting_started_test_aid(), &basic)?;
            management.install(client, crate_rustlet_getting_started_test_aid())?;
            select(client, crate_rustlet_getting_started_test_aid())?;
            let basic_total =
                basic_total + run_getting_started_post_select_apdus(client, "dyn-rustlet basic")?;
            // SVC entry requires one 32-byte hardware exception frame.
            management.begin(client, zero_aid, &zero_stack, false)?;
            management.fragments(client, &zero_stack, false, (0x6A, 0x80))?;
            management.absent(client, zero_aid)?;
            management.load(client, minimum_aid, &minimum_stack)?;
            management.load(client, unavailable_aid, &unavailable_stack)?;
            management.command(
                client,
                CommandBuilder::install(unavailable_aid),
                (0x6a, 0x84),
                "dyn-rustlet insufficient RAM for declared stack",
            )?;
            management.command(
                client,
                CommandBuilder::gp_get_status(0x40, false, unavailable_aid),
                (0x6A, 0x88),
                "dyn-rustlet failed allocation creates no instance",
            )?;
            select(client, crate_rustlet_minimal_valid_test_aid())?;
            expect_status(
                client.exchange(&CommandBuilder::process_no_data(0))?,
                (0x90, 0),
                "dyn-rustlet survives stack allocation failure",
            )?;
            management.begin(client, crate_rustlet_state_test_aid(), &state, false)?;
            management.fragments(client, &state, true, (0x90, 0))?;
            // Return immediately: the next target boot resets without another APDU
            // that could cancel the pending load before the interruption.
            Ok(management.total + basic_total + 5)
        },
    )?;
    total += target.reboot(
        "dyn-rustlet interrupted LOAD recovery",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, protected)?;
            management.absent(client, zero_aid)?;
            management.present(client, minimum_aid)?;
            management.absent(client, crate_rustlet_state_test_aid())?;
            management.begin(client, crate_rustlet_state_test_aid(), &state, true)?;
            management.fragments(client, &state, false, (0x6A, 0x80))?;
            management.absent(client, crate_rustlet_state_test_aid())?;
            // Force an unrelated publication: the rejected package must not leak
            // from RAM into a later valid registry snapshot.
            management.command(
                client,
                CommandBuilder::gp_store_data_with_tag(0xDF42, b"sentinel"),
                (0x90, 0),
                "dyn-rustlet unrelated publication after rejection",
            )?;
            Ok(management.total)
        },
    )?;
    for (label, aid, payload) in [
        (
            "dyn-rustlet incompatible CPU",
            crate_rustlet_state_test_aid(),
            &wrong_cpu,
        ),
        (
            "dyn-rustlet incompatible ABI",
            crate_rustlet_isolation_fault_test_aid(),
            &wrong_abi,
        ),
    ] {
        total += target.reboot(label, APDU_RESPONSE_TIMEOUT, |client| {
            let mut management = Management::open(client, protected)?;
            // Also checks the previous rejected fixture after a real reboot.
            management.absent(client, crate_rustlet_state_test_aid())?;
            management.absent(client, crate_rustlet_isolation_fault_test_aid())?;
            management.begin(client, aid, payload, false)?;
            management.fragments(client, payload, false, (0x6A, 0x80))?;
            management.absent(client, aid)?;
            management.command(
                client,
                CommandBuilder::gp_store_data_with_tag(0xDF42, label.as_bytes()),
                (0x90, 0),
                "dyn-rustlet publication after incompatible FAE rejection",
            )?;
            Ok(management.total)
        })?;
    }
    total += target.reboot(
        "dyn-rustlet valid publication and isolation",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut management = Management::open(client, protected)?;
            management.absent(client, crate_rustlet_state_test_aid())?;
            management.absent(client, crate_rustlet_isolation_fault_test_aid())?;
            management.load(client, crate_rustlet_state_test_aid(), &state)?;
            management.install(client, crate_rustlet_state_test_aid())?;
            let mut checks = counter(client, 0)?;
            management.load(client, crate_rustlet_isolation_fault_test_aid(), &fault)?;
            for ins in [0x50, 0x51, 0x52, 0x53] {
                management.install(client, crate_rustlet_isolation_fault_test_aid())?;
                select(client, crate_rustlet_isolation_fault_test_aid())?;
                expect_status(
                    client.exchange(&CommandBuilder::process_no_data(0x54))?,
                    (0x90, 0),
                    "user SVC 0 cannot invoke kernel entry",
                )?;
                checks += 1;
                expect_status(
                    client.exchange(&CommandBuilder::process_no_data(ins))?,
                    (0x6F, 1),
                    "dyn-rustlet isolated fault",
                )?;
                checks += 2;
                select(client, crate_rustlet_minimal_valid_test_aid())?;
                expect_status(
                    client.exchange(&CommandBuilder::process_no_data(0))?,
                    (0x90, 0),
                    "dyn-rustlet unrelated instance survives fault",
                )?;
                checks += 2;
            }
            checks += counter(client, 1)?;
            Ok(management.total + checks)
        },
    )?;
    for expected in [2, 3, 4] {
        total +=
            target.reboot(
                "dyn-rustlet persistent execution",
                APDU_RESPONSE_TIMEOUT,
                |client| {
                    let count = counter(client, expected)?;
                    select(client, crate_rustlet_getting_started_test_aid())?;
                    Ok(count
                        + 1
                        + run_getting_started_post_select_apdus(client, "dyn-rustlet reboot")?)
                },
            )?;
    }
    Ok(total)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incompatible_fixtures_have_valid_integrity_and_preserve_body() {
        // Both ISA subgroups are accepted by the host format validator, which
        // independently checks CRC; only the running target selects one subgroup.
        let mut fae = vec![0x5a; 128];
        for word in [
            64u32,
            0xA990_1000,
            0,
            0,
            0xAC1D_A992,
            0x0102_0000,
            0xFAEC_0D10,
        ] {
            fae.extend_from_slice(&word.to_le_bytes());
        }
        // Seed the fixture with a CRC using the same public build-independent
        // format as real files; the known checksum guards this synthetic input.
        let crc = 0x65200850u32;
        let offset = fae.len() - 20;
        fae[offset..offset + 4].copy_from_slice(&crc.to_le_bytes());
        let source = DynamicLoadPayload {
            hash: Sha256::digest(&fae).to_vec(),
            fae,
        };
        let mutated = incompatible_payload(&source, IncompatibleFooter::Cpu).unwrap();
        assert_eq!(
            apdu_tool::fae::validate(&mutated.fae).unwrap().isa,
            0x0103_0000
        );
        assert_eq!(&mutated.fae[..128], &source.fae[..128]);
        assert_eq!(mutated.hash, Sha256::digest(&mutated.fae).to_vec());
        let abi = incompatible_payload(&source, IncompatibleFooter::Abi).unwrap();
        assert_eq!(&abi.fae[..128], &source.fae[..128]);
        // Independently generated CRC-32 known answer for the legacy ABI fixture.
        assert_eq!(&abi.fae[offset..offset + 4], &0x6d7db773u32.to_le_bytes());
        assert_eq!(
            &abi.fae[abi.fae.len() - 12..abi.fae.len() - 8],
            &0xFACA_DE16u32.to_le_bytes()
        );
        assert_eq!(abi.hash, Sha256::digest(&abi.fae).to_vec());
    }
}
