//! Registry authority tests across sibling kernel and Rustlet Security Domains.
use super::*;

const ROOT: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 1];
const KERNEL: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 3];
const RUSTLET: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 4];
const GRANDCHILD: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 5];
const APP_A: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 0x28];
const APP_B: &[u8] = &[0xA0, 0, 0, 0x47, 0x50, 0x4F, 0x53, 0x29];
const SHARED_TAG: u16 = 0xDF60;

struct Probe<'a> {
    client: &'a mut ApduClient,
    session: HostScp03Session,
    total: usize,
}

impl<'a> Probe<'a> {
    fn open(client: &'a mut ApduClient) -> Result<Self, Box<dyn Error>> {
        Self::open_for(client, ROOT)
    }

    fn open_for(client: &'a mut ApduClient, sd: &[u8]) -> Result<Self, Box<dyn Error>> {
        let (enc, mac) = if sd == KERNEL || sd == GRANDCHILD {
            (&SCP03_ROTATED_ENC_KEY, &SCP03_ROTATED_MAC_KEY)
        } else {
            (&SCP03_TEST_ENC_KEY, &SCP03_TEST_MAC_KEY)
        };
        let session =
            open_host_scp03_session(client, HostScp03Profile::S8, 1, 3, enc, mac, "SD authority")?;
        Ok(Self {
            client,
            session,
            total: 2,
        })
    }

    fn check(
        &mut self,
        command: OwnedT0Command,
        status: (u8, u8),
        data: Option<&[u8]>,
        label: &str,
    ) -> Result<(), Box<dyn Error>> {
        eprintln!("SD authority: {label}");
        let protected = scp03_encrypt_command_data(
            command,
            &self.session.session_enc_key,
            &self.session.session_mac_key,
            &mut self.session.command_mac_chain,
            &mut self.session.command_enc_counter,
            self.session.profile.mac_len(),
        )?;
        let response = self.client.exchange(&protected)?;
        self.total += 1;
        if let Some(data) = data {
            expect_response(response, data, status, label)
        } else {
            expect_status(response, status, label)
        }
    }
}

fn select(client: &mut ApduClient, aid: &[u8], status: (u8, u8)) -> Result<(), Box<dyn Error>> {
    let response = client.exchange(&CommandBuilder::select(aid))?;
    if response.status != status || (status != (0x90, 0) && !response.data.is_empty()) {
        return Err(format!(
            "SD authority SELECT {aid:02X?}: expected {status:02X?}, got {response:?}"
        )
        .into());
    }
    Ok(())
}

fn install(aid: &[u8]) -> OwnedT0Command {
    let package = crate_rustlet_minimal_valid_test_aid();
    CommandBuilder::install_with_aids_privileges_and_data(package, package, aid, &[0, 0, 0], &[])
}

pub(super) fn run(ctx: &TestContext, board: &str) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let mut total = target.boot(
        "SD authority parent fixture",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut p = Probe::open(client)?;
            p.check(
                CommandBuilder::gp_store_data_with_tag(0xDF63, &[0xC3]),
                (0x90, 0),
                None,
                "parent owns its marker",
            )?;
            Ok(p.total)
        },
    )?;

    // SELECT cannot climb out of the active subtree. Reboot restores the root
    // authority; flash must survive so both branches coexist during the attacks.
    let branches = [
        (KERNEL, APP_A, RUSTLET, APP_B, 0xDF61, 0xDF62, 0xA1),
        (RUSTLET, APP_B, KERNEL, APP_A, 0xDF62, 0xDF61, 0xB2),
    ];
    for &(sd, app, _, _, tag, _, marker) in &branches {
        total += target.reboot(
            "SD authority create branch",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                let mut parent = Probe::open(client)?;
                select(parent.client, sd, (0x90, 0))?;
                parent.total += 1;
                // The Rustlet child shares the root's keys: rejecting this stale
                // session must not rely solely on static-key separation.
                parent.check(
                    CommandBuilder::gp_store_data_with_tag(0xDF64, &[0xEE]),
                    (0x69, 0x85),
                    None,
                    "parent session rejected in child",
                )?;
                let previous = parent.total;
                let mut p = Probe::open_for(parent.client, sd)?;
                p.check(
                    CommandBuilder::gp_get_data(0xDF64, 1),
                    (0x6A, 0x88),
                    Some(&[]),
                    "stale-session mutation absent",
                )?;
                p.check(
                    install(app),
                    (0x90, 0),
                    None,
                    "own application installation succeeds",
                )?;
                p.check(
                    CommandBuilder::gp_store_data_with_tag(tag, &[marker]),
                    (0x90, 0),
                    None,
                    "own unique marker created",
                )?;
                p.check(
                    CommandBuilder::gp_store_data_with_tag(SHARED_TAG, &[marker]),
                    (0x90, 0),
                    None,
                    "same tag belongs independently to each SD",
                )?;
                Ok(previous + p.total)
            },
        )?;
    }
    for &(sd, app, sibling, foreign_app, tag, foreign_tag, marker) in &branches {
        total += target.reboot(
            "SD authority sibling attacks",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                select(client, sd, (0x90, 0))?;
                let mut p = Probe::open_for(client, sd)?;
                p.total += 1;
                for forbidden in [sibling, ROOT, foreign_app] {
                    select(p.client, forbidden, (0x6A, 0x82))?;
                    p.total += 1;
                    p.check(
                        CommandBuilder::gp_get_data(tag, 1),
                        (0x90, 0),
                        Some(&[marker]),
                        "failed SELECT preserves current authority and session",
                    )?;
                }
                for foreign in [foreign_app, sibling, ROOT] {
                    p.check(
                        CommandBuilder::gp_delete_aid(foreign),
                        (0x69, 0x82),
                        None,
                        "foreign DELETE denied",
                    )?;
                }
                p.check(
                    CommandBuilder::gp_delete_aid(&gp_data_object_aid(foreign_tag)),
                    (0x69, 0x82),
                    None,
                    "sibling DATA deletion denied",
                )?;
                p.check(
                    CommandBuilder::gp_delete_aid(&gp_data_object_aid(0xDF63)),
                    (0x69, 0x82),
                    None,
                    "parent DATA deletion denied",
                )?;
                for foreign in [sibling, ROOT] {
                    p.check(
                        CommandBuilder::gp_install_for_load(
                            &[0xA0, 0, 0, 0, 0x77],
                            foreign,
                            256,
                            &[0; 32],
                        ),
                        (0x69, 0x82),
                        None,
                        "LOAD cannot nominate another owner",
                    )?;
                }
                p.check(
                    CommandBuilder::gp_get_data(foreign_tag, 1),
                    (0x6A, 0x88),
                    Some(&[]),
                    "sibling DATA is not readable",
                )?;
                p.check(
                    CommandBuilder::gp_get_data(0xDF63, 1),
                    (0x6A, 0x88),
                    Some(&[]),
                    "parent DATA is not readable",
                )?;
                p.check(
                    CommandBuilder::gp_store_data_with_tag(SHARED_TAG, &[marker, 0x55]),
                    (0x90, 0),
                    None,
                    "own write succeeds after denied operations",
                )?;
                p.check(
                    CommandBuilder::gp_get_data(SHARED_TAG, 2),
                    (0x90, 0),
                    Some(&[marker, 0x55]),
                    "own replacement is readable",
                )?;
                p.check(
                    CommandBuilder::gp_delete_aid(app),
                    (0x90, 0),
                    None,
                    "own application deletion succeeds",
                )?;
                p.check(
                    install(app),
                    (0x90, 0),
                    None,
                    "own application can be reinstalled",
                )?;
                select(p.client, app, (0x90, 0))?;
                p.total += 1;
                Ok(p.total)
            },
        )?;
    }
    for &(sd, app, _, _, tag, _, marker) in &branches {
        total += target.reboot(
            "SD authority durable isolation",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                select(client, sd, (0x90, 0))?;
                let mut p = Probe::open_for(client, sd)?;
                p.total += 1;
                p.check(
                    CommandBuilder::gp_get_data(tag, 1),
                    (0x90, 0),
                    Some(&[marker]),
                    "unique branch marker survives sibling attacks",
                )?;
                p.check(
                    CommandBuilder::gp_get_data(SHARED_TAG, 2),
                    (0x90, 0),
                    Some(&[marker, 0x55]),
                    "same-tag branch values remain distinct after reboot",
                )?;
                select(p.client, app, (0x90, 0))?;
                p.total += 1;
                Ok(p.total)
            },
        )?;
    }
    total += target.reboot(
        "SD authority parent survival",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut p = Probe::open(client)?;
            p.check(
                CommandBuilder::gp_get_data(0xDF63, 1),
                (0x90, 0),
                Some(&[0xC3]),
                "parent marker survives both children",
            )?;
            Ok(p.total)
        },
    )?;
    // Boot and reboot both authenticate against the overridden keys inherited
    // through three generations. The manifest declares the grandchild first.
    for _ in 0..2 {
        total += target.reboot(
            "SD grandchild key inheritance",
            APDU_RESPONSE_TIMEOUT,
            |client| {
                select(client, KERNEL, (0x90, 0))?;
                select(client, GRANDCHILD, (0x90, 0))?;
                let mut p = Probe::open_for(client, GRANDCHILD)?;
                p.check(
                    CommandBuilder::gp_store_data_with_tag(0xDF65, &[0xD5]),
                    (0x90, 0),
                    None,
                    "grandchild inherited explicit parent keys",
                )?;
                Ok(p.total + 2)
            },
        )?;
    }
    Ok(TestReport::passed(total))
}
