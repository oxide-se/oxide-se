//! Target qualification of resident SD state and APDU registry rollback.
use super::*;

fn command(p1: u8, p2: u8, le: u8) -> OwnedT0Command {
    OwnedT0Command {
        cla: 0x80,
        ins: 0xA0,
        p1,
        p2,
        lc: 0,
        le,
        data: vec![],
    }
}

fn counters(
    client: &mut ApduClient,
    session: &mut HostScp03Session,
) -> Result<[u32; 3], Box<dyn Error>> {
    let command = scp03_encrypt_command_data(
        CommandBuilder::process_no_data_with_le(0x0C, 12),
        &session.session_enc_key,
        &session.session_mac_key,
        &mut session.command_mac_chain,
        &mut session.command_enc_counter,
        session.profile.mac_len(),
    )?;
    let response = client.exchange(&command)?;
    if response.status != (0x90, 0) || response.data.len() != 12 {
        return Err(format!("SD transaction counters: {response:?}").into());
    }
    Ok(std::array::from_fn(|i| {
        u32::from_be_bytes(response.data[i * 4..i * 4 + 4].try_into().unwrap())
    }))
}

fn prepare(client: &mut ApduClient, level: u8) -> Result<HostScp03Session, Box<dyn Error>> {
    prepare_with_error_crash(client, level, false)
}

fn prepare_with_error_crash(
    client: &mut ApduClient,
    level: u8,
    crash: bool,
) -> Result<HostScp03Session, Box<dyn Error>> {
    select_complete_security_domain(client, "SD transaction")?;
    let mut reset = CommandBuilder::process_no_data(0x0B);
    reset.p1 = u8::from(crash);
    expect_status(
        client.exchange(&reset)?,
        (0x90, 0),
        "reset SD transaction probe",
    )?;
    let profile = HostScp03Profile::S8;
    let keys = exchange_scp03_initialize_update(
        client,
        profile,
        profile.challenge(),
        &SCP03_TEST_ENC_KEY,
        &SCP03_TEST_MAC_KEY,
        1,
        3,
        "SD transaction",
    )?;
    let (authenticate, chain) = CommandBuilder::scp03_external_authenticate(
        level,
        &keys.host_cryptogram,
        &keys.session_mac_key,
        profile.mac_len(),
    )?;
    expect_status(
        client.exchange(&authenticate)?,
        (0x90, 0),
        "SD transaction authenticate",
    )?;
    Ok(HostScp03Session {
        profile,
        session_enc_key: keys.session_enc_key,
        session_mac_key: keys.session_mac_key,
        command_mac_chain: chain,
        command_enc_counter: 0,
    })
}

pub(super) fn run(ctx: &TestContext, board: &str) -> Result<TestReport, Box<dyn Error>> {
    let board = board_spec(board)?;
    let mut target =
        testing::target::prepare_apdu_session(ctx, board, LayoutImageFormat::Elf, true)?;
    let mut failures = Vec::new();
    let mut total = 0;
    // Continue independent rebooted cases even when one regression is found.
    let result = target.boot("SD management rollback", APDU_RESPONSE_TIMEOUT, |client| {
        let mut session = prepare(client, 0x03)?;
        exchange_protected_scp03_expected_status(client, &mut session, command(12,1,0),
            (0x69,0x85), "SD hook mutates then rejects operation")?;
        let observed = counters(client, &mut session)?;
        if observed != [0,2,0] {
            return Err(format!("SD management rollback must preserve unwrap only: expected [0, 2, 0], got {observed:?}").into());
        }
        Ok(6)
    });
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }

    let result = target.reboot(
        "selected SD process crash",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut session = prepare(client, 0x03)?;
            let mut crash = CommandBuilder::process_no_data(0x0B);
            crash.p1 = 2;
            exchange_protected_scp03_expected_status(
                client,
                &mut session,
                crash,
                (0x6F, 0),
                "selected SD process_apdu mutates then panics",
            )?;
            let old = scp03_encrypt_command_data(
                CommandBuilder::process_no_data_with_le(0x0C, 12),
                &session.session_enc_key,
                &session.session_mac_key,
                &mut session.command_mac_chain,
                &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?;
            if client.exchange(&old)?.status == (0x90, 0) {
                return Err("faulted selected SD resumed its previous session".into());
            }
            let mut fresh = prepare(client, 0x03)?;
            if counters(client, &mut fresh)? != [0, 1, 0] {
                return Err("selected SD crash recovery retained volatile mutations".into());
            }
            Ok(12)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }

    for level in [0x03, 0x33] {
        let result = target.reboot(
            &format!("SD crash rollback SCP03-{level:02X}"),
            APDU_RESPONSE_TIMEOUT,
            |client| {
                let mut session = prepare(client, level)?;
                exchange_protected_scp03_expected_status(
                    client,
                    &mut session,
                    command(12, 2, 0),
                    (0x6F, 0),
                    "SD hook mutates then panics",
                )?;
                // A faulted SD must not resume the old authenticated session.
                let protected = scp03_encrypt_command_data(
                    CommandBuilder::process_no_data_with_le(0x0C, 12),
                    &session.session_enc_key,
                    &session.session_mac_key,
                    &mut session.command_mac_chain,
                    &mut session.command_enc_counter,
                    session.profile.mac_len(),
                )?;
                expect_status(
                    client.exchange(&protected)?,
                    (0x69, 0x85),
                    "old SD session rejected after crash",
                )?;
                select_complete_security_domain(client, "SD reselect after crash")?;
                let expected = [0; 12]; // An SD crash aborts the complete APDU.
                expect_response(
                    client.exchange(&CommandBuilder::process_no_data_with_le(0x0C, 12))?,
                    &expected,
                    (0x90, 0),
                    "faulted resident state was discarded",
                )?;
                expect_status(
                    client.exchange(&command(2, 0xF0, 1))?,
                    (0x6A, 0x88),
                    "crashed operation DATA absent",
                )?;
                let mut fresh = prepare(client, 0x03)?;
                exchange_protected_scp03_status(
                    client,
                    &mut fresh,
                    command(12, 0, 0),
                    "new session succeeds after SD crash",
                )?;
                if counters(client, &mut fresh)? != [1, 2, 0] {
                    return Err("new SD session has incorrect persistent counters".into());
                }
                exchange_protected_scp03_status(
                    client,
                    &mut fresh,
                    command(3, 0xF0, 0),
                    "remove successful recovery fixture",
                )?;
                Ok(16)
            },
        );
        match result {
            Ok(n) => total += n,
            Err(e) => {
                eprintln!("SD qualification failure: {e}");
                failures.push(e.to_string());
            }
        }
    }

    let result = target.reboot(
        "SD protected publication failure",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut session = prepare(client, 0x33)?;
            // Fail the final BOSS after a normal hook and response wrapping.
            exchange_protected_scp03_expected_status(
                client,
                &mut session,
                command(14, 0, 0),
                (0x65, 0x81),
                "SD publication failure discards protected response",
            )?;
            Ok(5)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }

    let result = target.reboot("SD publication recovery", APDU_RESPONSE_TIMEOUT, |client| {
        select_complete_security_domain(client, "SD recovery")?;
        expect_response(
            client.exchange(&CommandBuilder::process_no_data_with_le(0x0C, 12))?,
            &[0; 12],
            (0x90, 0),
            "SD state restored after publication failure",
        )?;
        expect_status(
            client.exchange(&command(2, 0xF0, 1))?,
            (0x6A, 0x88),
            "staged DATA absent after reboot",
        )?;
        let mut session = prepare(client, 0x03)?;
        exchange_protected_scp03_status(
            client,
            &mut session,
            command(12, 0, 0),
            "later successful SD mutation",
        )?;
        let observed = counters(client, &mut session)?;
        if observed != [1, 2, 0] {
            return Err(format!("later SD mutation: {observed:?}").into());
        }
        Ok(9)
    });
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }
    let result = target.reboot(
        "application rollback after SD wrap crash",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut installer = prepare(client, 0x03)?;
            exchange_protected_scp03_status(
                client,
                &mut installer,
                CommandBuilder::install(crate_rustlet_minimal_valid_test_aid()),
                "install counter application",
            )?;
            let mut session = prepare(client, 0x33)?;
            let select = scp03_encrypt_command_data(
                CommandBuilder::select(crate_rustlet_minimal_valid_test_aid()),
                &session.session_enc_key,
                &session.session_mac_key,
                &mut session.command_mac_chain,
                &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?;
            let selected = client.exchange(&select)?;
            if selected.status != (0x90, 0) {
                return Err(format!("protected application SELECT: {selected:?}").into());
            }
            exchange_protected_scp03_expected_status(
                client,
                &mut session,
                CommandBuilder::process_no_data_with_le(0x0D, 5),
                (0x6F, 0),
                "wrap crash returns only SW, no plaintext or partial protected data",
            )?;
            // Reboot immediately: no recovery APDU may overwrite evidence of
            // an accidental commit before the flash assertion below.
            Ok(11)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }
    let result = target.reboot(
        "application wrap crash reboot recovery",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_status(
                client.exchange(&CommandBuilder::select(
                    crate_rustlet_minimal_valid_test_aid(),
                ))?,
                (0x90, 0),
                "select application after reboot",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x0E, 1))?,
                &[0],
                (0x90, 0),
                "application mutation absent from flash",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x0D, 5))?,
                &[1, 0xD3, 0x91, 0xA7, 0x5E],
                (0x90, 0),
                "application succeeds without wrap fault",
            )?;
            Ok(3)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }
    let result = target.reboot(
        "application successful commit after wrap crash",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            expect_status(
                client.exchange(&CommandBuilder::select(
                    crate_rustlet_minimal_valid_test_aid(),
                ))?,
                (0x90, 0),
                "select recovered application",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x0E, 1))?,
                &[1],
                (0x90, 0),
                "later successful mutation persists",
            )?;
            Ok(2)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }
    let result = target.reboot(
        "application wrap crash live recovery",
        APDU_RESPONSE_TIMEOUT,
        |client| {
            let mut session = prepare(client, 0x33)?;
            let select = scp03_encrypt_command_data(
                CommandBuilder::select(crate_rustlet_minimal_valid_test_aid()),
                &session.session_enc_key,
                &session.session_mac_key,
                &mut session.command_mac_chain,
                &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?;
            let selected = client.exchange(&select)?;
            if selected.status != (0x90, 0) {
                return Err(format!("protected application SELECT: {selected:?}").into());
            }
            exchange_protected_scp03_expected_status(
                client,
                &mut session,
                CommandBuilder::process_no_data_with_le(0x0D, 5),
                (0x6F, 0),
                "second wrap crash discards response",
            )?;
            exchange_protected_scp03_expected_status(
                client,
                &mut session,
                CommandBuilder::process_no_data_with_le(0x0E, 1),
                (0x69, 0x85),
                "wrap crash rejects old session",
            )?;
            expect_status(
                client.exchange(&CommandBuilder::select(
                    crate_rustlet_minimal_valid_test_aid(),
                ))?,
                (0x90, 0),
                "reselect after wrap crash without reboot",
            )?;
            expect_response(
                client.exchange(&CommandBuilder::process_no_data_with_le(0x0E, 1))?,
                &[1],
                (0x90, 0),
                "RAM state retains previous successful commit",
            )?;
            Ok(9)
        },
    );
    match result {
        Ok(n) => total += n,
        Err(e) => {
            eprintln!("SD qualification failure: {e}");
            failures.push(e.to_string());
        }
    }
    // Case 3 is covered above by a completed application and a crashing wrap.
    // Check the other matrix rows, with immediate reboot before recovery APDUs.
    let mut expected_app = 1u8;
    for (label, app_crash, sd_crash) in [
        ("matrix no crash", false, false),
        ("matrix application crash only", true, false),
        ("matrix both crash", true, true),
    ] {
        let result = target.reboot(label, APDU_RESPONSE_TIMEOUT, |client| {
            let mut session = prepare_with_error_crash(client, 0x33, sd_crash)?;
            let select = scp03_encrypt_command_data(
                CommandBuilder::select(crate_rustlet_minimal_valid_test_aid()),
                &session.session_enc_key, &session.session_mac_key,
                &mut session.command_mac_chain, &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?;
            let response = client.exchange(&select)?;
            if response.status != (0x90, 0) { return Err(format!("matrix SELECT: {response:?}").into()); }
            let cmd = scp03_encrypt_command_data(
                CommandBuilder::process_no_data_with_le(if app_crash {0x0F} else {0x10}, 0xFF),
                &session.session_enc_key, &session.session_mac_key,
                &mut session.command_mac_chain, &mut session.command_enc_counter,
                session.profile.mac_len(),
            )?;
            let response = client.exchange(&cmd)?;
            let expected_sw = if app_crash {(0x6F, 0)} else {(0x90, 0)};
            let expected_len = if sd_crash {0} else if app_crash {8} else {24};
            if response.status != expected_sw || response.data.len() != expected_len {
                return Err(format!("{label}: expected SW {expected_sw:?} and {expected_len} protected bytes, got {response:?}").into());
            }
            Ok(6)
        });
        match result {
            Ok(n) => total += n,
            Err(e) => {
                eprintln!("SD qualification failure: {e}");
                failures.push(e.to_string());
            }
        }
        if !app_crash && !sd_crash {
            expected_app += 1;
        }
        let result = target.reboot(
            &format!("{label} persistent outcome"),
            APDU_RESPONSE_TIMEOUT,
            |client| {
                select_complete_security_domain(client, "matrix SD state after reboot")?;
                let mut expected_sd = [0; 12];
                // Protected SELECT committed one unwrap and one wrap previously.
                expected_sd[7] = if sd_crash { 1 } else { 2 };
                expected_sd[11] = if sd_crash { 1 } else { 2 };
                expect_response(
                    client.exchange(&CommandBuilder::process_no_data_with_le(0x0C, 12))?,
                    &expected_sd,
                    (0x90, 0),
                    "matrix committed SD state",
                )?;
                expect_status(
                    client.exchange(&CommandBuilder::select(
                        crate_rustlet_minimal_valid_test_aid(),
                    ))?,
                    (0x90, 0),
                    "matrix select application",
                )?;
                expect_response(
                    client.exchange(&CommandBuilder::process_no_data_with_le(0x0E, 1))?,
                    &[expected_app],
                    (0x90, 0),
                    "matrix committed application state",
                )?;
                Ok(4)
            },
        );
        match result {
            Ok(n) => total += n,
            Err(e) => {
                eprintln!("SD qualification failure: {e}");
                failures.push(e.to_string());
            }
        }
    }
    if !failures.is_empty() {
        return Err(failures.join("\n").into());
    }
    Ok(TestReport::passed(total))
}
