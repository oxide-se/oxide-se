//! End-to-end loading through the actual user-facing CLI binary.
use super::*;
use crate::testing::target::prepare_apdu_session;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

struct Workspace(PathBuf);
impl Workspace {
    fn new() -> Result<Self, Box<dyn Error>> {
        let path = std::env::temp_dir().join(format!("oxide-gp-cli-{}", std::process::id()));
        std::fs::create_dir(&path)?;
        #[cfg(unix)]
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))?;
        Ok(Self(path))
    }
    fn write(&self, name: &str, data: impl AsRef<[u8]>) -> Result<PathBuf, Box<dyn Error>> {
        let path = self.0.join(name);
        std::fs::write(&path, data)?;
        #[cfg(unix)]
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
        Ok(path)
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Ensures a failed read/wait cannot leave a CLI process owning the UART.
struct CliProcess(std::process::Child);
impl Drop for CliProcess {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

struct Profile {
    name: &'static str,
    config: &'static str,
    protocol: &'static str,
    scp03: Option<&'static str>,
    sd: &'static str,
}
const ROOT: &str = "A0000047504F5301";
const RUSTLET_SD: &str = "A0000047504F5304";
const PROFILES: &[Profile] = &[
    Profile {
        name: "rustlet-sd-scp03-s16",
        config: "configs/config_rustlet_security_domain_delegated_scp03_test.toml",
        protocol: "scp03",
        scp03: Some("s16"),
        sd: RUSTLET_SD,
    },
    Profile {
        name: "scp03-s8",
        config: "configs/config_scp03_test.toml",
        protocol: "scp03",
        scp03: Some("s8"),
        sd: ROOT,
    },
    Profile {
        name: "scp03-s16",
        config: "configs/config_scp03_s16_test.toml",
        protocol: "scp03",
        scp03: Some("s16"),
        sd: ROOT,
    },
    Profile {
        name: "scp11a",
        config: "configs/config_scp11a_test.toml",
        protocol: "scp11a",
        scp03: None,
        sd: ROOT,
    },
    Profile {
        name: "scp11c",
        config: "configs/config_scp11c_test.toml",
        protocol: "scp11c",
        scp03: None,
        sd: ROOT,
    },
    Profile {
        name: "scp11b-rejection",
        config: "configs/config_scp11b_test.toml",
        protocol: "scp11b",
        scp03: None,
        sd: ROOT,
    },
];

fn hex(data: &[u8]) -> String {
    data.iter().map(|b| format!("{b:02X}")).collect()
}

#[derive(Clone, Copy)]
enum Expected {
    Success,
    ProfileRejection,
    SecureFailure,
    Action,
    Data(&'static str),
    Status(u8, u8),
}

struct Cli<'a> {
    binary: PathBuf,
    workspace: &'a Workspace,
    profile: &'a Profile,
    credentials: PathBuf,
}
impl Cli<'_> {
    fn run(
        &self,
        link: &apdu_tool::LinkSpec,
        args: &[&str],
        secure: bool,
        expected: Expected,
    ) -> Result<(), Box<dyn Error>> {
        let endpoint = match link {
            apdu_tool::LinkSpec::UnixSocket { path } => path.display().to_string(),
            apdu_tool::LinkSpec::Tcp { host, port } => format!("{host}:{port}"),
            apdu_tool::LinkSpec::SerialPort { path, baud } => format!("{path}:{baud}"),
        };
        let mut command = Command::new(&self.binary);
        // A developer's live session and credentials must never affect a test.
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("APDU_") {
                command.env_remove(key);
            }
        }
        command
            .env("APDU_SESSION_FILE", self.workspace.0.join("session.json"))
            .args([
                "--serial",
                &endpoint,
                "--quiet",
                "--response-timeout",
                "30s",
            ]);
        if secure {
            command
                .args([
                    "--secure-channel",
                    self.profile.protocol,
                    "--security-domain",
                    self.profile.sd,
                    "--security-level",
                    if self.profile.scp03.is_some() && self.profile.sd == ROOT {
                        "c-mac+c-enc"
                    } else {
                        "c-mac+c-enc+r-mac+r-enc"
                    },
                    "--credentials",
                ])
                .arg(&self.credentials);
            if let Some(profile) = self.profile.scp03 {
                command.args(["--scp03-profile", profile]);
            }
        }
        eprintln!("gp-cli-load {}: {}", self.profile.name, args.join(" "));
        let mut process = CliProcess(
            command
                .args(args)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()?,
        );
        let child = &mut process.0;
        let stdout = target::drain(child.stdout.take().ok_or("missing CLI stdout")?);
        let stderr = target::drain(child.stderr.take().ok_or("missing CLI stderr")?);
        let deadline = Instant::now() + Duration::from_secs(300);
        let status = loop {
            if let Some(status) = child.try_wait()? {
                break status;
            }
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                let _ = stdout.join();
                let _ = stderr.join();
                return Err("CLI command exceeded its deadline".into());
            }
            thread::sleep(Duration::from_millis(10));
        };
        let stdout = stdout.join().map_err(|_| "CLI stdout reader panicked")??;
        let stderr = stderr.join().map_err(|_| "CLI stderr reader panicked")??;
        let output = String::from_utf8_lossy(&stdout);
        let error = String::from_utf8_lossy(&stderr);
        let accepted = match expected {
            Expected::Data(bytes) => status.success() && output.trim() == bytes,
            Expected::Action => status.success(),
            Expected::Success => status.success() && output.trim().ends_with("90 00"),
            Expected::SecureFailure => {
                status.code() == Some(14) && !output.trim().ends_with("90 00")
            }
            Expected::ProfileRejection => !status.success() && error.contains("cannot authorize"),
            Expected::Status(sw1, sw2) => {
                !status.success() && output.trim().ends_with(&format!("{sw1:02X} {sw2:02X}"))
            }
        };
        if !accepted {
            return Err(format!(
                "unexpected CLI outcome ({status}): stdout={output} stderr={error}"
            )
            .into());
        }
        Ok(())
    }
}

pub(crate) fn run_gp_cli_load_test_for_board(
    ctx: &TestContext,
    board: &str,
) -> Result<TestReport, Box<dyn Error>> {
    let root = repo_root()?;
    let status = Command::new("cargo")
        .current_dir(&root)
        .args(["build", "--offline", "-p", "apdu_tool"])
        .status()?;
    if !status.success() {
        return Err("cannot build apdu_tool".into());
    }
    let workspace = Workspace::new()?;
    let board_spec = board_spec(board)?;
    let load = build_dynamic_load_payload(&ctx.build, board_spec, "getting_started_test")?;
    let deploy = build_dynamic_load_payload(&ctx.build, board_spec, "minimal_valid_test")?;
    let load_path = workspace.write("load.fae", &load.fae)?;
    let deploy_path = workspace.write("deploy.fae", &deploy.fae)?;
    let host_secret = p256::SecretKey::from_slice(&[0x31; 32])?;
    workspace.write("host.key", host_secret.to_bytes())?;
    workspace.write(
        "host.cert",
        build_dev_oce_certificate(&host_secret.public_key().to_sec1_bytes())?,
    )?;
    workspace.write(
        "card.key",
        p256::SecretKey::from_slice(&SCP11_DEV_CARD_STATIC_PRIVATE_KEY)?
            .public_key()
            .to_sec1_bytes(),
    )?;
    let mut total = 0;
    for profile in PROFILES {
        let credentials = if let Some(mode) = profile.scp03 {
            workspace.write(
                "credentials.toml",
                format!(
                    "version = 1\nid = 3\nprofile = \"{mode}\"\nenc = \"{}\"\nmac = \"{}\"\n",
                    hex(&SCP03_TEST_ENC_KEY),
                    hex(&SCP03_TEST_MAC_KEY)
                ),
            )?
        } else {
            workspace.write("credentials.toml", format!("profile = \"{}\"\nversion = 0\nid = 1\nhost_private_key_file = \"host.key\"\nhost_certificate_file = \"host.cert\"\ncard_public_key_file = \"card.key\"\n", profile.protocol))?
        };
        let mut config: toml::Value =
            toml::from_str(&std::fs::read_to_string(root.join(profile.config))?)?;
        let root_table = config["root"].as_table_mut().ok_or("missing root config")?;
        root_table.remove("packages");
        let config_path = workspace.write("config.toml", toml::to_string(&config)?)?;
        let cli = Cli {
            binary: root.join("target/debug/apdu_tool"),
            workspace: &workspace,
            profile,
            credentials,
        };
        total +=
            run_with_build_config(ctx, config_path.to_str().ok_or("non-UTF8 config")?, |ctx| {
                let mut target =
                    prepare_apdu_session(ctx, board_spec, LayoutImageFormat::Elf, true)?;
                let rejected = profile.protocol == "scp11b";
                let load_aid = hex(crate_rustlet_getting_started_test_aid());
                let deploy_aid = hex(crate_rustlet_minimal_valid_test_aid());
                let first = target.boot_cli(profile.name, APDU_RESPONSE_TIMEOUT, |link| {
                    cli.run(link, &["select", profile.sd], false, Expected::Success)?;
                    cli.run(
                        link,
                        &[
                            "gp",
                            "install-for-load",
                            "--package-aid",
                            &load_aid,
                            "--security-domain",
                            profile.sd,
                            "--hash",
                            &hex(&load.hash),
                            "--size",
                            &load.fae.len().to_string(),
                        ],
                        false,
                        Expected::Status(0x69, 0x82),
                    )?;
                    let mut client = ApduClient::connect_link(link, APDU_RESPONSE_TIMEOUT)?;
                    verify_package(
                        &mut client,
                        crate_rustlet_getting_started_test_aid(),
                        profile.sd,
                        false,
                    )?;
                    drop(client);
                    let expected = if rejected {
                        Expected::ProfileRejection
                    } else {
                        Expected::Success
                    };
                    let mut checks = 8 + primitive_session(&cli, link, &load, &load_aid)?;

                    cli.run(
                        link,
                        &["gp", "load", &load_aid, load_path.to_str().unwrap()],
                        true,
                        expected,
                    )?;
                    let mut client = ApduClient::connect_link(link, APDU_RESPONSE_TIMEOUT)?;
                    verify_package(
                        &mut client,
                        crate_rustlet_getting_started_test_aid(),
                        profile.sd,
                        !rejected,
                    )?;
                    expect_status(
                        client.exchange(&CommandBuilder::gp_get_status(
                            0x40,
                            false,
                            crate_rustlet_getting_started_test_aid(),
                        ))?,
                        (0x6a, 0x88),
                        "gp load creates no instance",
                    )?;
                    drop(client);
                    if !rejected {
                        cli.run(
                            link,
                            &[
                                "gp",
                                "install-make-selectable",
                                "--package-aid",
                                &load_aid,
                                "--module-aid",
                                &load_aid,
                                "--instance-aid",
                                &load_aid,
                            ],
                            true,
                            Expected::Success,
                        )?;
                        let mut client = ApduClient::connect_link(link, APDU_RESPONSE_TIMEOUT)?;
                        expect_status(
                            client.exchange(&CommandBuilder::select(
                                crate_rustlet_getting_started_test_aid(),
                            ))?,
                            (0x90, 0),
                            "CLI separately installed instance",
                        )?;
                        checks += 2 + run_getting_started_post_select_apdus(
                            &mut client,
                            "CLI separately installed instance",
                        )?;
                    }
                    cli.run(
                        link,
                        &[
                            "gp",
                            "deploy",
                            &deploy_aid,
                            deploy_path.to_str().unwrap(),
                            &deploy_aid,
                        ],
                        true,
                        expected,
                    )?;
                    let mut client = ApduClient::connect_link(link, APDU_RESPONSE_TIMEOUT)?;
                    verify_package(
                        &mut client,
                        crate_rustlet_minimal_valid_test_aid(),
                        profile.sd,
                        !rejected,
                    )?;
                    if !rejected {
                        expect_status(
                            client.exchange(&CommandBuilder::select(
                                crate_rustlet_minimal_valid_test_aid(),
                            ))?,
                            (0x90, 0),
                            "CLI deployed instance select",
                        )?;
                        checks += 1 + run_minimal_valid_post_select_apdus(
                            &mut client,
                            "CLI deployed instance",
                            false,
                        )?;
                    }
                    drop(client);
                    checks += key_lifecycle(&cli, link)?;
                    if !rejected {
                        checks += resume_application(&cli, link, &load_aid)?;
                    }
                    Ok(checks)
                })?;
                let second =
                    target.reboot("CLI loading persistence", APDU_RESPONSE_TIMEOUT, |client| {
                        verify_package(
                            client,
                            crate_rustlet_getting_started_test_aid(),
                            profile.sd,
                            !rejected,
                        )?;
                        verify_package(
                            client,
                            crate_rustlet_minimal_valid_test_aid(),
                            profile.sd,
                            !rejected,
                        )?;
                        let mut checks = 2;
                        if !rejected {
                            expect_status(
                                client.exchange(&CommandBuilder::select(
                                    crate_rustlet_getting_started_test_aid(),
                                ))?,
                                (0x90, 0),
                                "CLI separately installed instance after reboot",
                            )?;
                            checks += 1 + run_getting_started_post_select_apdus(
                                client,
                                "CLI loaded instance after reboot",
                            )?;
                            expect_status(
                                client.exchange(&CommandBuilder::select(
                                    crate_rustlet_minimal_valid_test_aid(),
                                ))?,
                                (0x90, 0),
                                "CLI deployed instance after reboot",
                            )?;
                            checks += 1 + run_minimal_valid_post_select_apdus(
                                client,
                                "CLI instance after reboot",
                                false,
                            )?;
                        }
                        Ok(checks)
                    })?;
                Ok(first + second)
            })?;
    }
    Ok(TestReport::passed(total))
}

fn resume_application(
    cli: &Cli<'_>,
    link: &apdu_tool::LinkSpec,
    aid: &str,
) -> Result<usize, Box<dyn Error>> {
    let path = cli.workspace.0.join("session.json");
    apdu_tool::session::save(
        &path,
        &apdu_tool::session::SessionFile::new(link.clone(), vec![]),
    )?;
    let channel = if cli.profile.scp03.is_some() {
        "scp03"
    } else {
        "scp11"
    };
    cli.run(link, &[channel, "open"], true, Expected::Action)?;
    cli.run(link, &["select", aid], false, Expected::Success)?;
    cli.run(
        link,
        &["raw", "80", "04", "00", "00", "00", "03"],
        false,
        Expected::Data("10 11 12 90 00"),
    )?;
    cli.run(link, &[channel, "close"], false, Expected::Action)?;
    apdu_tool::session::remove(&path)?;
    Ok(4)
}

/// Send each primitive in its own process while retaining one authenticated channel.
fn primitive_session(
    cli: &Cli<'_>,
    link: &apdu_tool::LinkSpec,
    payload: &DynamicLoadPayload,
    aid: &str,
) -> Result<usize, Box<dyn Error>> {
    let path = cli.workspace.0.join("session.json");
    // boot_cli already consumed the ATR; seed its transport record without resetting the SE.
    apdu_tool::session::save(
        &path,
        &apdu_tool::session::SessionFile::new(link.clone(), vec![]),
    )?;
    let channel = if cli.profile.scp03.is_some() {
        "scp03"
    } else {
        "scp11"
    };
    cli.run(link, &[channel, "open"], true, Expected::Action)?;
    cli.run(link, &[channel, "inspect"], false, Expected::Action)?;
    cli.run(link, &["gp", "get-data", "9F70"], false, Expected::Success)?;
    let install = [
        "gp",
        "install-for-load",
        "--package-aid",
        aid,
        "--security-domain",
        cli.profile.sd,
        "--hash",
        &hex(&payload.hash),
        "--size",
        &payload.fae.len().to_string(),
    ];
    if cli.profile.protocol == "scp11b" {
        cli.run(link, &install, false, Expected::ProfileRejection)?;
        if path.exists() {
            return Err("rejected SCP11b session remained reusable".into());
        }
        return Ok(4);
    }
    cli.run(link, &install, false, Expected::Success)?;
    let data = apdu_tool::gp::encode_load_file_data_block(&payload.fae)?;
    let chunks: Vec<_> = data.chunks(192).collect();
    for (number, chunk) in chunks.iter().enumerate() {
        let block = cli.workspace.write("block.bin", chunk)?;
        let number = number.to_string();
        let mut args = vec!["gp", "load-block", "--number", &number];
        if number.parse::<usize>()? + 1 == chunks.len() {
            args.push("--last");
        }
        args.push(block.to_str().unwrap());
        cli.run(link, &args, false, Expected::Success)?;
    }
    // The CLI exposes this GP primitive, but the Oxide SE profile accepts only P1=0C.
    cli.run(
        link,
        &[
            "gp",
            "install-for-install",
            "--package-aid",
            aid,
            "--module-aid",
            aid,
            "--instance-aid",
            aid,
        ],
        false,
        Expected::Status(0x6a, 0x80),
    )?;
    cli.run(
        link,
        &["gp", "delete", "--aid", aid],
        false,
        Expected::Success,
    )?;
    cli.run(link, &[channel, "close"], false, Expected::Action)?;
    apdu_tool::session::remove(&path)?;
    Ok(7 + chunks.len())
}

/// Exercise version selection and failed replacement through separate CLI processes.
fn key_lifecycle(cli: &Cli<'_>, link: &apdu_tool::LinkSpec) -> Result<usize, Box<dyn Error>> {
    let Some(mode) = cli.profile.scp03 else {
        return scp11_key_lifecycle(cli, link);
    };
    let enc = cli
        .workspace
        .write("rotated-enc.key", SCP03_ROTATED_ENC_KEY)?;
    let mac = cli
        .workspace
        .write("rotated-mac.key", SCP03_ROTATED_MAC_KEY)?;
    let original = std::fs::read(&cli.credentials)?;
    cli.run(
        link,
        &[
            "gp",
            "put-key",
            "--version",
            "2",
            "--id",
            "1",
            "--key-file",
            &format!("enc:{}", enc.display()),
            "--key-file",
            &format!("mac:{}", mac.display()),
        ],
        true,
        Expected::Success,
    )?;
    let use_rotated = || -> Result<(), Box<dyn Error>> {
        cli.workspace.write(
            "credentials.toml",
            format!(
                "version = 2\nid = 1\nprofile = \"{mode}\"\nenc = \"{}\"\nmac = \"{}\"\n",
                hex(&SCP03_ROTATED_ENC_KEY),
                hex(&SCP03_ROTATED_MAC_KEY)
            ),
        )?;
        Ok(())
    };
    use_rotated()?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    // Valid first replacement, invalid second entry: neither may be committed.
    let mut malformed =
        CommandBuilder::gp_put_key(2, 1, &[(&SCP03_TEST_ENC_KEY, 1), (&SCP03_TEST_MAC_KEY, 2)]);
    malformed.data[20] = 0xff;
    let path = cli
        .workspace
        .write("malformed-key.apdu", hex(&malformed.display_bytes()))?;
    cli.run(
        link,
        &["raw", "--file", path.to_str().unwrap()],
        true,
        Expected::Status(0x6a, 0x80),
    )?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    // Selecting the original version still works after creating version 2.
    cli.workspace.write("credentials.toml", &original)?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    for (id, usage) in [(1, 1), (2, 2)] {
        cli.run(
            link,
            &[
                "gp",
                "delete",
                "--aid",
                &hex(&scp03_key_object_aid(2, id, usage)),
            ],
            true,
            Expected::Success,
        )?;
    }
    use_rotated()?;
    cli.run(
        link,
        &["gp", "get-data", "9F70"],
        true,
        Expected::SecureFailure,
    )?;
    cli.workspace.write("credentials.toml", &original)?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    Ok(9)
}

fn scp11_key_lifecycle(cli: &Cli<'_>, link: &apdu_tool::LinkSpec) -> Result<usize, Box<dyn Error>> {
    if cli.profile.protocol == "scp11b" {
        return Ok(0);
    }
    let original = std::fs::read(&cli.credentials)?;
    let original_public = std::fs::read(cli.workspace.0.join("card.key"))?;
    let secret = p256::SecretKey::from_slice(&[0x61; 32])?;
    let private = cli.workspace.write("rotated-card.key", secret.to_bytes())?;
    let ca = p256::SecretKey::from_slice(&SCP11C_DEV_CA_PRIVATE_KEY)?
        .public_key()
        .to_sec1_bytes();
    let ca_path = cli.workspace.write("rotated-ca.key", &ca)?;
    cli.run(
        link,
        &[
            "gp",
            "put-key",
            "--version",
            "2",
            "--id",
            "1",
            "--key-file",
            &format!("scp11-sd-ecka:{}", private.display()),
            "--key-file",
            &format!("scp11-ca-kloc:{}", ca_path.display()),
        ],
        true,
        if cli.profile.protocol == "scp11c" {
            Expected::Status(0x69, 0x82)
        } else {
            Expected::Success
        },
    )?;
    let use_rotated = || -> Result<(), Box<dyn Error>> {
        cli.workspace.write("credentials.toml", format!("profile = \"{}\"\nversion = 2\nid = 1\nca_version = 2\nca_id = 2\nhost_private_key_file = \"host.key\"\nhost_certificate_file = \"host.cert\"\ncard_public_key_file = \"card.key\"\n", cli.profile.protocol))?;
        cli.workspace
            .write("card.key", secret.public_key().to_sec1_bytes())?;
        Ok(())
    };
    if cli.profile.protocol == "scp11c" {
        use_rotated()?;
        cli.run(
            link,
            &["gp", "get-data", "9F70"],
            true,
            Expected::SecureFailure,
        )?;
        cli.workspace.write("credentials.toml", original)?;
        cli.workspace.write("card.key", original_public)?;
        cli.run(
            link,
            &[
                "gp",
                "delete",
                "--aid",
                &hex(&scp03_key_object_aid(2, 1, 0x11)),
            ],
            true,
            Expected::Status(0x69, 0x82),
        )?;
        cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
        return Ok(4);
    }
    use_rotated()?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    let mut malformed = CommandBuilder::gp_put_key(
        2,
        1,
        &[(&SCP11_DEV_CARD_STATIC_PRIVATE_KEY, 0x11), (&ca, 0x12)],
    );
    // Reject an invalid EC point in the second entry, after a valid first key.
    malformed.data[38..103].fill(0);
    let path = cli
        .workspace
        .write("malformed-key.apdu", hex(&malformed.display_bytes()))?;
    cli.run(
        link,
        &["raw", "--file", path.to_str().unwrap()],
        true,
        Expected::Status(0x6a, 0x80),
    )?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    cli.workspace.write("credentials.toml", &original)?;
    cli.workspace.write("card.key", &original_public)?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    for (id, usage) in [(1, 0x11), (2, 0x12)] {
        cli.run(
            link,
            &[
                "gp",
                "delete",
                "--aid",
                &hex(&scp03_key_object_aid(2, id, usage)),
            ],
            true,
            Expected::Success,
        )?;
    }
    use_rotated()?;
    cli.run(
        link,
        &["gp", "get-data", "9F70"],
        true,
        Expected::SecureFailure,
    )?;
    cli.workspace.write("credentials.toml", original)?;
    cli.workspace.write("card.key", original_public)?;
    cli.run(link, &["gp", "get-data", "9F70"], true, Expected::Success)?;
    Ok(9)
}

fn verify_package(
    client: &mut ApduClient,
    aid: &[u8],
    sd: &str,
    present: bool,
) -> Result<(), Box<dyn Error>> {
    // A new observer starts outside the CLI's secure session. SELECT closes that
    // session before unprotected registry consultation (required by SCP11).
    let selected = client.exchange(&CommandBuilder::select(&parse_hex_bytes(
        sd,
        "Security Domain AID",
    )?))?;
    if selected.status != (0x90, 0x00) {
        return Err(format!(
            "cannot select registry observer SD: {:02X?}",
            selected.status
        )
        .into());
    }
    let response = client.exchange(&CommandBuilder::gp_get_status(0x20, false, aid))?;
    if !present {
        return expect_status(
            response,
            (0x6a, 0x88),
            "rejected CLI load leaves no package",
        );
    }
    expect_get_status_record(&response, aid, false, "CLI loaded package")?;
    let records = apdu_tool::gp::decode_status(&response.data)?;
    if hex(&records[0].parent_security_domain_aid) != sd {
        return Err("CLI loaded package has the wrong authorizing Security Domain".into());
    }
    Ok(())
}
