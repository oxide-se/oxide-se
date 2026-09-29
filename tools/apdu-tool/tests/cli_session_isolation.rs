//! Exercise the real CLI with a private session and environment per process.
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "apdu-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn command(&self, port: u16) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_apdu_tool"));
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("APDU_") {
                command.env_remove(key);
            }
        }
        command
            .current_dir(&self.0)
            .env("APDU_SESSION_FILE", self.0.join("session.json"))
            .args([
                "--serial",
                &format!("127.0.0.1:{port}"),
                "--connect-timeout",
                "2s",
                "--response-timeout",
                "1s",
                "--retry-interval",
                "10ms",
                "--output",
                "json",
            ]);
        command
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn listener() -> TcpListener {
    TcpListener::bind(("127.0.0.1", 0)).unwrap()
}
fn accept(listener: &TcpListener) -> TcpStream {
    listener.set_nonblocking(true).unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        match listener.accept() {
            Ok((stream, _)) => {
                stream.set_nonblocking(false).unwrap();
                stream
                    .set_read_timeout(Some(Duration::from_secs(2)))
                    .unwrap();
                return stream;
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock && Instant::now() < deadline => {
                thread::sleep(Duration::from_millis(5))
            }
            Err(e) => panic!("CLI did not connect: {e}"),
        }
    }
}
fn success(output: &Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
#[test]
fn raw_sends_before_reading_any_atr() {
    let fixture = Fixture::new();
    let socket = listener();
    let port = socket.local_addr().unwrap().port();
    let server = thread::spawn(move || {
        let mut stream = accept(&socket);
        let mut header = [0; 5];
        stream.read_exact(&mut header).unwrap();
        assert_eq!(header, [0x80, 0x02, 0, 0, 0]);
        stream.write_all(&[0x90, 0]).unwrap();
    });
    let output = fixture
        .command(port)
        .args(["raw", "80", "02", "00", "00", "00", "00"])
        .output()
        .unwrap();
    server.join().unwrap();
    success(&output);
    assert!(!fixture.0.join("session.json").exists());
}
#[test]
fn atr_retries_delayed_listener_and_persists_only_its_own_session() {
    let fixture = Fixture::new();
    let reservation = listener();
    let port = reservation.local_addr().unwrap().port();
    drop(reservation);
    let server = thread::spawn(move || {
        thread::sleep(Duration::from_millis(200));
        let socket = TcpListener::bind(("127.0.0.1", port)).unwrap();
        let mut stream = accept(&socket);
        stream.write_all(&[0x3b, 0]).unwrap();
        let mut byte = [0];
        assert_eq!(stream.read(&mut byte).unwrap(), 0, "ATR must not transmit");
    });
    let output = fixture
        .command(port)
        .args(["--atr-timeout", "1s", "atr"])
        .output()
        .unwrap();
    server.join().unwrap();
    success(&output);
    let state = apdu_tool::session::load(&fixture.0.join("session.json")).unwrap();
    assert_eq!(state.atr, [0x3b, 0]);
    assert_eq!(
        state.link,
        apdu_tool::LinkSpec::Tcp {
            host: "127.0.0.1".into(),
            port
        }
    );
}
#[test]
fn atr_reports_open_but_silent_secure_element() {
    let fixture = Fixture::new();
    let socket = listener();
    let port = socket.local_addr().unwrap().port();
    let server = thread::spawn(move || {
        let mut stream = accept(&socket);
        let mut byte = [0];
        assert_eq!(stream.read(&mut byte).unwrap(), 0);
    });
    let output = fixture
        .command(port)
        .args(["--atr-timeout", "100ms", "atr"])
        .output()
        .unwrap();
    server.join().unwrap();
    assert!(!output.status.success());
    assert_eq!(output.status.code(), Some(11));
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("did not send an ATR"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(!fixture.0.join("session.json").exists());
}

fn test_fae(size: usize) -> Vec<u8> {
    let mut bytes = vec![0x55; size - 28];
    for word in [
        0x0001_0001u32,
        0xA990_1000,
        0,
        0,
        0xAC1D_A992,
        0x0102_0000,
        0xFAEC_0D10,
    ] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    let mut crc = !0u32;
    for byte in &bytes {
        crc ^= u32::from(*byte);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xedb8_8320 & 0u32.wrapping_sub(crc & 1));
        }
    }
    let at = bytes.len() - 20;
    bytes[at..at + 4].copy_from_slice(&(!crc).to_le_bytes());
    bytes
}

#[test]
fn invalid_load_files_are_rejected_before_connecting() {
    let fixture = Fixture::new();
    let socket = listener();
    socket.set_nonblocking(true).unwrap();
    let port = socket.local_addr().unwrap().port();
    let mut incompatible = test_fae(256);
    incompatible[244..248].copy_from_slice(&0x12345678u32.to_le_bytes());
    for bytes in [vec![], vec![0; 27], incompatible] {
        let path = fixture.0.join("invalid.fae");
        std::fs::write(&path, bytes).unwrap();
        for operation in ["load", "deploy"] {
            let mut command = fixture.command(port);
            command.args(["gp", operation, "A000000001"]).arg(&path);
            if operation == "deploy" {
                command.arg("A000000002");
            }
            let output = command.output().unwrap();
            assert!(!output.status.success());
            assert_eq!(
                socket.accept().unwrap_err().kind(),
                std::io::ErrorKind::WouldBlock
            );
        }
    }
}

fn answer_discovery(stream: &mut TcpStream, mut header: [u8; 5]) {
    assert_eq!(header[1], 0xf2);
    stream.write_all(&[0xf2]).unwrap();
    let mut query = vec![0; header[4] as usize];
    stream.read_exact(&mut query).unwrap();
    let record = [
        0xE3, 0x10, 0x4F, 5, 0xA0, 0, 0, 0, 1, 0x9F, 0x70, 1, 7, 0xC5, 3, 0xA0, 0, 0,
    ];
    stream.write_all(&[0x61, record.len() as u8]).unwrap();
    stream.read_exact(&mut header).unwrap();
    assert_eq!(header[1], 0xc0);
    stream.write_all(&[0xc0]).unwrap();
    stream.write_all(&record).unwrap();
    stream.write_all(&[0x90, 0]).unwrap();
}

#[test]
fn interrupted_deploy_stops_without_installing() {
    let fixture = Fixture::new();
    let socket = listener();
    let port = socket.local_addr().unwrap().port();
    let path = fixture.0.join("load.fae");
    std::fs::write(&path, test_fae(512)).unwrap();
    let server = thread::spawn(move || {
        let mut stream = accept(&socket);
        let mut header = [0; 5];
        stream.read_exact(&mut header).unwrap();
        answer_discovery(&mut stream, header);
        stream.read_exact(&mut header).unwrap();
        assert_eq!(header[1..3], [0xe6, 0x02]);
        stream.write_all(&[0xe6]).unwrap();
        let mut payload = vec![0; header[4] as usize];
        stream.read_exact(&mut payload).unwrap();
        stream.write_all(&[0x90, 0]).unwrap();
        stream.read_exact(&mut header).unwrap();
        assert_eq!(header[1], 0xe8);
        stream.write_all(&[0xe8]).unwrap();
        payload.resize(header[4] as usize, 0);
        stream.read_exact(&mut payload).unwrap();
        // The block may have reached the SE, but no response reaches the host.
        drop(stream);
        socket.set_nonblocking(true).unwrap();
        thread::sleep(Duration::from_millis(100));
        assert_eq!(
            socket.accept().unwrap_err().kind(),
            std::io::ErrorKind::WouldBlock
        );
    });
    let output = fixture
        .command(port)
        .args(["gp", "deploy", "A000000001"])
        .arg(&path)
        .arg("A000000002")
        .output()
        .unwrap();
    server.join().unwrap();
    assert!(!output.status.success());
}

#[test]
fn scp11_transport_and_verification_failures_remove_saved_state() {
    use apdu_tool::secure_channel::{SecureChannelProtocol, SecurityLevel};
    use apdu_tool::session::{self, PersistedSecureChannel, SessionFile};
    for broken_mac in [false, true] {
        let fixture = Fixture::new();
        let socket = listener();
        let port = socket.local_addr().unwrap().port();
        let path = fixture.0.join("session.json");
        let mut state = SessionFile::new(
            apdu_tool::LinkSpec::Tcp {
                host: "127.0.0.1".into(),
                port,
            },
            vec![],
        );
        let snapshot = serde_json::from_value(serde_json::json!({
            "profile":"scp11a", "level":"c-mac-c-enc-r-mac-r-enc",
            "enc":([1;16]), "mac":([2;16]), "rmac":([3;16]),
            "command_chain":([4;16]), "response_chain":([5;16]),
            "command_counter":7, "response_counter":9
        }))
        .unwrap();
        state.secure_channel = Some(PersistedSecureChannel {
            protocol: SecureChannelProtocol::Scp11a,
            security_domain: None,
            security_level: SecurityLevel::CMacCEncRMacREnc,
            scp03: None,
            scp11: Some(snapshot),
        });
        session::save(&path, &state).unwrap();
        let server = thread::spawn(move || {
            let mut stream = accept(&socket);
            let mut header = [0; 5];
            stream.read_exact(&mut header).unwrap();
            assert_eq!(&header[..2], &[0x84, 0xca]);
            stream.write_all(&[0xca]).unwrap();
            let mut protected = vec![0; header[4] as usize];
            stream.read_exact(&mut protected).unwrap();
            if broken_mac {
                stream.write_all(&[0x90, 0]).unwrap();
            }
            // Either truncated transport or a response lacking its required R-MAC.
        });
        let output = fixture
            .command(port)
            .args(["raw", "80", "CA", "9F", "70", "00", "04"])
            .output()
            .unwrap();
        server.join().unwrap();
        assert!(!output.status.success());
        assert!(!path.exists());
    }
}

#[test]
fn load_full_last_block_and_256_block_limit_over_transport() {
    for blocks in [2usize, 256, 257] {
        let fixture = Fixture::new();
        let socket = listener();
        let port = socket.local_addr().unwrap().port();
        let path = fixture.0.join("boundary.fae");
        let fae = test_fae(blocks * 255 - 4);
        let expected = apdu_tool::gp::encode_load_file_data_block(&fae).unwrap();
        assert_eq!(expected.len(), blocks * 255);
        std::fs::write(&path, fae).unwrap();
        let server = thread::spawn(move || {
            let mut stream = accept(&socket);
            stream.set_nodelay(true).unwrap();
            if blocks > 256 {
                // Size is checked before the first management APDU.
                assert_eq!(stream.read(&mut [0]).unwrap(), 0);
                return;
            }
            let mut header = [0; 5];
            stream.read_exact(&mut header).unwrap();
            answer_discovery(&mut stream, header);
            stream.read_exact(&mut header).unwrap();
            assert_eq!(header[1..3], [0xe6, 0x02]);
            stream.write_all(&[0xe6]).unwrap();
            stream.read_exact(&mut vec![0; header[4] as usize]).unwrap();
            stream.write_all(&[0x90, 0]).unwrap();
            let mut received = Vec::new();
            for number in 0..blocks {
                stream.read_exact(&mut header).unwrap();
                assert_eq!(
                    header,
                    [
                        0x80,
                        0xe8,
                        if number + 1 == blocks { 0x80 } else { 0 },
                        number as u8,
                        255
                    ]
                );
                stream.write_all(&[0xe8]).unwrap();
                let mut block = [0; 255];
                stream.read_exact(&mut block).unwrap();
                received.extend_from_slice(&block);
                stream.write_all(&[0x90, 0]).unwrap();
            }
            assert_eq!(received, expected);
        });
        let output = fixture
            .command(port)
            .args(["gp", "load", "A000000001"])
            .arg(&path)
            .output()
            .unwrap();
        server.join().unwrap();
        assert_eq!(
            output.status.success(),
            blocks <= 256,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
