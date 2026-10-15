//! Hardware primitive profiling, using the normal deployment/session machinery.
use super::*;
use serde::{Deserialize, Serialize};
const COUNT: usize = 50;
const CONFIG: &str = "configs/config_svc_profile.toml";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
struct Case {
    svc: u8,
    variant: u8,
    input_len: usize,
    output_len: usize,
}
impl Case {
    fn group(&self) -> &'static str {
        match self.svc {
            9 | 11 => "aes",
            10 => "random",
            13 | 14 => "p256",
            15 | 16 => "hash",
            0xf0 => "flash_program",
            0xf1 => "flash_erase",
            _ => unreachable!(),
        }
    }
    fn work(&self) -> u32 {
        let n = self.input_len;
        (match self.svc {
            9 if matches!(self.variant & 7, 4 | 5) => n + 16,
            9 | 10 | 11 => n,
            15 => n + 32 + 96 * self.output_len.div_ceil(32),
            16 => (n + 36) * self.output_len.div_ceil(32),
            _ => 0,
        }) as u32
    }
    fn command(&self, count: usize) -> OwnedT0Command {
        let mut data = (self.input_len as u16).to_be_bytes().to_vec();
        data.extend_from_slice(&(self.output_len as u16).to_be_bytes());
        OwnedT0Command {
            cla: 0x80,
            ins: 0x0b,
            p1: (self.variant << 4)
                | match self.svc {
                    9 => 1,
                    10 => 2,
                    11 => 3,
                    13 => 4,
                    14 => 5,
                    15 => 6,
                    16 => 7,
                    240 => 8,
                    241 => 9,
                    _ => unreachable!(),
                },
            p2: count as u8,
            lc: 4,
            le: (24 + 4 * count) as u8,
            data,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Row {
    case: Case,
    core_hz: u32,
    timer_hz: u32,
    min_us: u32,
    max_us: u32,
    mean_us: u32,
    samples_ticks: Vec<u32>,
}
#[derive(Clone, Serialize, Deserialize)]
struct Report {
    schema: u32,
    board: String,
    backend: String,
    revision: String,
    dirty: bool,
    firmware_sha256: String,
    unix_seconds: u64,
    samples_per_case: usize,
    engineering_margin_us: u32,
    rows: Vec<Row>,
    /// Schema 2: top-level metadata describes the last run; each group below
    /// identifies the actual source of its rows, including retained old groups.
    #[serde(default)]
    group_sources: std::collections::BTreeMap<String, Provenance>,
}
const GROUPS: [&str; 6] = [
    "aes",
    "hash",
    "random",
    "p256",
    "flash_program",
    "flash_erase",
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Provenance {
    revision: String,
    dirty: bool,
    firmware_sha256: String,
    unix_seconds: u64,
    samples_per_case: usize,
    core_hz: u32,
    timer_hz: u32,
    // Absent for schema-1 captures; never invent information for old samples.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    build_context_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    rustc_version: Option<String>,
}

fn group_for_svc(svc: u8) -> Result<&'static str, Box<dyn Error>> {
    Ok(match svc {
        9 | 11 => "aes", 10 => "random", 13 | 14 => "p256",
        15 | 16 => "hash", 240 => "flash_program", 241 => "flash_erase",
        _ => return Err(format!("SVC {svc} is not profiled; supported: 9 10 11 13 14 15 16, and internal flash IDs 240 241").into()),
    })
}

/// Strip selection options before the common board/transport parser sees them.
/// Group expansion intentionally does NOT infer transitive source dependencies:
/// annotations list all affected SVCs (e.g. RNG changes require --svc 10 13).
fn parse_selection(
    args: Vec<String>,
) -> Result<(Vec<String>, Option<Vec<String>>), Box<dyn Error>> {
    let mut args = args.into_iter().peekable();
    let mut rest = Vec::new();
    let mut selection = None;
    let mut explicit_all = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--all" => {
                if explicit_all || selection.is_some() {
                    return Err("use either --all or one --svc list".into());
                }
                explicit_all = true;
            }
            "--svc" => {
                if explicit_all || selection.is_some() {
                    return Err("use either --all or one --svc list".into());
                }
                let mut groups = Vec::new();
                while args.peek().is_some_and(|s| s.parse::<u8>().is_ok()) {
                    let svc = args.next().unwrap().parse::<u8>()?;
                    let group = group_for_svc(svc)?.to_owned();
                    if !groups.contains(&group) {
                        groups.push(group);
                    }
                }
                if groups.is_empty() {
                    return Err("--svc requires decimal IDs, e.g. --svc 9 10 13".into());
                }
                groups.sort();
                selection = Some(groups);
            }
            _ => rest.push(arg),
        }
    }
    Ok((rest, selection))
}

fn selected_cases(flash: bool, groups: Option<&[String]>) -> Result<Vec<Case>, Box<dyn Error>> {
    let all = cases(flash);
    if let Some(groups) = groups {
        if groups.iter().any(|g| !all.iter().any(|c| c.group() == g)) {
            return Err(
                "selected group unavailable on this board (flash profiling requires Pico geometry)"
                    .into(),
            );
        }
    }
    Ok(all
        .into_iter()
        .filter(|c| groups.is_none_or(|gs| gs.iter().any(|g| g == c.group())))
        .collect())
}

fn attach_sources(report: &mut Report, context: Option<String>, rustc: Option<String>) {
    for row in &report.rows {
        report
            .group_sources
            .entry(row.case.group().into())
            .or_insert_with(|| Provenance {
                revision: report.revision.clone(),
                dirty: report.dirty,
                firmware_sha256: report.firmware_sha256.clone(),
                unix_seconds: report.unix_seconds,
                samples_per_case: report.samples_per_case,
                core_hz: row.core_hz,
                timer_hz: row.timer_hz,
                build_context_sha256: context.clone(),
                rustc_version: rustc.clone(),
            });
    }
}

/// Validate exact group membership, unique cases, clocks and all raw statistics.
/// A completed selected campaign is different from an interrupted checkpoint.
fn validate_report(report: &Report, complete: bool) -> Result<(), Box<dyn Error>> {
    if !matches!(report.schema, 1 | 2)
        || report.rows.is_empty()
        || report.engineering_margin_us != 20_000
    {
        return Err("unsupported or empty profiling report".into());
    }
    let observed: std::collections::BTreeSet<_> =
        report.rows.iter().map(|r| r.case.clone()).collect();
    let expected: std::collections::BTreeSet<_> = cases(matches!(
        report.board.as_str(),
        "raspi-pico1" | "raspi-pico2"
    ))
    .into_iter()
    .filter(|c| complete || report.rows.iter().any(|r| r.case.group() == c.group()))
    .collect();
    if observed.len() != report.rows.len() || observed != expected {
        return Err(
            "duplicate, missing or unexpected profile cases; entire budget groups are required"
                .into(),
        );
    }
    let row_groups: std::collections::BTreeSet<_> =
        report.rows.iter().map(|r| r.case.group()).collect();
    if row_groups != report.group_sources.keys().map(String::as_str).collect() {
        return Err("missing or extraneous group provenance".into());
    }
    for row in &report.rows {
        let source = &report.group_sources[row.case.group()];
        if row.core_hz != source.core_hz
            || row.timer_hz != source.timer_hz
            || source.firmware_sha256.len() != 64
            || !source
                .firmware_sha256
                .bytes()
                .all(|b| b.is_ascii_hexdigit())
        {
            return Err("inconsistent group provenance/clock".into());
        }
        let count = source.samples_per_case;
        let mut data = vec![2, row.case.svc, row.case.variant, count as u8];
        for word in [
            row.core_hz,
            row.timer_hz,
            row.min_us,
            row.max_us,
            row.mean_us,
        ]
        .into_iter()
        .chain(row.samples_ticks.iter().copied())
        {
            data.extend_from_slice(&word.to_be_bytes());
        }
        decode(
            row.case.clone(),
            T0Response {
                status: (0x90, 0),
                data,
            },
            count,
            count,
        )?;
    }
    Ok(())
}

fn merge_groups(mut base: Report, fresh: Report) -> Result<Report, Box<dyn Error>> {
    if base.schema == 1 {
        attach_sources(&mut base, None, None);
    }
    validate_report(&base, true)?;
    validate_report(&fresh, false)?;
    if base.board != fresh.board || base.backend != fresh.backend || fresh.backend != "hardware" {
        return Err("partial calibration requires the same board and hardware backend".into());
    }
    let clock = fresh.rows[0].core_hz;
    let timer = fresh.rows[0].timer_hz;
    if base
        .rows
        .iter()
        .chain(&fresh.rows)
        .any(|r| r.core_hz != clock || r.timer_hz != timer)
    {
        return Err("clock changed: rerun --all".into());
    }
    let current_context = fresh
        .group_sources
        .values()
        .next()
        .unwrap()
        .build_context_sha256
        .as_ref();
    for old in base.group_sources.values() {
        if let (Some(old), Some(current)) = (old.build_context_sha256.as_ref(), current_context) {
            if old != current {
                return Err("build context changed: rerun --all".into());
            }
        }
    }
    let mut merged = fresh;
    base.rows
        .retain(|r| !merged.group_sources.contains_key(r.case.group()));
    merged.rows.extend(base.rows);
    for (group, source) in base.group_sources {
        merged.group_sources.entry(group).or_insert(source);
    }
    merged.rows.sort_by(|a, b| a.case.cmp(&b.case));
    merged.schema = 2;
    validate_report(&merged, true)?;
    Ok(merged)
}

fn build_context(root: &Path) -> Result<(String, String), Box<dyn Error>> {
    let toolchain = preferred_nightly_toolchain()?;
    let output = Command::new("rustup")
        .args(["run", &toolchain, "rustc", "-Vv"])
        .current_dir(root)
        .output()?;
    if !output.status.success() {
        return Err("cannot identify rustc".into());
    }
    let rustc = String::from_utf8(output.stdout)?;
    let mut hash = Sha256::new();
    hash.update(rustc.as_bytes());
    for path in [
        "Cargo.lock",
        "Cargo.toml",
        "rust-toolchain.toml",
        "kernel/core/Cargo.toml",
        "kernel/firmware/Cargo.toml",
        CONFIG,
    ] {
        hash.update(path.as_bytes());
        hash.update(fs::read(root.join(path))?);
    }
    for key in [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_PROFILE_RELEASE_OPT_LEVEL",
        "CARGO_PROFILE_RELEASE_LTO",
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS",
    ] {
        hash.update(key.as_bytes());
        hash.update(std::env::var(key).unwrap_or_default().as_bytes());
    }
    Ok((hex_bytes_upper(&hash.finalize()), rustc.trim().into()))
}

#[derive(Serialize)]
struct PartialReport<'a> {
    complete: bool,
    board: &'a str,
    firmware_sha256: &'a str,
    rows: &'a [Row],
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
struct Envelope {
    base_us: u32,
    per_byte_us: u32,
}
impl Envelope {
    fn at(self, bytes: u32) -> u32 {
        self.base_us
            .saturating_add(self.per_byte_us.saturating_mul(bytes))
    }
}

fn cases(flash: bool) -> Vec<Case> {
    let mut cases = Vec::new();
    for n in [16, 64, 256, 1024] {
        for v in [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13] {
            cases.push(Case {
                svc: 9,
                variant: v,
                input_len: n,
                output_len: 0,
            });
        }
        for v in [0, 8] {
            cases.push(Case {
                svc: 11,
                variant: v,
                input_len: n,
                output_len: 0,
            });
        }
        cases.push(Case {
            svc: 10,
            variant: 0,
            input_len: n,
            output_len: 0,
        });
        for svc in [15, 16] {
            for out in [32, 128, 1024] {
                cases.push(Case {
                    svc,
                    variant: 0,
                    input_len: n,
                    output_len: out,
                });
            }
        }
    }
    for (svc, variant) in [(13, 0), (13, 1), (14, 0)] {
        cases.push(Case {
            svc,
            variant,
            input_len: 0,
            output_len: 0,
        });
    }
    if flash {
        for svc in [0xf0, 0xf1] {
            cases.push(Case {
                svc,
                variant: 0,
                input_len: 0,
                output_len: 0,
            });
        }
    }
    cases
}

fn decode(
    case: Case,
    response: T0Response,
    nulls: usize,
    count: usize,
) -> Result<Row, Box<dyn Error>> {
    if response.status != (0x90, 0)
        || !(1..=COUNT).contains(&count)
        || response.data.len() != 24 + 4 * count
        || response.data[..4] != [2, case.svc, case.variant, count as u8]
        || nulls != count
    {
        return Err(format!("profile {:?}: status={:02x?}, bytes={}, NULLs={nulls}; expected {count} manual NULLs and complete statistics", case, response.status, response.data.len()).into());
    }
    let words: Vec<u32> = response.data[4..]
        .chunks_exact(4)
        .map(|b| u32::from_be_bytes(b.try_into().unwrap()))
        .collect();
    let row = Row {
        case,
        core_hz: words[0],
        timer_hz: words[1],
        min_us: words[2],
        max_us: words[3],
        mean_us: words[4],
        samples_ticks: words[5..].to_vec(),
    };
    if row.timer_hz == 0
        || row.core_hz == 0
        || row
            .samples_ticks
            .iter()
            .any(|&x| x == 0 || x > i32::MAX as u32)
    {
        return Err("invalid profile clock/sample".into());
    }
    let us = |ticks: u64| (ticks * 1_000_000).div_ceil(row.timer_hz as u64) as u32;
    if row.min_us != us(*row.samples_ticks.iter().min().unwrap() as u64)
        || row.max_us != us(*row.samples_ticks.iter().max().unwrap() as u64)
        || row.mean_us
            != (row.samples_ticks.iter().map(|&v| v as u64).sum::<u64>() * 1_000_000)
                .div_ceil(row.timer_hz as u64 * count as u64) as u32
    {
        return Err("profile statistics do not match raw samples".into());
    }
    Ok(row)
}

// An upper envelope of observed maxima, not a regression of their averages.
// The 20 ms engineering margin is applied independently by time_manager.
fn envelope(rows: &[Row], group: &str) -> Result<Envelope, Box<dyn Error>> {
    let rows: Vec<_> = rows.iter().filter(|r| r.case.group() == group).collect();
    if rows.is_empty() {
        return Err("missing profile group".into());
    }
    // Absorb fixed/cold-start overhead from the shortest case of every
    // algorithm variant; do not turn that overhead into a per-byte slope.
    let base_us = rows
        .iter()
        .filter(|r| {
            !rows.iter().any(|other| {
                other.case.svc == r.case.svc
                    && other.case.variant == r.case.variant
                    && other.case.work() < r.case.work()
            })
        })
        .map(|r| r.max_us)
        .max()
        .unwrap();
    let per_byte_us = rows
        .iter()
        .map(|r| {
            if r.case.work() == 0 {
                0
            } else {
                r.max_us.saturating_sub(base_us).div_ceil(r.case.work())
            }
        })
        .max()
        .unwrap();
    let base_us = if rows.iter().all(|r| r.case.work() == 0) {
        rows.iter().map(|r| r.max_us).max().unwrap()
    } else {
        base_us
    };
    let budget = Envelope {
        base_us,
        per_byte_us,
    };
    if rows.iter().any(|r| budget.at(r.case.work()) < r.max_us) {
        return Err("budget underestimates a measured maximum".into());
    }
    Ok(budget)
}

pub(super) fn help() {
    println!("Usage: cargo run -- extract-svc-profile <board> --on openocd --serial <device:baud> --allow-destructive [--probe-serial ID] [--output path.toml] [--update-budgets] [--samples 1..50] [--all | --svc ID ID ...]\n--all is the default; --svc expands to complete shared budget groups. Without --update-budgets, writes a .measurement.toml capture. Partial updates preserve unselected groups and their provenance.\nMeasures 50 samples by default for every primitive/variant/size. QEMU may validate the protocol, but cannot update hardware budgets. Budget generation supports Pico1 at 12 MHz and Pico2 at 150 MHz.");
}
pub(super) fn run_cli(args: Vec<String>) -> Result<(), Box<dyn Error>> {
    if args.iter().any(|s| s == "--help" || s == "-h") {
        help();
        return Ok(());
    }
    let (args, groups) = parse_selection(args)?;
    let mut forwarded = vec!["kernel_crypto".to_owned()];
    let mut output = None;
    let mut update = false;
    let mut count = None;
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--samples" => {
                if count.is_some() {
                    return Err("duplicate --samples".into());
                }
                let value: usize = args.next().ok_or("--samples requires a count")?.parse()?;
                if !(1..=COUNT).contains(&value) {
                    return Err("--samples must be between 1 and 50".into());
                }
                count = Some(value);
            }
            "--output" => {
                if output.is_some() {
                    return Err("duplicate --output".into());
                }
                output = Some(PathBuf::from(
                    args.next().ok_or("--output requires a path")?,
                ));
            }
            "--update-budgets" => {
                if update {
                    return Err("duplicate --update-budgets".into());
                }
                update = true;
            }
            "--on" | "--serial" | "--probe-serial" => {
                let value = args.next().ok_or("missing target option value")?;
                forwarded.extend([arg, value]);
            }
            "--allow-destructive" => forwarded.push(arg),
            s if !s.starts_with('-') => forwarded.push(arg),
            _ => return Err(format!("unsupported profiling option: {arg}").into()),
        }
    }
    let count = count.unwrap_or(COUNT);
    if !forwarded.iter().any(|s| s == "--on") {
        forwarded.extend(["--on".into(), "openocd".into()]);
    }
    let Mode::Test(invocation) = testing::parse(forwarded)? else {
        return Err("invalid profiling invocation".into());
    };
    let Scenario::KernelCrypto { board, .. } = invocation.scenario else {
        unreachable!()
    };
    if update
        && (profile_target(&board).is_none()
            || !matches!(invocation.target, testing::TargetOptions::OpenOcd(_)))
    {
        return Err("--update-budgets requires Pico1/Pico2 hardware, never QEMU".into());
    }
    let root = repo_root()?;
    let canonical = root.join(format!("profiles/svc/{board}.toml"));
    let output = output.unwrap_or_else(|| {
        if update {
            canonical.clone()
        } else {
            root.join(format!("profiles/svc/{board}.measurement.toml"))
        }
    });
    let output = if output.is_absolute() {
        output
    } else {
        root.join(output)
    };
    let output = fs::canonicalize(&output).unwrap_or(output);
    if !update && output == canonical {
        return Err("canonical calibration is only written with --update-budgets; choose a capture --output".into());
    }
    let selected = selected_cases(
        matches!(board.as_str(), "raspi-pico1" | "raspi-pico2"),
        groups.as_deref(),
    )?;
    let (context, rustc) = build_context(&root)?;
    let base = if update && groups.is_some() {
        let mut base: Report = toml::from_str(&fs::read_to_string(&canonical).map_err(|e| {
            format!(
                "partial update needs a complete baseline at {}: {e}; run --all first",
                canonical.display()
            )
        })?)?;
        if base.schema == 1 {
            attach_sources(&mut base, None, None);
        }
        validate_report(&base, true)?;
        if base
            .group_sources
            .values()
            .any(|p| p.build_context_sha256.is_none())
        {
            eprintln!("Legacy baseline: retained groups have unknown build context; review full-recalibration triggers before merging.");
        }
        if base.board != board
            || base.backend != "hardware"
            || base
                .rows
                .iter()
                .any(|r| Some(r.core_hz) != profile_target(&board).map(|p| p.0))
            || base.group_sources.values().any(|p| {
                p.build_context_sha256
                    .as_ref()
                    .is_some_and(|s| s != &context)
            })
        {
            return Err("baseline board/backend/build context incompatible: rerun --all".into());
        }
        Some(base)
    } else {
        None
    };
    eprintln!(
        "SVC-PROFILE selection: {} cases; groups {:?}",
        selected.len(),
        selected
            .iter()
            .map(Case::group)
            .collect::<std::collections::BTreeSet<_>>()
    );
    if let Some(parent) = output.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    let partial_path = output.with_extension("partial.toml");
    let ctx = TestContext {
        build: BuildContext::default().with_config(CONFIG),
        target: invocation.target,
        ..TestContext::default()
    };
    let revision = git_output(&root, &["rev-parse", "HEAD"])?;
    let dirty = !git_output(&root, &["status", "--porcelain"])?
        .trim()
        .is_empty();
    let mut target = testing::target::prepare_apdu_session(
        &ctx,
        board_spec(&board)?,
        LayoutImageFormat::Elf,
        true,
    )?;
    let firmware_sha256 = hex_bytes_upper(&Sha256::digest(fs::read(target.image_path())?));
    let measured_cases = selected.len();
    let rows = target.boot("svc-profile", Duration::from_secs(120), |client| {
        let mut rows = Vec::new();
        for case in selected {
            let mut nulls = 0;
            let response = client.protocol.exchange_with_progress(
                case.command(count).as_borrowed(),
                || {
                    nulls += 1;
                    if matches!(case.svc, 13 | 14) && (nulls == 1 || nulls % 10 == 0) {
                        eprintln!(
                            "SVC-PROFILE svc={} variant={} starting sample {nulls}/{count}",
                            case.svc, case.variant
                        );
                    }
                },
            )?;
            let row = decode(case, response, nulls, count)?;
            eprintln!(
                "SVC-PROFILE svc={} variant={} n={} out={} min={} max={} mean={} us",
                row.case.svc,
                row.case.variant,
                row.case.input_len,
                row.case.output_len,
                row.min_us,
                row.max_us,
                row.mean_us
            );
            rows.push(row);
            // Preserve expensive completed samples if a later case fails.
            // Partial reports are never accepted for budget generation.
            let partial = PartialReport {
                complete: false,
                board: &board,
                firmware_sha256: &firmware_sha256,
                rows: &rows,
            };
            fs::write(&partial_path, toml::to_string_pretty(&partial)?)?;
        }
        Ok(rows)
    })?;
    let mut report = Report {
        schema: 2,
        board,
        backend: ctx.execution_env().into(),
        revision: revision.trim().into(),
        dirty,
        firmware_sha256,
        unix_seconds: SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)?
            .as_secs(),
        samples_per_case: count,
        engineering_margin_us: 20_000,
        group_sources: Default::default(),
        rows,
    };
    attach_sources(&mut report, Some(context), Some(rustc));
    validate_report(&report, groups.is_none())?;
    if let Some(base) = base {
        report = merge_groups(base, report)?;
    }
    // Validate and render before changing any published report or budget.
    let generated = if update {
        Some(render_budgets(&report)?)
    } else {
        None
    };
    let encoded = toml::to_string_pretty(&report)?;
    if let Some((file, code)) = generated {
        publish_calibration(&root, &canonical, file, &encoded, &code)?;
    }
    if !update || output != canonical {
        atomic_write(&output, encoded.as_bytes())?;
    }
    fs::remove_file(&partial_path)?;
    println!(
        "Profile saved: {} ({measured_cases} cases measured, {count} samples each; {} cases stored)",
        output.display(),
        report.rows.len()
    );
    Ok(())
}
fn profile_target(board: &str) -> Option<(u32, &'static str)> {
    match board {
        "raspi-pico1" => Some((12_000_000, "pico1.rs")),
        "raspi-pico2" => Some((150_000_000, "pico2.rs")),
        _ => None,
    }
}
fn render_budgets(report: &Report) -> Result<(&'static str, String), Box<dyn Error>> {
    validate_report(report, true)?;
    let (core_hz, file) = profile_target(&report.board).ok_or("unsupported budget target")?;
    if report.backend != "hardware" || report.rows.iter().any(|r| r.core_hz != core_hz) {
        return Err("incompatible board clock/backend".into());
    }
    let mut generated = format!("// Generated by extract-svc-profile; provenance per group below and in profiles/svc/{}.toml.\n// Maxima envelope; time_manager adds the separate 20 ms engineering margin.\nuse super::MeasuredProfile;\npub(super) const PROFILE: Option<MeasuredProfile> = Some(MeasuredProfile {{\n    core_hz: {core_hz},\n", report.board);
    for group in GROUPS {
        let e = envelope(&report.rows, group)?;
        let p = &report.group_sources[group];
        eprintln!(
            "BUDGET {group}: {} + {} * bytes us",
            e.base_us, e.per_byte_us
        );
        let works: Vec<_> = report
            .rows
            .iter()
            .filter(|r| r.case.group() == group)
            .map(|r| r.case.work())
            .collect();
        writeln!(
            generated,
            "    // {group}: firmware={} revision={} dirty={} unix={} samples={}",
            p.firmware_sha256, p.revision, p.dirty, p.unix_seconds, p.samples_per_case
        )?;
        writeln!(
            generated,
            "    {group}: ({}, {}, {}, {}),",
            e.base_us,
            e.per_byte_us,
            works.iter().min().unwrap(),
            works.iter().max().unwrap()
        )?;
    }
    generated.push_str("});\n");
    Ok((file, generated))
}

fn atomic_write(path: &Path, contents: &[u8]) -> Result<(), Box<dyn Error>> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let tmp = path.with_extension(format!("tmp-{}", std::process::id()));
    fs::write(&tmp, contents)?;
    fs::rename(tmp, path)?;
    Ok(())
}

fn publish_calibration(
    root: &Path,
    canonical: &Path,
    file: &str,
    report: &str,
    code: &str,
) -> Result<(), Box<dyn Error>> {
    let budget = root
        .join("kernel/core/src/core/operation_timing")
        .join(file);
    let report_tmp = canonical.with_extension(format!("staged-{}", std::process::id()));
    let budget_tmp = budget.with_extension(format!("staged-{}", std::process::id()));
    let result = (|| -> Result<(), Box<dyn Error>> {
        // Stage both completely before replacing either published artifact.
        fs::create_dir_all(canonical.parent().ok_or("report has no parent")?)?;
        fs::create_dir_all(budget.parent().unwrap())?;
        fs::write(&report_tmp, report)?;
        fs::write(&budget_tmp, code)?;
        let previous_budget = match fs::read(&budget) {
            Ok(bytes) => Some(bytes),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
            Err(e) => return Err(e.into()),
        };
        fs::rename(&budget_tmp, &budget)?;
        if let Err(error) = fs::rename(&report_tmp, canonical) {
            if let Some(bytes) = previous_budget {
                atomic_write(&budget, &bytes)?;
            } else {
                fs::remove_file(&budget)?;
            }
            return Err(error.into());
        }
        Ok(())
    })();
    let _ = fs::remove_file(report_tmp);
    let _ = fs::remove_file(budget_tmp);
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    fn baseline() -> Report {
        toml::from_str(include_str!("../../profiles/svc/raspi-pico1.toml")).unwrap()
    }
    fn fresh_random() -> Report {
        let mut r = baseline();
        r.schema = 2;
        r.rows.retain(|row| row.case.group() == "random");
        r.group_sources.clear();
        r.revision = "new-source-revision".into();
        r.firmware_sha256 = "ab".repeat(32);
        r.unix_seconds += 100;
        r.samples_per_case = 2;
        for row in &mut r.rows {
            row.samples_ticks = vec![1200, 1400];
            row.min_us = 1200;
            row.max_us = 1400;
            row.mean_us = 1300;
        }
        attach_sources(
            &mut r,
            Some("new-build-context".into()),
            Some("rustc test".into()),
        );
        r
    }
    #[test]
    fn svc_selection_expands_complete_groups_and_rejects_bad_lists() {
        assert!(parse_selection(vec![]).unwrap().1.is_none());
        assert!(parse_selection(vec!["--all".into()]).unwrap().1.is_none());
        for (ids, expected) in [
            (vec![9, 11, 9], 56),
            (vec![10, 13], 7),
            (vec![15], 24),
            (vec![240], 1),
        ] {
            let args = std::iter::once("--svc".to_owned())
                .chain(ids.iter().map(ToString::to_string))
                .collect();
            let (_, groups) = parse_selection(args).unwrap();
            assert_eq!(
                selected_cases(true, groups.as_deref()).unwrap().len(),
                expected
            );
        }
        for args in [
            vec!["--svc"],
            vec!["--svc", "12"],
            vec!["--svc", "256"],
            vec!["--all", "--svc", "9"],
            vec!["--svc", "9", "--svc", "10"],
            vec!["--all", "--all"],
        ] {
            assert!(parse_selection(args.into_iter().map(str::to_owned).collect()).is_err());
        }
        assert!(selected_cases(false, Some(&["flash_program".into()])).is_err());
    }
    #[test]
    fn partial_update_preserves_unselected_samples_budgets_and_provenance() {
        let mut old = baseline();
        attach_sources(&mut old, None, None);
        let before = render_budgets(&old).unwrap().1;
        let fresh = fresh_random();
        let merged = merge_groups(old.clone(), fresh.clone()).unwrap();
        assert_eq!(merged.schema, 2);
        assert_eq!(merged.rows.len(), 89);
        assert_eq!(
            merged.group_sources["random"],
            fresh.group_sources["random"]
        );
        let after = render_budgets(&merged).unwrap().1;
        for group in GROUPS.into_iter().filter(|g| *g != "random") {
            assert_eq!(merged.group_sources[group], old.group_sources[group]);
            let old_rows: Vec<_> = old
                .rows
                .iter()
                .filter(|r| r.case.group() == group)
                .collect();
            let new_rows: Vec<_> = merged
                .rows
                .iter()
                .filter(|r| r.case.group() == group)
                .collect();
            for row in old_rows {
                assert!(new_rows.contains(&row));
            }
            let prefix = format!("    {group}:");
            assert_eq!(
                before.lines().find(|l| l.starts_with(&prefix)),
                after.lines().find(|l| l.starts_with(&prefix))
            );
        }
        let encoded = toml::to_string_pretty(&merged).unwrap();
        let decoded: Report = toml::from_str(&encoded).unwrap();
        validate_report(&decoded, true).unwrap();
        assert_eq!(decoded.group_sources, merged.group_sources);
        assert_eq!(decoded.rows, merged.rows);
    }
    #[test]
    fn partial_update_rejects_missing_duplicate_corrupt_and_incompatible_sources() {
        let base = baseline();
        let mut fresh = fresh_random();
        fresh.rows.pop();
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut fresh = fresh_random();
        fresh.rows[0] = fresh.rows[1].clone();
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut fresh = fresh_random();
        fresh.rows[0].max_us += 1;
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut fresh = fresh_random();
        fresh.board = "raspi-pico2".into();
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut fresh = fresh_random();
        fresh.backend = "qemu".into();
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut fresh = fresh_random();
        for row in &mut fresh.rows {
            row.core_hz = 150_000_000;
        }
        fresh.group_sources.get_mut("random").unwrap().core_hz = 150_000_000;
        assert!(merge_groups(base.clone(), fresh).is_err());
        let mut old = base.clone();
        attach_sources(&mut old, Some("old-context".into()), None);
        assert!(merge_groups(old, fresh_random()).is_err());
        let mut fresh = fresh_random();
        fresh.group_sources.clear();
        assert!(merge_groups(base, fresh).is_err());
    }
    #[test]
    fn legacy_reports_retain_their_real_capture_identity() {
        for data in [
            include_str!("../../profiles/svc/raspi-pico1.toml"),
            include_str!("../../profiles/svc/raspi-pico2.toml"),
        ] {
            let mut r: Report = toml::from_str(data).unwrap();
            attach_sources(&mut r, None, None);
            validate_report(&r, true).unwrap();
            render_budgets(&r).unwrap();
            for p in r.group_sources.values() {
                assert_eq!(p.firmware_sha256, r.firmware_sha256);
                assert_eq!(p.unix_seconds, r.unix_seconds);
                assert!(p.build_context_sha256.is_none());
            }
        }
    }
    #[test]
    fn failed_publication_preserves_both_previous_artifacts() {
        let root = std::env::temp_dir().join(format!("svc-profile-publish-{}", std::process::id()));
        fs::create_dir_all(&root).unwrap();
        let report = root.join("profile.toml");
        let budget = root.join("kernel/core/src/core/operation_timing/pico1.rs");
        publish_calibration(&root, &report, "pico1.rs", "old-report", "old-budget").unwrap();
        // A directory in place of the report causes final rename to fail.
        let blocked_report = root.join("blocked.toml");
        fs::create_dir_all(&blocked_report).unwrap();
        assert!(publish_calibration(
            &root,
            &blocked_report,
            "pico1.rs",
            "new-report",
            "new-budget"
        )
        .is_err());
        assert_eq!(fs::read_to_string(&budget).unwrap(), "old-budget");
        assert_eq!(fs::read_to_string(&report).unwrap(), "old-report");
        fs::remove_dir_all(root).unwrap();
    }
    fn row(n: usize, max: u32) -> Row {
        Row {
            case: Case {
                svc: 9,
                variant: 0,
                input_len: n,
                output_len: 0,
            },
            core_hz: 150_000_000,
            timer_hz: 1_000_000,
            min_us: max,
            max_us: max,
            mean_us: max,
            samples_ticks: vec![max; COUNT],
        }
    }
    #[test]
    fn variable_sample_counts_and_packed_selectors() {
        for count in [1, 2, 50] {
            let case = Case {
                svc: 9,
                variant: 13,
                input_len: 16,
                output_len: 0,
            };
            let command = case.command(count);
            assert_eq!(
                (command.p1, command.p2, command.lc, command.le),
                (0xd1, count as u8, 4, (24 + 4 * count) as u8)
            );
            assert_eq!(command.data, [0, 16, 0, 0]);
            let mut data = vec![2, 9, 13, count as u8];
            for word in [12_000_000u32, 1_000_000, 17, 17, 17]
                .into_iter()
                .chain(core::iter::repeat(17).take(count))
            {
                data.extend_from_slice(&word.to_be_bytes());
            }
            let response = || T0Response {
                data: data.clone(),
                status: (0x90, 0),
            };
            assert_eq!(
                decode(case.clone(), response(), count, count)
                    .unwrap()
                    .samples_ticks
                    .len(),
                count
            );
            assert!(decode(case, response(), count, count + 1).is_err());
        }
        for count in ["0", "51", "256"] {
            assert!(run_cli(vec!["--samples".into(), count.into()]).is_err());
        }
    }
    #[test]
    fn envelope_covers_every_maximum_and_saturates() {
        let rows = [row(16, 17), row(64, 84), row(256, 301), row(1024, 501)];
        let e = envelope(&rows, "aes").unwrap();
        for row in rows {
            assert!(e.at(row.case.work()) >= row.max_us);
        }
        assert_eq!(e.at(u32::MAX), u32::MAX);
        assert!(envelope(&[], "aes").is_err());
    }
    #[test]
    fn decoder_rejects_missing_nulls_and_corrupt_statistics() {
        let case = Case {
            svc: 9,
            variant: 0,
            input_len: 16,
            output_len: 0,
        };
        let mut data = vec![2, 9, 0, COUNT as u8];
        for w in [150_000_000u32, 1_000_000, 17, 17, 17]
            .into_iter()
            .chain([17; COUNT])
        {
            data.extend_from_slice(&w.to_be_bytes());
        }
        let response = || T0Response {
            data: data.clone(),
            status: (0x90, 0),
        };
        assert!(decode(case.clone(), response(), COUNT, COUNT).is_ok());
        assert!(decode(case.clone(), response(), COUNT - 1, COUNT).is_err());
        data[15] = 18;
        assert!(decode(
            case,
            T0Response {
                data,
                status: (0x90, 0)
            },
            COUNT,
            COUNT
        )
        .is_err());
    }
}
