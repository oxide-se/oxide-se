use std::env;
use std::error::Error;
use std::path::{Path, PathBuf};
use std::process::Command;

const DEFAULT_TARGET: &str = "thumbv7em-none-eabi";
type DynError = Box<dyn Error>;

fn main() -> Result<(), DynError> {
    let mut args = env::args().skip(1);
    match args.next().as_deref() {
        Some("build-fae") => build_fae_command(),
        Some("-h") | Some("--help") | None => {
            eprintln!("Usage: cargo build-fae");
            Ok(())
        }
        Some(other) => Err(format!("unknown command '{other}'").into()),
    }
}

fn build_fae_command() -> Result<(), DynError> {
    let xtask_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let rustlet_dir = xtask_dir
        .parent()
        .ok_or("xtask directory has no Rustlet parent")?;
    let repo_root = find_repo_root(&xtask_dir)?;
    let target = env::var("RUSTLET_TARGET").unwrap_or_else(|_| DEFAULT_TARGET.to_owned());
    run_checked(
        Command::new("cargo")
            .arg("run")
            .arg("--manifest-path")
            .arg(repo_root.join("tooling/build-fae/Cargo.toml"))
            .arg("--bin")
            .arg("build_fae_rust")
            .arg("--")
            .arg("--manifest-path")
            .arg(rustlet_dir.join("Cargo.toml"))
            .arg("--target")
            .arg(target)
            .arg("--align_payload")
            .arg("0")
            .arg("--align_size")
            .arg("2048")
            .arg("--securitydomain")
            .arg("--fae"),
        "cargo run build-fae-rust --fae",
    )
}

fn find_repo_root(start: &Path) -> Result<PathBuf, DynError> {
    start
        .ancestors()
        .find(|path| path.join("tooling/build-fae/Cargo.toml").is_file())
        .map(Path::to_path_buf)
        .ok_or_else(|| format!("cannot locate repository root from {}", start.display()).into())
}

fn run_checked(command: &mut Command, label: &str) -> Result<(), DynError> {
    let status = command
        .status()
        .map_err(|error| format!("failed to run {label}: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("{label} failed with status {status}").into())
    }
}
