# Oxide SE contributor instructions

- Write contributor-facing text, comments, and commit messages in English.
- Run workspace commands from the repository root unless a guide specifies a
  different directory. Use the nightly toolchain selected by `rust-toolchain.toml`.
- Start with the [Getting Started guide](docs/getting-started.md) and
  [host prerequisites](tooling/README.md). Initialize the build helper with
  `git submodule update --init tooling/build-fae` before building firmware
  or Rustlet FAE files.
- For firmware changes, select the board and execution backend explicitly.
  Follow the [kernel guide](docs/kernel.getting.started.md) for board-specific
  checks. Use a dedicated board for tests that erase flash.
- When changing commands, options, or expected output, update the affected
  public examples. Keep generated firmware and other build outputs out of commits.

For Rust changes, choose the checks relevant to the change. The public CI uses:

```sh
cargo fmt --all -- --check
cargo clippy -p xtask --all-targets
cargo test --offline
```

The offline test command needs locally cached Cargo dependencies. See the
[CI workflow](.github/workflows/ci.yml) for the complete setup and build checks.
