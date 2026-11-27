# Rustlets

- Use `rustlet_template/` for the standalone starter, `tests/` for regression
  applications, and `rustlet_runtime/` for shared APIs and ABI definitions.
  See the [workspace overview](README.md) and the
  [Rustlet authoring guide](../docs/rustlets.getting.started.md).
- Build the FAE for the target that will run it. Set `RUSTLET_TARGET` to
  `thumbv6m-none-eabi` for Pico 1 (hardware or QEMU) or
  `thumbv8m.main-none-eabihf` for Pico 2. Run `cargo build-fae` from the
  standalone Rustlet directory.
- When changing package, module, or instance AIDs, check their uses in the
  firmware configuration, test scenarios, and APDU examples.
- For runtime changes, review the kernel-facing ABI and update the Rustdoc
  and examples when the application-facing API changes.

From the repository root, run the relevant embedded Rustlet scenario. For
public API changes, also run the Rustdoc checker:

```sh
cargo run test rustlet raspi-pico1 minimal_valid_test --on qemu
sh scripts/check_rustlet_docs.sh
```
