# Oxide SE Bootstrap and Workspace Notes

This document describes the current bootstrap path of the repository and
how the different crates fit together.

## Goal

The repository is split into two layers:

- the Oxide SE repository hosts the project-owned sources and the Rust workspace;
- `tooling/build-fae` stays a separate Git submodule used as external FAE
  build and packaging tooling for Rustlet images and the legacy kernel FAE
  image mode.

The bootstrap uses a small multi-crate workspace architecture:

- `kernel/core`: reusable embedded library crate (`oxi_core`)
- `kernel/firmware`: production firmware crate
- `core_test`: QEMU-oriented embedded test firmware
- `xtask`: local orchestration commands

This lets the project keep the runtime and hardware services reusable,
while still supporting multiple firmware entry points above the same
embedded core.

## Prerequisites

The current flow expects these tools to be available:

- `cargo`
- `rustup`
- a nightly Rust toolchain with `rust-src`
- `arm-none-eabi-gcc`
- `qemu-system-arm`

## Repository Layout

- `kernel/core/`: reusable embedded library crate (`oxi_core`)
- `kernel/firmware/`: production firmware crate
- `core_test/`: embedded test firmware crate
- `rustlets/rustlet_runtime/`: shared runtime crate and ABI definitions for Rustlets
- `rustlets/complete_security_domain/`: full embedded administrative Rustlet
- `rustlets/tests/`: Rustlet functional test applications
- `xtask/`: local orchestration commands
- `tools/apdu-tool/`: host-side APDU client
- `tooling/build-fae/`: external FAE toolchain kept as a Git submodule

Within `kernel/core/src/`, the reusable layer is split as follows:

- `lib.rs`: crate root
- `core/mod.rs`: top-level wiring and public runtime-facing API
- `core/runtime.rs`: runtime initialization and low-level support
- `core/allocator.rs`: buddy allocator with external bit-tree metadata used
  as the Rust global allocator
- `core/semihosting.rs`: semihosting support
- `core/serial.rs`: minimal synchronous serial API (`send_byte`,
  `receive_byte`)
- `core/crypto.rs`: low-level crypto facade and target dispatch
- `core/flash.rs`: flash service API
- `core/target/`: target-specific implementations

The production APDU loop lives in `kernel/firmware/src/`, while
`core_test/src/main.rs` provides a distinct
firmware entry point dedicated to QEMU-backed embedded testing.

## Entry Model

Native ELF startup masks interrupts, establishes MSP, clears the reserved
boot ABI and initializes RAM before calling the exported `start()` symbol
owned by the firmware crate. Core initialization publishes exception handlers
before enabling interrupts. See the
[native startup contracts](kernel.developer.guide.md#diagnostic-and-startup-safety-boundaries).

The shared pattern is:

1. the firmware `start()` calls `oxi_core::core::initialize()`;
2. the firmware executes its own logic;
3. the firmware returns through `oxi_core::core::shutdown(exit_code)`.

This keeps the ABI-facing entry point out of the reusable library while
still centralizing runtime initialization and shutdown policy.

## Runtime Split

The current runtime split is:

- APDU traffic uses the target UART;
- kernel console/debug traces are disabled by default and can be enabled with
  `--trace=semihosting` for QEMU or `--trace=jtag` on supported hardware
  targets;
- cryptographic services are provided by `oxi_core`, with board-aware
  routing between hardware support and fallback logic;
- QEMU-backed entropy uses semihosting file access, while real hardware
  keeps its target RNG path.

## Commands

Build only the default production native ELF:

```bash
cargo run build --elf
```

Build a native ELF for a selected board:

```bash
cargo run build --elf mps2-an385
cargo run build --elf raspi-pico1
cargo run build --elf raspi-pico2
```

`cargo run build --fae <board>` retains the legacy bootable kernel FAE mode.
That kernel path is no longer supported; the option is deprecated and emits
a warning on stderr. Rustlets still use FAE images in the normal native ELF
workflow; these are distinct uses of the format.

Run the kernel-local APDU ping check under QEMU:

```bash
cargo run test kernel_ping mps2-an385
```

Run the kernel-local T=0 APDU transcript check under QEMU:

```bash
cargo run test kernel_t0 mps2-an385
cargo run test kernel_t0 olimex-stm32-h405
```

Run the Rustlet functional campaign on one board:

```bash
cargo run test rustlet_all mps2-an385
```

Run the Rustlet functional campaign on all functional APDU/QEMU boards:

```bash
cargo run test rustlet_all
```

This selects catalogue entries at `Rustlet` level with QEMU support:
`mps2-an385`, `olimex-stm32-h405` and `raspi-pico1`. Pico2 hardware is selected
explicitly with `raspi-pico2 --on openocd --allow-destructive`; it requires a
connected debug probe and UART bridge. The `b-l475e-iot01a` target remains
build-only, without a currently claimed execution runner.

Run the default workspace test entry point:

```bash
cargo test --offline
```

This runs the default workspace member, `xtask`, including host tests and
its configured QEMU integration tests. Use `cargo test --workspace --offline`
for all workspace test harnesses. Neither command substitutes for the full
target scenario catalogue or hardware campaigns.

## Generated Artifacts

Firmware outputs are written under `target/kernel/firmware/`. The selected
build mode determines which image is produced; an old `.fae` file is not
evidence that the current native build refreshed it. Paths include:

- `target/kernel/firmware/kernel.elf`
- `target/kernel/firmware/kernel.fae` (deprecated, unsupported kernel format)
- `target/kernel/firmware/kernel.gdbinit` (legacy FAE symbol relocation helper)

Embedded test firmware artifacts are written under:

- `target/kernel/firmware/core_test.elf`
- `target/kernel/firmware/core_test.fae` (legacy FAE diagnostic artifact; not
  evidence of support for FAE kernel images)
- `target/kernel/firmware/core_test.gdbinit` (legacy FAE symbol relocation helper)

## Validation Notes

The maintained startup qualification uses native ELF kernels. The
[diagnostic/startup qualification](kernel.getting.started.md#diagnostic-and-startup-qualification-september-2026)
records the exercised Pico1/QEMU, Pico2/OpenOCD and MPS2/QEMU paths and their
limits. Build-only targets and the legacy bootable kernel FAE path must not
inherit that validation claim.

`core_test` remains a separate embedded firmware entry point; ordinary host
`cargo test` success does not establish that it ran on a board. Embedded
semihosting trace checks require an explicit trace/debug build; the normal
kernel build remains `--trace=none`.

`build_fae` may emit heuristic warnings about possible absolute pointers in
read-only sections. Investigate them against the actual image, relocation
contract and execution path; a successful build alone is not validation.
