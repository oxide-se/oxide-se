# Rustlets Getting Started

This guide follows the dynamic authoring and deployment path:

1. start from the Rustlet template;
2. write a minimal APDU handler;
3. build a FAE payload for the target board;
4. boot the development-kit kernel, which contains no Rustlet package;
5. load and install the FAE with `apdu-tool gp deploy`;
6. select the instance and exchange APDUs with `apdu-tool`.

Cargo builds your application payload; `apdu-tool` performs every on-card
operation below. The optional preloaded-image workflow appears at the end.

Before starting, obtain the project sources and prepare Rust,
the ARM toolchain and `apdu-tool` as described in the
[main Getting Started](getting-started.md). The main path builds the kernel
locally; precompiled images are an alternative.

## What We Build

You will create `my_first_rustlet`, not merely run a checked-in test. It
implements two commands:

- `INS = 04`: return `CA FE`, so your own code has an unmistakable result;
- `INS = 08`: echo up to 16 incoming bytes.

The repository also contains `rustlets/tests/getting_started_test` as a
regression fixture. It is useful for comparing behavior, but it is not used by
the main authoring walkthrough below.

## 1. Start From The Template

The standalone template lives here:

```text
rustlets/rustlet_template/
```

Its structure is deliberately small:

- `src/main.rs`: the embedded `no_std` Rustlet payload.
- `Cargo.toml`: the Rustlet package.
- `.cargo/config.toml`: a local Cargo alias for `cargo build-fae`.
- `xtask/`: the host-side helper used by that alias.
- `build/`: generated ELF, FAE, and debug artifacts.

For a new Rustlet, first make sure the destination does not already exist.
If `rustlets/my_first_rustlet` is present from an earlier attempt, choose a
different name or move it deliberately before continuing: repeating `cp -R`
would copy the template inside the existing directory. Then copy the template
and rename the package:

```bash
cp -R rustlets/rustlet_template rustlets/my_first_rustlet
```

Then edit `rustlets/my_first_rustlet/Cargo.toml`:

```toml
[package]
name = "my_first_rustlet"
```

All remaining authoring, build, deployment, and APDU commands use this copy.

## 2. Write A Minimal Rustlet

Replace `rustlets/my_first_rustlet/src/main.rs` with:

```rust
#![no_std]
#![no_main]

use rustlet_runtime::{declare_rustlet, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_rustlet!(MyFirstRustlet, 256);

struct MyFirstRustlet;

impl Rustlet for MyFirstRustlet {
    type Persistent = ();
    type Session = ();

    fn process_apdu(
        _state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            0x04 => apdu.as_sending().send(&[0xCA, 0xFE]),
            0x08 => {
                let rx = apdu.as_receiving();
                let mut echo = [0u8; 16];
                let len = rx.data().len();
                if len > echo.len() {
                    return rx.reject(ApduStatus::wrong_length());
                }
                echo[..len].copy_from_slice(rx.data());
                rx.accept_and_send(&echo[..len])
            }
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}
```

The important pieces are:

- `#![no_std]` and `#![no_main]`: Rustlets are embedded payloads, not
  host executables.
- `declare_rustlet!(MyFirstRustlet, 256)`: declares the Rustlet entry
  points and reserves 256 bytes for the Rustlet runtime heap.
- `Persistent = ()` and `Session = ()`: this first application keeps no state
  between commands. The developer guide introduces state when you need it.
- `process_apdu()`: receives APDUs routed to the selected Rustlet
  instance.
- `Apdu::new(ctx)`: exposes the APDU helper API from the Rustlet runtime.

## 3. Build The Rustlet FAE Payload

From the repository root, choose the target matching the card:

| Target | `RUSTLET_TARGET` |
| --- | --- |
| Pico1 | `thumbv6m-none-eabi` |
| Pico2 | `thumbv8m.main-none-eabihf` |

For Pico1, build the copy you just edited:

```bash
cd rustlets/my_first_rustlet
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..
```

The payload is `rustlets/my_first_rustlet/build/my_first_rustlet.fae`. The
`xtask/` helper inside the template copy implements this Cargo build alias; it
is not the APDU deployment client. The builder's `Total flash image` value
describes the executable image; the `.fae` file on disk also contains format
framing, its footer, and alignment padding, so its file size can be larger.

## 4. Build And Start The Empty Development Kit

### Continue From The Main Getting Started

If you have just completed the [main Getting Started](getting-started.md), do
not rebuild or reflash the devkit. Its fixture uses AID `A0000047504F5320`,
while this guide reserves package `A0000047504F5321` and instance
`A0000047504F5322`; both can coexist in the registry.

If that client session is still open, skip directly to
[Check The APDU Path](#check-the-apdu-path). If you already ran
`apdu_tool close`, start the waiting `apdu_tool ... atr` command below and reset
or power-cycle the Pico without erasing its flash. The fixture remains
installed, a new `session.json` is created, and you can then continue with the
APDU check and deployment. The empty-devkit procedure below is only for a fresh
start.

From the repository root, compile the empty Pico1 devkit and the APDU client
using the same sources as your FAE:

```bash
cargo run -- build --config configs/config_devkit.toml raspi-pico1
mkdir -p target/devkit
cp target/kernel/firmware/kernel.elf target/devkit/oxide-se-devkit-pico1.elf
cargo build -p apdu_tool
```

For Pico2, replace `raspi-pico1` with `raspi-pico2` and name the copied ELF
`oxide-se-devkit-pico2.elf`. Copy each image before building another board,
since `target/kernel/firmware/kernel.elf` is shared.

Alternatively, use the [published devkit images](https://oxide-se.github.io/downloads/)
and follow the
[download and checksum instructions](getting-started.md#alternative-download-precompiled-images).
This skips the kernel build;
you still compile the FAE and APDU client.

The fresh devkit has an open development root and no Rustlet package or
instance. Your compiled FAE is installed later through `apdu-tool`, without
reflashing the kernel.

### Main Path: Physical Pico1 With OpenOCD

Connect the SWD probe and a 3.3 V UART bridge: Pico1 GPIO0 (TX) to bridge RX,
GPIO1 (RX) to bridge TX, and common ground. The UART uses 115200 baud, 8N1,
without flow control. The commands below use a CMSIS-DAP probe; choose the
interface configuration matching your probe if different.

These commands erase the Pico1's declared 2 MiB flash, including its registry.
Use a test board whose contents can be replaced. Run both terminals from the
repository root.

In the first terminal, open the UART and wait for the boot ATR:

```bash
target/debug/apdu_tool -v \
  --serial /dev/ttyACM0:115200 \
  --connect-timeout 120s --atr-timeout infinite atr
```

Replace `/dev/ttyACM0` with the connected UART bridge. On macOS, use its
`/dev/cu.usbmodem...` device. Keep this command waiting while the second
terminal programs the empty devkit and starts it:

```bash
openocd \
  -f interface/cmsis-dap.cfg \
  -f target/rp2040.cfg \
  -c "adapter speed 1000" \
  -c init \
  -c "reset init" \
  -c "flash erase_address 0x10000000 0x200000" \
  -c "flash write_image {target/devkit/oxide-se-devkit-pico1.elf}" \
  -c "verify_image {target/devkit/oxide-se-devkit-pico1.elf}" \
  -c "reset run" \
  -c shutdown
```

The UART must be open before reset is released because the ATR is emitted once
at boot. OpenOCD exits after programming; the firmware continues running. The
ATR command creates `session.json`. Keep subsequent `apdu-tool` commands in
that directory so they reuse the recorded connection. Do not commit this file.
At 1 MHz, the validated write takes only a few seconds. You can adjust
`adapter speed` if your probe or wiring needs a different value; OpenOCD's
default is often deliberately slow.

For the Pico2 alternative, use `target/devkit/oxide-se-devkit-pico2.elf`, compile the Rustlet with
`thumbv8m.main-none-eabihf`, replace `target/rp2040.cfg` with
`target/rp2350.cfg`, and replace the erase length `0x200000` with `0x400000`.
The installed OpenOCD must support RP2350. The APDU steps remain identical.

### USB BOOTSEL Alternative

Use the matching Pico1 or Pico2 UF2 instead of the OpenOCD programming command.
Follow the [BOOTSEL steps](getting-started.md#usb-bootsel-alternative-install-the-uf2),
opening the UART client before copying the file. These images reset all flash,
including the persistent registry. APDUs still use GPIO0/GPIO1 and the UART bridge;
the USB connector is only used to install the firmware.

### QEMU Pico1

The tutorial can also run with the experimental
[Pico1 QEMU port](https://github.com/2xs/qemu-rp2040-pico). Its `raspi-pico`
machine is not available in upstream QEMU; compiling and starting that fork is
not documented here.

### Check The APDU Path

Before loading, check that an application command returns `6985` because no
Rustlet is selected:

```bash
target/debug/apdu_tool raw 00:00:00:00:00:00
```

This expected rejection produces process exit code 15. It is not a failed boot.

## 5. Load And Install With apdu-tool

```bash
target/debug/apdu_tool --progress gp deploy \
  A0000047504F5321 \
  rustlets/my_first_rustlet/build/my_first_rustlet.fae \
  A0000047504F5322 --security-domain A0000047504F5301
```

This validates the FAE, sends INSTALL for load, transfers its LOAD blocks, and
installs the instance after the package is accepted. The final status must be
`9000`. No firmware rebuild or reflash occurs during deployment. The first AID
identifies the package; the last identifies the new instance. The explicit
`--security-domain` after `gp deploy` selects the devkit's root as the load
owner. This open manifest has no separate Issuer SD for automatic discovery.

`A0000047504F5321` and `A0000047504F5322` are the package and instance AIDs
reserved by this tutorial. They are available after starting from the empty
devkit or explicitly erasing its registry. For another application, allocate a
different pair in your own registered or project-assigned AID namespace; do not
invent production AIDs by incrementing these tutorial values.

## 6. Select And Call The Rustlet

```bash
target/debug/apdu_tool select A0000047504F5322
```

Expected status: `9000`. Exercise the two instructions you implemented:

| Command | Expected response data | Status |
| --- | --- | --- |
| `target/debug/apdu_tool raw 00:04:00:00:00:02` | `CA FE` | `9000` |
| `target/debug/apdu_tool raw 00:08:00:00:04:04:DE:AD:BE:EF` | `DE AD BE EF` | `9000` |

The raw command format is `CLA:INS:P1:P2:Lc:Le` followed by incoming bytes.
The echo command sends four bytes and requests four response bytes. Receiving
`CA FE` from `INS = 04` confirms that the deployed FAE came from your edited
source rather than the checked-in regression fixture.

Close the host client's session when finished:

```bash
target/debug/apdu_tool close
```

This removes local client state, not the installed package. On physical hardware,
the package remains in the registry across reboot. Repeating `gp deploy` with
identical AIDs requires deleting the earlier deployment or starting with an
explicitly erased test card. Do not silently reflash as part of application loading.

### Reference Validation

On 2026-10-14 the same dynamic deployment path was replayed on physical
Pico2/OpenOCD with the checked-in `getting_started_test` regression fixture:
empty devkit boot and ATR, the expected `6985` before deployment, `gp deploy`,
SELECT, five application APDUs, and `close`. All responses matched. The
commands above apply that validated path to the Rustlet you created.

The `devkit-2026.10.15` bundle records its source identity, build tools and
validation results in `manifest.json`. Both UF2 files were checked against
their ELF-derived full-flash images; physical USB BOOTSEL installation was not
exercised for this delivery.

## Optional: Build An Image With A Preloaded Rustlet

Predeployment is an alternative for a known firmware composition, not a step in
the dynamic walkthrough above. The checked-in configuration
`configs/config_rustlet_getting_started_test.toml` embeds the separate
`getting_started_test` regression fixture and installs instance
`A0000047504F5320` during initial provisioning:

```bash
cargo run build --config configs/config_rustlet_getting_started_test.toml raspi-pico1
```

This optional build produces `target/kernel/firmware/kernel.elf`; use that
path instead of the empty devkit ELF in the same board-specific boot procedure.
Skip `gp deploy`: the regression fixture is already present. Select it and use
the five APDUs documented in the
[main Getting Started](getting-started.md#exercise-the-rustlet). This path
changes the firmware image; the dynamic path only transfers your separately
built FAE over the APDU link.

## API Reference

The function-by-function reference is the `rustlet_runtime` Rustdoc. From the
repository root, generate and open it with:

```sh
cargo doc -p rustlet_runtime --features runtime --no-deps --open
```

Start with `Rustlet`, `declare_rustlet!`, `Apdu`, `ApduStatus` and
`CryptoProvider`. The `runtime` feature includes the entry traits and macros.
The local entry page is `target/doc/rustlet_runtime/index.html`; no hosted
reference is assumed. See the [reference build and validation instructions](rustlet.developper.guide.md#api-reference)
for strict checks and the packaged HTML artifact.

## Next Step

Continue with
[`security.domain.getting.started.md`](security.domain.getting.started.md).

That guide keeps this Pico1 and the Rustlet you just built, replaces the open
development root with a Rustlet-backed Security Domain, opens SCP03 with
`apdu-tool`, and deploys your Rustlet through the protected management path.

For the Rustlet runtime API independently of that guided sequence, see
[`rustlet.developper.guide.md`](rustlet.developper.guide.md).

That guide explains the Rustlet runtime API in more detail: APDU helpers,
installation hooks, persistent state, serialization, allocation, crypto
helpers, and the current validation pipeline.
