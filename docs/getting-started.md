# Getting Started

This guide is the shortest path from a fresh Oxide SE checkout to a running
kernel, an APDU exchange, and one dynamically loaded Rustlet.

The main target is `raspi-pico1`:

- under the Oxide SE RP2040 QEMU fork;
- on a physical Raspberry Pi Pico programmed and started through OpenOCD.

The same native ELF is used in both cases. The QEMU path is convenient for
development and repeatable tests; the OpenOCD path validates the real boot,
flash, UART, and board implementation.

For a first run, use Pico 1 under QEMU: no board, debug probe, or UART bridge
is needed. You will build the development image, start it, load a Rustlet,
and receive an echo response ending in `SW: 90 00`.

The commands use a Linux or macOS terminal (Bash or Zsh). On Windows, use an
Ubuntu WSL environment; physical hardware additionally requires
[USB forwarding into WSL](https://learn.microsoft.com/en-us/windows/wsl/connect-usb).

Follow these steps in order:

1. Prepare the prerequisites and external tools below.
2. [Build the devkit image](#build-the-rustlet-development-kit-image).
3. Start **one** target: [Pico 1 QEMU](#start-pico-1-under-qemu) or
   [a physical Pico 1](#start-a-physical-pico-1-through-openocd).
4. [Check the connection](#check-the-atr-and-base-apdu-path),
   [build the Rustlet](#build-a-minimal-pico-1-rustlet), then
   [deploy it](#load-install-and-select-the-rustlet) and
   [exchange APDUs](#exercise-the-rustlet).

An APDU is a command/response exchanged with the Secure Element. The ATR
(Answer To Reset) is the startup message used to establish the connection.

## Prerequisites

### For Both QEMU And Hardware

- **Git** to clone this repository and fetch its external components:
  [installation instructions](https://git-scm.com/downloads).
- **Rust and Cargo through rustup**:
  [official installer](https://rust-lang.org/tools/install/).
  Cargo is included. The repository's [`rust-toolchain.toml`](../rust-toolchain.toml)
  selects nightly and the required components; follow the
  [Rust setup and checks](../tooling/README.md#install-and-check-rust).
- **The ARM cross-compiler and binutils** (`arm-none-eabi-gcc`,
  `arm-none-eabi-ld`): follow the
  [Ubuntu/macOS package instructions](../tooling/README.md#2-install-the-baseline-host-packages).
  The [Arm GNU Toolchain documentation](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads)
  provides other installation options; select the bare-metal `arm-none-eabi` variant.

### For A Physical Pico 1 Only

- A Raspberry Pi Pico 1 and a USB cable for power.
- **OpenOCD**, including `interface/cmsis-dap.cfg` and `target/rp2040.cfg`:
  [installation and checks](../tooling/README.md#optional-prepare-physical-pico-1-access),
  with [upstream installation guidance](https://openocd.org/pages/getting-openocd.html).
  On Ubuntu 22.04, use the
  [Raspberry Pi OpenOCD procedure](../tooling/README.md#ubuntu-2204-openocd):
  the `apt` package is too old for this Pico 1 command.
- A **CMSIS-DAP SWD probe** and a **3.3 V UART bridge** supporting 115200 baud.
  The [Raspberry Pi Debug Probe guide](https://www.raspberrypi.com/documentation/microcontrollers/debug-probe.html)
  describes a device that provides both interfaces and explains the wiring.

### Get The Sources

If you already have a Git checkout, open a terminal in its root directory.
Otherwise, clone the public repository from a directory of your choice:

```bash
git clone https://github.com/oxide-se/oxide-se.git
cd oxide-se
```

The **repository root** is the directory containing `Cargo.toml`,
`rust-toolchain.toml`, `docs/`, and `tooling/`. Run commands there unless a
step explicitly changes directory. Open each additional terminal there too.

## External Host Tools

The Pico QEMU tutorial depends on two external components:

1. The Pico-enabled QEMU executable at:

   ```text
   tooling/qemu-rp2040-pico/build/qemu-system-arm
   ```

2. The `build-fae` tool sources at:

   ```text
   tooling/build-fae/Cargo.toml
   ```

   The tutorial commands build and invoke `build_fae_rust` through Cargo; no
   separately installed executable is required.

QEMU is only needed for the virtual target; `build-fae` is needed for both
QEMU and hardware. If the required components are not ready, follow the
[host-tooling preparation guide](../tooling/README.md).

The preparation guide covers submodules, Ubuntu/macOS packages, Rust setup,
the Pico QEMU build, and step-by-step troubleshooting. Once its readiness
checks pass for your chosen path, return here and build `apdu-tool`, the host
command-line client, before starting a target. This prevents host compilation
from making the first connection miss the boot ATR:

```bash
cargo build -p apdu_tool
```

The expected executable is `target/debug/apdu_tool`. If a preparation command
fails, resolve it using the
[tooling troubleshooting guide](../tooling/README.md#step-by-step-validation-and-troubleshooting)
before continuing.

## Build The Rustlet Development-Kit Image

The tutorial uses `configs/config_devkit.toml`. This manifest produces
an image **for developing Rustlets**.  The initial system contains no Rustlet
package or application instance, so each application can be built separately
and loaded after boot.

`rustlet-devkit` is the name of this useful manifest composition, not a hidden
build profile. The same schema describes every Oxide SE image: this one simply
declares a permissive technical root, no child Security Domain (and therefore
no Issuer Security Domain), no predeployed application, and no Secure Channel.

From the repository root, use this recommended command to build the bootable
devkit image for Pico 1:

```bash
cargo run build --config configs/config_devkit.toml raspi-pico1
```

Replace `raspi-pico1` with another supported oXiDe SE target to build the
devkit for that board. Run `cargo run build --help` for the available targets
and build options.

The command produces the bootable native ELF image:

```text
target/kernel/firmware/kernel.elf
```

Build does not flash the board or start QEMU. The following sections show how
to boot this ELF in QEMU or program it onto a physical Pico.

The complete manifest is intentionally short:

```toml
[secure_channel]
protocols = []

[root.package]
name = "NullSecurityDomain"
aid = "A0:00:00:47:50:4F:53:01"

[root.instance]
aid = "A0:00:00:47:50:4F:53:01"
install_bytes = "FF:FF:FF"
```

Its fields mean:

- protocols = [] enables neither SCP03 nor SCP11; the only supported
  communication channel is the unencrypted one;
- `name = "NullSecurityDomain"` selects a development Security Domain that
  accepts clear deployment commands without cryptographic authentication;
- the package and instance AIDs give that root authority its stable identity;
- `install_bytes = "FF:FF:FF"` supplies the permissive development install data
  expected by this root instance.

`NullSecurityDomain` does **not** disable validation of the loaded program:
Oxide SE still checks the FAE structure, declared size, hash, target ISA, ABI,
and publication rules. It means that anybody with access to the APDU link may
request deployment without first proving possession of a cryptographic key.
This is appropriate for a development device and must not be treated as a
production security policy.

If Security Domains are unfamiliar, no further knowledge of them is required
for this tutorial. For now, consider `NullSecurityDomain` the permissive
development authority that lets you load and test small Secure Element
applications written in Rust.

Choose either the QEMU or OpenOCD startup path below. Both expose the same T=0
APDU protocol, so every command after the ATR is identical.

## Start Pico 1 Under QEMU

In the first terminal, start the Oxide SE Pico QEMU fork:

```bash
tooling/qemu-rp2040-pico/build/qemu-system-arm \
  -machine raspi-pico \
  -display none \
  -monitor none \
  -chardev socket,id=serial0,path=/tmp/oxide-se-pico1.sock,server=on,wait=on \
  -serial chardev:serial0 \
  -semihosting-config enable=on,target=native \
  -kernel target/kernel/firmware/kernel.elf
```

Use a socket path that does not already exist. QEMU waits for the APDU client
before allowing the firmware to boot, so the client receives the ATR emitted
at reset.

In a second terminal:

```bash
target/debug/apdu_tool \
  -v \
  --serial /tmp/oxide-se-pico1.sock \
  --atr-timeout infinite \
  atr
```

The successful `atr` command creates `session.json` in the current directory.
Later commands reuse the recorded link, so `--serial` need not be repeated.
The session file contains transport state and, in protected workflows, may
contain live Secure Channel secrets. Do not commit it.

Leave QEMU running. Continue with
[Check The ATR And Base APDU Path](#check-the-atr-and-base-apdu-path), using
the client terminal for all subsequent APDU commands. Skip the physical
hardware section below.

## Start A Physical Pico 1 Through OpenOCD

Oxide SE uses UART0 on GPIO0 (TX) and GPIO1 (RX), at 115200 baud, 8 data bits,
no parity, one stop bit, and no flow control, with 3.3 V logic.
Connect target TX to bridge RX,
target RX to bridge TX, and a common ground. Connect the SWD probe separately.

The commands below erase the complete declared 2 MiB Pico flash, including the
persistent registry. Use a dedicated board or back up anything that matters.
(The complete reusable procedure, including automatic serial selection and
probe options, is documented in
[OpenOCD execution](kernel.developer.guide.md#openocd-execution).)

On Linux, the UART bridge is commonly `/dev/ttyACM0` or `/dev/ttyUSB0`.
Choose the actual port for the bridge connected to GPIO0/GPIO1. On macOS, use
the matching `/dev/cu.usbmodem...` device rather than its `tty.*` alias. In
WSL, attach both the debug probe and UART USB interfaces to the distribution
before looking for `/dev/ttyACM*`.

In the first terminal, open the APDU link before releasing reset:

```bash
target/debug/apdu_tool \
  -v \
  --serial /dev/ttyACM0:115200 \
  --connect-timeout 120s \
  --atr-timeout infinite \
  atr
```

While that command waits, program and start the board from a second terminal:

```bash
openocd \
  -f interface/cmsis-dap.cfg \
  -f target/rp2040.cfg \
  -c init \
  -c "reset init" \
  -c "flash erase_address 0x10000000 0x200000" \
  -c "flash write_image {target/kernel/firmware/kernel.elf}" \
  -c "verify_image {target/kernel/firmware/kernel.elf}" \
  -c "reset run" \
  -c shutdown
```

Opening the UART first is important: Oxide SE emits the ATR once during boot.
OpenOCD programs and verifies the ELF, releases reset, and exits; the firmware
then continues independently.

### Hardware alternative: Pico 2

The same hardware workflow can use a Pico 2. Build `raspi-pico2`, select
`target/rp2350.cfg`, erase the board's declared 4 MiB flash range
(`0x400000`), and later build the Rustlet with
`RUSTLET_TARGET=thumbv8m.main-none-eabihf`. The installed OpenOCD must include
RP2350 support. (See the same
[OpenOCD execution](kernel.developer.guide.md#openocd-execution) recipe for
Pico 1 and Pico 2.)

## Check The ATR And Base APDU Path

For the unprotected development image, the expected ATR bytes are:

```text
ATR: 3B 1C 11 80 56 09 C1 DE 5E 10 00 73 80 00 00
```

The `-v` used during startup decodes its compact-TLV historical bytes. Run
`atr` only for a new boot whose ATR has not already been consumed: it sends no
APDU, whereas normal commands transmit immediately and must not be used to
consume an ATR.

The historical bytes contain:

- `80`: compact-TLV category indicator;
- `56 09 C1 DE 5E 10 00`: Oxide SE (`SE` means Secure Element) marker,
  version 1.0 beta, and build
  capabilities;
- `73 80 00 00`: conservative ISO card capabilities.

For capability byte `00`, verbose mode explains that the image uses
`NullSecurityDomain` and supports no Secure Channel. More generally:

- bit 7 distinguishes `NullSecurityDomain` from a non-null root authority;
- bits 6, 5, and 4 advertise SCP11a, SCP11b, and SCP11c respectively;
- bits 3 and 2 are reserved;
- bits 1..0 encode the SCP03 profile: `00` means none, `10` means S8, and
  `11` means S16.

Before loading an application, send an application APDU:

```bash
target/debug/apdu_tool raw 00:00:00:00:00:00
```

The expected result is:

```text
SW: 69 85
```

`69 85` means “conditions of use not satisfied”. It is correct here: no
Rustlet instance is selected. Because `apdu-tool` maps every failing status
word to a non-zero process status, this deliberately negative probe exits with
code 15 even though the observed Oxide SE behavior is the expected one.

At this point the selected startup path has validated:

- native kernel boot;
- the Pico UART implementation or its QEMU model;
- T=0 transport;
- ATR reception;
- the host APDU client.

## Build A Minimal Pico 1 Rustlet

The tutorial Rustlet is:

```text
rustlets/tests/getting_started_test/src/main.rs
```

Build it as an ARMv6-M FAE for Pico 1:

```bash
cd rustlets/tests
RUSTLET_TARGET=thumbv6m-none-eabi cargo run build-fae getting_started_test
cd ../..
```

The loadable payload is:

```text
rustlets/tests/getting_started_test/build/rustlet_getting_started_test.fae
```

The FAE is separate from the already running kernel ELF. It was not embedded by
the kernel build and will now be transferred through GlobalPlatform management
APDUs.

FAE is the loadable application format produced by `build-fae`. This step
uses the supplied example so you can check your setup before writing code.
After completing it, follow [Rustlet authoring](rustlets.getting.started.md)
to create your own application from the template.

## Load, Install, And Select The Rustlet

Deploy the FAE under the tutorial package AID and create an instance with the
same AID:

```bash
target/debug/apdu_tool --progress gp deploy \
  A0000047504F5320 \
  rustlets/tests/getting_started_test/build/rustlet_getting_started_test.fae \
  A0000047504F5320
```

`gp deploy` performs the complete dynamic path:

1. validates the FAE footer, CRC, target ISA, ABI, and size locally;
2. sends `INSTALL [for load]` with the package, Security Domain, hash, and
   total size;
3. splits the FAE into T=0-compatible `LOAD` blocks;
4. numbers the blocks and marks the final block;
5. lets Oxide SE validate and publish the persistent package;
6. sends `INSTALL [for install and make selectable]` for the instance.

It does not send the final INSTALL if any LOAD block fails. The expected final
status is `90 00`.

Select the new instance:

```bash
target/debug/apdu_tool select A0000047504F5320
```

The expected status is again `90 00`.

This is deliberately different from predeployment. A predeployment manifest
embeds a package in the kernel image; this walkthrough started with no Rustlet
package and exercised the actual `INSTALL [for load] → LOAD → INSTALL [for
install]` path.

## Exercise The Rustlet

The example implements the four short T=0 shapes plus an echo command.

No incoming or outgoing application data:

```bash
target/debug/apdu_tool raw 00:00:00:00:00:00
```

Expected status:

```text
SW: 90 00
```

Receive three bytes and return only a status word:

```bash
target/debug/apdu_tool raw 00:02:00:00:03:00:AA:BB:CC
```

Expected status:

```text
SW: 90 00
```

Return the fixed three-byte response:

```bash
target/debug/apdu_tool raw 00:04:00:00:00:03
```

Expected result:

```text
DATA OUT (3): 10 11 12
SW: 90 00
```

Receive data and return a different fixed response:

```bash
target/debug/apdu_tool raw 00:06:00:00:03:03:01:02:03
```

Expected result:

```text
DATA OUT (3): AA BB CC
SW: 90 00
```

Echo four incoming bytes:

```bash
target/debug/apdu_tool raw 00:08:00:00:04:04:DE:AD:BE:EF
```

Expected result:

```text
DATA OUT (4): DE AD BE EF
SW: 90 00
```

The same commands and expected responses apply to QEMU, Pico 1 hardware, and
the Pico 2 hardware alternative. Only the target build, startup mechanism,
Rustlet target triple, and APDU link differ.

When finished, close the local APDU session and erase its state:

```bash
target/debug/apdu_tool close
```

This closes the client session. Stop QEMU with Ctrl+C in its terminal when
you have finished. For a fresh QEMU run, repeat startup and the ATR command
before deploying again; use a new socket path if the old one still exists.
On physical hardware, deployed packages persist across reboot: repeating the
hardware programming procedure above erases them and restarts the tutorial
with an empty registry.

For Pico 1 hardware, the exact linear transcript is also available in
`tools/apdu-tool/tests/hardware_null_deploy_getting_started.sh`. It is tied to
a local serial-device name, so inspect it before running it.

## Automated Validation

The test runner performs build, deployment, APDU validation, and reporting in
one command.

Under Pico 1 QEMU:

```bash
cargo run test rustlet raspi-pico1 getting_started_test --on qemu
```

On a dedicated Pico 1 through OpenOCD:

```bash
cargo run test rustlet raspi-pico1 getting_started_test \
  --on openocd \
  --allow-destructive
```

If exactly one suitable USB serial interface exists, the runner selects it at
115200 baud. Otherwise it lists the candidates and prints commands using
`--serial`. `--allow-destructive` is mandatory because the runner erases the
declared flash range before programming.

For Pico 2 hardware, replace `raspi-pico1` with `raspi-pico2`.
Other target scenarios are described in the
[kernel getting started](kernel.getting.started.md). The separate
[Rustlet authoring exercise](rustlets.getting.started.md) uses predeployment
on MPS2-AN385; it is a different workflow from this Pico dynamic-load tutorial.

## If Something Goes Wrong

Stop at the first failing step and keep the command's complete output.
Use the matching reference below before continuing:

| Symptom | Where to start |
| --- | --- |
| `git`, `cargo`, `rustc`, or `brew` is not found | [Host packages](../tooling/README.md#2-install-the-baseline-host-packages) and [Rust installation/PATH](../tooling/README.md#install-and-check-rust). Open a new terminal after installation. |
| QEMU configure fails with Python, Meson, or `distutils` | [Step-by-step tooling diagnosis](../tooling/README.md#step-by-step-validation-and-troubleshooting), beginning with the host and Python checks. |
| QEMU configuration prints `NO` probes or only creates `qemu-system-arm.p` | Check for `build.ninja`, then run `ninja qemu-system-arm` in `tooling/qemu-rp2040-pico/build`; see [QEMU build stages](../tooling/README.md#diagnose-a-qemu-compilation-failure). |
| `arm-none-eabi-gcc` or `arm-none-eabi-ld` is missing, or FAE packaging fails | [build-fae prerequisites](../tooling/README.md#validate-the-build-fae-prerequisites). |
| QEMU executable is missing or `raspi-pico` is unknown | [Pico QEMU build](../tooling/README.md#3-build-pico-qemu). Use the executable at the exact path shown here. |
| OpenOCD cannot find `rp2040.cfg`, the probe, or the serial device | [Hardware setup and permissions](../tooling/README.md#optional-prepare-physical-pico-1-access). |
| `atr` waits indefinitely | Check that QEMU is running on the same socket; for hardware, open the correct UART before reset, then check TX/RX, ground, and 115200 baud. See [Pico porting notes](porting-caveats/rp2040.md). |
| An APDU or `gp deploy` fails | Compare with the expected status for that step and consult the [APDU client guide](../tools/apdu-tool/README.md). The initial `69 85` is expected; a successful deployment and selection return `90 00`. |

If you still need help, follow
[Collect A Useful Failure Report](../tooling/README.md#collect-a-useful-failure-report).
Include your host OS, the chosen QEMU/hardware path, the first failing command,
and its output. Share those details through the project's
[issue tracker](https://github.com/oxide-se/oxide-se/issues).

## Configuration And Predeployment

The public tutorial manifest is `configs/config_devkit.toml`. It is kept
separate from test manifests so test requirements can evolve without silently
changing the development image described here. It currently defines a root
`NullSecurityDomain`, no child or Issuer Security Domain, no Secure Channel,
and no preinstalled Rustlet. Nothing in the TOML labels this image as a
devkit: that meaning follows from the hierarchy and policies it declares.

Build with another manifest when an image must start with Security Domains,
keys, packages, or instances already present:

```bash
cargo run build \
  --config configs/config_rustlet_getting_started_test.toml \
  raspi-pico1
```

For example, a predeployed Rustlet package is declared beneath its owning
Security Domain:

```toml
[[root.packages]]
path = "./rustlets/tests/getting_started_test"

[[root.packages.instances]]
aid = "A0:00:00:47:50:4F:53:20"
install_bytes = ""
```

At first initialization, Oxide SE applies the manifest and commits the
registry. On persistent Pico targets, later boots recover the latest valid
registry snapshot instead of replaying the manifest. Predeployment is useful
for fixed images, but it is not a substitute for validating dynamic LOAD.

## Workspace Overview

The main components used by this walkthrough are:

- `kernel/core`: reusable architecture- and board-independent kernel core;
- `kernel/firmware`: production firmware and APDU management;
- `kernel/native/raspi-pico`: Pico 1 startup, boot2, and linker support;
- `kernel/native/raspi-pico2`: Pico 2 startup and linker support;
- `rustlets/rustlet_runtime`: Rustlet ABI and runtime;
- `rustlets/tests/getting_started_test`: tutorial Rustlet;
- `tools/apdu-tool`: TCP, Unix-socket, and physical-serial APDU client;
- `tooling/build-fae`: FAE packaging tools;
- `tooling/qemu-rp2040-pico`: QEMU fork with the RP2040 Pico machine;
- `xtask`: build, QEMU/OpenOCD deployment, and validation orchestration.

Inspect the supported targets and options with:

```bash
cargo run build --help
cargo run test --help
target/debug/apdu_tool --help
```

The current board catalogue distinguishes the porting level from its validated
execution environment. In particular, `raspi-pico1` supports QEMU and an
OpenOCD recipe, `raspi-pico2` uses OpenOCD, and `mps2-an385` uses QEMU.

## Other Guides

Read these next depending on what you want to do:

- [Kernel getting started](kernel.getting.started.md): target layouts,
  manifests, kernel modules, validation campaigns, and stack checks.
- [Rustlet getting started](rustlets.getting.started.md): authoring a Rustlet
  from the template.
- [Rustlet developer guide](rustlet.developper.guide.md): Rustlet runtime and
  ABI details.
- [Security Domain getting started](security.domain.getting.started.md):
  protected management scenarios.
- [Security Domain developer guide](security.domain.developper.guide.md):
  authority backends and policy hooks.
- [New-board porting guide](newboard.porting.guide.md): progressing a target
  from build-only support to Rustlet execution.
- [Pico 1 porting caveats](porting-caveats/rp2040.md): RP2040 boot, flash,
  UART, OpenOCD, and hardware validation details.
- [Isolated application debugging](isolated-app-debugging.md): low-level
  Rustlet entry, return, and fault debugging.
