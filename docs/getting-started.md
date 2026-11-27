# Getting Started

This guide is the shortest path from a fresh Oxide SE checkout to a running
kernel, an APDU exchange, and the dynamically loaded supplied
`getting_started_test` application. The separate
[Rustlet authoring guide](rustlets.getting.started.md) then walks through
creating `my_first_rustlet` from the template.

Choose **Pico 1 with QEMU** for emulation or **Pico 2 with OpenOCD** for
hardware. A physical Pico 1 also works with OpenOCD, and either board can
install the precompiled UF2 through USB BOOTSEL. After boot, the APDU and
Rustlet deployment steps are the same.

Build the DevKit, APDU client and tutorial Rustlet from the same checkout.
Published firmware is an alternative for the matching release.

The commands use a Linux or macOS terminal (Bash or Zsh). On Windows, use an
Ubuntu WSL environment; physical hardware additionally requires
[USB forwarding into WSL](https://learn.microsoft.com/en-us/windows/wsl/connect-usb).

Follow these steps in order:

1. Prepare the prerequisites and external tools below.
2. [Build the devkit firmware](#get-the-rustlet-development-kit-firmware), or use
   the [precompiled images](#alternative-download-precompiled-images).
3. Start the Pico with [QEMU](#software-emulation-of-pico1),
   [OpenOCD](#start-a-physical-pico-through-openocd), or
   [USB BOOTSEL](#usb-bootsel-alternative-install-the-uf2).
4. [Check the connection](#check-the-atr-and-base-apdu-path),
   [build the Rustlet](#build-a-minimal-rustlet), then
   [deploy it](#load-install-and-select-the-rustlet) and
   [exchange APDUs](#exercise-the-rustlet).

> **Precompiled devkit firmware is available.** If you want to start with a
> Rustlet instead of compiling the kernel, download the published Pico1 or
> Pico2 ELF/UF2 image and verify its checksum in
> [Alternative: Download Precompiled Images](#alternative-download-precompiled-images).
> You still build your own Rustlet FAE and `apdu-tool` from the matching source
> release.

> **Choose your path:** (1) Pico + SWD probe + UART → OpenOCD; (2) Pico + UART
> only → precompiled UF2; (3) no hardware →
> [run the Pico 1 DevKit ELF in QEMU](#software-emulation-of-pico1);
> (4) none of these → build only, without end-to-end validation.

An APDU is a command/response exchanged with the Secure Element. The ATR
(Answer To Reset) is the startup message used to establish the connection.

## Prerequisites

### Build Prerequisites

- **Git** to obtain the project and its FAE build tool:
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

### For A Physical Pico

- A Raspberry Pi Pico 1 or Pico 2 and a USB cable for power.
- **OpenOCD** for the SWD path, with `interface/cmsis-dap.cfg` and the target
  script for your board (`target/rp2040.cfg` for Pico 1 or `target/rp2350.cfg`
  for Pico 2):
  [installation and checks](../tooling/README.md#optional-prepare-physical-pico-access).
  For Pico 2 on Ubuntu 22.04 or 24.04, use the
  [Raspberry Pi OpenOCD bundle](../tooling/README.md#raspberry-pi-openocd-on-ubuntu).
- A **CMSIS-DAP SWD probe** for OpenOCD and a **3.3 V UART bridge** supporting
  115200 baud for either physical path.
  The [Raspberry Pi Debug Probe guide](https://www.raspberrypi.com/documentation/microcontrollers/debug-probe.html)
  describes a device that provides both interfaces and explains the wiring.

### Get The Sources

Build the firmware, `apdu-tool` and your Rustlet from the same source tree:

```bash
git clone --branch v1.0.0-beta.2 https://github.com/oxide-se/oxide-se.git
cd oxide-se
git submodule update --init tooling/build-fae
```

The command above retrieves the public release. If you are working in an
existing development checkout, initialize `tooling/build-fae` there and build
the firmware locally so the image, client, and Rustlet come from that checkout.
The **repository root** contains `Cargo.toml`, `rust-toolchain.toml`, `docs/`, and
`tooling/`. Run commands there unless a step explicitly changes directory; open
additional terminals there too.

The [precompiled firmware alternative](#alternative-download-precompiled-images)
skips the kernel build. Keep using the repository to build `apdu-tool` and
your Rustlet FAE.

## Host Tools For Your Application

Rust/Cargo and the ARM toolchain are needed to compile **your Rustlet FAE**.
The `tooling/build-fae` sources are invoked by the Cargo build alias;
no separate installed `build-fae` binary is required. Follow the Rust and ARM
setup links above, then build the APDU client before starting the card:

```bash
cargo build -p apdu_tool
```

The executable is `target/debug/apdu_tool`. The first FAE build may need
network access to fetch Cargo dependencies even after the client builds.

## Get The Rustlet Development-Kit Firmware

### Main Path: Compile Locally

From the repository root, build the empty Pico1 devkit and keep a named copy
of the result for the startup commands below:

```bash
cargo run -- build --config configs/config_devkit.toml raspi-pico1
mkdir -p target/devkit
cp target/kernel/firmware/kernel.elf target/devkit/oxide-se-devkit-pico1.elf
```

For a physical Pico2, use these commands instead:

```bash
cargo run -- build --config configs/config_devkit.toml raspi-pico2
mkdir -p target/devkit
cp target/kernel/firmware/kernel.elf target/devkit/oxide-se-devkit-pico2.elf
```

The kernel output path is shared between boards, so copy each image before
building another target. Continue with
[physical Pico startup](#start-a-physical-pico-through-openocd) or
[QEMU startup](#software-emulation-of-pico1).

### Alternative: Download Precompiled Images

This replaces the kernel build only. You still compile your Rustlet FAE and
`apdu-tool` locally from the repository. No separate source archive is required.

Download **devkit-2026.11.27** from the
[Oxide SE downloads page](https://oxide-se.github.io/downloads/).
Choose the image for your board and startup method:

| Board | ELF (OpenOCD or Pico 1 QEMU) | UF2 (USB BOOTSEL) |
| --- | --- | --- |
| Pico1 | [Pico1 ELF](https://oxide-se.github.io/downloads/devkit-2026.11.27/oxide-se-devkit-pico1.elf) | [Pico1 UF2](https://oxide-se.github.io/downloads/devkit-2026.11.27/oxide-se-devkit-pico1.uf2) |
| Pico2 | [Pico2 ELF](https://oxide-se.github.io/downloads/devkit-2026.11.27/oxide-se-devkit-pico2.elf) | [Pico2 UF2](https://oxide-se.github.io/downloads/devkit-2026.11.27/oxide-se-devkit-pico2.uf2) |

The published [SHA256SUMS](https://oxide-se.github.io/downloads/devkit-2026.11.27/SHA256SUMS)
covers all four images. From the repository root, download and
verify all four with the following commands. This keeps the checksum check
identical on both boards and for both installation methods:

```bash
mkdir -p target/devkit
cd target/devkit
devkit_url=https://oxide-se.github.io/downloads/devkit-2026.11.27
for file in oxide-se-devkit-pico1.elf oxide-se-devkit-pico1.uf2 \
            oxide-se-devkit-pico2.elf oxide-se-devkit-pico2.uf2 SHA256SUMS; do
  curl --fail --location --remote-name "$devkit_url/$file" || exit 1
done
sha256sum -c SHA256SUMS       # Linux: every line must report OK
# shasum -a 256 -c SHA256SUMS # macOS: use this instead
cd ../..
```

The Pico1 ELF is now at `target/devkit/oxide-se-devkit-pico1.elf`, as used below.
For Pico2, use `target/devkit/oxide-se-devkit-pico2.elf`. The UF2 files are in the
same directory. Stop if any checksum fails.

These public checksums cover the firmware images. See
[distribution metadata](devkit.distribution.md) for their build configuration
and packaging procedure.

### Development-Kit Configuration

Both the locally built and precompiled firmware use
`configs/config_devkit.toml`: an open development root, no secure channel,
no Issuer SD, and no preinstalled Rustlet package or application instance.
Your separately compiled FAE will be transferred over the APDU connection.
The open management policy is for development, not production deployment.

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

<a id="start-a-physical-pico-1-through-openocd"></a>
<a id="hardware-alternative-pico-2"></a>

## Start A Physical Pico Through OpenOCD

Use the row for your board:

| Board | OpenOCD target | Flash size | DevKit ELF |
| --- | --- | --- | --- |
| Pico 1 | `target/rp2040.cfg` | `0x200000` (2 MiB) | `target/devkit/oxide-se-devkit-pico1.elf` |
| Pico 2 | `target/rp2350.cfg` | `0x400000` (4 MiB) | `target/devkit/oxide-se-devkit-pico2.elf` |

Both boards use UART0 on GPIO0 (TX) and GPIO1 (RX), at 115200 baud, 8 data
bits, no parity, one stop bit, no flow control, and 3.3 V logic. Connect Pico
TX to bridge RX, Pico RX to bridge TX, and a common ground. Connect the SWD
probe separately.

Choose the UART bridge's actual serial port. On Linux it is often
`/dev/ttyACM0` or `/dev/ttyUSB0`. On macOS use the matching
`/dev/cu.usbmodem...` device. In WSL attach the probe and UART interfaces
to the distribution first.

In the first terminal, start waiting for the ATR before releasing reset:

```bash
target/debug/apdu_tool -v --serial /dev/ttyACM0:115200 \
  --connect-timeout 120s --atr-timeout infinite atr
```

In a second terminal, set the values for your board. The example uses Pico 2.
Check that OpenOCD can see the probe and board before programming.

```bash
PICO_TARGET=target/rp2350.cfg
PICO_FLASH_SIZE=0x400000
PICO_ELF=target/devkit/oxide-se-devkit-pico2.elf
openocd -f interface/cmsis-dap.cfg -f "$PICO_TARGET" -c init -c shutdown
```

The next command erases the **entire flash**, including the persistent
registry. Use a dedicated board or back up anything that matters.

```bash
openocd -f interface/cmsis-dap.cfg -f "$PICO_TARGET" \
  -c init \
  -c "reset init" \
  -c "flash erase_address 0x10000000 $PICO_FLASH_SIZE" \
  -c "flash write_image {$PICO_ELF}" \
  -c "verify_image {$PICO_ELF}" \
  -c "reset run" \
  -c shutdown
```

OpenOCD programs and verifies the ELF, then releases reset. At 1 MHz, flashing
and verification can take only a few seconds. If OpenOCD's default is slow
and your probe and wiring support it, add `-c "adapter speed 1000"` before
`-c init`. After the ATR arrives, continue with
[the base APDU check](#check-the-atr-and-base-apdu-path).

### USB BOOTSEL Alternative: Install The UF2

You can replace the OpenOCD programming step with the supplied UF2. A SWD
probe and OpenOCD are then unnecessary for this tutorial; keep the 3.3 V
UART bridge on GPIO0/GPIO1 for APDU communication. The board's USB connector
is used for BOOTSEL installation, not as an APDU USB serial port.

Copying the DevKit UF2 erases the **entire flash**, including installed Rustlets
and persistent data. Back up anything you need before copying the image.

1. Download and verify the DevKit UF2 for your board.
2. Hold BOOTSEL while plugging the target board into USB, then release it.
3. Copy the UF2 to the mounted BOOTSEL drive (`RPI-RP2` for Pico1,
   `RP2350` for Pico2). Use a USB cable that carries data.
4. After the Pico restarts, connect the UART bridge and run the
   `apdu_tool ... atr` command above with the bridge's serial device. Leave
   the command waiting.
5. Reset the Pico to emit a fresh ATR. You can also power-cycle the Pico
   without holding BOOTSEL, while keeping the UART bridge connected to the
   host. Once the client receives the ATR, continue with the base APDU check.

To generate a UF2 from your local ELF instead, follow the
[UF2 packaging commands](devkit.distribution.md#build-and-package) with
`target/devkit/oxide-se-devkit-pico1.elf` (or the Pico2 file). This additional
step requires picotool on your machine.

### Software emulation of Pico1

It is also possible to use the devkit without hardware by running the Pico 1
firmware in QEMU.

Download and extract the archive for your host from the
[Pico 1 QEMU RFC v4 release](https://github.com/2xs/qemu-rp2040-pico/releases/tag/rp2040-pico-rfc-v4).
Use the official RFC v4 archives below. They were built from commit
`99f89c1efc4ebe7e9efbebe0fb0d91576b1f735d` and support the persistent flash
option used in later guides. To compile the same revision, follow the
[standalone build instructions](../tooling/README.md#3-build-pico-qemu) for the
[separate QEMU port](https://github.com/2xs/qemu-rp2040-pico).

| Host | Archive |
| --- | --- |
| Linux x86-64 | [`qemu-pico1-rfc-v4-linux-amd64.tar.gz`](https://github.com/2xs/qemu-rp2040-pico/releases/download/rp2040-pico-rfc-v4/qemu-pico1-rfc-v4-linux-amd64.tar.gz) |
| macOS on Apple Silicon | [`qemu-pico1-rfc-v4-macos-arm64.tar.gz`](https://github.com/2xs/qemu-rp2040-pico/releases/download/rp2040-pico-rfc-v4/qemu-pico1-rfc-v4-macos-arm64.tar.gz) |

In each terminal that launches QEMU directly or through Cargo, put the
directory containing the extracted executable first on `PATH`. Replace the
example directory with its actual path.

```bash
export PATH="/path/to/extracted-qemu-directory:$PATH"
command -v qemu-system-arm
qemu-system-arm -machine help | grep raspi-pico
```

The last command must print a `raspi-pico` entry. Both the manual commands
and the Cargo test runner use the executable on `PATH`. From the repository
root, start QEMU with the Pico 1 devkit ELF you built or downloaded above.

```bash
qemu-system-arm -machine raspi-pico -display none -monitor none \
  -serial tcp:127.0.0.1:4444,server=on,wait=on \
  -semihosting-config enable=on,target=native \
  -kernel target/devkit/oxide-se-devkit-pico1.elf
```

Leave QEMU waiting for a connection. In a second terminal, from the same
repository root, connect `apdu-tool` to the emulated UART and read the ATR.

```bash
cargo run -p apdu_tool -- -v --serial 127.0.0.1:4444 atr
```

`wait=on` holds the firmware at startup until the client connects, so
`apdu-tool` can read the ATR sent at boot. Keep QEMU running while you follow
the rest of the tutorial from the second terminal. After closing the APDU
session, stop QEMU with Ctrl+C in the first terminal.

## Check The ATR And Base APDU Path

For the unprotected development image, the expected ATR bytes are:

```text
ATR: 3B 1C 11 80 56 09 C1 DE 5E 10 00 73 80 00 00
```

The `-v` used during startup decodes its compact-TLV historical bytes. Run
`atr` only for a new boot whose ATR has not already been consumed: it sends no
APDU, whereas normal commands transmit immediately and must not be used to
consume an ATR.

The successful `atr` command creates `session.json` in the current directory.
Later commands reuse the recorded link, so `--serial` need not be repeated.
The session file contains transport state and, in protected workflows, may
contain live Secure Channel secrets. Do not commit it.

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
- the Pico UART implementation;
- T=0 transport;
- ATR reception;
- the host APDU client.

<a id="build-a-minimal-pico-1-rustlet"></a>

## Build A Minimal Rustlet

The tutorial Rustlet is:

```text
rustlets/tests/getting_started_test/src/main.rs
```

For physical or emulated Pico 1, build the ARMv6-M FAE:

```bash
cd rustlets/tests
RUSTLET_TARGET=thumbv6m-none-eabi cargo run build-fae getting_started_test
cd ../..
```

For physical Pico 2, build the ARMv8-M FAE:

```bash
cd rustlets/tests
RUSTLET_TARGET=thumbv8m.main-none-eabihf cargo run build-fae getting_started_test
cd ../..
```

Both commands write to the same path. Build for the board you will actually
use, or save a separate copy for each target before switching boards.

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
  A0000047504F5320 --security-domain A0000047504F5301
```

The command-specific `--security-domain` after `gp deploy` names the devkit's root. The open devkit has no
separate Issuer SD for automatic discovery; naming the root also makes ownership
of the loaded package explicit.

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

The APDU commands and expected responses are the same for each startup path.

When finished, close the local APDU session and erase its state:

```bash
target/debug/apdu_tool close
```

This closes the client session. On physical hardware, deployed packages persist
across reboot: repeating the hardware programming procedure above erases them
and restarts the tutorial with an empty registry. To continue with the authoring
guide, use its [restart instructions](rustlets.getting.started.md#continue-from-the-main-getting-started).

## Automated Validation

Run the manual APDUs above before starting these independent tests.
`devkit` checks the empty image. `devkit_hello` also transfers the Rustlet
with LOAD, installs it, and checks the same application responses.

For Pico 1 QEMU, use a terminal with the [Pico QEMU binary on PATH](#software-emulation-of-pico1):

```bash
cargo run test devkit raspi-pico1 --on qemu
cargo run test devkit_hello raspi-pico1 --on qemu
```

For a dedicated Pico 2 via OpenOCD, both commands below erase its flash:

```bash
cargo run test devkit raspi-pico2 --on openocd --allow-destructive
cargo run test devkit_hello raspi-pico2 --on openocd --allow-destructive
```

For stack regression checks, see the
[stack-budget procedure](kernel.getting.started.md#stack-budget-checks).

To test installation and APDUs with a package already embedded in the ELF,
run the single-Rustlet scenario on a dedicated Pico 1:

```bash
cargo run test rustlet raspi-pico1 getting_started_test \
  --on openocd --allow-destructive
```

If exactly one suitable USB serial interface exists, the runner selects it at
115200 baud. Otherwise it lists the candidates and prints commands using
`--serial`. `--allow-destructive` is mandatory because the runner erases the
declared flash range before programming.

For the single-Rustlet scenario on Pico 2, replace `raspi-pico1` with `raspi-pico2`.
Other target scenarios are described in the
[kernel getting started](kernel.getting.started.md). The separate
[Rustlet authoring exercise](rustlets.getting.started.md) creates
`my_first_rustlet` from the template and dynamically loads it on the same Pico
devkit.

## If Something Goes Wrong

Stop at the first failing step and keep the command's complete output.
Use the matching reference below before continuing:

| Symptom | Where to start |
| --- | --- |
| `git`, `cargo`, `rustc`, or `brew` is not found | [Host packages](../tooling/README.md#2-install-the-baseline-host-packages) and [Rust installation/PATH](../tooling/README.md#install-and-check-rust). Open a new terminal after installation. |
| `arm-none-eabi-gcc` or `arm-none-eabi-ld` is missing, or FAE packaging fails | [build-fae prerequisites](../tooling/README.md#validate-the-build-fae-prerequisites). |
| OpenOCD cannot find the target script, the probe, or the serial device | [Hardware setup and permissions](../tooling/README.md#optional-prepare-physical-pico-1-access). |
| `atr` waits indefinitely | Open the correct UART before reset, then check TX/RX, ground, and 115200 baud. See [Pico porting notes](porting-caveats/rp2040.md). |
| An APDU or `gp deploy` fails | Compare with the expected status for that step and consult the [APDU client guide](../tools/apdu-tool/README.md). The initial `69 85` is expected; a successful deployment and selection return `90 00`. |

If you still need help, follow
[Collect A Useful Failure Report](../tooling/README.md#collect-a-useful-failure-report).
Include your host OS, the chosen installation path, the first failing command,
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
- `xtask`: build, OpenOCD deployment, and validation orchestration.

Inspect the supported targets and options with:

```bash
cargo run build --help
cargo run test --help
target/debug/apdu_tool --help
```

The current board catalogue distinguishes the porting level from its validated
execution environment. This walkthrough uses the OpenOCD recipes for
`raspi-pico1` and `raspi-pico2`.

## Other Guides

Read these next depending on what you want to do:

- [Kernel getting started](kernel.getting.started.md): target layouts,
  manifests, kernel modules, validation campaigns, and stack checks.
- [Rustlet getting started](rustlets.getting.started.md): authoring a Rustlet
  from the template.
- [Rustlet developer guide](rustlet.developper.guide.md): Rustlet runtime and
  ABI details.
- [Security Domain getting started](security.domain.getting.started.md):
  preinstall, operate, and use a Security Domain with `apdu-tool` on Pico1.
- [Rustlet Security Domain getting started](rustlet.security.domain.getting.started.md):
  implement a delegated SCP03 Security Domain from the minimal Rustlet
  skeleton.
- [Security Domain developer guide](security.domain.developper.guide.md):
  authority backends and policy hooks.
- [New-board porting guide](newboard.porting.guide.md): progressing a target
  from build-only support to Rustlet execution.
- [Pico 1 porting caveats](porting-caveats/rp2040.md): RP2040 boot, flash,
  UART, OpenOCD, and hardware validation details.
- [Isolated application debugging](isolated-app-debugging.md): low-level
  Rustlet entry, return, and fault debugging.

## On-Card State Lifetimes

Rustlets and Rustlet Security Domains share `State<Persistent, Session>`.
Persistent is recovered from the committed registry; Session is retained only
for a valid activation, including ordinary rollback; volatile working data has
no runtime conservation guarantee beyond APDU processing. Reset or power loss
does not recover Session or working data. A resident SD can retain its Session
while its child application is selected.

Persistent rollback and session retirement are independent decisions: a normal
management rejection can restore Persistent while retaining current Session;
a protocol reset can end a channel without undoing committed Persistent. There
is no generic rewind of Session to APDU entry. Conservation guarantees do not
promise secure memory erasure. See the [state lifecycle, transition matrix and
cleanup boundaries](rustlet.developper.guide.md#state-lifetimes-and-rollback).

The host APDU tool's `session.json` describes a client transport/secure-channel
session. It is distinct from the Rustlet's on-card `Session` object.
