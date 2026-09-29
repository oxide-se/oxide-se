# Host Tooling Preparation

This guide installs the host prerequisites and prepares the external
components used by the Oxide SE Rustlet development-kit tutorial:

- the Pico-enabled `qemu-system-arm` executable (QEMU path only);
- the `build-fae` Rust workspace used to package Rustlets.

Use the quick setup first, choosing the commands for your operating system.
Run one block at a time and continue only when it succeeds. If a command
fails, keep its output and follow the
[step-by-step validation and troubleshooting](#step-by-step-validation-and-troubleshooting)
section instead.

The commands assume a Git checkout and start at its root (the directory
containing `Cargo.toml` and `tooling/`). To get one, follow the
[Getting Started prerequisites](../docs/getting-started.md#prerequisites).
The first setup requires internet access to download packages and dependencies.

For QEMU, follow steps 1–5. For physical Pico 1 only, initialize `build-fae`
in step 1, install the host packages and Rust in step 2, skip step 3, then
complete steps 4–5 and the optional hardware section. The package lists in
step 2 include QEMU build dependencies for convenience; the hardware path
does not need to compile QEMU.

## Quick Setup

### 1. Initialize The External Components

From the Oxide SE repository root:

```bash
git submodule update --init tooling/build-fae tooling/qemu-rp2040-pico
```

For the hardware-only path:

```bash
git submodule update --init tooling/build-fae
```

The checkout pins each component to the revision qualified with this Oxide SE
release. Do not replace either revision with the tip of its upstream branch
when following the tutorial.

### 2. Install The Baseline Host Packages

#### Ubuntu 24.04

```bash
sudo apt update
sudo apt install \
  git curl ca-certificates build-essential ninja-build pkg-config \
  python3 python3-venv python3-pip \
  libglib2.0-dev libpixman-1-dev \
  gcc-arm-none-eabi binutils-arm-none-eabi
```

Ubuntu 24.04 provides Python 3.12. Older Ubuntu releases may not provide a
suitable Python through their standard repositories; follow
[Use A Supported Python Without Replacing The System Python](#use-a-supported-python-without-replacing-the-system-python)
instead of changing `/usr/bin/python3`.

On **Ubuntu 22.04**, the same package command supplies the build dependencies,
but the distribution's Python is too old for this pinned QEMU fork. Install a
separate Python 3.12 or newer and follow the
[Ubuntu 22.04 Python instructions](#use-a-supported-python-without-replacing-the-system-python).
The system's OpenOCD 0.11 also lacks the RP2040 target script; physical Pico
users should follow the [Ubuntu 22.04 OpenOCD setup](#ubuntu-2204-openocd).

#### macOS With Homebrew

Install [Apple's command-line developer tools](https://developer.apple.com/documentation/xcode/installing-the-command-line-tools/)
if they are not already present:

```bash
xcode-select --install
```

Finish the installation dialog before continuing. If the tools are already
installed, `xcode-select` reports that no action is needed.

Install [Homebrew](https://brew.sh/) if `brew` is not found. Follow the
installer's shell setup instructions, open a new terminal, and return to the
repository root. Then run:

```bash
brew --version
brew update
brew install python ninja pkg-config glib pixman arm-none-eabi-gcc
```

For shell setup difficulties, see
[Homebrew's post-installation instructions](https://docs.brew.sh/Installation#post-installation-steps).
The commands use `brew --prefix` to locate the installation on your machine.
Homebrew's [`arm-none-eabi-gcc` package](https://formulae.brew.sh/formula/arm-none-eabi-gcc)
also installs the corresponding binutils.

#### Install And Check Rust

On either operating system, install Rust with the
[official rustup installer](https://rust-lang.org/tools/install/).
This supplies `rustup`, `rustc`, and Cargo. Open a new terminal after
installation so its `PATH` changes take effect, and return to the repository
root. Check:

```bash
rustup --version
rustc --version
cargo --version
rustup show active-toolchain
rustup component list --installed
```

Invoking `rustc` in this checkout lets rustup install the toolchain and
components requested by [`rust-toolchain.toml`](../rust-toolchain.toml).
The active toolchain should be nightly, and the component list must include
`rust-src`, `rustfmt`, and `clippy`. The file currently selects the rolling
`nightly` channel, not a dated compiler release. See
[how rustup selects a toolchain](https://rust-lang.github.io/rustup/overrides.html#the-toolchain-file)
if an existing local override selects something else.

If `cargo` or `rustc` is still missing, follow the
[Rust installation page](https://rust-lang.org/tools/install/), under
"Configuring the PATH environment variable".
Do not proceed until these commands succeed.

Finally, check the ARM tools used by the kernel and Rustlet builds:

```bash
arm-none-eabi-gcc --version
arm-none-eabi-ld --version
```

Both commands must print a version. For alternative host installations, use
the [Arm GNU Toolchain documentation](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads)
and choose the bare-metal `arm-none-eabi` variant.

### 3. Build Pico QEMU

Skip this section for hardware-only use. For QEMU, first validate the Python
interpreter as shown below; it must be version 3.12 or newer.

On Ubuntu 24.04:

```bash
python3 --version
python3 -c 'import sys, venv, ensurepip; print(sys.executable)'
```

If either check fails, follow the
[Python diagnosis](#validate-python-before-running-qemu-configure).
Otherwise configure and build from the repository root:

```bash
cd tooling/qemu-rp2040-pico
mkdir -p build
cd build
../configure \
  --python="$(command -v python3)" \
  --target-list=arm-softmmu
test -f build.ninja
ninja qemu-system-arm
test -x qemu-system-arm
./qemu-system-arm -machine help | grep raspi-pico
cd ../../..
```

On Ubuntu 22.04 with a separately installed Python 3.12 or newer, use this
sequence instead. Substitute the interpreter's **absolute path** if its
location differs. An activated user-created virtual environment is optional;
QEMU creates its own `build/pyvenv` regardless.

```bash
cd tooling/qemu-rp2040-pico
mkdir -p build
cd build
python3.12 --version
python3.12 -c 'import sys, venv, ensurepip; print(sys.executable)'
../configure \
  --python="$(command -v python3.12)" \
  --target-list=arm-softmmu
test -f build.ninja
ninja qemu-system-arm
test -x qemu-system-arm
./qemu-system-arm -machine help | grep raspi-pico
cd ../../..
```

On macOS with Homebrew:

```bash
"$(brew --prefix python)/bin/python3" --version
"$(brew --prefix python)/bin/python3" \
  -c 'import sys, venv, ensurepip; print(sys.executable)'
```

If either check fails, follow the
[Python diagnosis](#validate-python-before-running-qemu-configure).
Otherwise configure and build from the repository root:

```bash
cd tooling/qemu-rp2040-pico
mkdir -p build
cd build
../configure \
  --python="$(brew --prefix python)/bin/python3" \
  --target-list=arm-softmmu
test -f build.ninja
ninja qemu-system-arm
test -x qemu-system-arm
./qemu-system-arm -machine help | grep raspi-pico
cd ../../..
```

QEMU creates its own `build/pyvenv` and prepares the Meson environment used by
the build. A global Meson installation is not required. If `configure` fails,
resolve that failure before running `ninja`; a missing `build.ninja` after
failed configuration is a consequence of the earlier error. `configure` only
prepares the build; **`ninja qemu-system-arm` creates the executable**. The
`qemu-system-arm.p` directory holds intermediate build files and may be empty
before compilation. Red `NO` results in individual Meson feature probes are
not, by themselves, errors: check that `configure` exits successfully and
creates `build.ninja`, then check the result of Ninja.

### 4. Prepare `build-fae`

The repository's `rust-toolchain.toml` selects the Rust toolchain and the
`rust-src` component. With `rustup` and Cargo already available, run:

```bash
cargo build \
  --manifest-path tooling/build-fae/Cargo.toml \
  --bin build_fae_rust
```

The Devkit tutorial invokes `build_fae_rust` through Cargo. There is no stable
executable path to install or add to `PATH`.

### 5. Check That The Host Is Ready

From the Oxide SE repository root, for the QEMU path:

```bash
test -x tooling/qemu-rp2040-pico/build/qemu-system-arm
tooling/qemu-rp2040-pico/build/qemu-system-arm \
  -machine help | grep raspi-pico
```

The first command succeeds silently; the second must print a `raspi-pico`
machine. For both QEMU and hardware:

```bash
test -f tooling/build-fae/Cargo.toml
cargo build --manifest-path tooling/build-fae/Cargo.toml --bin build_fae_rust
```

The file check succeeds silently and Cargo should finish successfully.
QEMU users can return to the
[Devkit tutorial](../docs/getting-started.md#external-host-tools) and build
`apdu-tool`. Hardware users should complete the next section first.

### Optional: Prepare Physical Pico 1 Access

Skip this section for QEMU. On Ubuntu 24.04, install OpenOCD with:

```bash
sudo apt install openocd
```

Ubuntu 22.04 supplies OpenOCD 0.11.0, which lacks `target/rp2040.cfg`.
Follow the [Ubuntu 22.04 OpenOCD setup](#ubuntu-2204-openocd) below instead.

On macOS:

```bash
brew install open-ocd
```

#### Ubuntu 22.04 OpenOCD

For an `x86_64` Ubuntu 22.04 host, use Raspberry Pi's
[versioned OpenOCD archive](https://github.com/raspberrypi/pico-sdk-tools/releases/tag/v2.3.1-0).
It was built on Ubuntu 22.04 and contains both `openocd` and its `scripts/`
directory. Check `uname -m` first: the commands below are for `x86_64`; the
same release also provides an `aarch64` archive. Keep the files together in a
user-owned directory, outside this repository:

```bash
uname -m
test "$(uname -m)" = x86_64
mkdir -p "$HOME/.local/opt/openocd-rpi-v2.3.1-0"
curl -fL \
  -o /tmp/openocd-rpi-v2.3.1-0-x86_64.tar.gz \
  'https://github.com/raspberrypi/pico-sdk-tools/releases/download/v2.3.1-0/openocd-0.12.0%2Bdev-x86_64-lin.tar.gz'
printf '%s\n' \
  '7b2ad4bb310356c7e50c17d0a813f7f803765ea4a0610a2191909767835f3b0d  /tmp/openocd-rpi-v2.3.1-0-x86_64.tar.gz' \
  | sha256sum -c -
tar -xzf /tmp/openocd-rpi-v2.3.1-0-x86_64.tar.gz \
  -C "$HOME/.local/opt/openocd-rpi-v2.3.1-0"
```

The checksum is published with the archive on the Raspberry Pi release page.
On `aarch64`, download its matching asset and use the checksum on that page.
The binary may need the same USB libraries installed by Raspberry Pi's Linux
build tests. On Ubuntu 22.04, install them before running it:

```bash
sudo apt install libftdi1-2 libhidapi-hidraw0
```

In **the terminal that will run OpenOCD**, select this version and its own
scripts. Repeat these exports in a new terminal; they do not persist across
shell sessions:

```bash
export PATH="$HOME/.local/opt/openocd-rpi-v2.3.1-0:$PATH"
export OPENOCD_SCRIPTS="$HOME/.local/opt/openocd-rpi-v2.3.1-0/scripts"
command -v openocd
openocd --version
```

`command -v openocd` must name the binary under `.local/opt`, not Ubuntu's
`/usr/bin/openocd`. The archive does not install anything into `/usr/bin`.
It is not necessary to remove an older system package. If you have already
built Raspberry Pi's OpenOCD from source, its uninstalled binary is
`src/openocd`; run it with `-s tcl` from the OpenOCD source directory, as
described in the [official Pico guide](https://pip-assets.raspberrypi.com/categories/610-raspberry-pi-pico/documents/RP-008276-DS-1-getting-started-with-pico.pdf).
Do not pair that binary with the scripts from Ubuntu's older package.

Return to the Oxide SE repository root for the common check below.

Check the executable and its installed configuration files without connecting
to or programming a board:

```bash
openocd --version
openocd -c 'echo [find interface/cmsis-dap.cfg]' \
  -c 'echo [find target/rp2040.cfg]' -c shutdown
```

The second command must print a path for each configuration file and exit
successfully. If a file is missing, follow
[Getting OpenOCD](https://openocd.org/pages/getting-openocd.html) and the
[Raspberry Pi tool installation guide](https://www.raspberrypi.com/documentation/microcontrollers/debug-probe.html#install-tools).
Check which executable is selected with `command -v openocd` if more than one
version is installed.

Follow the [Debug Probe wiring guide](https://www.raspberrypi.com/documentation/microcontrollers/debug-probe.html#getting-started)
for SWD and UART. Oxide SE uses GPIO0 (TX) and GPIO1 (RX), with 3.3 V logic,
a common ground, and 115200 baud. The board needs its own power connection.

On Linux, access to the probe and UART may require device permissions.
For `Permission denied`, inspect the serial device's group with
`ls -l /dev/ttyACM0` (substitute your actual device). On Ubuntu, if it belongs
to `dialout`, add your login user to that group:

```bash
sudo usermod -aG dialout "$USER"
```

Log out and log back in for the group change to take effect. Probe access
uses OpenOCD's udev rules; follow the
[OpenOCD permissions guidance](https://openocd.org/doc-release/html/Running.html)
if USB access still fails. On WSL, first follow
[Microsoft's USB attachment guide](https://learn.microsoft.com/en-us/windows/wsl/connect-usb)
for the probe and UART interfaces.

Return to the [Devkit tutorial](../docs/getting-started.md#external-host-tools)
to build `apdu-tool` and the kernel, then follow its physical Pico startup
section for the programming commands.

## Step-By-Step Validation And Troubleshooting

### Identify The Host

Start each diagnostic section from the repository root unless it explicitly
specifies another directory. If the failing command changed directory, open
a fresh terminal at the root before following these checks.

On Ubuntu or WSL:

```bash
cat /etc/os-release
uname -m
```

On macOS:

```bash
sw_vers
uname -m
xcode-select -p
brew --prefix
```

Record this output when asking for help. Package names, Python availability and
Homebrew paths depend on the host version and architecture.

### Validate Python Before Running QEMU `configure`

The pinned Pico QEMU fork requires Python 3.12 or newer. Check the exact
interpreter selected by the shell:

```bash
command -v python3
python3 --version
python3 -c 'import sys, venv, ensurepip; print(sys.executable)'
```

The last command must print an interpreter path without raising an exception.
If `venv` or `ensurepip` is missing on Ubuntu 24.04, run:

```bash
sudo apt update
sudo apt install python3-venv python3-pip
```

On macOS, validate the Homebrew interpreter independently of the shell's
`PATH`:

```bash
"$(brew --prefix python)/bin/python3" --version
"$(brew --prefix python)/bin/python3" \
  -c 'import sys, venv, ensurepip; print(sys.executable)'
```

To update an existing Homebrew Python installation:

```bash
brew update
brew upgrade python
```

Do not run `sudo pip`, change ownership of macOS-managed Python directories, or
modify Apple's system Python.

### Use A Supported Python Without Replacing The System Python

Never replace `/usr/bin/python3` or change its symlink on Ubuntu. System tools
depend on the Python selected by the distribution.

Ubuntu 24.04 users can install the supported interpreter and its virtual
environment module directly:

```bash
sudo apt update
sudo apt install python3.12 python3.12-venv
python3.12 --version
python3.12 -c 'import venv, ensurepip; print("Python environment: OK")'
```

Ubuntu 22.04 does not provide Python 3.12 in its standard repositories. The
recommended path is to use Ubuntu 24.04 or newer. If the host must remain on an
older release, install a parallel Python 3.12 or newer through the package or
version-management policy approved for that machine, leave `/usr/bin/python3`
unchanged, and pass its absolute path to QEMU:

```bash
cd tooling/qemu-rp2040-pico/build
../configure \
  --python=/absolute/path/to/python3.12 \
  --target-list=arm-softmmu
```

Validate any parallel interpreter before using it:

```bash
/absolute/path/to/python3.12 --version
/absolute/path/to/python3.12 \
  -c 'import sys, venv, ensurepip; print(sys.executable)'
```

### Validate Ninja, GLib And Pixman

```bash
command -v ninja
ninja --version
command -v pkg-config
pkg-config --modversion glib-2.0 pixman-1
```

Every command must succeed and print a path or version. On Ubuntu 24.04, repair
missing packages with:

```bash
sudo apt install ninja-build pkg-config libglib2.0-dev libpixman-1-dev
```

On macOS, use:

```bash
brew install ninja pkg-config glib pixman
```

### Recover From An Incomplete QEMU Configuration

A failed configure attempt may leave a partial virtual environment or Meson
state in `build`. Preserve it for diagnosis and start from a new directory:

```bash
cd tooling/qemu-rp2040-pico
mv build build.failed
mkdir build
cd build
```

If `build.failed` already exists, choose another backup name. Then rerun
`configure` with an explicit supported interpreter. On Ubuntu 24.04:

```bash
../configure \
  --python="$(command -v python3.12)" \
  --target-list=arm-softmmu
```

On macOS:

```bash
../configure \
  --python="$(brew --prefix python)/bin/python3" \
  --target-list=arm-softmmu
```

The first configuration may download QEMU's pinned Meson subprojects. If the
host uses a proxy or restricted network, make sure Git can reach the URLs
reported by `configure`.

### Understand Python, Meson And `distutils` Errors

Do not try to repair this build by installing the removed standard-library
`distutils` module. Python 3.12 removed it, and the current QEMU build does not
require users to install it. QEMU creates `build/pyvenv` and installs or reuses
the compatible Python tooling there.

Installing `setuptools` for a different Python installation does not change
the interpreter selected by QEMU. Always compare the path printed by
`command -v python3` with the `python determined to be` line printed by
`configure`.

If a separately installed `python3.12` is already available, do not install
Python packages into an empty user virtual environment to guess what QEMU
needs. Check `python3.12 --version` and `python3.12 -c 'import venv, ensurepip'`,
then pass that interpreter explicitly to QEMU's `configure`. QEMU manages its
own `build/pyvenv` and Meson dependencies.

The Python documentation explains
[the removal of distutils](https://docs.python.org/3/library/distutils.html)
and [how virtual environments isolate Python packages](https://docs.python.org/3/library/venv.html).
If your host needs a separately installed interpreter, consult
[Python on Unix](https://docs.python.org/3/using/unix.html) and validate that
interpreter before selecting it with `--python`.

If configuration still fails, inspect the Meson log from the QEMU build
directory:

```bash
tail -n 80 meson-logs/meson-log.txt
```

Preserve the complete `configure` output as well as the log before replacing a
failed build directory.

### Diagnose A QEMU Compilation Failure

From `tooling/qemu-rp2040-pico/build`, first identify the failed stage:

```bash
test -f build.ninja
ninja qemu-system-arm
test -x qemu-system-arm
```

If `build.ninja` is absent, `configure` did not finish successfully. Read
`config.log` and the last `configure` error before trying Ninja. If
`build.ninja` exists but Ninja fails, rerun the specific target in verbose
mode:

```bash
ninja -v qemu-system-arm
```

The first `FAILED:` block normally identifies the missing header, library or
compiler invocation. Do not infer the cause from later cascading failures.

After a successful build, validate the exact binary used by Oxide SE:

```bash
test -x qemu-system-arm
./qemu-system-arm --version
./qemu-system-arm -machine help | grep raspi-pico
```

### Validate The `build-fae` Prerequisites

From the Oxide SE repository root:

```bash
command -v rustup
command -v cargo
rustc --version
cargo --version
rustup component list --installed | grep rust-src
command -v arm-none-eabi-gcc
command -v arm-none-eabi-ld
arm-none-eabi-gcc --version
```

If the ARM compiler is missing on Ubuntu 24.04:

```bash
sudo apt install gcc-arm-none-eabi binutils-arm-none-eabi
```

On macOS with Homebrew:

```bash
brew install arm-none-eabi-gcc
```

Then run the same build used by the readiness check:

```bash
cargo build \
  --manifest-path tooling/build-fae/Cargo.toml \
  --bin build_fae_rust
```

For `build-fae` behavior outside Oxide SE, consult its own
[getting-started guide at the pinned revision](https://github.com/2xs/build-fae/blob/e5fe5f460a17b77c9e0925eea19f35541f1de026/docs/getting-started.md).
The same guide is available locally at
`tooling/build-fae/docs/getting-started.md` after initializing the submodule.

### Collect A Useful Failure Report

Include the output of the applicable commands below instead of reporting only
the final Python or Meson exception:

```bash
cat /etc/os-release 2>/dev/null || sw_vers
uname -m
command -v python3
python3 --version
python3 -c 'import sys, venv, ensurepip; print(sys.executable)'
command -v ninja
ninja --version
command -v pkg-config
pkg-config --modversion glib-2.0 pixman-1
command -v arm-none-eabi-gcc
rustc --version
cargo --version
```

For QEMU configuration failures, also include:

```bash
tail -n 80 tooling/qemu-rp2040-pico/build/meson-logs/meson-log.txt
```

State the command that failed and attach its complete output. This distinguishes
an unsupported interpreter, a missing Python module, a missing native library,
and an actual source-build failure.
