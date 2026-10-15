# Devkit Distribution

The local delivery `devkit-2026.10.15` contains the empty development firmware
for Raspberry Pi Pico1 (RP2040, 2 MiB flash) and Pico2 (RP2350, 4 MiB flash).
The four ELF/UF2 images and an image-only `SHA256SUMS` are published on the
[Oxide SE downloads page](https://oxide-se.github.io/downloads/) under
[`devkit-2026.10.15`](https://oxide-se.github.io/downloads/devkit-2026.10.15/SHA256SUMS).
The local output directory is
`.local/releases/devkit-2026.10.15/`.

## Local Delivery Contents And Identity

- `oxide-se-devkit-pico1.elf`, `oxide-se-devkit-pico2.elf`: OpenOCD images;
  the Pico1 ELF also supports the optional Oxide SE QEMU Pico1 variant.
- `oxide-se-devkit-pico1.uf2`, `oxide-se-devkit-pico2.uf2`: USB BOOTSEL images
  that reset the entire declared flash, including the persistent registry.
- `oxide-se-devkit-sources.tar.gz`: matching source snapshot, including
  `tooling/build-fae`, the tutorial Rustlet and the APDU client.
- `source.patch`: tracked changes relative to the recorded base Git revision;
  new files are supplied in the source archive, which is the authoritative snapshot.
- `manifest.json`: bundle version, firmware version, ABI, build configuration,
  tools, provenance, file hashes and validation results.
- `SHA256SUMS`: checksums for the delivery files.
- `PUBLISHING.txt`: handoff instructions for website publication.

The bundle identifier is distinct from the firmware's ATR version, **1.0 beta**.
These images are built from the refreshed public `v1.0.0-beta.1` snapshot.
The exact source commit and file hashes are recorded in the local manifest.
The archive and provenance files are release records, not prerequisites for
the Getting Started tutorial. Developers use the repository to compile their
FAE and host tool. A first Cargo build may need network access to download
dependencies.

For the published images, use the
[Getting Started download commands](getting-started.md#get-the-rustlet-development-kit-firmware).
The public `SHA256SUMS` covers only the four images. No source archive or
public manifest is required by the tutorial. The full local delivery retains
its own checksums and provenance for release maintenance.

Continue with [Getting Started](getting-started.md). You compile your own FAE
and load it dynamically with `apdu-tool`. The main tutorial builds the kernel
locally, with the published images as an alternative. QEMU installation and
compilation are not prerequisites.

## Build And Package

Both images use `configs/config_devkit.toml`: an open development root,
no secure channel, no Issuer SD and no preinstalled Rustlet. This is a
development policy, not a production configuration.

Build each target and copy its output before building the other target,
since the output path is shared:

```sh
cargo run -- build --config configs/config_devkit.toml raspi-pico1
cp target/kernel/firmware/kernel.elf oxide-se-devkit-pico1.elf
cargo run -- build --config configs/config_devkit.toml raspi-pico2
cp target/kernel/firmware/kernel.elf oxide-se-devkit-pico2.elf

python3 scripts/build_devkit_uf2.py pico1 oxide-se-devkit-pico1.elf oxide-se-devkit-pico1.uf2
python3 scripts/build_devkit_uf2.py pico2 oxide-se-devkit-pico2.elf oxide-se-devkit-pico2.uf2
```

UF2 generation uses the official [Raspberry Pi picotool](https://github.com/raspberrypi/picotool),
version 2.3.1 for this delivery. `--picotool /path/to/picotool` selects its
executable. The script takes ELF load segments at their physical flash
addresses, fills the rest of flash with `FF`, invokes picotool with the
board's family ID, and verifies every UF2 header and payload against that
complete flash image. Pico2 uses the ARM Secure family, matching its image
definition; its UF2 also includes picotool’s RP2350-E10 workaround block.
UF2 generation requires picotool only on the packaging machine;
a developer copying the supplied UF2 does not need it.

The full-flash policy makes BOOTSEL installation equivalent to the tutorial's
OpenOCD erase/program sequence. Keep the APDU UART connection open before
copying the UF2, because the boot ATR is emitted once. Installation over USB
and runtime communication over UART are distinct operations.

## Publication

Publish the files together in an immutable directory named for the bundle
version. Preserve their names and contents, publish the image `SHA256SUMS`,
and link both ELF and UF2 choices. Retain the local manifest and source
provenance with the release records.
Keep validation evidence with the release. Do not silently replace a file
under an existing version: issue a new bundle version and new checksums.
The local manifest records which hardware/emulator paths were actually
validated; format verification alone is not a physical USB BOOTSEL test.
