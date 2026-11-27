# Devkit Distribution

The `devkit-2026.11.27` bundle contains empty development firmware for
Raspberry Pi Pico 1 (RP2040, 2 MiB flash) and Pico 2 (RP2350, 4 MiB flash).
The [downloads page](https://oxide-se.github.io/downloads/) lists both ELF
and UF2 images and their `SHA256SUMS`. Use the
[Getting Started download commands](getting-started.md#alternative-download-precompiled-images)
to verify the images, then build your Rustlet and APDU client from the
`v1.0.0-beta.2` source tag.

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
version 2.3.1 for this bundle. `--picotool /path/to/picotool` selects its
executable. The script takes ELF load segments at their physical flash
addresses, fills the rest of flash with `FF`, invokes picotool with the
board's family ID, and verifies every UF2 header and payload against that
complete flash image. Pico2 uses the ARM Secure family, matching its image
definition; its UF2 also includes picotool’s RP2350-E10 workaround block.
UF2 generation requires picotool only on the packaging machine;
a developer copying the supplied UF2 does not need it.

The full-flash policy makes BOOTSEL installation equivalent to the tutorial's
OpenOCD erase/program sequence. After copying the UF2, open the APDU UART
connection and reset the Pico to receive a fresh ATR. Installation over USB
and runtime communication over UART are distinct operations.
