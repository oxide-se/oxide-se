# Pico2 SRAM repeatability experiment

This opt-in kernel module measures startup repeatability, not cross-device
uniqueness, cryptographic entropy, or resistance to physical attacks.

## Memory contract

OxideSE has a global 64 KiB RAM envelope on Pico2, starting at 0x20000000.
The last 16 KiB is reserved for RAM-executed kernel code; stack, globals and
allocator share the first 48 KiB. This is an OxideSE budget, not the physical
RP2350 SRAM capacity. The experimental privileged read is outside this envelope;
no new userland MPU access is granted.

The probe reads the first 1020 bytes of physical bank SRAM4, with 255 volatile
32-bit reads at `0x20040000 + 16*i`. The last word is at `0x20040fe0`.
Bytes within each word are little-endian. The RP2350 has no non-striped mirror.
Banks 4–7 share the SRAM1 power domain; do not assume individual bank power
switching. Normal allocator use cannot reach this range. Before interpreting
cold-start results, check the boot path, debugger and residual power: software
writes or SRAM retention can create an artificial stable fingerprint.

Reference: [RP2350 datasheet, section 4.2](https://datasheets.raspberrypi.com/rp2350/rp2350-datasheet.pdf).

## Build and flash

```sh
cargo run --offline build --config configs/config_sram_fingerprint.toml raspi-pico2
```

Start the ATR receiver in another terminal before flashing/resetting:

```sh
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 \
  --connect-timeout 120s --atr-timeout 120s atr
```

Flash only the image sectors, preserving the registry:

```sh
openocd -f interface/cmsis-dap.cfg -c 'set USE_CORE 0' \
  -f target/rp2350.cfg -c 'adapter speed 1000' -c init \
  -c 'reset init' \
  -c 'flash write_image erase target/kernel/firmware/kernel.elf' \
  -c 'verify_image target/kernel/firmware/kernel.elf' \
  -c 'reset run' -c 'poll off' -c 'rp2350.dap dpreg 0x4 0' -c shutdown
```

For a reset without flashing:

```sh
openocd -f interface/cmsis-dap.cfg -c 'set USE_CORE 0' \
  -f target/rp2350.cfg -c 'adapter speed 1000' -c init \
  -c 'reset run' -c 'poll off' -c 'rp2350.dap dpreg 0x4 0' -c shutdown
```

Disabling polling and releasing DAP power requests must precede shutdown.
Otherwise the debugger can prevent SRAM power transitions (6985). Receive the
ATR before sending APDUs. After a reboot, use B1 directly with the stored mask.

## Private command protocol

B0 enrolls, B1 reconstructs, and B2 reads the stored mask. They replace the former
B4/B5 instruction numbers; the old cold-campaign and B3 group commands
have been removed. Old cold-campaign objects DF00/DF01 are no longer used;
this firmware does not automatically delete existing objects.

The CLI takes six header fields, including zero LC for commands without data.
These commands are unauthenticated diagnostics; do not include the module in
an image protecting a secret fingerprint. The current experiment still uses
1020 bytes and returns 2040 bits, not the proposed 512-byte/256-bit boot PUF with
AES verification.

## Enroll fixed positions (B0) and reconstruct by majority vote (B1)

These commands use a separate DATA object, tag DF02 under the root SD. It holds
1020 raw mask bytes where zero is selected and one is
rejected. Old 32 KiB masks are rejected with 6985 by B1/B2. Run B0 again to enroll
the reduced window; firmware flashing alone does not replace DF02.

| Command | P1 | P2 | Response |
| --- | --- | --- | --- |
| `80 B0 P1 P2 00 04` | Cycle count divided by 256, 1..255 | Off hold time, 1..255 ms | Total selected bit count, four bytes, big-endian |
| `80 B1 P1 P2 00 FF` | Odd vote count, 1..255 | Off hold time, 1..255 ms | 255 bytes of fingerprint, no count prefix |

B2 takes P1=0..3, P2=0, LC=0 and Le=FF. It returns the raw persisted mask,
not SRAM values or majority-voted fingerprint bits, and performs no power cut.
Zero mask bits identify selected positions; one bits identify rejected positions.
B2 does not change the mask. Wrong parameters return 6A80, wrong Le returns
6CFF, and missing or incompatible enrollment returns 6985.

| B2 P1 | Inclusive mask byte offsets |
| --- | --- |
| 0 | 0–254 |
| 1 | 255–509 |
| 2 | 510–764 |
| 3 | 765–1019 |

```sh
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B2 00 00 00 FF
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B2 01 00 00 FF
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B2 02 00 00 FF
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B2 03 00 00 FF
```

For B0/B1, zero parameters and even B1 vote counts return 6A80. B1 returns 6985 if DF02
is missing, has the wrong size, contains fewer than 2040 selected positions,
or a power transition fails. Le is validated before acquisition: an incorrect
length returns 6C04 (B0) or 6CFF (B1), without power cuts or registry writes.
The kernel response limit remains 255 bytes; B1 uses Le=FF.

B0 captures one current reference, initializes a mask to zero, then performs
exactly P1*256 cuts and comparisons against that reference. Preloads alternate
00/FF. Only after all cycles succeed does it stage the DATA pages and publish
one BOSS. Interrupting acquisition leaves the previous enrollment intact;
publication uses the existing crash-consistent DATA/BOSS writer. A new B0
replaces enrollment; repeating B1 does not change selection.

B1 selects the first 2040 zero-mask positions once, in increasing byte order
and bit 0..7 within each byte. It performs exactly P1 cuts, with alternating
00/FF preloads, and counts ones at those fixed positions after each power-on.
It outputs one iff ones > P1/2, packed bit 0 upward. The pre-command SRAM
sample is not an extra vote. Odd P1 avoids ties. There is no error-correcting
code; majority voting does not guarantee perfectly repeatable output.

B0/B1 use the existing experimental SRAM0 scratch range. The working buffers
are 8160 and 2040 bytes: B0 uses 1020 bytes of each for reference and mask,
while B1 uses them for 2040 u32 positions and 2040 u8 vote counters. No large
kernel-stack arrays are needed; both buffers are cleared on return. T=0 NULL emission remains active while acquiring. Large B0 requests may take
hours: 255*256 cuts at 255 ms imply at least 16646.4 seconds of off hold alone.

Example: enroll with 512 cycles of 1 ms, then reconstruct with 15 votes of 1 ms:

```sh
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B0 02 01 00 04
cargo run --offline -p apdu_tool -- --serial /dev/cu.usbmodemXXXX:115200 raw 80 B1 0F 01 00 FF
```

## Functional test

```sh
cargo run --offline test sram_fingerprint raspi-pico2 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 --allow-destructive
```

This test erases flash, including enrollment, and creates a temporary mask.
It checks missing enrollment, invalid parameters, rejection of removed
instructions, enrollment with 512 cuts at 1 ms, reconstruction with 1/15/255
votes, and reconstruction after three resets. The four mask fragments must reproduce the
enrollment count and remain byte-identical across those resets. It releases OpenOCD power
requests during acquisition. It does not require identical noisy fingerprints
and does not qualify a PUF. Run it before a measurement campaign.
The runner halts the CPU at completion; use the reset command above to resume.

The two scratch buffers occupy 0x20020000..0x200227d8 in powered SRAM0,
outside the kernel's 64 KiB and OpenOCD's work area. MPU permissions are unchanged.

## Repeatability measurements

Enroll once with B0 (P1=02 for 512 comparisons), then freeze the mask and collect
B1 responses. Keep vote count, off time, preloads and board identity in the
measurement record. Repeat after complete power removal as well as software
bank cycling. A reset alone is not a physical SRAM power cycle.

A single board and finite observations do not establish uniqueness, entropy,
or independence. Power-off durations and preloads can affect retention.
Historical campaign scripts use the former protocol and must not be replayed
against this firmware without adapting their instruction numbers and semantics.
