# Measuring primitive execution behind SVC

The private `svc-profile` kernel module measures the crypto operations called
by SVC 9, 10, 11, 13, 14, 15 and 16. It also measures public-key derivation
and flash page programming/sector erasure. It uses a dedicated `kernel-only`
image (`configs/config_svc_profile.toml`); both the manifest resolver and the
firmware build reject this module in a GlobalPlatform image.

For function annotations, dependency review, partial updates and full-recalibration
triggers, follow [SVC performance maintenance](kernel.developer.guide.md#svc-performance-maintenance).

Run on a Pico1 or Pico2 reserved for tests (select the connected board):

```sh
cargo run -- extract-svc-profile raspi-pico1 \
  --on openocd --serial /dev/cu.usbmodem21402:115200 \
  --allow-destructive --update-budgets
```

The existing OpenOCD deployment erases firmware and persistent data. This
invocation compiles the diagnostic image, programs it, runs 89 cases with 50
samples each by default, writes `profiles/svc/raspi-pico1.toml`, and updates
`kernel/core/src/core/operation_timing/pico1.rs`. Using `raspi-pico2` selects
the separate Pico2 report and budgets. Without `--update-budgets`, it
only writes a capture (`profiles/svc/<board>.measurement.toml` by default).
`--all` is the default. `--svc 9 10 13` selects complete shared budget groups;
`--update-budgets` merges them with the canonical baseline while preserving
unselected groups and their capture provenance. `--samples N` selects 1–50 measurements per case
(P2 on the wire); the upper bound keeps all raw samples in one short response.
For a quick verification, use `--samples 2` without `--update-budgets`. `--output path.toml` changes the report destination;
`--probe-serial ID` selects a debug probe. The deployment/session machinery
performs the same cleanup as other target tests.

Other supported boards may collect measurements. Flash cases currently require
the Pico 256-byte page / 4096-byte sector geometry. QEMU can exercise the
protocol but must not calibrate hardware: budget updates currently require
Pico1 hardware at 12 MHz or Pico2 hardware at 150 MHz. An incomplete or failed campaign never updates
budgets; failed operations are not silently discarded from statistics. Completed
cases are checkpointed to a `.partial.toml` file after every response. This file
is removed after the complete report is saved and is never used to update budgets.

## Measurement protocol

The APDU is `80 0B P1 P2`, with four incoming bytes: big-endian `u16` input
length followed by big-endian `u16` output length. P2 is the number of samples
(1–50, zero is rejected). Request `24 + 4 * P2` response bytes.
P1 packs the variant in its high nibble and a profiling operation ID in its low
nibble: `P1 = (variant << 4) | operation_id`. These compact IDs map to SVCs:

| Operation ID | SVC / primitive | Variant |
|---|---|---|
| 1 | 9 / AES | 0 CBC encrypt, 1 CBC decrypt, 2 ECB encrypt, 3 ECB decrypt, 4 padded CBC encrypt, 5 padded CBC decrypt; add 8 for AES-256 |
| 2 | 10 / Random generation | 0 |
| 3 | 11 / AES-CMAC | 0 AES-128, 8 AES-256 |
| 4 | 13 / P-256 | 0 key generation, 1 public-from-private (internal primitive) |
| 5 | 14 / P-256 ECDH | 0 |
| 6 | 15 / HKDF-SHA256 | 0 |
| 7 | 16 / X9.63 SHA256 KDF | 0 |
| 8 | 240 / Program flash page (internal primitive) | 0 |
| 9 | 241 / Erase flash sector (internal primitive) | 0 |

For example, `P1=0x14, P2=0x02` measures public-from-private twice;
`P1=0xD1, P2=0x0A` measures AES-256 padded CBC decryption ten times.

AES, CMAC and RNG use lengths 16, 64, 256 and 1024; AES inputs must be
block-aligned. Padded encryption reserves another block; padded decryption
first prepares a valid ciphertext outside the timed interval. KDF cases cross
those input lengths with output lengths 32, 128 and 1024, using fixed 32-byte
salt/info where applicable. P-256 and flash require zero length parameters.
Unused output lengths and unsupported variants are rejected before work starts.

The response is big-endian:

- Bytes 0–3: version (2), actual SVC number, variant, successful sample count (P2).
- Five `u32`: CPU frequency, timer frequency, minimum microseconds, maximum
  microseconds, mean microseconds (rounded upward).
- P2 `u32`: raw elapsed timer ticks, including the first sample.

The host recomputes all statistics and checks exactly P2 NULL bytes were
received. No cryptographic output or private key is returned.

## What the clock measures

Each sample uses the hardware monotonic clock with interrupts masked around
the primitive, then restores the previous interrupt mask. It excludes SVC
entry/exit, parameter validation, host traffic, test-data setup and verification.
It measures the primitive including its internal work, such as RNG during key
generation. Buffers and private scalars vary between samples. The first sample
is retained; no warm-up outliers are discarded.

A scoped guard suspends automatic NULL emission from both timer and operation
anticipation, without changing watchdog policy. The module sends a manual NULL
before each sample's preparation, outside the measured interval and only while
the transport window is open. Suppression remains active through response preparation, including an error
status; the first real response byte closes the window and restores normal
emission. This prevents an overdue timer from appending a 51st NULL after a
long final sample. One primitive that lasts beyond a NULL interval still
cannot emit a NULL internally; the host allows up to 120 seconds of silence per measurement for these
diagnostic calls. In production, an operation whose budget exceeds 500 ms
receives one anticipated NULL if the separate APDU watchdog admits the
operation; there is no extra emission mechanism inside the opaque primitive.

The module reserves one flash sector before registry initialization. Each page
measurement starts with erased storage. Each sector-erase measurement starts
with all 16 pages programmed. Preparation is excluded; persisted bytes are
checked after the timed operation. At the default 50 repetitions, page trials and erase trials
consume at least 100 erase cycles on the reserved sector.

## Using the results

The TOML report records the source revision, dirty-worktree flag, exact ELF
SHA-256, capture time, CPU/timer clocks, parameters and all raw samples.
Schema 2 keeps this provenance per budget group in `group_sources`; top-level
metadata describes only the most recent run when groups have different origins.
Legacy reports retain their actual metadata, with unknown build context left unknown. Values
characterize that firmware image and hardware configuration, not a universal
bound across builds or flash parts.

For AES, hash/KDF and RNG, the generator takes the largest observed maximum
among the shortest cases for each algorithm variant as the fixed cost. It then
chooses an integer microseconds-per-effective-byte slope high enough to cover
every recorded maximum. P-256 uses the largest maximum across key generation,
public derivation and ECDH; flash operations each use their own maximum.
A final check rejects any envelope below a recorded maximum. Means are for
performance analysis, not scheduling.

Effective bytes follow the kernel's existing accounting: AES uses input size
(or input + 16 for padding); HKDF uses `IKM + salt + (info + 64) * ceil(out/32)`;
X9.63 uses `(secret + info + 4) * ceil(out/32)`.

Each generated profile applies only to its own Pico board at the measured CPU
frequency.
Outside the measured sizes, the kernel takes the larger of the extrapolated
envelope and the original estimate. Other boards/clocks retain the original
table. The **20 ms engineering margin** is added separately when comparing
`now + budget + margin` with the **500 ms NULL deadline** and the separate
**10-second APDU watchdog deadline**.
