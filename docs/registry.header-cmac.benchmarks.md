# Registry: CMAC header and CRC64 body — Pico1, 18 October 2026

The [registry performance guide](registry.flash-reference-migration.md#run-the-current-
performance-campaign) shows how to collect comparable measurements with the current
checkout.

Comparison on the same Pico1 at 12 MHz, with a 1 MHz on-device timer, 64 KiB area, and 256-byte pages. Values are intrinsic medians in milliseconds, excluding APDU transport. Logical load is identical; format differences change physical positions, occupancy, and recycling timing.

| Operation | Old CRC | Full encryption, initial campaign | Header CMAC + CRC | Change vs CRC | n CRC / new | New p95 | New observed maximum |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Replace 244 bytes — commit | 410.352 | 6328.486 | **344.851** | -16.0 % | 14 / 14 | 654.625 | 654.625 |
| Create 244 bytes — commit | 354.122 | 5184.033 | **333.797** | -5.7 % | 1 / 1 | 333.797 | 333.797 |
| Delete object — commit | 345.132 | 5252.679 | **199.417** | -42.2 % | 15 / 15 | 201.911 | 201.911 |
| Reread 244 bytes | 1.344 | 1.930 | **2.100** | +56.2 % | 15 / 15 | 2.493 | 2.493 |
| Read 4 KiB in 244-byte ranges | 47.522 | 10231.250 | **73.801** | +55.3 % | 3 / 3 | 75.215 | 75.215 |
| Partial read within 4 KiB Data | 0.975 | 574.843 | **2.529** | +159.4 % | 27 / 27 | 4.683 | 5.039 |
| Finalize 10 KiB LOAD | 511.748 | 2443.518 | **579.753** | +13.3 % | 3 / 3 | 587.522 | 587.522 |
| Recovery with flash noise | 923.507 | 11226.602 | **1261.996** | +36.7 % | 3 / 3 | 1262.123 | 1262.123 |
| Scan with noise | 468.376 | 6979.766 | **779.201** | +66.4 % | 3 / 3 | 779.337 | 779.337 |
| Recovery near capacity | 1055.021 | 12412.193 | **1431.125** | +35.6 % | 3 / 3 | 1432.507 | 1432.507 |
| Rollback transaction | 7.136 | 6.004 | **4.445** | -37.7 % | 15 / 15 | 4.825 | 4.825 |
| Savepoint rollback | 3.310 | 2.350 | **3.173** | -4.1 % | 15 / 15 | 3.563 | 3.563 |

Each campaign has only one 244-byte creation observation: this is not a distribution. Maxima are campaign observations, not real-time bounds. Nested internal operations are not additive. The full-encryption column is from the initial complete campaign; its later optimization yielded 2918.738 ms in a single replacement replay, without a new complete matrix.

The new format authenticates only the 16 header-metadata bytes, with domain separation and the actual address. The tag occupies 16 bytes; the body is plaintext with a trailing CRC64. Each page is programmed once. Unchanged references and flash views are reused; CMACs for already-validated headers are cached in 64 bytes of metadata for this area and invalidated before any program/erase. No body is copied into a cache.

The Data threshold is 216/217 payload bytes for one/two pages (32 header bytes + 8 CRC bytes). BOSS entries retain the CRC baseline layout: 44 bytes with 8-byte references. Measured LOAD finalization excludes the transport exchanges required for downloading.

- 244-byte replacement APDU (before-final), including transport: 836.649 ms, n=14.
- 244-byte replacement APDU (after-final), including transport: 6703.146 ms, n=14.
- 244-byte replacement APDU (final), including transport: 784.201 ms, n=14.

An intermediate campaign was interrupted after identifying CMAC recalculations during recycling; it is not used in the final table. Stack is measured cumulatively per boot, with a different crypto probe: no maximum-heap comparison or absolute memory/time bound is claimed.

Publication gains include removal of redundant checks and reuse of validated references. This comparison measures complete registry versions, not the isolated cost of a CMAC. Reads and recovery remain slower than the CRC baseline, as shown in the table.

## Validation

- Host tests: 225 kernel tests, 94 oxi-core tests, 87 xtask unit tests and its 6 integration tests passed.
- QEMU RP2040 and physical Pico1/OpenOCD functional campaigns: **2272 checks passed on each backend**, including 192 successive replacements for recycling.
- Pico1/OpenOCD performance campaign: complete, with 495 main observations, then LOAD, range reads, noise, and capacity scenarios.
- Registry-boundary check and `git diff --check`: passed.

Tests cover header alterations and address relocation, body CRC, 216/217-byte page thresholds, interrupted BOSS writes/publications, repeated restarts, and interrupted recycling erases. Host fixtures explicitly check that a modified body with a recalculated CRC is accepted: authentication covers only the header, as required by this version's scope.

The subsequent [physical read breakdown](registry.read-performance.md) identifies a slow XIP mode retained after writes and sensitivity to code/cache placement. The read differences above remain those of this campaign; they are not the cost of a CMAC executed on every read.

The [post-fix XIP benchmarks](registry.fast-xip.benchmarks.md) report the gains and physical validation of fast-mode restoration.
