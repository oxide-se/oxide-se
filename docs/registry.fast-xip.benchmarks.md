# Pico1: fast XIP restoration and registry benchmarks

The [registry performance guide](registry.flash-reference-migration.md#run-the-current-
performance-campaign) shows how to collect comparable measurements with the current
checkout.

18 October 2026. Comparison of the header-CMAC / body-CRC registry before and after restoring fast XIP mode. Same Pico1, CPU 12 MHz, timer 1 MHz, 64 KiB area, 256-byte pages, 4 KiB sectors, and logical workload. Intrinsic times in milliseconds exclude transport.

| Operation | Before XIP fix | After | Change | n after | p95 after | Max after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Replace 244 bytes — commit | 344.851 | **94.648** | -72.6 % | 14 | 197.117 | 197.117 |
| Create 244 bytes — commit | 333.797 | **91.083** | -72.7 % | 1 | 91.083 | 91.083 |
| Delete — commit | 199.417 | **56.066** | -71.9 % | 15 | 56.371 | 56.371 |
| Read 244 bytes | 2.100 | **0.814** | -61.2 % | 15 | 0.842 | 0.842 |
| Read 4 KiB by ranges | 73.801 | **18.023** | -75.6 % | 3 | 18.107 | 18.107 |
| Partial 4 KiB Data read | 2.529 | **0.809** | -68.0 % | 27 | 1.074 | 1.080 |
| Finalize 10 KiB LOAD | 579.753 | **407.101** | -29.8 % | 3 | 407.487 | 407.487 |
| Recovery with noise | 1261.996 | **1262.181** | +0.0 % | 3 | 1262.695 | 1262.695 |
| Scan with noise | 779.201 | **779.252** | +0.0 % | 3 | 779.773 | 779.773 |
| Recovery near capacity | 1431.125 | **1432.511** | +0.1 % | 3 | 1432.539 | 1432.539 |
| Rollback | 4.445 | **0.960** | -78.4 % | 15 | 0.998 | 0.998 |
| Savepoint rollback | 3.173 | **0.663** | -79.1 % | 15 | 0.704 | 0.704 |

There is only one 244-byte creation observation; maxima are observed values, not real-time guarantees. LOAD finalization excludes download. Nested internal metrics are not additive. The comparison measures complete images. The three checked read functions retain exactly the same addresses, sizes, and machine bytes.

## Fix

The driver retains the ROM programming/erasure primitives. After the ROM flush, it calls `__RestoreXip`, an SRAM copy of the same boot2 used at startup, then restores the caller's exact PRIMASK. A shared macro guarantees identical bytes in both copies. The existing critical section is loaded at startup: one 256-byte code copy in SRAM and in the flash image, with no per-operation buffer or copy. The registry format and protections are unchanged.

The physical `kernel_flash` test checks separately after erase and program: SSI CTRLR0=0x005f0300, BAUDR=2, SPI_CTRLR0=0x2022, XIP CTRL=3. Reset boot2 is unchanged and its RAM copy is byte-for-byte identical in the measured ELF. Flash-path disassembly confirms restoration from SRAM before interrupts are reenabled. The full critical section grows from 4460 to 4672 bytes, a net increase of 212 bytes after removing the previous path.

Internal flash budgets were recalibrated with 50 measurements per primitive on Pico1: program min/max 4.217/4.234 ms; erase 46.795/52.254 ms. Only rows 240/241 and their budgets changed; other groups and their provenance were preserved.

## Fixed-state reads without a new firmware probe

The exact before/after binaries are replayed with eleven identical objects, twenty reading rounds, then two reboots without writing. The host scenario reads the existing ReadData counter; no decomposition instrumentation changes the measured code.

| 244-byte read | Before (µs) | After (µs) | Change | n per version |
| --- | ---: | ---: | ---: | ---: |
| After creation | 1689.0 | 781.0 | -53.8 % | 20 |
| After reboot | 780.0 | 779.5 | -0.1 % | 40 |

## Validation and traceability

- Host: 94 oxi-core and 225 kernel tests passed; registry-boundary checks and `git diff --check` passed.
- Physical flash: persistent A5/5A scenario across three boots and XIP checks after each erase/program passed.
- QEMU: 2272 functional checks passed (cuts, reboot, recycling).
- Physical Pico1: 2272 functional checks passed, including interrupted writes/erases, repeated reboots, 192 successive replacements, and the durable graph.
- Complete physical matrix: 495 main observations, followed by LOAD, large Data, noise, and capacity.

Prefix injections do not qualify physical power cuts or brownouts.

The exploratory decomposition probes are absent from these firmware images.
