# Pico1: registry read breakdown

The [registry performance guide](registry.flash-reference-migration.md#run-the-current-
performance-campaign) shows how to collect comparable measurements with the current
checkout.

18 October 2026. Each of the six main replays passed 660 checked reads: eleven identical objects, twenty rounds without intervening writes, then two restarts retaining the same logical state. CPU 12 MHz; times below are medians in microseconds. Body values (244 bytes) and metadata are in RAM, as confirmed by recorded addresses, both before and after reboot. Flash formats differ; requested objects do not.

## Original binaries without new probes

The exact images from previous campaigns are replayed with the new fixed-state scenario. The existing last ReadData sample is read without rebuilding those images.

| State | Old CRC | Header CMAC | Difference | Samples per version |
| --- | ---: | ---: | ---: | ---: |
| After eleven creations | 740.0 | 1689.0 | +128.2 % | 20 |
| After reboot, no further write | 672.0 | 780.0 | +16.1 % | 40 |

The previous campaign's +56.2% concerned a different sequence, with interleaved writes and reads, measuring 1344 versus 2100 µs. It is not a fixed CMAC cost per read. New measurements do not retroactively replace previous results.

## Breakdown with identical timestamps

First probe pair, before adding XIP counters. Samples are recorded after copying. Timer calls and changed code placement perturb measurements; stage medians need not sum to the total median.

| Stage | CRC after writes | Header after writes | CRC after reboot | Header after reboot |
| --- | ---: | ---: | ---: | ---: |
| AID and registry borrow | 144.5 | 24.0 | 37.0 | 24.0 |
| Table lookup | 909.0 | 1218.0 | 515.0 | 529.0 |
| Data slice access | 244.0 | 73.0 | 33.0 | 13.0 |
| Size check and copy | 238.0 | 221.0 | 165.0 | 165.0 |
| Instrumented total | 1467.5 | 1576.5 | 761.0 | 793.0 |

The search source is identical. In the first two instrumented ELFs, `find_slot_by_identity` is 100 bytes and disassembles to the same instructions apart from relocated addresses. It is located at 0x10005b78 (CRC) and 0x10005ba4 (header); the called AID comparison is at 0x100121c8 and 0x100123f8. Reading computes neither CMAC nor CRC.

## Flash controller and cache: physical observations

The second probe pair resets saturating hardware counters before each window without changing flash mode. Addresses are checked against the [official XIP definitions](https://raw.githubusercontent.com/raspberrypi/pico-sdk/master/src/rp2040/hardware_regs/include/hardware/regs/xip.h). Counters include probe instructions; they are not search-only counters.

| State, identical in both versions | SSI CTRLR0 | BAUDR | SPI CTRLR0 | XIP CTRL |
| --- | --- | ---: | --- | --- |
| After programming | 0x1f0300 | 6 | 0x218 | 0x3 |
| After reboot | 0x5f0300 | 2 | 0x2022 | 0x3 |

| Probe with counters | Total CRC | Total header | CRC cache misses | Header cache misses |
| --- | ---: | ---: | ---: | ---: |
| After programming | 1286.0 | 2354.5 | 18.5 | 57.5 |
| After reboot | 741.5 | 878.0 | 23.0 | 66.0 |

## Interpretation and limitations

The oxi-core driver uses ROM primitives from a RAM-executed sequence. After programming and erasing, it ends with `flash_enter_cmd_xip()`: generic read mode remains active instead of the fast mode installed at startup. Both versions share this behavior. It amplifies the cost of cache misses for flash-executed code even when data is in RAM. The [official Raspberry Pi driver](https://raw.githubusercontent.com/raspberrypi/pico-sdk/master/src/rp2_common/hardware_flash/flash.c) also uses ROM to program/erase, then restores XIP through a RAM copy of boot2. Replacing ROM with a complete programming implementation is therefore unnecessary to fix restoration.

Measurements locate the dominant cost in searching and show substantial sensitivity to code placement and flash mode. They establish more cache misses in the new instrumented image. They do not attribute the earlier benchmark's 756 µs difference exactly to individual stages: probes change placement, and the fixed-state sequence differs from the previous matrix. Reporting the +56% as the cryptographic cost of a read would be incorrect.

The fix to qualify is restoration of fast XIP after flash operations. This campaign is diagnostic and does not modify the production driver. Temporary probes are removed from active code after archiving.

## XIP fix

Restoration was subsequently fixed in oxi-core: programming and erasing call an SRAM copy of firmware boot2 after the ROM flush and before restoring PRIMASK. The same macro assembles the two identical 256-byte copies; there is no per-write buffer or copy. Existing startup loads this copy with the critical-code section. The physical `kernel_flash` test checks fast XIP mode after both operations. The measurements above remain pre-fix results.

The [post-fix XIP benchmarks](registry.fast-xip.benchmarks.md) report the gains and physical validation of fast-mode restoration.
