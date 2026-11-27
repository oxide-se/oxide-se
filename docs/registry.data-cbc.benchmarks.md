# Pico1: encryption of Data bodies only

The [registry performance guide](registry.flash-reference-migration.md#run-the-current-
performance-campaign) shows how to collect comparable measurements with the current
checkout.

Historical comparison against the [header-CMAC/CRC and fast-XIP baseline](registry.fast-xip.benchmarks.md). The same Pico 1, clock rates, registry geometry and logical workload were used. Intrinsic times exclude APDU transport. The baseline values come from the previous physical campaign.

| Operation | Before (ms) | Encrypted Data (ms) | Change | n after | p95 after | Max after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Create 244-byte Data — preparation + commit | 94.833 | **132.391** | +39.6 % | 1 | 132.391 | 132.391 |
| Replace 244-byte Data — preparation + commit | 97.679 | **134.560** | +37.8 % | 14 | 237.010 | 237.010 |
| Read empty Data (lookup without AES) | 0.254 | **0.270** | +6.3 % | 15 | 0.324 | 0.324 |
| Read warm 17-byte Data | 0.335 | **12.912** | +3754.3 % | 15 | 13.019 | 13.019 |
| First 17-byte read after reboot | 0.344 | **38.394** | +11060.9 % | 2 | 38.556 | 38.556 |
| Read warm 244-byte Data | 0.814 | **23.010** | +2726.8 % | 15 | 23.354 | 23.354 |
| Read 4 KiB by ranges | 18.023 | **297.671** | +1551.6 % | 3 | 298.099 | 298.099 |
| Partial 4 KiB Data read (33 bytes max) | 0.809 | **8.044** | +894.3 % | 27 | 18.384 | 18.389 |
| Delete — commit | 56.066 | **56.287** | +0.4 % | 15 | 56.493 | 56.493 |
| Finalize 10 KiB LOAD | 407.101 | **406.644** | -0.1 % | 3 | 406.885 | 406.885 |
| Recovery with noise | 1262.181 | **1255.728** | -0.5 % | 3 | 1257.126 | 1257.126 |
| Scan with noise | 779.252 | **778.332** | -0.1 % | 3 | 779.586 | 779.586 |
| Recovery near capacity | 1432.511 | **1426.853** | -0.4 % | 3 | 1427.134 | 1427.134 |
| Rollback | 0.960 | **1.507** | +57.0 % | 15 | 1.661 | 1.661 |
| Savepoint rollback | 0.663 | **0.806** | +21.6 % | 15 | 0.840 | 0.840 |

Writes compare preparation + commit for each observation: the Data writer now programs its pages before BOSS publication. Comparing commit alone would hide that transfer. AES padding reduces usable single-page Data capacity from 216 to 208 bytes; physical placement and recycling may therefore differ despite identical logical load. There is only one 244-byte creation observation. Nested metrics are not additive, except for this sum of two distinct phases. Observed maxima are not real-time guarantees. LOAD finalization excludes download. The first nonempty read after reboot includes Data key derivation, performed once per boot. Raw keys are retained, but their expanded AES schedules are not: the body key is expanded once per range; initial IV calculation separately uses Kiv for block zero. Small changes on unencrypted paths may include code placement and flash object layout effects.

The first Data version used block-by-block CBC: reading 244 bytes on this same Pico1 took 36.931 ms (median of 15). Batching with a single body-key expansion per range reduces this to 23.010 ms, or -37.7%. This optimization does not change the ciphertext.

## RAM

Reading allocates no buffer proportional to object size: complete blocks are decrypted into the destination, with a 16-byte temporary block for edges and 16 bytes of chaining state. Internal AES/KDF stack use is included in the global stack maximum below. There is no full plaintext cache or allocation in `read_range`. Even small Data references remain in flash after publication and reboot. The object enum and journal sizes do not decrease: key/state variants retain their existing arrays.

| RAM measurement | Before (bytes) | After (bytes) | Difference |
| --- | ---: | ---: | ---: |
| Static data (.data + .bss) | 23980 | 24076 | +96 |
| SRAM-executed code | 4672 | 6564 | +1892 |
| Observed campaign stack peak | 3904 | 3904 | +0 |

The watermark is cumulative per boot and sampled outside timed operations. It measures the complete scenario peak, not an isolated read cost. ELF sections exclude reserved stack and heap. Derived keys and the seed counter have fixed per-boot size; no additional RAM depends on Data size.

## Behavior and validation

Internal API: `object.read_range(i, &mut destination[..n])`. It returns the number of extracted bytes, bounded by EOF. It also works for keys and instance/SD states, which remained unencrypted in this version; LOAD is excluded and BOSS is not exposed through this API. No Rustlet syscall is added. Authority checks remain the caller's responsibility.

Headers remain CMAC-authenticated. The compact Data header carries its length and a 64-bit seed; its CBC IV binds the seed to physical position. Other formats remain unencrypted. CRC64 covers the encrypted body and padding; the body is not cryptographically authenticated in this version. Unchanged references retain their seed without reencryption. See `docs/registry.contracts.md` for details.

The oxi-core `aes_cbc_decrypt_range_into` primitive expands the key once and uses batched AES processing (two blocks on Pico1), directly between flash and the destination. CBC reads use the preceding ciphertext block as IV and decrypt only requested blocks. Writes use the destination page and retain chaining across pages. The scanner keeps the rule: authenticated header → skip the extent; otherwise → advance one page.

- Host: 95 oxi-core and 231 kernel tests passed, covering ranges, edges, EOF, preservation of the rest of the destination, keys/states, nonce, ciphertext, CRC, scanning, and transactions.
- Pico1: 2258 functional checks before the CBC read optimization; QEMU: 2258 with the optimized primitive. Prefix cuts, repeated recovery, and 192 replacements with recycling. The injector counts prefixes across streamed Data pages.
- Final Pico1 version: 495 main observations with read-value assertions, followed by LOAD, large Data, unaligned ranges, noise, and near-capacity scenarios. CBC optimization leaves writing/recovery unchanged; redundant writes of an already-empty object are avoided.
- Physical large Data: no capacity rejection, final object size 8193 bytes, as in the baseline. The cumulative stack maximum during the large-Data boot remains 3504 bytes for 4 and 8 KiB (3496 in the baseline); this is not an isolated measurement of each read.
- These injections are not physical power-cut or brownout tests.
