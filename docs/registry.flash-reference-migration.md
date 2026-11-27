# Flash-reference registry migration

## Run the current performance campaign

Use a dedicated Pico 1 with the OpenOCD and UART setup from the
[Getting Started guide](getting-started.md#start-a-physical-pico-through-openocd).
The command builds the current firmware and erases the board before collecting
the performance samples. Use the same board, clock and scenario when comparing
two public checkouts. Set `OXIDE_REGISTRY_PERF_SHORT=1` for the shorter sweep.

```sh
OXIDE_REGISTRY_PERF_CSV=registry.csv \
  cargo run test kernel_registry raspi-pico1 --on openocd --allow-destructive
```

The archived comparisons below describe historical firmware configurations.
Use measurements taken on the current checkout when reporting its performance.

## Required model

The mutable RAM registry is an index, not a cache of persisted object bodies.
At boot, reconstruct entries and references from the last valid BOSS
(`0x600DB055`). Read object metadata as needed, but do not retain copies of
serialized instance/Security Domain state or key material in registry slots.

Create or replace an object by writing its immutable flash body first, then
attaching its reference to the RAM registry. Publish the new BOSS only at
transaction commit. Unchanged objects retain their physical references.
Rollback restores references without physically undoing object writes.

The allocator must protect the union of objects reachable from the mutable RAM
registry and the last committed flash BOSS, plus that BOSS itself. Temporary
LOAD reservations and references retained by nested rollback scopes remain
protected until attached or released. An abandoned object becomes recyclable
when none of these roots reaches it. Sector erase must preserve every live
object sharing the sector. No orphan sweep is required for logical deletion.

## Implementation and validation stages

1. Record the current implementation's physical Pico1 timing and RAM baseline.
2. Replace owned state/key bodies with flash references; write new bodies before
   attachment and publish only index entries at commit. Keep the existing clear
   state/key format during this stage so its effects can be measured separately.
3. Extend destination-buffer extraction to every state/key consumer. Preserve
   authority checks and volatile-only target behavior. Remove redundant staging
   copies and body-sized undo snapshots.
4. Validate transactions, nested rollback, reset recovery, orphan reuse and
   sector pressure under QEMU Pico1. Measure the same workloads on physical
   Pico1, then commit the validated stage.
5. Encrypt Security Domain state, instance state and key bodies using bounded
   destination-buffer extraction. BOSS and LOAD remain clear. Validate under
   QEMU Pico1 and repeat physical benchmarks before committing.

Use intrinsic device timings rather than APDU transport timings. Compare full
mutation cost (body preparation plus BOSS publication), not commit alone.
Report static RAM, registry entry size, rollback storage and observed stack
high-water mark separately. Include small and page-boundary payloads, first and
warm reads, boot recovery with noise, and reuse near capacity. Avoid claiming
physical power-cut validation from software fault injection.

## Baseline

The baseline used the earlier flash format. Functional regression runs used
Pico 1 QEMU and the performance campaign used physical Pico 1 over OpenOCD.

The physical reference run completed successfully: 495 main observations,
plus LOAD, large Data, noisy recovery and near-capacity recovery scenarios.
Static RAM is 24,076 bytes (.data 15,544 + .bss 8,532); SRAM code is
6,564 bytes. Stack and heap are not included in these section totals.

## Clear-state/key flash-reference stage

Validated with 233 host kernel tests, 2,258 QEMU Pico1 registry checks, and
199 QEMU Pico1 GP persistence checks (including SCP03/SCP11 and Rustlet SD
reboots). The physical Pico1 benchmark completed its 495 main observations and
LOAD, large-body, noisy and near-capacity recovery workloads.

The immutable state/key bodies are now programmed before attachment. Recovery
borrows their mapped flash slices. Entries and rollback records retain references
instead of 244-byte arrays. Volatile-only targets and host tests use immutable
reference-counted content, scrubbed when its last owner is dropped. Persistent
objects allocate no such content. The existing staging buffer is scrubbed after
programming. Neutral state/key updates retain their previous references.

Static RAM falls from 24,076 to 18,376 bytes (5,700 bytes saved). SRAM code
remains 6,564 bytes and the observed whole-campaign stack peak remains 3,904
bytes. Median physical timings (milliseconds):

| Operation | Baseline | Flash references |
| --- | ---: | ---: |
| Create Data 244 B, preparation + commit | 132.691 | 131.088 |
| Replace Data 244 B, preparation + commit | 134.620 | 134.197 |
| Read Data 244 B, warm | 22.930 | 22.525 |
| Delete commit | 56.298 | 56.207 |
| Recovery with noise | 1256.279 | 1258.664 |
| Recovery near capacity | 1425.850 | 1428.715 |

These timings characterize the existing Data-centric harness, not isolated
state/key encryption costs. Readings include code-placement and allocator-layout
effects; one creation sample is available at each size. Both images use the
same logical workload, CPU clock and physical board. Artifacts use the `before`
and `clear` prefixes in the campaign directory.

## Encrypted state/key stage

Security Domain and instance bodies and key material now remain encrypted in
flash. They are extracted directly into the state exchange buffer or caller's
key storage. BOSS and LOAD remain clear. Boot reconstructs metadata and
references by decrypting only bounded metadata prefixes; it never caches whole
states or keys. Metadata prefixes are padded to align the content on AES blocks.
The BOSS lifecycle overrides older immutable key-body metadata. Key inheritance
shares immutable bodies; SCP03 selector lookup does not decrypt keys.

The following physical Pico1 results compare the same logical workloads and
configuration (12 MHz CPU, 1 MHz timer, 64 KiB test area, 256-byte logical pages,
4 KiB erase sectors). `before` is a56f588; `clear` is the reference migration
0343e53; `encrypted` is this final stage. Timings exclude transport. Write rows
include preparation plus commit, because body programming moved before commit.

| Operation (median ms) | before | clear | encrypted |
| --- | ---: | ---: | ---: |
| Create Data 244 B | 132.691 | 131.088 | 132.394 |
| Replace Data 244 B | 134.620 | 134.197 | 135.001 |
| Read 17 B warm | 12.894 | 12.475 | 12.670 |
| Read 244 B warm | 22.930 | 22.525 | 22.866 |
| Delete commit | 56.298 | 56.207 | 56.629 |
| Recovery with noise | 1256.279 | 1258.664 | 1296.600 |
| Recovery near capacity | 1425.850 | 1428.715 | 1470.709 |
| Rollback | 1.493 | 1.539 | 1.265 |
| Savepoint rollback | 0.802 | 0.985 | 0.675 |

| RAM (bytes) | before | clear | encrypted |
| --- | ---: | ---: | ---: |
| Static data | 24076 | 18376 | 18376 |
| SRAM code | 6564 | 6564 | 6564 |
| Observed stack peak | 3904 | 3904 | 3904 |

Rollback rows time the RAM undo scope only. An abandoned transaction may already
have programmed an unreferenced body, as required by the eager-write model;
these rows do not measure the full cost of that aborted transaction.

The state/key campaign replays the same existing diagnostic commands against
archived ELFs. Creation and deletion rows add the command-body timer to the
outer commit timer. Read rows use the command-body timer. They are composite
registry workloads, not isolated AES timings. The key extraction case includes
lookup and two destination-buffer reads; it does not establish a secure channel.

| Operation (median ms) | Before | Flash references, clear states/keys | Encrypted states/keys | n per image |
| --- | ---: | ---: | ---: | ---: |
| Create two SDs and two Data objects | 194.669 | 199.404 | 198.143 | 1 |
| Read two SD states and two Data objects | 21.268 | 20.361 | 28.817 | 5 |
| Delete SD graph | 36.864 | 36.233 | 36.337 | 1 |
| Create SD and two 16-byte keys | 111.268 | 120.774 | 148.456 | 1 |
| Install SD with inherited keys | 123.990 | 77.703 | 87.719 | 1 |
| Extract two 16-byte keys | 1.587 | 1.161 | 12.882 | 15 |
The key read cost is material: removing RAM copies does not remove AES work.
State/key reads use the preceding ciphertext block as their CBC chaining value,
avoiding IV derivation and extra boundary blocks on aligned reads. Neutral state
serialization still decrypts existing content into reused scratch to compare it
with the caller's new content; this prevents redundant flash versions. There is
no full-content cache and no per-read allocation. Derived key initialization
moves earlier into boot, so first-operation timings are not isolated crypto
comparisons. Creation samples are single observations, not latency bounds.

Static RAM excludes stack and heap; SRAM code is shown separately. The stack
watermark is the cumulative maximum of the benchmark scenarios, not a per-call
AES stack measurement. Heap peak was not instrumented. The registry's static
allocation shrinks from 7,724 to 2,024 bytes; rollback records now retain body
references rather than body-sized copies. Other diagnostic scratch tables are
unchanged. Padding can change flash placement and erase frequency.

Validation:

- 235 kernel host tests passed, including encrypted range boundaries, EOF,
  untouched destination tails, reference rollback and key lifecycle recovery.
- QEMU Pico1: 2,258 registry checks, 685 GlobalPlatform checks (including
  persistence), and 1,786 dynamic Rustlet checks passed.
- Physical Pico1: all three full benchmark campaigns passed their 495 main
  observations plus LOAD, large Data, noisy recovery and near-capacity recovery.
  The state/key campaign passed 24 observations per image.
- The runner's 50 host tests passed. The full xtask library has 85 passes and two
  pre-existing failures in SVC profile provenance:
  `legacy_reports_retain_their_real_capture_identity` and
  `partial_update_preserves_unselected_samples_budgets_and_provenance`.
  Both failures also occurred on the baseline sources.
- Release cargo check passed without warnings. Fault injection simulates torn
  operations; these are not electrical brownout tests.

The tables use only the baseline and final measurements.

See [Run the current performance campaign](#run-the-current-performance-campaign).
Functional commands are `cargo run --offline test kernel_registry raspi-pico1 --on qemu`,
`cargo run --offline test gp_all raspi-pico1 --on qemu` and
`cargo run --offline test dyn_rustlet raspi-pico1 --on qemu`.
