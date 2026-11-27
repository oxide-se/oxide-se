# Compact registry and deferred flash snapshots

Status: firmware implementation, 20 October 2026. Capacity is **63 entries**.
The compact image, deferred snapshots and retained-page bitmap now replace the
old object table, duplicate serialization/reference arrays and heap undo journal.
No persistent-format migration is supported; tests start from reset images.

## Representation

Keep one compact registry image in RAM. Its bytes are the plaintext of a BOSS;
there is no parallel array of decoded objects, persistent entries, or references.
An entry occupies 40 bytes: object AID (17), parent AID (17), kind/lifecycle (2),
and absolute flash address (4). Integers use little endian. AID padding is
canonical zero padding. Addresses are integers, never unchecked Rust pointers.
Validate region, alignment, extent and expected object type before accessing an
address. Embedded packages resolve through the firmware's declared packages;
an arbitrary address in the firmware region is not sufficient authorization.

The generation occupies eight bytes. The maximum useful image is therefore
8 + 63 * 40 = 2,528 bytes. With the existing 32-byte authenticated header a
full BOSS occupies 2,560 bytes on 256-byte pages. There is one header for the whole BOSS, not one per page: exactly ten pages
at full capacity. RAM has capacity for 63 entries. Slots remain stable because
existing kernel selections use slot handles. Vacant slots are canonical zero
entries, and trailing vacant slots are omitted. The encoded count is the occupied
prefix length, not necessarily the number of live objects. This deliberately
preserves runtime handle behavior; identity-only handles are not implemented.
No compatibility with previous persistent formats is required; test images
must be explicitly reset. Absolute addresses assume the same flash mapping
for the lifetime of an image. They do not change the existing relative-offset
cryptographic domain or permit relocating ciphertext without reauthentication.

Metadata (package binding, SD backend and privileges, key descriptors and body
lengths) stays in object bodies. Recovery authenticates and decrypts the BOSS without eagerly opening object
bodies. It validates identities and topology from the image. Later boot activation
of the root SD can access its metadata through the same authenticated path as
ordinary use. At access,
authenticate the object before decrypting or interpreting its metadata. Reuse
the programming scratch, check lengths and discriminants, then return only the
small values needed by the caller. Decrypt content ranges on demand. No resident
metadata cache and no object-sized plaintext buffers are introduced.

The prior metadata-in-BOSS proposal was one possible remedy for unauthenticated
boot decisions, not a storage requirement. Moving those decisions to the first
authenticated access avoids both duplicated metadata and larger BOSS entries.

## Transactions

Replace heap undo records with at most six nested transaction boundaries,
including the outer APDU transaction. Each boundary retains one snapshot address.
Reject a seventh begin before any effects. No-op scopes perform neither flash
writes nor crypto. Boundaries opened on the same view share its snapshot.

Before changing a view needed by an unresolved boundary, synchronously write
and protect its snapshot. Resolve every boundary that denotes that same view
to this one address. Only then mutate the RAM image. A failed preparation leaves
the RAM image and all boundaries unchanged. Place this invariant next to the
mutation barrier in code:

```rust
// Invariant: before mutating the registry, every active rollback boundary
// that depends on the current view has a complete, protected flash snapshot.
// Snapshot preparation failure leaves the registry unchanged.
```

An inner commit pops a boundary without publishing the durable root. Rollback
authenticates and reloads the boundary's BOSS into the same RAM image, then pops
the boundary. A boundary still denoting the current view needs no reload.
Only final commit appends a reference to the existing two-sector durable root
journal, after writing the current snapshot if needed. Reset discards the stack
and recovers only the durable root, never an unpublished snapshot.

Distinguish snapshot identity from the publication generation. Do not reuse a
generation-derived crypto nonce after rollback; the existing seed reservation
must remain monotonic within the boot independently of the registry contents.
Every begin/end is LIFO; stale scope tokens must not consume a later scope.

An unexpected authenticated reload failure is a fatal persistence failure.
Freeze mutations/publication, panic and stop processing commands. A memory-failure SW before the stop is not
guaranteed by this implementation. Do not silently bootstrap or keep running
with a partially reloaded registry. Automatic reboot is not a recovery guarantee.

## Used pages

Use one bit per logical page for retention. This is separate from the two-bit
authentication cache. Mark the marker, durable BOSS and its objects, current
objects, snapshots reachable from the six boundaries and their objects, and an
unfinished LOAD reservation. A page is reusable only if no live root needs it.
An unretained page is not necessarily erased.

Initialize the union once, then maintain it incrementally. An allocation marks
its pages immediately, before programming or attaching the reference. Mutations
and scope completion nominate only their retired headers/bodies for release.
Subtract every surviving root from these candidates before clearing any used bit;
shared bodies and unrelated in-flight reservations remain protected. Duplicate
root addresses are visited once; the current root uses the image already in RAM.
The temporary candidate mask borrows 128 bytes of the existing 512-byte payload
scratch and is wiped afterwards. There is no added resident table or page counter.
A completed LOAD transfers its reservation to the attached package; an abandoned
LOAD releases its unreferenced reservation. Preparation failures release theirs.

Rollback authenticates and decrypts the target BOSS once into existing page
scratch. The runtime observer, slot comparison and restoration share those bytes.
Reconcile retired pages only after releasing that scratch; the restored target is
then represented by the current RAM image and is not decrypted again. Other
surviving flash roots, if distinct, still need inspection when checking sharing.
On uncertain ownership, fail closed without clearing candidates. Erase-sector
eligibility includes every logical page in the sector and adjacent live blocks.

## Identity and metadata access

The compact image is authoritative for AID, parent, kind and lifecycle. Identity
and ancestry queries read it directly, including provisional changes; they must
not open object bodies merely to obtain those fields. Parent traversal is bounded
by registry capacity and fails closed on cycles or missing/non-SD parents.
Metadata queries still authenticate the body before decrypting its prefix. The
visibility check uses the compact graph and does not reopen the requested body.

On APDU reception, the delegated-establishment check can return the already
resolved native/null backend classification to the session check. This is a
local enum, not a resident metadata cache. No classification is retained across a
Rustlet hook: hooks may change registry or authority even when they return false.
The original session checks and authentication requirements remain in place.

## API replacement

Remove the `object_registry` and `object_registry_persistence` compatibility
modules and their consumers. The final API exposes identity lookup, authenticated
metadata/range access, typed mutations, transaction begin/commit/rollback, reset
recovery, and streamed LOAD reservation/finalization. No public mutable table,
`DerefMut` back door, retained object reference, or duplicated resident metadata table.
Runtime selections still retain stable slot handles with their existing identity
checks. Rollback observers invalidate disappeared/rebound identities, including
changed package bindings. Migrating these handles to AIDs is separate work.
Delete the old object table and undo journal rather than wrapping them.

Rewrite consumers in selection, SD hooks, secure channels, GP management,
predeployment, LOAD and diagnostic modules. Preserve the SD/app crash outcome
matrix. Host tests must exercise the same transaction engine with a fake flash
backend; retaining the old journal under `cfg(test)` would test another design.

## Validation and measured memory

Measurement results are recorded below.
The baseline is `main` at 7fa08a77, default Pico1 profile: `.data + .bss` 13,756
bytes, RAM code 6,396, reserved stack 7,168 and ABI 32. Old projections using
metadata-rich entries or 64 entries are superseded.

The resident Registry<63> is 2,568 bytes: image 2,532, six-boundary stack 28,
current-root address 4 and outer-token/control/alignment 4. The KernelCell guard
adds 4 bytes. The 4,096-byte programming scratch and 512-byte payload scratch
are retained; their guarded storage must be counted among static sections.

The runtime diagnostic reads allocator occupancy without adding a second
allocation table. Samples measure live allocations, not transient heap peaks.
The stack watermark is cumulative per boot. The registry-test profile has a
64-KiB flash region and a 64-byte authentication cache; the default region needs
256 bytes. These profiles must not be conflated. The current allocator keeps its
existing metadata and available heap partition; this change does not enforce a
32-KiB RAM limit or change MPU placement.

## Proof follow-up and remaining limits

The old Rocq models are not proofs of this implementation. Establish a refinement
between the canonical sparse image and logical identity map; prove the mutation
barrier, six-root LIFO stack, shared roots, rollback reload, and final publication.
Prove retention is the union of durable/current/snapshot objects and pending LOAD,
including erase-sector neighbours. Separate authenticated metadata access and
address validation from flash and cryptographic assumptions. Resets discard the
stack and select only the journal's durable root. Provisional generation numbers
are not crypto seeds; seed allocation remains independent of rollback.

Host tests use a fake immutable flash store with the production image and snapshot
state machine; that store is not linked into firmware. QEMU exercises real codecs,
allocation, interrupted operations, reboot recovery and LOAD. QEMU timings are
not physical Pico1 performance measurements. No new hardware timing claim is made.

The bitmap supports at most 1,024 logical pages. Unexpected authenticated reload
failure stops execution. Interrupted first initialization remains outside the
assumed guaranteed bootstrap. No broad 32-KiB guarantee is made for arbitrary
Rustlet private memory, secure-channel sessions or unmeasured heap peaks.

## Results — Pico1 / thumbv6m-none-eabi, 20 October 2026

The refactor targets main. The default build uses the
project's default configuration (NullSD, no preinstalled Rustlet/secure channel).
`arm-none-eabi-size -A` and `nm -S -C` measure the linked sections and globals;
allocator partition capacity is computed from those actual addresses with the
same address-sensitive algorithm as `allocator.rs`.

| Component | Bytes | Evidence / meaning |
| --- | ---: | --- |
| `.data` | 5,716 | Initialized statics in ELF |
| `.bss` | 6,796 | Zero-initialized statics in ELF |
| All statics | **12,512** | Includes compact registry and scratchs |
| RAM code | **6,396** | `.critical.kernel.fct` |
| Reserved kernel stack | **7,168** | Linker symbols; not observed consumption |
| Boot ABI | 32 | Linker reservation |
| Alignment | 8 | Gaps through `__ram_end` |
| Allocator metadata | **4,096** | Outside `.data/.bss`, before usable heap |
| Fixed footprint with reserved stack | **30,212** | Excludes live heap allocations |
| Standard authentication cache | 256 | 992 pages / 4 = 248 bytes, rounded by buddy allocator |
| Fixed footprint plus standard cache | **30,468** | Leaves **2,300** of 32,768 bytes |
| Available heap capacity in current mapping | **25,336** | Capacity, not live occupancy; includes the cache |

Static footprint decreased by **1,244 bytes** from the 25-entry baseline while
capacity grew to 63. RAM code and stack reservation stayed unchanged. Removed
five globals totalled 3,980 bytes. Their replacements occupy 2,736: guarded
registry 2,572; publication control 28; guarded page bitmap 136. The registry
itself includes the compact image and all six roots, with no heap undo storage.

Main static consumers (guard/padding included where part of the symbol):
programming scratch 4,097; registry 2,572; syscall table 1,024; app-gate storage
1,024; root SD control 548; payload scratch 513. Other globals and alignment
account for the remaining 2,734 bytes. No object bodies are resident as a table.

The current mapped capacity remains 49,152 bytes for kernel data/stack/allocator/
heap plus 6,396 bytes of RAM code, i.e. **55,548 bytes** in aggregate. RAM code
starts in a separate region at 0x20010000. This is not a 32-KiB linker layout.
The 30,468-byte figure is a fixed-footprint/cache accounting, not a measured
upper bound on all allocations in every application.

### Execution measurements

The full registry diagnostic campaign yielded **925 samples**: live heap 64 bytes
at each sampling point, cumulative stack peak **4,700 bytes**. The final short
campaign added **68 samples**, peak 3,844 bytes; the full-63-entry nested rollback
probe had reached 3,820 bytes. The short campaign is not a smaller global bound.
Neither campaign measures transient heap maxima between samples. LOAD snapshot
preservation can temporarily allocate one logical page (256 bytes on Pico1).

These are QEMU Pico1 observations, not physical-device timing measurements.
The instrumented registry profile reserves 64 KiB of flash: its cache is only
64 bytes. Its ELF has 17,204 static bytes and 7,396 bytes of RAM code, because it
includes test/performance/fault-injection machinery. Its usable heap is 20,648
bytes. Do not apply that ELF's static sizes to the default profile, or call the
64-byte sample the standard firmware's entire heap consumption. The reserved
stack is retained in the conservative default budget; it is not reduced using
the measured watermark.

A standard profile with arbitrary Rustlet memory and secure-channel sessions is
**not yet validated within 32 KiB**. It has only 2,300 bytes beyond the fixed
footprint/cache if the current reserved stack and allocator metadata are kept.
Enforcing 32 KiB requires a defined application profile, measurement/bounds on
transient and persistent heap allocations, and a separately validated memory map.

### Validation

- Kernel host tests: **257 passed**; oxi-core host tests: **96 passed**.
- xtask: **88 unit tests** and **6 integration tests** passed (local sockets require execution outside the sandbox).
- Clippy kernel host library with `-D warnings`: passed.
- Registry boundary audit and `git diff --check`: passed.
- Default Cortex-M0+ build: passed (`thumbv6m-none-eabi`).
- Final QEMU registry campaign: **2,258 checks** (cuts, interrupted erase, resets,
  192 sustained replacements and SD inheritance).
- Full QEMU registry performance/recovery campaign: **495 checks**.
- Final short performance campaign: **66 operation checks**, plus the explicit
  63-entry/full-BOSS rollback and six-scope/seventh-rejection probe.
- Dynamic Rustlet/LOAD campaign, devkit and SCP03: **1,786 checks** (including
  interrupted LOAD, incompatible images, isolation faults and persistent reboot).
- Final focused SCP03 INSTALL/LOAD: **44 checks**.

## Unchanged data and publication

A streamed Data update compares its logical plaintext with the existing object
before allocating a payload or materializing a deferred snapshot. Comparison
uses authenticated reads into the existing payload scratch, in bounded chunks;
it does not retain a plaintext cache or allocate a body-sized buffer. An
identical update leaves both the reference and the transaction's dirty state
unchanged. Finalizing an otherwise clean APDU closes its transaction without
publishing a BOSS. Other changes already staged in that APDU still publish.
For a two-object update only changed members are prepared, preserving original
producer indices and atomic attachment. Producers must remain deterministic.
Authentication/read errors are propagated rather than treated as equality.
The existing instance and Security Domain serialization comparisons remain in
place, including their metadata checks; equality of bytes alone cannot suppress
a change of package, backend, privileges, or lifecycle metadata.

## Four-bit ownership and authentication table (supersedes incremental retirement)

The resident page table now packs two pages per byte: bits 0..2 are free (0),
base ownership (1), or transaction depths 1..6 (2..7); bit 3 caches complete
block validation at its header page. The table payload is 512 bytes for 1024
pages. The separate heap authentication cache is removed. A free candidate is
not cached. Authentication failures and LOAD header-only successes are not
cached; they still return their actual verification results. Reservations are
owned before programming and are never implicitly authenticated by ownership.

At local acceptance, ownership moves one level outward. At local rollback,
the pre-state is restored before that level's allocations are released. No
surviving BOSS graph is decrypted to reconcile local retirement. A newly
materialized pre-state BOSS belongs to the parent of the earliest unresolved
boundary: the restored current root must survive the rollback that uses it.
The six-boundary limit includes the external APDU transaction. LOAD reservations
are explicitly base-owned across APDUs and released on cancellation or retained
by attachment. Body writes/erases invalidate earlier overlapping cached header
validation without changing ownership.

Obsolete versions remain allocated during a transaction. At external close a
live mask is built in the existing payload scratch from the current RAM image,
its BOSS extent, the active LOAD reservation and the area marker. Extents are
read structurally from clear headers; no body crypto is required for collection.
This relies on the immutable, previously created/recovered references and the
absence of spontaneous flash corruption; structural recognition alone is not
an authenticity guarantee for an arbitrary candidate. The mask is applied only
when complete. If the current image differs from an existing durable root
outside a scope (bootstrap), collection is deferred until publication. After
an uncertain physical failure, ownership is retained and the write freeze
prevents allocation until reset. Longer transactions can retain more obsolete
versions and reach flash capacity earlier than the previous eager retirement.

The flash format is unchanged. The existing common `header_total_len` plus
bounded structural object decoding obtains physical extents for every family;
it does not decrypt metadata. Recovery reconstructs ownership from the compact
BOSS and these extents, not by authenticating every object's body at boot.

Follow-up experiment: measure whether full LOAD validation on first header
inspection is preferable to repeated header CMAC checks that are no longer
cached. Full validation includes the existing body CRC check; this would not
upgrade LOAD's body to cryptographic authentication. This policy is deliberately
unchanged here. Formalize ownership, validation, snapshot sharing, final
collection and reset separately before claiming the new state machine proved.

LOAD progress is not encoded by transaction ownership. The current format has
no explicit loading/loaded header field: RAM tracks received bytes; CRC and CMAC
fields remain erased until sealing. `Loaded/Locked` is stored in the registry
entry after attachment. A sealed LOAD is not necessarily published. This change
preserves that protocol and does not add a flash-resume mechanism for a LOAD
interrupted by reset. A dedicated persistent loading-state field, if needed,
would be a separate format change.

Clean transaction exits skip both page ownership traversal and final collection.
A conservative scope bitmask records levels that may own allocations; accepting
an allocating child transfers its bit to the parent. Rehoming and release may
leave false positives, which only cause an unnecessary traversal. A separate
collection flag is raised by successful reservations and registry slot changes
(including deletion without allocation). Authentication-cache updates do not set
it. Only successful collection clears it; postponed collection remains pending
across later clean transactions. Both fields fit the existing table padding on
Cortex-M0+, without increasing its resident size. The flags are reconstructed
with the page table after reset; neither is persisted.
