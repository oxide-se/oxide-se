# Registry contracts: characterization baseline

This document records the implementation before extraction into a registry
component. It is a review baseline for that refactoring, not a Rocq proof or a
replacement API. No production behavior is changed by this first lot.

Names such as `commit_transaction` below identify operations for reasoning;
they do not claim that a Rust function with that name already exists.

## State and scope

Use the following distinct state components:

- `F`: persistent flash bytes, including incomplete and unreferenced blocks.
- `W`: the current RAM registry, including tentative mutations.
- `J`: the optional RAM undo journal and its nested savepoint boundaries.
- `L`: the optional volatile dynamic LOAD context and reserved flash extent.
- `C`: volatile publication caches, including the latest BOSS and object refs.
- `A`: the APDU-wide abort latch.

`Recover(F)` denotes reconstruction from the selected BOSS and its referenced
payloads, together with immutable firmware objects. It is not simply the RAM
view `W`. Failed decoding/restoration and first initialization must also be
represented; recovery is not a total successful lookup on arbitrary bytes.

Registry access is serialized by the privileged owner-core/APDU path. There
is one top-level transaction; nested operations use savepoints, not independent
durable transactions. Object identity includes owner, kind and AID, with the
existing kind-specific uniqueness rules. Data services derive the AID from
the GP tag and qualify lookup by owner.

## 1. Transactional registry operations

Implementation: [selected_app.rs](../kernel/firmware/src/selected_app.rs)
and the [registry module](../kernel/firmware/src/registry/).

| Logical operation | Current implementation | Current contract |
| --- | --- | --- |
| Initialize after reset | `initialize`, `initialize_registry`, `ensure_predeployment_initialized`, `restore_persistent_registry_if_available` | Seed immutable objects, attempt restoration, otherwise follow the existing bootstrap path. Initialization also installs runtime hooks; there is no isolated registry reset API. |
| Begin | `begin_registry_apdu` / `ObjectRegistry::begin_transaction` | The low-level begin rejects an active transaction with `InvalidState`; on success opens an empty journal without changing objects or flash. The APDU wrapper first clears fault/abort state and is intended for a fresh APDU, not nested begin. |
| Read | `load_registry_data_object`, find/resolve/entries, GET STATUS helpers | Observe `W`, including accepted provisional writes. Data read returns `NotFound` or `OutputTooSmall` before copying; successful copy changes only the returned prefix of the output buffer. Reads do not dirty the journal. |
| Write | `upsert_registry_data_object`, typed object upserts and lifecycle setters | Create/replace an object or update metadata in `W`. Record the previous slot before mutation. Inside an active transaction, success is staging, not durable commit. Large Data writes may already allocate/program flash. |
| Delete | `delete_object`, `delete_visible_managed_object_under_authority` | Remove from `W`; retain rollback information. The management service validates the dependency closure and uses one operation scope for all deletions. Deleted slots can be reused; rollback must recover their previous identities. |
| Commit/finalize | `finish_registry_apdu`, snapshot publisher, `finish_transaction(true)` | If not aborted and dirty, attempt publication once. On success retain `W` and retire the RAM journal. Clean finalization does not invoke the publisher. Identical persistent snapshots need no new BOSS. |
| Request abort | `abort_registry_apdu` | Set a sticky latch only. Does not immediately restore `W`; later successful scopes cannot clear the latch. |
| Roll back | `finish_transaction(false)` and aborted/failed APDU finalization | Restore journaled slots and close the journal. Aborted finalization skips publication and returns `Ok`; this is not a commit acknowledgement. Finalization also clears pending LOAD and retires affected runtime/session state on abort or publication error. |

`registry_operation` is a context-dependent adapter: it joins an active
transaction, otherwise begins and owns one. It always uses an operation
savepoint. A successful owned operation finalizes before returning; an error
or host unwind abandons its changes. A successful nested operation leaves the
enclosing transaction open. These two meanings of success must survive the
extraction until callers are migrated explicitly.

Publication currently returns success without flash publication during
bootstrap or when the persistence area has zero pages. Host tests using this
mode establish RAM behavior, not durability.

Publication errors restore the RAM view. The stronger assertion that every
returned flash error leaves the previous BOSS authoritative requires an
additional low-level error contract; it does not follow from RAM rollback.

## 2. Savepoint operations

Implementation: `RegistryOperationScope`, `savepoint`, `finish_savepoint`.

- Preconditions: an active transaction for the low-level savepoint methods;
  nested scopes are used in stack order. An enabled high-level scope without
  an active transaction is currently inert.
- Begin captures the journal boundary; it does not publish or copy the whole
  registry. Undo storage is allocated on mutation, before changing the slot.
- Accept retains mutations in `W` and preserves their undo information for
  an outer rollback. It does not commit to flash.
- Rollback replays the scope's undo entries backwards and restores its prior
  boundary. Earlier enclosing changes survive. Dropping an unfinished scope
  rolls it back.
- An accepted inner scope remains subject to outer rollback.
- Rollback reports identity changes for runtime invalidation; same-identity
  persistent updates can require reconstruction of a resident object too.
  Restored/reused slots must not silently retarget runtime handles.

The APDU policy is separate: an ordinary error status does not universally
abort the APDU. Management rejection rolls back its scope; legitimate protocol
progress outside it may remain. Abnormal SD hooks can mark the whole APDU for
abandonment. Session retirement is not restoration of an old cryptographic
session.

## 3. Payload preparation operations

Implementation: `prepare_dynamic_package_load`,
`append_dynamic_package_load_block`, `finalize_dynamic_package_load`,
`cancel_dynamic_package_load`, `write_registry_data_objects`, and storage
helpers in `selected_app.rs`.

| Operation | Current effect and obligation to preserve |
| --- | --- |
| Prepare LOAD | A new preparation first discards the previous volatile context, then validates and reserves storage. Consequently a rejected new preparation can still cancel the former one. No package entry is published at preparation. |
| Append | Program payload pages progressively; keep partial-page state in RAM. The preparation can span APDUs while other registry participants publish. Its reserved extent must remain protected. |
| Finalize | Validate size, hash and FAE, finish the CRC, decode the payload, clear LOAD context and stage the package entry through `registry_operation`. Completing a payload is distinct from publishing its registry entry. |
| Cancel | Drop the volatile context only. Unreferenced bytes remain in flash and can later be recycled. Cancellation does not roll back previously committed APDUs. |
| Stream Data | `write_registry_data_objects` prepares one or two payloads, then stages their references in one operation scope. It rejects an active dynamic LOAD; currently requires 256-byte pages. The producer must be deterministic and must not mutate registry or flash. |

Protection includes the area marker, latest BOSS and its payloads, current
runtime flash payloads and rollback payloads, plus active LOAD storage. New
payloads are protected as publication progresses. Failed preparation may leave
unreferenced bytes; byte-for-byte flash rollback is not the contract.

Consumers include GP LOAD/STORE DATA/PUT KEY/DELETE/SET STATUS in `main.rs`,
Security Domain state persistence and Data lookup, and runtime serialization
of Rustlet Persistent objects. Compound installation, key inheritance and
deletion compose the same transaction/savepoint mechanism. GET STATUS and
key lookup are read services. Large Data streaming also has a diagnostic
consumer in `kernel_main_app/sram_fingerprint/power_cycle.rs`.

## Flash boundary and reset

The publisher calls `oxi_core::core::flash::write_page` and `erase_sector`;
reads use the mapped flash area. It does not call `write_page_atomic` or
`flush_page`. No page/sector atomicity is assumed for the intended proof.

The future flash contract must specify geometry, bounds, read visibility,
successful-write durability/order, the locality of interrupted operations,
and possible effects of errors. In particular, successful programming must
have the durability needed before a referencing BOSS can commit; the current
publisher does not add a flush for an asynchronously staged backend.

Reset interrupts an operation at an internal step, discards `W/J/L/C/A`, and
restarts initialization from the surviving flash image and immutable objects.
It does not run Rust destructors or the explicit rollback operation. It can
also interrupt initialization or another recovery attempt. A physical flash
operation in progress may leave a partial result within its specified fault
footprint.

The desired theorem, still unproved, is old-or-new recovery for a complete
transaction, not an atomic flash write. It needs reference closure, protected
erase, payload-before-BOSS ordering and sound recovery. A valid new BOSS can
precede the caller observing success; interruption is not equivalent to a
returned rejection.

Unresolved obligations, deliberately not changed in this lot:

- Counter increment wraps at `u32::MAX`, whereas the scanner uses ordinary
  greater-than comparison. Bound execution or revise ordering in a later change.
- CRC validation is not an unconditional proof of completeness under arbitrary
  torn writes. State a fault/detection assumption or prove the required property
  for a specified model; CRC is not a cryptographic authenticity guarantee.
- Separate definite rejection from a flash error after a possibly valid BOSS.
- Recovery selects the highest valid BOSS before restoring referenced objects;
  it does not implement a general search backwards through fully restorable
  snapshots. Reference validity must follow from the invariant.
- Bootstrap, missing/corrupt marker and unsupported persistence modes require
  separate initialization outcomes, not a blanket successful-recovery axiom.
- `model.md` still describes single-delta publication. The current APDU path
  can publish several object mutations together; preserve the implementation.

## Characterization and evidence

Run host characterization with `cargo test -p kernel --lib`. Tests named below
are in `selected_app.rs` unless another file is named. Mock publisher success
or failure is evidence about orchestration/RAM only.

Lot 1 validation (2026-10-15): all 211 kernel library host tests passed,
including the three added characterizations. Target multi-boot and physical
power-loss campaigns were not run for this documentation/test-only change.

| Contract | Existing or added characterization | Evidence boundary |
| --- | --- | --- |
| Staged reads and deferred abort | **Added:** `contract_data_reads_observe_staged_writes_until_global_rollback` | Read-your-writes, abort latch, final rollback; no physical flash |
| Read-only behavior and copy errors | **Added:** `contract_data_reads_and_read_errors_do_not_dirty_transaction` | Owner qualification, untouched error buffer, no publication |
| Accepted inner scope / outer Drop | **Added:** `contract_accepted_inner_scope_remains_subject_to_outer_rollback` | Both repeated update and insertion undone; prior change retained |
| Autonomous/nested unwind | `standalone_and_nested_operations_roll_back_on_unwind` | Host unwind only, not reset |
| Single publication and clean APDU | `apdu_stages_all_services_and_publishes_dirty_registry_once` | Mock publisher |
| Sticky abort | `apdu_abort_is_sticky_across_later_successful_savepoints` | Later acceptance cannot authorize publication |
| Publication failure | `failed_apdu_publication_restores_replacements_insertions_and_deletions` | RAM restoration, reused identity, LOAD cancellation |
| Local rejection | `management_abandon_preserves_protocol_changes_before_and_after_dispatch` | Earlier/later participants retained |
| Runtime references | `rollback_retires_authority_before_a_restored_slot_can_be_reused` | Authority invalidation |
| Compound writes/capacity | `sd_inherited_key_capacity_failure_restores_the_whole_operation`, `sd_and_inherited_keys_share_the_apdu_publication_failure` | Grouped changes |
| LOAD cancellation | `dynamic_load_cancel_drops_only_volatile_context` | Volatile fixture, not flash recycling |
| Interrupted snapshot | `object_registry_persistence::tests::every_torn_registry_prefix_recovers_one_complete_graph` | Synthetic prefix/partial-byte cuts, entry lists; not real referenced payload closure |
| Scan and protected recycling | `scanner_treats_erased_pages_as_free_space_not_as_end_marker`, `reusable_span_never_erases_sector_touching_protected_range`, `unfinished_containers_never_promote_embedded_boss`, `recycling_neutralizes_tail_before_header_without_extra_erases` in `object_registry_persistence.rs` | Byte-array format/allocator tests |

Target qualification remains separate. Existing multi-boot scenarios live in
`xtask/src/testing/scenarios/persistence.rs`; SD transaction scenarios in
`sd_transaction.rs`; registry-test images use `registry_write_fault.rs` for
write/erase prefix injection. Injection models durable byte images, not an
electrical power failure or every possible interrupted bit pattern.

Before extraction is accepted, retain coverage of payload preparation followed
by reset/cancel, reuse after abandoned writes, commit after multiple mutations,
and LOAD reservation coexisting with another publication. Reset during first
initialization, repeated resets during recovery, late flash-error outcomes and
counter wrap are explicit additional qualification/proof gaps, not guarantees
established by this host suite. No new target harness is introduced in lot 1.

## Extraction progress

### Physical-model clarification after baseline approval

The six obligations above record the original review baseline. Subsequent user
decisions refine their status; see [the registry proof scope](../proofs/registry/README.md).
Valid flash requests complete synchronously, without pending flush work; bytes
are assumed programmed in order. Physical interruption leads to reset, not a
returned partial-write error. The proof may start from a guaranteed valid initial
BOSS with no mutable references. Reference closure is an inductive obligation
of object creation, publication and protected recycling, not a requirement to
search older snapshots. Version wrap and incomplete-block validation still
require work. Returned `VerifyFailed` is now included as a failed, unaccepted
write; this does not establish byte-for-byte preservation of flash. The proof
scope records the corresponding non-publication obligation and the preference
for SHA-256 over CRC, with a final validity byte as an alternative. None of
these format/error-policy changes is part of the mechanical extraction.

### First extraction step

The first extraction step moves the binary format and its existing tests to
`kernel/firmware/src/registry/format.rs`. `object_registry_persistence.rs`
keeps compatibility exports, so consumers retain their current API. The format
implementation and test bodies are unchanged; their test module path is now
`registry::format::tests`.

`registry/storage.rs` owns flash-area access, marker initialization, block
programming, reusable-span allocation, neutralization and sector erasure,
together with the shared page scratch buffer. `registry/state.rs` owns the
volatile publication cache, registry storage, scratch buffers and LOAD context.
These remain crate-visible during migration;
it is not a new public registry contract. The fault-injection implementation
moves to `registry/write_fault.rs` with a compatibility export in `selected_app`.

`registry/publication.rs` owns snapshot publication, payload serialization and
the protection helpers. `registry/recovery.rs` owns scanning/restoration of the
selected BOSS into RAM, entry reconstruction and topology validation. It still
uses the existing root-identity helpers exposed by `selected_app`, and firmware
seeding and Security Domain privilege policy; this dependency is explicit.

At the end of the first step, transactions, savepoints, initial seed/bootstrap
orchestration and GP LOAD protocol operations remained in `selected_app`.
Storage is not yet the sole flash writer: the existing LOAD path still programs
pages directly. This completes the mechanical persistence extraction, not the
autonomous transactional facade. Flash operation order, error paths, buffer
sizes, borrow scopes, static initializers and formats are preserved.

Extraction validation: 211 host tests pass both with the default configuration
and with `OXIDE_SE_KERNEL_APP_MODULES=registry-test`. Workspace formatting and
diff whitespace checks pass. Comparison with the lot 1 commit confirms that
all 30 moved function bodies are unchanged (ignoring whitespace),
and format/fault-injection files are byte-identical. Workspace Clippy with
warnings denied encounters an existing `unit_arg` diagnostic in
`rustlets/rustlet_runtime/src/state.rs:98`; the kernel-only check without the
host-test feature encounters existing unused semihosting items in oxi-core.
The targeted kernel Clippy check with `--features oxi_core/host-test` passes
with warnings denied.
The embedded binary also passes `cargo check -p kernel --bin kernel --target
thumbv7em-none-eabi --offline` with `OXIDE_SE_BOARD=b-l475e-iot01a`,
`OXIDE_SE_KERNEL_IMAGE_MODE=kernel-only`, `OXIDE_SE_KERNEL_APP_MODULES=registry-test`
and `OXIDE_SE_BUILD_CONFIG` pointing to `configs/config_kernel_registry_test.toml`.
No target execution or electrical power-loss campaign was performed.

### Second extraction step: transactions and savepoints

`registry/transaction.rs` now owns the top-level lifecycle and abort latch:

| Entry point | Contract |
| --- | --- |
| `begin_transaction()` | Open a fresh journal and failure scope. The historical clearing of the abort latch before attempting begin is preserved; callers must not use begin for nesting. |
| `transaction_active()` | Query whether an operation joins an existing owner. |
| `request_abort()` | Set sticky deferred abandonment without changing the current objects. |
| `commit_transaction()` | Attempt publication once if dirty and not aborted; retire the journal on success, otherwise restore it. Return `Retained`, `Aborted`, or the publication error. |
| `rollback_transaction()` | Restore and close the RAM journal without publishing or performing runtime cleanup. A closed journal remains a no-op. |
| `run_operation<H, T>(operation)` | Join or temporarily own a transaction, use a savepoint, and preserve the previous error/unwind behavior. |

`Retained` intentionally includes clean transactions and persistence-disabled
or bootstrap modes: it does not assert that bytes were newly written. The
private `retire_journal_after_publication` only discards undo storage; publication
is a separate action. The abort latch remains until the next begin, as before.
The injected-publisher variant is used by host characterization.

`registry/savepoint.rs` owns `OperationScope<H>` with `begin`, `accept`,
`rollback`, and rollback on `Drop`. `finish(retain)` remains a compatibility
adapter. Disabled scopes and scopes without an active transaction stay inert.
Scopes must finish in stack order before their owning transaction finalizes.
Accepted inner changes retain their undo history for outer rollback.

`RollbackObserver` notifies runtime policy before restoring touched slots and
after restoring them, supplying the identity-invalidation set. Notifications
hold no registry borrow and must not mutate the registry or enter userland.
`OperationOwner` supplies begin/finalization policy for autonomous calls.
These are synchronous, statically dispatched hooks, not new allocations or
user callbacks.

`selected_app::RegistryRuntimePolicy` retains the actual runtime actions:
requesting reconstruction before rollback; retiring rebound handles and
authority afterwards; and clearing LOAD, selections and failed sessions after
global abandonment/publication failure. The APDU wrappers preserve their old
return values (including `Ok(())` on explicit abandonment). Existing consumers
use the compatibility scope alias and operation adapter; the mechanisms no
longer reside in `selected_app`. Neither transaction nor savepoint modules
depend on `selected_app` in production code.

The read/write/delete services and GP payload-preparation facade have not been
redesigned in this step. The flash format, CRC, counter behavior and open proof
obligations are unchanged. Direct object access remains during this migration.

The original 211 host characterizations pass unchanged in their assertions.
Three direct interface tests additionally cover distinct finalization outcomes,
explicit rollback/reopening, and notification ordering around restoration
without holding registry borrows (including accepted inner changes).

Step 2 validation (2026-10-15): all 214 host tests pass in default and
`registry-test` configurations. The STM32L475 kernel-only/registry-test binary
passes the same cross-target `cargo check` documented above. Formatting and
diff checks pass. Library Clippy with `oxi_core/host-test` and warnings denied
passes. Including test targets exposes three existing diagnostics in unchanged
files: `manual_is_multiple_of` in `kernel_main_app/svc_profile.rs:206`, and
`items_after_test_module` / `single_match` in `time_manager.rs:211,367`.
The initial step 2 validation did not execute a target. The Cortex-M0+ follow-up
below supplies QEMU execution; no physical power-loss test was run.

### Cortex-M0+ validation of the extraction

On 2026-10-15, installed `thumbv6m-none-eabi` using
`rustup target add thumbv6m-none-eabi`, then ran:

```sh
cargo run --offline -- test kernel_registry raspi-pico1 --on qemu
```

The repository runner built the optimized Pico1 kernel with
`configs/config_kernel_registry_test.toml` and executed the bundled RP2040 QEMU.
The board configuration selects `thumbv6m-none-eabi` and Cortex-M0+ native startup.
This was a complete firmware build and QEMU run, not just `cargo check`.

Result: `KERNEL-REGISTRY-DONE board=raspi-pico1 total=1498`, exit status 0.
Coverage includes reset retention, object/BOSS prefix-write failures,
cumulative deletion, interrupted-erase images, repeated reconstruction,
192 replacements with 72 recycled-sector erases, and SD inheritance publication
failure/recovery. The first sandboxed run built successfully but QEMU exited
before serial connection; the complete run succeeded outside that sandbox.

Validation log: `oxide-registry-m0-validation/kernel-registry.log` (local,
temporary). Tested ELF: `target/kernel/firmware/kernel.elf`, SHA-256
`b51d490b058202a6332a62e1e879fae73c28375f17592226008e4d5f120bbf45`.
Fault injection still models flash images; it is not an electrical interruption
test or a Rocq proof. No registry implementation changes were needed for this run.

### Third extraction step: payload preparation

`registry/payload.rs` now owns the physical preparation mechanisms:

| Entry point | Preserved contract |
| --- | --- |
| `prepare_payload` | Reserve a protected, MPU-compatible package span and stage its header in the shared page buffer. The GP caller immediately installs the returned physical cursor in the active LOAD context. |
| `append_payload` | Append sequential bytes, flushing full pages in the existing order. Advance the accepted byte count on success; on failure the caller abandons the context. Size and block-sequence checks remain the caller's responsibility. |
| `finalize_payload` | After GP size, SHA-256 and FAE checks, write the existing CRC64 trailer and decode the physical block. Return a prepared reference, without inserting or committing an object. |
| `abandon_payload` | Clear the volatile LOAD context; do not erase already programmed bytes. Also used immediately before successful attachment, as before. |
| `with_prepared_data_payloads` | Prepare one or two Data blocks and invoke synchronous attachment after releasing the protection-table borrow. Reject an active LOAD and retain the current 256-byte-page restriction. |

The GP facade retains authorization, package identity, block numbering, TLV
parsing, expected digest, FAE validation and APDU status mapping. Its context
contains a `PayloadPreparation` physical cursor alongside protocol metadata.
The caller still provides the shared page borrow and performs FAE reads across
mapped flash and the pending page. This is an internal interface with explicit
preconditions, not a new independently callable public API.

Calls are serialized. No allocation may intervene between reservation and
installation of its active context, or between completion and attachment of
its reference. Data attachment must stage all references before further flash
allocation. The Data producer must remain deterministic and cannot mutate flash
or the registry. The current LOAD reservation remains visible to publication
across APDUs; retained, live and rollback payload protection is unchanged.
Abandonment and attachment retain their previous ordering and error paths.

The extraction changes neither persistence format nor fault policy. It adds no
SHA-256 trailer, validity marker, version-wrap handling or stronger guarantee
for returned verification failures. The proof obligations above remain open.

Step 3 host validation: 216 kernel tests pass both with the default module set
and with `OXIDE_SE_KERNEL_APP_MODULES=registry-test`. The two added tests cover
fragment concatenation without disturbing the staged header, and early rejection
of unsupported Data batch sizes without invoking producer/attachment callbacks.
Existing cancellation, authority and transaction characterization tests remain
unchanged apart from the test fixture's physical-cursor nesting. Library Clippy
with `oxi_core/host-test` and formatting checks pass.

Pico1 validation (2026-10-15), using the runner's release builds for
`thumbv6m-none-eabi` (Cortex-M0+) and QEMU:

- `cargo run --offline -- test kernel_registry raspi-pico1 --on qemu`:
  1,498 checks pass; 192 replacements and 72 recycled-sector erases.
- `cargo run --offline -- test gp_scp03_install_load raspi-pico1 --on qemu`:
  44 checks pass.
- `cargo run --offline -- test dyn_rustlet raspi-pico1 --on qemu`:
  1,786 checks pass across devkit and SCP03 profiles, including incomplete LOAD
  recovery, digest/CPU/ABI rejection, isolation and persistent execution.

Logs for this run: `oxide-registry-step3/{registry,load-scp03,dyn-rustlet}.log`.
These are characterization/emulation results, not a physical power-cut proof.

### Fourth extraction step: consumer facade and physical boundary

The kernel's single `OBJECT_REGISTRY` is now visible only within `registry`.
`registry::read()` borrows the current view without copying it; `resolve`,
`find_*`, `find_index` and `entries` provide reads, lookup and stable-slot
iteration. `registry::edit()` returns a `Mutation` guard with explicit typed
write, metadata-update, clone-key and delete methods. It preserves existing
exclusive-borrow lifetimes, but exposes no mutable dereference, clear, journal
retirement or transaction/savepoint methods in firmware builds. Read-only
methods remain available through the guard. The old `object_registry` module
re-exports the object model, now in `registry/objects.rs`, for compatibility.
Standalone object-model values are not handles to the global registry.

The facade deliberately retains typed methods rather than introducing an
untyped `write_object` dispatcher. `edit()` acquires a borrow only: it does not
open a transaction and its methods do not publish. The same existing caller
preconditions apply, including bootstrap. The context-dependent operation
adapter remains separate. Tests alone retain mutable dereferencing for existing
fixtures that clear the registry or directly characterize the RAM journal.

| Abstract service | Concrete entry / implementation | Consumer policy retained outside the component |
| --- | --- | --- |
| Initialize after reset | `registry::init_on_reset<P>` in `boot.rs` | Runtime hook registration, root activation and bootstrap installation callbacks |
| Begin / commit / rollback / deferred abort | `transaction::{begin_transaction, commit_transaction, rollback_transaction, request_abort}` | APDU fault status, LOAD cancellation and session retirement |
| Autonomous or nested operation | `transaction::run_operation<P, T>` | `RegistryRuntimePolicy` supplies the existing begin/finalize and rollback notifications |
| Local scopes | `savepoint::OperationScope<P>` | Resident-state reconstruction and handle invalidation notifications |
| Read / find / list | `registry::read()` with object-model lookup and iteration | GP visibility filters, GET STATUS pagination/encoding, key selection, tag-to-AID conversion |
| Create or replace Data | `Mutation::{upsert_data_object, upsert_flash_data_object}` | STORE DATA, SD state services and diagnostic tag mapping; existing RAM/flash size threshold |
| Prepare large Data | `payload::with_prepared_data_payloads` then typed attachment | One operation scope for up to two references; producer and attachment preconditions unchanged |
| Attach a package | `Mutation::insert_package_object` | GP LOAD authorization, block/hash/FAE checks precede attachment |
| Save instance / SD state | `Mutation::{upsert_instance_object, upsert_security_domain_object}` | Rustlet serialization, buffer clearing and resident reference updates retain their order |
| PUT KEY / inherited keys | `Mutation::{upsert_key_object, clone_scp03_keys}` | Authority checks, decoding, multiple-key scope and installation composition |
| SET STATUS | `Mutation::set_{package,instance,security_domain,key}_state` | GP target decoding and authority checks |
| DELETE | `Mutation::delete_object` | Validate dependency closure and authority before mutation; invalidate runtime references before deletion, with the same reverse-slot traversal |

`boot::init_on_reset` retains seed -> runtime hooks -> recovery/bootstrap order.
It assumes fresh volatile state, does not implement an arbitrary runtime reset,
and returns no new durability acknowledgement. Existing seed-error handling,
bootstrap suppression and fallback branches are unchanged. Recovery obtains
root identity from predeployment directly rather than calling `selected_app`.

`registry/physical.rs` is the single registry dependency on the flash backend:
geometry queries (`persistence_area`, `logical_page_size`, `erase_sector_size`),
mapped `read_area`, `program_page` and `erase_sector`. Re-exporting the backend
functions preserves their signatures, argument checking, errors and call order.
The storage compatibility reader delegates to `read_area`. LOAD page writes and
the diagnostic prefix-injection backend now use this same physical boundary;
injection selection and placement are unchanged. No extra flush, atomic write,
retry, allocation or validation is introduced.

Run `python3 scripts/check_registry_boundary.py` to audit the source dependency
boundary, in addition to compiler visibility checks. It rejects external access
to the global registry and direct flash backend references in the component or
its selected_app adapter. Flash-probe/SVC diagnostics using separately reserved
tails are outside this registry-area boundary; their initialization reservations
are unchanged. This lexical audit supplements Rust privacy, not a semantic proof.

The initial six refactoring lots are now represented: contracts, persistence,
transactions, scopes, payloads and consumer migration. The correspondence above
is the starting point for Rocq. It does not settle the open physical/integrity
obligations or establish reset behavior at every machine instruction. Existing
fault campaigns exercise selected write/erase prefixes and interruption of LOAD;
complete interruption coverage belongs to the formal transition model.

Step 4 validation: 218 host tests pass with both the default module set and
`OXIDE_SE_KERNEL_APP_MODULES=registry-test`. Two facade-level tests additionally
check provisional visibility with deleted/reused identity restoration, and a
rejected typed write preserving earlier staged changes. All pre-existing object
model tests moved with their unchanged implementation. The source boundary
audit, formatting and kernel library Clippy (`oxi_core/host-test`) pass.

Pico1 release builds (`thumbv6m-none-eabi`, Cortex-M0+) and QEMU validation
on 2026-10-15:

| Campaign (`cargo run --offline -- test <name> raspi-pico1 --on qemu`) | Result |
| --- | --- |
| `kernel_registry` | 1,498 checks; 192 replacements, 72 recycled sectors |
| `gp_registry` | 71 checks |
| `gp_predeployment` | 8 checks |
| `kernel_publication_integrity` | 1,691 checks, including the registry campaign and resident SD rollback |
| `gp_scp03_install_load` | 44 checks |
| `dyn_rustlet` | 1,786 checks across devkit and SCP03 |

All campaigns pass. The final registry run also includes the last mechanical
move of diagnostic volatile reads into `physical.rs`. Logs are in
`oxide-registry-step4/` (`registry-final.log` is the final registry run).
Counts overlap between campaigns and must not be summed as unique checks.
These checks characterize the implementation under emulation; none establishes
an electrical power-cut guarantee or discharges the open proof obligations.

## Header-CMAC and body-CRC format (2026-10-18)

Branch `registry/header-cmac-crc` starts from the CRC implementation (dceefa2),
with the same intrinsic benchmark harness as the 2026-10-16 baseline. The full
payload encryption experiment is archived at `registry/full-encryption`.
This section supersedes the earlier format-specific descriptions above.

All payloads, including BOSS entries, keys, Data and LOAD code, are clear.
The header alone is authenticated. CRC64/ECMA-182 covers the body plus erased
padding, excluding the header and final eight-byte CRC. This deliberately
accepts replacement of a body together with its recalculated CRC. LOAD retains
its GP transport hash and FAE checks; it has no persistent cryptographic body
authentication in this variant.

The common header is 32 bytes, with little-endian integers:

| Bytes | BOSS | Object (Data, key, state, LOAD) |
| --- | --- | --- |
| 0–3 | type magic | type magic |
| 4–7 | total page-aligned block length | total page-aligned block length |
| 8–11 | mutation counter u32 | useful payload length u32 |
| 12–15 | entry count u32 | zero |
| 16–31 | full AES-256-CMAC | full AES-256-CMAC |

There is no IV or encryption seed. The CMAC input is assigned format/zone
identifier `0x00020001`, actual zone-relative offset u32, and header bytes
0–15. HKDF-SHA256 derives a distinct header-only key from `get_puf()` with
salt `oXiDe registry header v2` and info `AES-256-CMAC`; the key is cached for
one boot. Its domain differs from full-payload encryption. Moving a signed
header to another address invalidates its CMAC. A separate area marker rejects
mixing the old formats. BOSS counter overflow rejects publication.

The scanner advances by the full block length only after bounded structural
checks and a valid header CMAC, even if the body's CRC is incomplete. Otherwise
it advances by one page. A BOSS also needs a valid body CRC to be selected.
CRC-valid bodies and header CMACs are checked during recovery before exposing
payloads. Body and entry views directly borrow flash, without decryption or a
plaintext cache. The compact baseline reference and entry sizes remain 8 and
44 bytes respectively.

Publication computes a new header CMAC once at the assigned address. It writes
header/body then the trailing CRC in sequential page order; no second header
programming is required. Successful physical programming verifies exact bytes.
A returned publication-write or recycling-erase error freezes further
publication writes until reset because a full BOSS might already be durable. The previous BOSS and all its references remain
protected during publication. Retirement still clears old nested magics before
recycling sectors.

During a transaction, unchanged slots reuse their previously validated
references. Known immutable live blocks are read through bounded trusted views
for comparison and protection, without repeating CMAC/CRC calculations. This
assumes serialized owner-controlled flash, as in the original RAM registry:
unexpected external modification is checked at recovery, not on each slice
read. There is no additional payload-sized allocation; physical programming
uses the existing page and serialization scratch buffers, and the streaming
Data writer keeps one page plus a 32-byte header.

To avoid repeated CMAC work during circular allocation/recycling, two bits per
physical page cache an authenticated or rejected header result (64 bytes for
the 64-KiB diagnostic area). Only mapped physical headers at their real offset
use this cache; RAM fixtures always compute the CMAC. Every page program and
sector erase invalidates overlapping entries BEFORE touching flash, including
fault-injected/failed operations and retirement. Newly generated headers are
remembered only after exact successful physical readback. Reset clears this
volatile metadata. No body checksum result or payload bytes are cached here.

## Data-only encryption and destination-buffer extraction (2026-10-18)

Branch `registry/data-body-encryption` extends the fast-XIP header-CMAC baseline
(`243b9af`). This section supersedes the preceding clear-Data description.
Only `ManagedObjectKind::Data` bodies are encrypted. Keys, instance/SD state,
LOAD and BOSS remain clear, with their existing authenticated header and body
CRC. LOAD still follows its existing GP hash/FAE validation and XIP execution.

The internal `RegistryObject::read_range(start, out)` API extracts at most
`out.len()` logical bytes, returns the actual count, returns zero at EOF, and
rejects an index beyond EOF without changing the destination. Bytes after the
returned count are untouched. `content_len()` returns the logical length.
For keys the content is raw key bytes; for instance/SD objects it is serialized
state, excluding persistence metadata. Package code is rejected; BOSS is not a
runtime object. Callers retain responsibility for authority checks. This does
not add a Rustlet syscall or expose privileged keys to untrusted code.

Encrypted Data has distinct magic `0x600DDA7A` and a 32-byte header:

| Bytes | Meaning |
| --- | --- |
| 0–3 | encrypted Data magic |
| 4–7 | logical plaintext length, u32 little endian |
| 8–15 | encryption seed, u64 little endian |
| 16–31 | existing address-bound header CMAC |

Its physical size is `align_page(32 + align_16(logical_length) + 8)`. Only the
useful body and its final AES-block padding (0xff) are encrypted; remaining
page padding stays 0xff. The final CRC64 covers ciphertext and page padding.
The authenticated logical length bounds extraction, so padding is never
returned. The scanner derives the extent from this length and skips the extent
only after header authentication; rejected headers still advance one page.
The new area marker `0x600FB055600FB006` requires explicit reinitialization;
there is no migration of the previous format.

Two independent AES-256 keys are derived from `get_puf()` using HKDF-SHA256,
salt `oXiDe registry Data v3`, and labels `IV/AES-256` and
`body/AES-256-CBC`. The header-CMAC key is unchanged and separate. Keys are
cached once per boot. The IV is AES-ECB(Kiv, domain `0x00030001` || physical
zone-relative offset u32 || seed u64), with little-endian fields. A random
64-bit seed is drawn at first encryption after boot; each encryption attempt
consumes the next value before writing, including aborted/failed attempts.
Counter exhaustion rejects further encryption for that boot. Pico1's existing
ROSC entropy backend and firmware-UID-based `get_puf()` remain development
limitations; this change does not claim to remedy either.

CBC extraction reads the previous ciphertext block as the chaining value, or
computes the initial IV for block zero. It decrypts only intersecting blocks.
The oxi-core `aes_cbc_decrypt_range_into` primitive expands the key once per
range and decrypts complete blocks directly from flash into the destination,
using the AES backend batch path (two blocks on Pico1); one
reusable 16-byte scratch block handles unaligned edges, and a 16-byte chaining
value is retained. AES key expansion and primitive-local stack are additional
to those 32 bytes. No object-sized allocation, plaintext cache, or repeated
header/CRC verification occurs on reads. Recovery checks header and CRC and
retains a flash reference, even for small Data. Publication retains unchanged
references and their original seeds; it does not reencrypt unchanged objects.
Staged small Data from the internal mutation API is rebound to ciphertext and
scrubbed after successful durable publication.

The Data streaming writer encrypts directly in its existing page buffer and
carries the CBC chaining value across pages. It computes CRC incrementally and
relies on the backend's exact programmed-byte verification, avoiding a second
body scan. Publication, rollback protection and recovery still operate on the
same immutable referenced extents. Diagnostic prefix cuts count across streamed
pages, rather than restarting their position at each page.

The body remains protected against accidental corruption by CRC, **not by a
cryptographic MAC**. Encrypting Data does not change that previously accepted
integrity contract; CMAC authenticates only the header.

## Flash references and encrypted state/key bodies (2026-10-19)

This section supersedes the Data-only scope above. The registry's RAM entries
contain identities, administrative metadata and immutable flash references.
Security Domain state, instance state and key material are no longer retained
in per-entry plaintext arrays. Object creation/replacement writes its body
before attaching the new RAM reference. Commit publishes BOSS references;
unchanged bodies are neither copied nor rewritten. BOSS and LOAD remain clear.

Recycling protects the union of the current RAM registry and last committed
BOSS, including the BOSS itself. Nested rollback references and incomplete LOAD
reservations remain roots until released. Aborted object writes need no physical
undo; after their last reference is released they are eligible for recycling,
subject to sector erase geometry. The existing uncertain-write freeze remains.

Encrypted state blocks use magic `0x600DFADE`, encrypted keys `0x600D4B45`, and
Data retains `0x600DDA7A`. All use the existing seed/length/CMAC header and bounded
AES-CBC extraction. The new area marker is `0x600FB055600FB007`; deployment must
explicitly reinitialize the area. No in-place migration from earlier markers is
implemented. Key derivation retains the existing separate body, IV and header
keys; the historical `Data v3` KDF label now serves all encrypted body families.
CRC64 covers ciphertext and page padding, while CMAC authenticates the header
and its address context, not the body.

State/key metadata prefixes are encrypted too: 25 bytes for Security Domains,
21 for instances, 9 for keys. Pad that prefix with `0xff` to 32/32/16 bytes
respectively, then append logical content and AES padding. The aligned body
start avoids decrypting an extra block or deriving the initial IV on ordinary
state/key reads. The header length includes prefix padding plus logical content.
The physical length is `align_page(32 + align_16(prefix_storage + content) + 8)`.
Data has no metadata prefix and retains its 208-byte one-page useful capacity.
With 256-byte pages the one-page useful state/key capacities are 176/176/192
bytes. Padding can change flash allocation and erase frequency.

Recovery decrypts only the bounded metadata prefix (at most 25 returned bytes),
then attaches references. It does not decrypt or cache complete states or keys.
Lifecycle flags come from BOSS, so unlocking a key never requires rewriting its
immutable body. SCP03 inheritance shares immutable key content under distinct
owner-qualified entries. Later replacement changes only the target reference.

`RegistryObject::read_range(start, out)` extracts directly into caller storage,
with the same EOF, bounds, authority and destination-tail contracts as Data.
Rustlet state extraction writes directly into the shared state half, then zeros
its unused tail and publishes length. Key readers write into their caller's key
storage; selector resolution reads metadata without decrypting companion keys.
There is no whole-object read cache. Neutral serialization compares against the
stored content using existing publication scratch, scrubs it, and avoids a new
flash version; this comparison still has a decryption cost. Pico1 programming uses
the existing 512-byte publication scratch and scrubs it on success or failure.
Targets with larger logical pages reuse the existing physical-page scratch;
a pending LOAD page is preserved temporarily, as in BOSS publication.

Host tests and targets without registry flash retain immutable reference-counted
volatile content, scrubbed when the final owner is dropped. On targets without
registry flash, the compact image and the rollback snapshots refer to RAM slots.
A slot is reusable once the current image and all active rollback snapshots
release it. Commit retains the RAM image, and reset starts a fresh registry.
On persistent targets, the journal and authenticated snapshots remain the
backing store. The migration/measurement record is in
`docs/registry.flash-reference-migration.md`.

### Whole-block CMAC, no CRC (2026-10-19)

This section supersedes the header-only CMAC and trailing CRC rules above.
The area marker is `0x6010B0556010B007`; older areas require reinitialization,
not an in-place conversion. The 32-byte header contains 16 bytes of metadata
and one 16-byte AES-256-CMAC. There is no trailer. Authenticate the concatenation
of `LE32(0x00040001) || LE32(area_relative_offset) || header[0..16] || block[32..]`.
The body includes all stored ciphertext and page/MPU padding. BOSS and LOAD stay
clear, with their complete stored bodies covered by the same authentication.
The authentication key uses HKDF-SHA256 from `get_puf()`, salt
`oXiDe registry block v4`, info `AES-256-CMAC`. Body and IV derivation are unchanged.

Encrypted block size is `align_page(32 + align_16(prefix_storage + content))`.
A 256-byte page now holds 224 useful Data bytes, 192 SD/instance state bytes,
or 208 key bytes, with the existing aligned metadata prefixes. Clear blocks
use `align_page(32 + payload)` and LOAD may retain additional MPU padding.

Scanning checks magic and bounded lengths before touching a candidate body.
Only a complete valid CMAC authorizes a block-sized jump; otherwise advance one
page. Unlike the former independently authenticated header, a damaged body
cannot hide its interior pages. A genuinely signed BOSS at its original address
inside such a damaged container can therefore become discoverable. Authentication
does not provide anti-replay protection; arbitrary payload headers and transplanted
tags are rejected. Recycling still neutralizes recognizable interior magic words
before erasure, but the old guarantee of an opaque extent throughout interrupted
neutralization no longer applies once the outer CMAC becomes invalid.

The existing two-bit-per-page RAM cache now records whole-block validation.
It is used only for mapped physical blocks at their actual address. Before every
owner program/erase, invalidate all overlapping cached extents, including rejected
candidates and earlier headers whose bodies overlap the write. Other cached blocks
remain reusable. No body-sized RAM cache is added; trusted range reads continue
decrypting only the requested blocks into caller storage. Unobserved external flash
changes after validation are outside this cache's guarantee.

Buffered publications compute the tag after encryption, then program and verify
the block. Streamed Data retains the first page in existing shared scratch, writes
the remaining pages, computes CMAC over the staged prefix and XIP tail, then writes
the first page once with its tag. LOAD spans APDUs and leaves its tag erased until
the body is complete. It computes CMAC directly from XIP and reuses the page scratch
to program the first page with the tag, without copying or decrypting the full body.
Only LOAD needs an additional first-page program for this final tag. Successful
backend readback permits caching validation without a second CMAC pass. An omitted
write of padding already equal to erased flash is not an incomplete message.

The physical Pico1 before/after benchmark is deferred. The prior
header-CMAC/CRC run measured header authentication only.

### BOSS/LOAD header CMAC and embedded CRC32 (2026-10-19)

This supersedes whole-block CMAC for BOSS and LOAD only. Other objects retain
whole-block CMAC and their existing encryption. All headers remain 32 bytes;
there is no trailer. Integers are little-endian.

| Bytes | BOSS | LOAD |
|---|---|---|
| 0–3 | magic | magic |
| 4–5 | total length in logical pages, u16 | total length in bytes, u32 (4–7) |
| 6–7 | entry count, u16 | continuation of total length |
| 8–11 | mutation counter, u32 | useful payload length, u32 |
| 12–15 | body CRC32 | body CRC32 |
| 16–31 | header CMAC | header CMAC |

CRC32 covers every byte from offset 32 through the end of the stored block,
including page/MPU padding. Polynomial 0x04C11DB7, initial zero, non-reflected,
no final XOR (check value for ASCII 123456789: 0x89A1897F). It detects accidental
corruption, not deliberate CRC collisions. CMAC authenticates the expected CRC,
the metadata, and the physical placement, but not the body cryptographically.

The area marker for this header format was 0x6010B0556010B008. The CMAC context identifier is
0x00050001 and HKDF salt is 'oXiDe registry block v5'; older formats require
reinitialization, with no compatibility reader. BOSS/LOAD CMAC input is context,
offset and header bytes 0–15; other types additionally include the stored body.

Recovery scans authenticated extents and selects the largest BOSS counter.
Only that candidate's body is checked; corruption triggers selection of the
next candidate (physical offset breaks equal-counter ties). Retry scans reuse
header validation and allocate no candidate list. LOAD CRC is checked before
exposing its payload, not while scanning. Authenticated LOAD/BOSS extents remain
opaque even if their body is damaged.

The existing two-bit cache distinguishes unknown (00), rejected header (01),
validated body (10), and authenticated header with unchecked/invalid CRC (11).
Header-only state never permits trusted body access. Owner writes/erases
invalidate overlapping entries. There is no added RAM table or payload buffer.

Streamed LOAD reserves the CRC and CMAC bytes erased, computes CRC directly
from XIP after final payload checks, and programs CRC plus header CMAC using
the existing shared page buffer. Successful publication caches full validation.
Performance measurements are deferred; the smoke validation uses QEMU Pico1.

### BOSS address journal and deferred object authentication (2026-10-20)

This superseded the full-flash BOSS discovery described above. Its area
marker was `0x6010B0556010B009`; existing flash from an older layout was
reinitialized. The final two 4-KiB erase sectors of the core persistence area
are excluded from object allocation. The registry test image reserves 72 KiB
so its usable object area remains 64 KiB.
The normal Pico1 linker reserves 256 KiB for registry persistence, leaving
248 KiB for BOSS, LOAD and object blocks after the journal reservation.

The primary sector is an append-only sequence of eight-byte entries: a little-
endian 32-bit BOSS byte offset followed by its bitwise complement (also little-
endian). This supersedes the original CRC32 journal encoding; the LOAD body CRC
is unchanged. Old flash images must be explicitly reinitialized. A commit publishes the BOSS first, then its
journal entry; the latter is the durable commit point. Recovery tries entries
from newest to oldest, rejecting torn entries and BOSS blocks whose header
CMAC or body CRC fails. It never promotes an unjournaled BOSS found in flash.

When the primary sector is full, the secondary sector temporarily stores the
last validated BOSS offset and its complement. Rotation erases the primary, restores that
address as its first entry, then erases the secondary. Boot completes an
interrupted rotation before reading the primary. No additional RAM page buffer
is allocated: journal writes use the existing flash-page scratch.

After authenticating the selected BOSS, boot reconstructs only structural
references and small encrypted metadata prefixes. It does not authenticate
every live object body. Runtime object lookup or range extraction checks the
object CMAC on first access, using the existing two-bit validation cache on
later accesses. LOAD stays clear and retains its header CMAC plus body CRC32;
its body is checked before returning executable bytes. The BOSS identity graph
is checked at boot; privilege bytes are checked when their object is used.

The same `kernel_registry` performance campaign on the physical Pico1 gives:

| Measurement | Previous full scan | Journal + deferred authentication |
|---|---:|---:|
| Recovery, warm boot 1 / 2 | 2.336 / 2.452 s | 0.104 / 0.102 s |
| ATR, warm boot 1 / 2 | 2.509 / 2.629 s | 0.304 / 0.301 s |
| ATR, noisy flash | 2.388–2.392 s | 0.305–0.309 s |
| ATR, near-full flash | 2.675–2.680 s | 0.310–0.318 s |
| Write 244 B, median device time | 440.228 ms | 456.242 ms |
| Read 244 B, median device time | 28.544 ms | 28.775 ms |
| Hot read 244 B, median device time | 22.889 ms | 22.944 ms |

The write median increases by 3.6% because each durable BOSS publication also
programs one journal page. The measured read medians change by less than 1%.

### Circular allocation after BOSS (2026-10-20)

The normal append cursor still reserves erased pages directly. If that exact
placement is unavailable, allocation makes one circular traversal starting
immediately after the current BOSS and wrapping at the end of the usable area.
At each page it tries erased space; at erase-sector boundaries it remembers
the first complete sector that could be recycled without touching protected
ranges or crossing a surviving block boundary. Only if no erased placement
exists anywhere in the one traversal does it recycle that remembered sector.
Both erased-page reuse and recycling thus rotate from the BOSS, while avoiding
an unnecessary erase when an erased hole is available later in the circle.
The normal append path is unchanged.

Validation: 244 host tests and 2,258 `kernel_registry` checks on Pico1 QEMU
pass. Its sustained 192-replacement fixture erases 72 sectors, the same count
as before this change. The full intrinsic benchmark on the physical Pico1
passes 495 checks. Compared with the preceding journal build, it measures:

| Physical Pico1 metric | Before | Circular allocation |
|---|---:|---:|
| Allocation, create median | 1.220 ms | 1.238 ms |
| Allocation, replace median | 1.696 ms | 1.726 ms |
| Write APDU median, all 165 writes | 386.797 ms | 410.793 ms |
| Write APDU median, 244-byte objects | 456.242 ms | 441.562 ms |
| Warm recovery, two runs | 103.530 / 102.281 ms | 102.564 / 102.650 ms |
| Last large-object size retained | 4,097 B | 225 B |
| Additional 4,096-byte capacity write | accepted | rejected |

The allocation medians change by about 2%; the APDU write medians move in
opposite directions depending on the subset. Under pressure, the new circular
order changes the flash layout and fragments the free space earlier in this
fixture. This is a capacity trade-off, not evidence that the same flash image
lost an otherwise valid candidate: the fallback still traverses every page
and every eligible sector. The benchmark does not isolate a timing benefit
under pressure because its accepted object sequence diverges at the first
capacity rejection.

### Encrypted BOSS body (2026-10-20)

This format replaces the clear BOSS body and its CRC32. The area marker is
`0x6010B0556010B00A`; older registry images are reinitialized, with no mixed
reader. The 32-byte BOSS header contains magic (0–3), useful plaintext length
(4–7), a fresh 64-bit encryption seed (8–15), and a full AES-CMAC tag (16–31).
The ciphertext starts at byte 32 and covers the generation (u64), every
44-byte registry entry, and zero padding through the physical page boundary.
The plaintext generation must fit the runtime u32 mutation counter. AES-CBC
uses BOSS-specific HKDF-derived encryption and IV keys; the existing seed
allocator is shared with encrypted objects but the keys and IV context differ.

The BOSS CMAC authenticates its header and all ciphertext at the physical
address. Journal recovery verifies this complete tag before decrypting the
generation or entries. A single entry can be read by range into a 44-byte
local destination. Boot and publication decrypt the BOSS once into the
existing 4-KiB page scratch, consume its entries, then zero that scratch;
there is no second complete BOSS allocation or plaintext flash view. The same
page buffer encrypts the new BOSS in place. Runtime references are populated
during the first boot pass; publication compares old and new entries while
reusing the existing entry array.
LOAD remains clear, with header CMAC and body CRC32. The BOSS and LOAD magics
remain unchanged, while the CMAC key domain moves to version 6.

The full `kernel_registry` intrinsic campaign was replayed on the physical
Pico1, starting each image from erased flash and using the same 12-MHz CPU and
test manifest. Both versions pass 495 checks. Device timings are medians:

| Measurement | Clear BOSS, circular allocator | Encrypted BOSS | Change |
|---|---:|---:|---:|
| Write APDU, all 165 writes | 410.793 ms | 522.294 ms | +27.1% |
| Write APDU, 244 bytes | 441.562 ms | 592.895 ms | +34.3% |
| Read APDU, 244 bytes | 28.718 ms | 28.485 ms | −0.8% |
| Hot read APDU, 244 bytes | 23.067 ms | 22.992 ms | −0.3% |
| BOSS publication, replace median | 64.940 ms | 249.019 ms | +283.5% |
| Recovery, warm boots 1 / 2 | 102.564 / 102.650 ms | 248.384 / 247.796 ms | about +145 ms |
| ATR, warm boots 1 / 2 | 0.298 / 0.310 s | 0.447 / 0.439 s | +0.149 / +0.129 s |
| ATR, noisy flash | 0.311–0.312 s | 0.436–0.456 s | about +0.14 s |
| ATR, near-full flash | 0.314–0.319 s | 0.494–0.502 s | about +0.18 s |

The BOSS CBC and whole-body CMAC dominate publication and recovery; normal
Data reads do not touch the BOSS after boot. The benchmark's later flash layout
diverges: the clear-BOSS run rejected 17 large writes and retained a 225-byte
last large object; the encrypted-BOSS run accepted all of those writes and
retained 8,193 bytes. Timings and capacity in that phase are therefore not
paired measurements of identical flash states. The observed maximum stack
watermark is 4,336 bytes in both runs, and no additional full-BOSS buffer was
allocated. Host tests (245), the Pico1 QEMU functional campaign (2,256 checks,
72 recycled sectors), and a Pico2 registry-image build pass.
The fresh, erased-flash ATR includes bootstrap and journal initialization:
1.077 s before, 1.202 s after. Both campaigns used the same 64-KiB object area
and 15 samples per 244-byte operation; the physical journal campaign passed
495 checks. The complete QEMU registry campaign passed 2,254 checks.
The `registry-test` firmware image also builds for Pico2; the physical
functional and performance campaign here used Pico1 only.


### Journal complement encoding — 21 October 2026

Each valid offset/complement word has exactly 32 set bits. A monotone change
(only 1->0 or only 0->1) cannot turn it into another valid word. An interrupted
program from FF followed by a partial erase remains a bitwise superset of the
intended word, and cannot validate a different offset. Thus an interrupted erase
of the secondary backup can leave the same entry valid or invalidate it; it
cannot retarget that entry to another authentic provisional BOSS.

These are encoding properties under the stated physical model, not a completed
proof of rotation/recovery. Preservation of unchanged bytes in page reprogramming,
the primary/secondary invariant and repeated recovery cuts remain formal
obligations. The layout remains eight bytes per entry, with unchanged RAM and
flash operation count. No CRC normalization or sector generation is added.


## Journal error freeze (2026-10-22)

An error returned by a journal program, sector erase, or post-program readback
sets the existing sticky uncertainty latch before returning to the caller.
Further journal append, initialization and recovery attempts are rejected in
the same boot. Registry physical program/erase and reusable-span allocation
also reject work while frozen, including writes for an already active LOAD.
Only reset clears the production latch; recovery must then succeed before a
new publication can be acknowledged.

RAM rollback can still close scopes. Scope release and final collection retain
their existing conservative freeze behavior. Unattached snapshot, content and
LOAD reservations now use a guarded release helper, retaining their pages when
the outcome is uncertain. No new RAM state, flash encoding or ordinary-path
flash operation is introduced.

The host regression executes the real journal with a simulated flash transport
and the host BOSS encoder/decoder: fill primary with A, fail the secondary erase
without effect during append(C), reject append(D) and all further journal flash
work, then simulate reset, recover A, publish D and recover D on the next reset.
It also checks retained reservations and errors from programming and the
journal's additional readback. This is a control-flow regression, not a model
of electrical faults or a proof of the complete allocator/cryptographic stack.

Validation of this correction: 270 host library tests passed; Cortex-M0+
firmware builds and QEMU Pico1 campaigns `kernel_registry` (2276 cases) and
`gp_scp03_install_load` (44 cases) passed. The injected D-to-A regression runs
on the host transport; the QEMU campaigns exercise their existing recovery,
recycling and LOAD scenarios. `git diff --check` passed. Strict host Clippy
including tests still reports eight existing lints outside the changed logic
(svc_profile, data_crypto, publication's test branches, test-module placement
and time_manager); they were not changed in this correction.


## Data pair scope and reservation ownership (2026-10-22)

`write_registry_data_objects` compares values before opening a local scope.
If every value is unchanged, it returns without snapshot, reservation or
publication and preserves any dirty state already present in the caller.
Changed members keep their original producer indices; repeated tags keep
sequential replacement semantics.

One operation scope now surrounds the entire pair: prepare A, attach A,
prepare B, attach B, then accept the scope. Snapshot preparation completes
before an image mutation. There is at most one unattached Data reservation
in this path. Allocations belong to the local scope; failure of B restores
the prestate of the pair, including A. Scope acceptance inside a parent is
provisional; only final transaction commit publishes. No collection runs
between preparation and attachment; existing outer-scope retirement performs
collection when its guards permit it.

`DataReservation` is a non-Copy, non-Clone token with private fields and no
raw-reference accessor. The typed mutation facade consumes it at attachment.
The token relinquishes cleanup responsibility only after successful image
attachment. Before that point, Drop releases its RAM page reservation without
writing or erasing flash; the existing uncertainty latch suppresses release
when frozen. An invalid release follows the existing fatal/freeze policy.
Preparation errors and attachment errors therefore clean up before local
rollback. A reset does not run Drop: crash safety still depends on recovery
and the persistent publication protocol. The single outstanding token and
its scope lifetime follow from this caller's lexical control flow; the type
alone does not enforce a general transaction-lifetime discipline.

Regression coverage includes token abandonment, frozen abandonment, failed
attachment and successful ownership transfer on the host. A QEMU diagnostic
uses the real encrypted writer to check rollback after A is attached and B's
size is rejected, preservation of producer indices when only B changes,
repeated tags, unchanged values, and enclosing rollback. Existing campaigns
continue to cover torn writes, recovery, recycling and publication failures.

Validation: 270 host library tests passed. The Cortex-M0+ firmware compiled
for `thumbv6m-none-eabi`; QEMU Pico1 campaigns `kernel_registry` (2275 checks,
including the new pair diagnostic) and `gp_scp03_install_load` (44 checks)
passed. `git diff --check` passed. Logs: `registry-data-scope-host.log`,
`registry-data-scope-qemu.log`, `registry-data-scope-load-qemu.log`.
No Rocq source or proof documentation was changed by this implementation.
