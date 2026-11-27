# Assumptions and outstanding supplier obligations

The registry theorem proves a component contract under explicit supplier laws,
an initialized entry condition, and operational service executions. These are
three different kinds of premise. A supplier law is not an assertion that the
Rust implementation has been verified, and a service execution is not a promise
that the service always terminates.

The authoritative statements are [OwnedDataContract.v](theories/interface/OwnedDataContract.v),
[OwnedDataRequirements.v](theories/registry/semantics/OwnedDataRequirements.v),
[OwnedDataInvariant.v](theories/registry/semantics/OwnedDataInvariant.v), and
[OwnedDataServices.v](theories/registry/semantics/OwnedDataServices.v).
The [component map](Components.md) identifies the corresponding Rust boundaries.

## Physical flash contract

[FlashSpec.v](theories/suppliers/FlashSpec.v) and
[FreerFlash.v](theories/suppliers/FreerFlash.v) specify the physical interface:

- Reads faithfully observe the flash state.
- Successful programming and erasure have their exact effects before returning;
  their results are visible and durable. Calls are sequential.
- Interrupted programming changes only a subset of the requested 1→0 bits within
  the target page. No ordering of bits or bytes within the page is assumed.
- Interrupted erasure changes only a subset of 0→1 bits within the target sector.
- A returned `VerifyFailed` can retain physical effects, including a completed
  write. It is not evidence that nothing was written.
- Effects are confined to the target range. Bytes copied unchanged remain unchanged.
- Reset preserves the reached flash and abandons the interrupted continuation
  and volatile state. It does not execute destructors or rollback.

The flash state maps addresses to bytes in 0..255. Valid initial bytes and valid
geometry are environment preconditions. Physical operation relations cover
admissible requests; argument rejection is a distinct no-effect case. The
FreerDPS caller must establish request admissibility. Arithmetic in these
relations uses unbounded numbers; concrete machine-width correspondence is a
separate software obligation.

A `VerifyFailed` with an exact completed image is an explicit overapproximation
of a verification error after readback. Erase errors may likewise retain partial
effects. Identical possible physical images do not equate an error continuation
with a reset.

The model assumes no spontaneous corruption outside these operations. It does not
assume atomic pages, sectors, or journal slots. The relation between the concrete
oxi-core backend and these assumptions remains to be established for each target.
The modeled unit read does not require Rust to perform byte-by-byte reads.

## Permanent supplier laws

`owned_data_suppliers` groups the laws required by the component theorem.
Their concrete interpretation is given by
[OwnedDataBinding.v](theories/composition/OwnedDataBinding.v).

| Required law | Meaning and remaining obligation |
| --- | --- |
| `journal_geometry g sector 256`, `sector mod 8=0` | Journal layout and slot alignment. Relate logical coordinates to the configured flash regions. |
| `validator_accepts_decoded` | A successfully decoded BOSS is accepted by the validator on the same flash. Establish this for concrete decoding and validation. |
| `forall c, incarnation_reader_local ranges decode c` | Preserving a live certificate's byte ranges preserves its decoding. This does not itself preserve those bytes. |
| `marker_header_covered marker` | The protected marker extent covers the marker header. |
| `journal_object_mapping data_len pages`, `mapped_pages pages` | Journal/object coordinates and mapped page geometry agree. |
| `decoding_address_contract decode` | Decoded roots satisfy the address constraints consumed by installation. |
| `range_numeric word_max marker` | The marker extent passes the numerical range checks. |
| `decoded_numeric_contract word_max ranges decode` | Decoded ranges satisfy the numerical representation constraints. |
| `1024*256<=word_max` | The numeric representation can cover the modeled page table. |
| `area_start g+area_length g<=2*sector+1024*256` | The configured area fits the modeled journal and object regions. |
| `decoded_allocation_geometry pages decode` | A decoded root supplies the geometry required by allocation and cursor reconstruction. |
| `mapped_registry_base base` | The registry mapping supports the absolute-address calculations used by installation. |

These laws are parameters, not new Rocq axioms. Their implementation proofs remain
open. In particular, successful decoding must not be replaced by an assumed
transactional safety guarantee.

## Initial entry condition

`owned_data_entry` requires an initialized, usable owner-controlled boundary,
its numeric guarantees, and closed owner control. `owner_invariants` includes:

- safety and the relation between physical journal history and protected roots;
- raw journal order;
- coherent page-table and runtime metadata;
- generation-reader agreement and locality, and coherent runtime counter state;
- allocation metadata, durable-range provenance, and cursor bounds;
- coherent `latest_registry`, external scope structure, and a recognized marker.

The two generation-reader laws are exposed by `owned_data_entry_reader_laws`.
They remain supplier laws even though they are carried in the entry record.

The initial condition is supplied once. The modeled transitions transport or
reconstruct the required facts for later calls. After reset, usable recovery
rebuilds RAM observations; it does not reuse interrupted RAM. A marker alone is
not proof of a first durable publication. Producing this entry condition from
an interrupted first initialization is outside the current theorem.

## Local service contracts and actual executions

The service parameters retain their local scope:

- `boss_generation_format` relates the BOSS writer plan and its completed
  execution to decoding the expected image and generation.
- `boss_check_provider` relates envelope/format checks, authentication, and
  generation reads to logical decoding. It permits crypto-service errors,
  including after a successful writer and on a cache hit.
- Writer plans and command executions must correspond to the actual Data/BOSS
  bytes and flash calls. Errors and resets retain the reached flash.
- The range resolver must enumerate the correct extents for compact entries.
  Collection's returned mask must agree with `collect_ranges`.
- Prepass comparison must correspond to the requested contents and original
  producer indices. The behavior of a mutable Data callback between comparison
  and writing must be justified rather than silently assumed stable.
- Operational search, restoration, decoding, and validation responses must be
  produced by their concrete implementations.

The component derives transactional protection, closure conditions, and
receipt discipline from those services. It does not accept a final safe state
as a substitute for their execution. Resource availability and successful
termination are not guaranteed by the existence of the component theorem.

## Cryptographic boundary

There is no standalone verified `CryptoAPI` or global probabilistic security
proof in this development. Functional format/reader/validation contracts and
modeled crypto errors express the guarantees currently used. The software
wrappers and primitive assumptions must be distinguished when those suppliers
are implemented and verified.

The relevant Rust modules are `data_crypto.rs`, `boss_crypto.rs`, and
`header_auth.rs`, using oxi-core AES-CBC, AES-ECB, CMAC, and key derivation.
Key provisioning, seed generation, domain separation, authentication, and
confidentiality have separate obligations. An authentic prepared BOSS need not
be published; authentication alone establishes neither freshness nor authority.
The LOAD body CRC is not a cryptographic authenticity guarantee.

The current [device-root provider](../../kernel/core/src/core/puf.rs) uses the
firmware image UID as a development substitute, not a qualified hardware secret.
Identical firmware images share that root; its stability over the lifetime of
the persistent image is required. A claim made under a secret-root assumption
must not be presented as a guarantee already supplied by this implementation.

Seed/IV uniqueness across boots and devices requires a separate argument about
the generator, domains, and key sharing. No automatic probability bound follows
from a 64-bit seed. The raw erase relation carries no probability distribution;
a cryptographic claim about interrupted erase needs an explicitly defined
experiment and failure assumptions. Functional crash safety must remain distinct
from resistance to hostile modification or replay.

## Library axioms

The FreerDPS compositions inherit these three `boolp` principles:

- `boolp.constructive_indefinite_description`;
- `boolp.functional_extensionality_dep`;
- `boolp.propositional_extensionality`.

They are library dependencies, not flash or cryptographic guarantees. The audit
entry points print the assumptions of the exposed results. No additional project
axiom or `Admitted` is used to establish the component result. Ordinary premises
must still be reviewed: `Print Assumptions` alone does not establish that a
supplier contract is realizable or that an entry condition is non-vacuous.

## What the result does not establish

The theorem covers the modeled owner-controlled Data slice after successful
initialization. It does not establish complete Rust refinement, supplier
implementations, requested-versus-recovered Data byte equality, interrupted
bootstrap, LOAD streaming, general joined/nested callers, unconditional
termination, or capacity availability. See [ProofPlan.md](ProofPlan.md) for the
remaining verification work and [Statement.md](docs/Statement.md) for the result.
