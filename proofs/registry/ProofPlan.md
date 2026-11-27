# Remaining verification work

The [component theorem](theories/composition/OwnedDataComponent.v) establishes
transactional safety for modeled owner-controlled Data operations after
successful initialization. Its supplier contracts and operational executions
are explicit. This document identifies the obligations required to extend that result.

The [component map](Components.md), [assumption register](Assumptions.md), and
[Rust implementation map](ImplementationMap.md) identify the boundaries to use.
Follow the [freerSpec method](FreerSpec.md): prove each supplier's required
contract, then bind that implementation to the existing consumer.

## Establish the software suppliers

| Obligation | Expected result |
| --- | --- |
| Data comparison and writing | Relate callback bytes, prepass equality, writer plans, and recovered contents. Preserve original producer indices and repeated-tag semantics. |
| BOSS encoding and decoding | Establish `boss_generation_format`, generation agreement, reader locality, address constraints, and validation acceptance for the concrete formats. |
| Range resolution and collection | Show that resolved extents and `collect_ranges` cover the actual objects and roots; justify every concrete enumeration path. |
| Mapping and numeric representation | Establish the configured region layout, finite-width arithmetic, marker coverage, and decoded allocation geometry. |
| Page-table representation | Relate four-bit entries, authentication bits, ownership summaries, and mutation checks to the single abstract table. |
| Flash-command production | Show that concrete writers, neutralization, erasure, and journal operations generate the modeled commands and prefixes. |
| Crypto wrappers | Separate primitive security assumptions from functional correctness of derivation, IV construction, encryption, authentication, and cache use. |

A supplier proof must cover successful responses, errors, and interruptions
where applicable. It must not hide a registry safety invariant in its own
postcondition. Prove that caller obligations hold before each effect.

## Establish the initial entry boundary

Relate concrete initialization to `owned_data_entry`: a first durable root,
recognized marker, coherent image and runtime, initialized page table, correct
cursor/range metadata, and closed owner control.

Treat reset at every initialization stage. A marker alone is insufficient to
establish a durable root. Distinguish authorized bootstrap, absent persistence,
invalid data, and fatal recovery. Prove the actual initialization order and the
restart policy rather than inferring them from a successful boot test.

## Extend the API coverage

The current owner-controlled slice does not cover every registry client.
Separate extensions are required for:

- joined operations with an active parent and general physical deferred snapshots;
- all six nested scope levels, including rollback notifications and shared roots;
- LOAD preparation, streaming across APDUs, sealing, attachment, and abandonment;
- other object families and their metadata/state transitions;
- all callbacks and client adapters beyond the modeled owner-controlled path.

Keep one shared image, journal, and page table in the model. Do not create
independent states for components that access the same Rust globals. Compose
each extension with the existing recovery and publication relations.

## Refine the Rust implementation

The implementation map is a manual correspondence. A complete Rust claim needs
a justified refinement from actual execution to modeled steps, including guards,
indices, conversions, borrows, Drop behavior, error returns, and panic paths.

The refinement must preserve the distinction between physical publication,
append success, runtime synchronization, and delivery to the client. A reset
must discard the continuation and volatile state without inventing cleanup.
A returned error must retain any physical effects already performed.

## State separate security and availability claims

Transactional crash safety does not imply cryptographic authenticity against
arbitrary flash modification, confidentiality, anti-replay security, or capacity
availability. Specify these goals separately before proving them.

In particular, qualify key/seed provisioning and cross-boot IV behavior; do not
assign an automatic probability bound from seed width alone. The LOAD body CRC
requires its own integrity argument. Recovery termination requires conditions
such as a sufficiently long interruption-free interval and successful services.

## Completion criteria

For each obligation, record:

1. the consumer that uses the new result;
2. the premise replaced by a supplier implementation proof;
3. any remaining physical, cryptographic, configuration, or software assumptions;
4. the additional concrete execution paths covered.

Keep the public documentation focused on the resulting contracts and scope.
Development reports and exploratory notes belong outside the published proof
documentation.

Use the [Rocq 9 checks](README.md#reproducing-the-checks), including `coqchk` and
`Print Assumptions`, when changing proof sources. Review ordinary premises as
well as global axioms. Compilation alone is not a Rust-refinement proof.
