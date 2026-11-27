# Transactional registry proof

The kernel-managed registry is a worked example of oXiDe-SE’s approach to
program verification. A component states what it requires from the services it
calls and proves what it guarantees to callers under those contracts. This
development establishes transactional safety for the model of owner-controlled
Data updates after successful initialization. The rest of the kernel is
outside its scope. The proof assumes that the services the registry calls
satisfy their contracts. Establishing those contracts for the concrete suppliers
and proving that the Rust implementation follows the model are separate proof
obligations. See the [scope of the result](docs/Statement.md) and the
[Rust-to-Rocq implementation map](ImplementationMap.md). The
[component contracts](Components.md) detail the supplier obligations.

## What callers can rely on

- [`registry_satisfies_signature`](theories/composition/OwnedDataComponent.v)
  takes the supplier laws, the entry condition and the supplied service
  executions. It proves safety and numeric bounds for every admitted trace
  prefix from that initial state and produces a finite trace with the
  corresponding outcomes and publication receipts.
- [`episode_success_durable`](theories/internal/transactions/FreerGlobalDataTrace.v)
  shows that, after a delivered publication success and with no later physical
  publication, every recovery that reaches `Usable` restores the same offset
  and decoded image and preserves the bytes in the certified physical ranges.
- [`episode_uncertain_no_hybrid`](theories/internal/transactions/FreerGlobalDataTrace.v)
  applies when the old and candidate incarnations are certified at the
  uncertain boundary and the recovery suffix adds no physical publication.
  A recovery that reaches `Usable` restores one of the two complete
  offset-and-decoding pairs.

A **physical publication** makes the prepared candidate authoritative when its
journal slot becomes complete. **Delivery** is the later return to the caller, so a
reset can leave a publication in place without a delivered success.
A **receipt** is a proof-only record of a delivered publication, indexed by
its position in the physical history.
`Usable` is the point at which recovery has rebuilt state for ordinary access.
The recovery results are conditional on reaching that point. The link between
the bytes requested by a Rust Data callback and the bytes read after recovery
remains open.

## Reading the proof

1. Start with [`OwnedDataContract.v`](theories/interface/OwnedDataContract.v)
   for the public signature. Read `required`, `entry`, `executions` and
   `offered` to see which obligations the integrator supplies and which
   guarantees the theorem derives.
2. Read [`OwnedDataBinding.v`](theories/composition/OwnedDataBinding.v) for
   the interpretation of the signature and [`OwnedDataServices.v`](theories/registry/semantics/OwnedDataServices.v)
   for the executions and continuations it consumes. The
   [contract index](docs/Contracts.md) locates the lower-level contracts.
3. Follow [`OwnedDataComponent.v`](theories/composition/OwnedDataComponent.v)
   to [`owned_calls_from_idle`](theories/internal/transactions/FreerRecycledWriter.v)
   for the induction over calls. The [scenario witnesses](theories/verification/OwnedDataWitnesses.v)
   show how the induction is used for ordinary returns, interruption, recovery
   and historical address reuse. The [architecture guide](docs/Architecture.md)
   maps these files to the supporting lemmas.

## Reproducing the checks

The validation workflow uses **Rocq 9.0.0** for the foundations, the public
signature, the FreerDPS composition, the component theorem and the scenario
witnesses. Run the command from the repository root after setting up the
[Rocq switch and pinned FreerDPS dependency](FreerDPS-Setup.md#install-the-dependencies).

```sh
REGISTRY_SWITCH=registry-proof
opam exec --switch="$REGISTRY_SWITCH" \
  -- make -C proofs/registry -f Makefile.freer -j4 check check-interface
```

`check` generates dependencies with `coqdep`, compiles the selected audits,
prints theorem dependencies with `Print Assumptions` and runs `coqchk`.
`check-interface` independently compiles and checks the public signature
using only the standard library. These checks validate the Rocq development.
The supplier contracts and the Rust correspondence remain separate obligations.
Build products for this profile are written to `.local/registry-build/freer/`.

## Directory layout

| Directory | Contents |
| --- | --- |
| [`theories/interface/`](theories/interface/) and [`theories/composition/`](theories/composition/) | Public signature, interpretation and component proof. |
| [`theories/registry/semantics/`](theories/registry/semantics/) | Concrete registry types, entry invariant, service executions and offered observations. |
| [`theories/common/`](theories/common/) and [`theories/suppliers/`](theories/suppliers/) | Shared definitions and lower-level contracts for flash, format, reading and geometry. |
| [`theories/internal/`](theories/internal/) | Supporting models and proofs for transactions, allocation and recycling, the journal, and recovery. |
| [`theories/verification/`](theories/verification/) | Audit entry points, scenario witnesses and counterexamples. |
| [`docs/`](docs/) | Statement, contract index and architecture guide. |

The [`_CoqProject`](_CoqProject) manifest maps the proof sources under
`theories/` to the logical namespace `OxideSE.Registry`.
