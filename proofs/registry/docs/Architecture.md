# Proof organization

The service presented here is owner-controlled transactional Data modification after initialization. The [signature](../theories/interface/OwnedDataContract.v) is parameterized by a typed vocabulary. It can be read, compiled, and checked using only the standard library. In that file, a supplier law is a proposition whose proof is required from the caller. A service response describes an execution, including its error or interruption outcomes.

| Question | File or directory |
| --- | --- |
| What does the component require and guarantee? | [OwnedDataContract.v](../theories/interface/OwnedDataContract.v), definitions `required`, `entry`, `executions`, `offered`, and `signature` |
| What does each term mean for the registry? | [OwnedDataBinding.v](../theories/composition/OwnedDataBinding.v), interpretations `registry_supplier_laws` and `registry_vocabulary` |
| Where are the concrete services of part C defined? | [OwnedDataServices.v](../theories/registry/semantics/OwnedDataServices.v), from the prepass to `owned_call_services_for` and `owned_service_schedule` |
| Where are the types, initial invariant, and observations? | [registry/semantics](../theories/registry/semantics) and [common](../theories/common) |
| Where are the software and physical contracts? | [suppliers](../theories/suppliers), [map of Rust bindings](../Components.md) |
| How is the contract proved? | [OwnedDataComponent.v](../theories/composition/OwnedDataComponent.v), theorem `registry_satisfies_signature`, through the consumer [owned_calls_from_idle](../theories/internal/transactions/FreerRecycledWriter.v) |
| Which proofs does the consumer assemble? | [transactions](../theories/internal/transactions), [journal](../theories/internal/journal), [allocation and recycling](../theories/internal/allocation), [recovery](../theories/internal/recovery) |
| Where are assumptions and witnesses checked? | [verification](../theories/verification) for dedicated audits and examples. The [five witness groups](../theories/verification/OwnedDataWitnesses.v) consume the induction. `FreerAudit.v` checks their assumptions. |

## Meaning of the binding

The signature makes quantification over calls, prefixes, and responses explicit, together with receipt preservation and observation order. The meaning of the safety predicate, states, and services depends on the interpretation. For the registry, that interpretation reuses the registry execution machine and existing FreerDPS contracts. It imports their concrete modules. The dependency runs from the binding to the signature.

The proof `registry_signature_exact` is Rocq reflexivity. Once instantiated, the signature reduces to the same proposition as the four concrete component predicates. Rust correspondence and supplier implementations are documented separately. See the [scope of the result](Statement.md).

## Structural checks

The `check-interface` target copies only the signature file into a temporary directory, compiles it, and runs `coqchk` on it. The full build also checks the assumptions of `registry_signature_exact` and `registry_satisfies_signature` in `FreerAudit.v`.

The witnesses are imported from `OxideSE.Registry.OwnedDataWitnesses` and consume the owner-call induction.

## Publication

Compiled sources are in `theories/`. Logical names retain the `OxideSE.Registry` prefix.
