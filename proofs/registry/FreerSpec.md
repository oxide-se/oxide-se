# Component-and-contract proof method

The registry development follows **freerSpec**, our component-and-contract
specification method, using the **FreerDPS** library and its `Core`, `Impure`, and
`Hoare` modules. The method distinguishes the contract a component offers to its
clients from the contracts it requires of its suppliers.

## Service contracts

A service interface is indexed by result type. Its contract describes a witness
state, caller obligations, permitted responses, and the witness update associated
with a response. In FreerDPS, `make_contract` combines the update and caller/callee
predicates.

```text
ComponentAPI : interface
Witness : Type
caller : Witness -> forall A, ComponentAPI A -> Prop
callee : Witness -> forall A, ComponentAPI A -> A -> Prop
step   : Witness -> forall A, ComponentAPI A -> A -> Witness
component_contract := make_contract step caller callee
```

This is a documentation template, not a standalone compilable Rocq declaration.
[FreerFlash.v](theories/suppliers/FreerFlash.v) provides a concrete typed interface
and contract. The [component map](Components.md) locates the other interfaces and
identifies boundaries still expressed as parametric laws rather than standalone APIs.

The witness may contain ghost information such as certificates or publication
history. This does not propose additional firmware RAM. Relate concrete fields,
abstractions, and ghost information explicitly to the implementation.

## Separate obligations from conclusions

Define registry invariants separately from supplier contracts. Prove:

1. each internal call satisfies its supplier's caller obligations;
2. every permitted response preserves the required local invariant;
3. compositions of service executions satisfy the offered component contract;
4. clients respecting that contract preserve the intended observations.

Putting rollback safety or durability into a registry contract does not establish
that the implementation provides them. Derive those guarantees from the protocol
and the required services. Likewise, flash-call admissibility must not depend on
assuming the allocator safety it is intended to prove.

The shared image, page table, roots, and journal remain one state across
components. Internal contracts for snapshots, collection, or journal operations
must not introduce atomicity absent from the underlying flash operations.

## Programs, traces, and interruption

FreerDPS expresses programs as `impure` computations over required interfaces.
Their contract interpretation supports local and composed Hoare-style proofs.
Operational relations additionally represent physical outcomes, control phases,
and execution prefixes. The development relates these forms explicitly.

A reset is not a normal return to the interrupted continuation. Distinguish:

- successful and erroneous normal returns, which may continue execution;
- reset with reached flash, discarding volatile state and the continuation;
- recovery from that flash, itself subject to repeated interruption;
- fatal stop, with no subsequent client delivery.

A returned error can retain a partial or complete physical write. A reset can
occur after physical completion but before the caller receives success. Neither
case permits inventing rollback, Drop, or cleanup after the interruption.

For nondeterministic physical operations, represent all allowed outcomes through
contract-constrained responses or explicitly related trace semantics. Do not
replace the physical relation with a favorable deterministic update. Prove
safety of reachable prefixes as well as normal-return postconditions.

## The registry signature

[OwnedDataContract.v](theories/interface/OwnedDataContract.v) defines a typed,
implementation-independent vocabulary and four propositions:

- `required`: laws supplied by lower-level components and configuration;
- `entry`: the usable initial boundary;
- `executions`: actual first-call services and subsequent schedule;
- `offered`: trace safety, numeric guarantees, observations, and receipt properties.

Its `signature` states `required -> entry -> executions -> offered`.
[OwnedDataBinding.v](theories/composition/OwnedDataBinding.v) interprets these
terms using the registry machine. The direction of dependency is from the
binding to the signature. The signature can be checked independently with only
the standard library.

[OwnedDataComponent.v](theories/composition/OwnedDataComponent.v) proves the
instantiated signature by consuming the owner-call induction. The interpretation
of `safe` and the operational services matters: a generic signature alone is not
a verification of Rust. See [Statement.md](docs/Statement.md) for the exact scope.

## Supplier verification and trust

Required software laws remain implementation obligations until a concrete
supplier is proved to satisfy them. Keep them distinct from accepted hardware
and cryptographic assumptions. A supplier implementation proof must cover its
responses, updates, and interruptions, not merely its successful return value.

Inspect ordinary premises as well as `Print Assumptions`: the absence of project
axioms does not establish that a service contract is realizable, or that an
entry condition is non-vacuous. Conversely, a library axiom should be reported
as a library dependency, not as a hardware guarantee.

Use the [assumption register](Assumptions.md), [component map](Components.md), and
[verification instructions](README.md#reproducing-the-checks) to review and
reproduce the development. The proof of the model, manual Rust correspondence,
and mechanized Rust refinement are distinct claims.
