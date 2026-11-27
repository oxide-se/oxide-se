# Transactional registry component property

The goal is to prove the registry's transactional correctness assuming that the
components it calls satisfy their contracts. These assumptions concern flash,
configuration, readers, formats, and cryptographic services, among others.
Establishing their implementations is a separate proof obligation; the registry
proof alone does not establish them.

The currently composed result covers owner-controlled Data operations after
successful initialization. It distinguishes client returns from physical
publications: an uncertain publication can be recovered without a client receipt.
Completed recovery restores the old image or a complete new image, according to
the physical publication. Interruptions discard RAM.

Suppliers and their obligations are listed in [Components.md](../Components.md).
The current theorem is `registry_satisfies_signature` in
[OwnedDataComponent.v](../theories/composition/OwnedDataComponent.v).
The [Rust–Rocq implementation map](../ImplementationMap.md) relates execution
paths to the model and specifies the refinement obligations.

This result is not yet a complete proof of the Rust registry: interrupted
bootstrap, LOAD, joined contexts, supplier implementations, and code refinement
remain separate obligations. The link between the contents requested by a Data
callback and the contents read back also remains to be established. No
unconditional termination or capacity guarantee is claimed.
