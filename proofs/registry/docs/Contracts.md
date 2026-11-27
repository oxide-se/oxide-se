# Contract and proof index

| Boundary | Existing definitions | Status |
| --- | --- | --- |
| Flash | [FlashSpec.v](../theories/suppliers/FlashSpec.v), [FreerFlash.v](../theories/suppliers/FreerFlash.v): `flash_contract` and interruptions | Formalized physical assumption; backend binding outstanding |
| BOSS reading | [BossDecodingContract.v](../theories/suppliers/BossDecodingContract.v), [IncarnationReaderContract.v](../theories/suppliers/IncarnationReaderContract.v) | Parametric supplier laws; implementation proof open |
| Geometry | [DecodedGeometryContract.v](../theories/suppliers/DecodedGeometryContract.v) | Numeric predicates; implementation proof open |
| BOSS writing | [BossEncodingContract.v](../theories/suppliers/BossEncodingContract.v) | Conditional round trip to establish for the implementation |
| Validation | [BossValidationContract.v](../theories/suppliers/BossValidationContract.v), [FreerPreAppend.v](../theories/internal/transactions/FreerPreAppend.v) | Parametric supplier and local API |
| Crypto | Abstract functions and results used by suppliers | No standalone `CryptoAPI` or probabilistic proof yet |
| Owner-controlled Data registry | [OwnedDataContract.v](../theories/interface/OwnedDataContract.v), [OwnedDataComponent.v](../theories/composition/OwnedDataComponent.v) | Signature separated from the conditional composition proof |

The [complete map](../Components.md) details offered/required services, Rust
entry points, and bindings. Contracts are predicates and parameters, not axioms
asserting Rust conformance.
