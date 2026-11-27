# Shared RPC contract

This `no_std` library is the only service-specific source package that a caller
needs. It contains the interface identifier/version, typed methods, generated
client, service trait and dispatcher. It contains no service implementation and
produces no installable FAE image.

Both application manifests independently declare:

```toml
[dependencies]
rpc_shared_interface = { path = "../rpc_shared_interface" }
```

The caller imports and uses the generated client:

```rust
use rpc_shared_interface::{counter, CALLEE};
let value = counter::Client::new(CALLEE).add(7)?;
```

The private callee implements the generated trait:

```rust
use rpc_shared_interface::{counter, CALLER};
use rustlet_runtime::{declare_rpc_rustlet, Aid};

declare_rpc_rustlet!(Counter, counter::dispatch, 384usize);

// Counter derives Default, Serialize and Deserialize.
impl counter::Service for Counter {
    fn add(&mut self, caller: &Aid, value: u32) -> u32 {
        assert!(caller == &CALLER);
        self.value = self.value.wrapping_add(value);
        self.value
    }
    // Implement every remaining method declared by the shared interface.
}
```

See [the complete implementation](../rpc_calle/src/main.rs). The compiler checks
that its methods match the shared trait. The macro makes the service object the
persistent state and uses an empty session. It supplies APDU rejection; a pure
RPC service is still an installed, isolated Rustlet, not code linked into its
caller. For session state or custom installation, use `declare_rustlet!` and
implement `Rustlet::process_rpc` explicitly.

To distribute the contract without the callee source, share this crate's
`Cargo.toml` and `src/lib.rs`, plus access to its runtime dependency. The local
runtime path in this example must be adjusted to the consumer's SDK location.
A standalone Git repository or a private Cargo registry can distribute the same
crate; consumers then use a pinned Git revision or registry version instead of
the local path. Neither application needs the other application's directory.
The example has `publish = false`; registry distribution requires configuring the
registry and replacing local-only dependency declarations appropriately.

Compilation generates serialization and dispatch code separately in each image.
The kernel never links this contract or parses its interface/method identifiers.
The deployed callee must implement the interface version used by the caller.
Methods are numbered in declaration order: change the interface version when
reordering methods or changing argument/result types. AID constants here are
example deployment addresses, not part of the wire schema; `Client::new` accepts
any installed destination AID.

Check the standalone library on the host:

```sh
cargo check --manifest-path rustlets/tests/Cargo.toml -p rpc_shared_interface --offline
```

Run the two-image example using the command in
[the caller README](../rpc_caller/README.md).
