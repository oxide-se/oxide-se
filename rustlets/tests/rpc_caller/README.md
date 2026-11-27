# Synchronous RPC between two Rustlets

Run the complete example with:

```sh
cargo run test rustlet raspi-pico1 rpc_caller --on qemu --trace=semihosting
```

The runner builds and installs both `rpc_caller` and `rpc_calle`. The shared
interface is declared in the independent
[`rpc_shared_interface`](../rpc_shared_interface/README.md) library crate:

```rust
rustlet_runtime::rpc_interface! {
    pub mod counter, id = 0x525043, version = 1 {
        fn add(value: u32) -> u32;
        fn value() -> u32;
    }
}
```

The declaration generates `counter::Client`, the `counter::Service` trait and
`counter::dispatch`. A client invokes an ordinary typed method:

```rust
let service = counter::Client::new(CALLEE);
let updated = service.add(7)?;
```

The callee implements `counter::Service` on its persistent state. Each method
receives the kernel-supplied caller AID; the example checks it before modifying
the counter. Its declaration connects that implementation to the shared dispatcher:

```rust
declare_rpc_rustlet!(Counter, counter::dispatch, 384usize);
```

This macro supplies the runtime adapter, persistent-state lifecycle and APDU
rejection. The service implements no APDU handler. For separate session state or
both protocols, implement `Rustlet` explicitly and use `declare_rustlet!`.

All interface IDs, versions, method tags, arguments and return values are encoded
with Postcard in the Rustlet library. Methods are numbered in declaration order;
change the service version if the order or types change. There is no publication
registry, open handle or generated kernel dispatcher.

## Execution and ownership

SVC 19 takes a destination AID and a bounded in/out byte buffer. The kernel:

1. validates the caller's memory, allocates a separate 512-byte gateway and
   copies the request and authoritative 17-byte identity into it;
2. suspends the caller, retaining its stack, heap and original APDU gateway;
3. loads the destination as an independent instance and opens a scope using the
   existing registry savepoint mechanism;
4. invokes the existing binary `process_apdu` entry with the RPC flag set;
5. copies the successful response back, releases the callee and its gateway,
   then resumes the caller immediately after its syscall.

The runtime restores persistent state **before** testing the flag and dispatching
to the Rustlet's APDU or RPC method. Both paths use the existing state-save and
handler-return sequence. The kernel does not decode Postcard. It recopies the
request and identity after bootstrap because the callee's bootstrap can write its
gateway. No references into the caller are passed to the callee.

Requests are limited to 238 encoded bytes (255 minus the identity prefix),
responses to 255 bytes, and persistent state to the existing 244 bytes. The typed
client uses a 255-byte stack buffer and returns owned values, without heap
allocation for the codec. Gateway, image and allocator metadata are allocated by
the kernel; allocation failure is returned as a transport error. The gateway and
callee allocation are scrubbed on release.

Each RPC addresses an AID without changing the selected application. Two calls
to the same AID create two separate callee sessions. Each starts with default
volatile state and ends when that call returns or fails. A subsequent call sees
persistent updates accepted by the caller's pending transaction. Only ordinary
installed, selectable application instances are destinations. The callee decides
which callers may use its service; the kernel does not equate reachability with
service authorization. Self-calls and nested RPCs are refused.

## Failure and transaction semantics

A normal successful child call accepts its savepoint; it does not commit durable
state independently. A later caller failure rolls back the child's changes too.
A remote error, invalid output, panic or recoverable CPU fault rolls back the
child scope and returns an error to the caller. The child is unloaded before the
rollback observer runs, so no stale resident child state remains.

The APDU watchdog keeps the original command deadline. Exhausting that global
deadline may terminate the caller too. Kernel faults and unrecoverable platform
faults are not transformed into successful local recovery. Security counters that
must escape rollback remain a separate design question.

The RPC veneer saves the caller's callee-saved CPU registers on its own stack.
The kernel returns from SVC before executing the child and reuses the existing
exception-entry path to resume that veneer. Before each Rustlet entry the kernel programs and enables the MPU. During
the RPC the callee can access its own gateway. The suspended caller's APDU
gateway is outside the permitted regions.
The Pico 1 port uses the RP2040 MPU. The QEMU scenario checks that the caller's
APDU survives the RPC; it does not directly test a denied read of that buffer. This implementation follows the
runtime's existing basic exception-frame contract.

Kernel and Rustlets must be rebuilt together; there is no old-runtime fallback
or ABI negotiation.

## Scenario coverage

The scenario checks typed calls, persisted state, authoritative identity, child
panic and CPU-fault recovery, nested-call rejection, parent rollback, APDU gateway
preservation, missing/self destinations, repeated calls, service-version rejection,
and rejection of application APDUs by the RPC-only callee.

The shared interface includes deliberate panic/fault methods solely for these
tests; they are not an example of a production service's authorization policy.
