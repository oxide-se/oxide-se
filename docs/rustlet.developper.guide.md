# Rustlet Developer Guide

This guide describes how to develop an ordinary Rustlet for oXiDe SE, using
a Raspberry Pi Pico 1 devkit and dynamically loaded application images.

If you have not built a Rustlet yet, start with
[getting-started.md](getting-started.md). It covers tool installation, the
Pico 1 emulator, physical Pico 1 wiring and provisioning, and the first APDU
session. The development loop below assumes that devkit is already running.

It intentionally does not cover Security Domains. Those are documented in
[security.domain.developper.guide.md](security.domain.developper.guide.md).

## Scope

At the current project stage, a Rustlet is:

- a `no_std`, `no_main` FAE payload;
- built against `rustlets/rustlet_runtime`;
- loaded by the kernel and executed behind the Rustlet ABI boundary;
- stateful across installation and later APDU processing;
- isolated from the kernel by the current Rustlet runtime and MPU model.

Isolation capabilities depend on the processor: Pico 1's Cortex-M0+ does not
provide an MPU. Functional execution on Pico 1 must not be interpreted as
hardware-enforced memory isolation.

An ordinary Rustlet is an application object. It is not an administrative
authority. It processes APDUs routed to its selected instance.

## Mental Model

The current model is:

1. the kernel installs one Rustlet instance;
2. installation constructs the initial object and saves its serialized state;
3. later, `SELECT` activates one installed instance;
4. `process_apdu()` is called on that selected instance;
5. the persistent subset of the Rustlet state is saved and restored by the
   runtime.

From the author's point of view:

- `install()` is the constructor path;
- `process_apdu()` is the command-processing path;
- the Rustlet object is the application state.

## Develop Against A Running Pico 1 Devkit

The devkit is the reusable kernel image. Build and provision it once using
[the first-run guide](getting-started.md), or use a matching supplied devkit
image. Its source configuration is `configs/config_devkit.toml`. You do not
need to rebuild or reflash the kernel when changing an application.

Use Pico 1 QEMU for the initial experiments, then the same application target
on a physical Pico 1 through the devkit's UART transport. Pico 1 Rustlets must
be built for `thumbv6m-none-eabi`; an MPS2 or Pico 2 image is not interchangeable.
The devkit's permissive root Security Domain is intended for experimentation,
not a production authorization policy.

All commands below start at the repository root unless a `cd` is shown.
Build the host tool before starting the devkit:

```sh
cargo build -p apdu_tool
```

After starting QEMU with the socket configuration from the first-run guide,
connect once for that boot:

```sh
target/debug/apdu_tool -v --serial /tmp/oxide-se-pico1.sock --atr-timeout infinite atr
```

For physical Pico 1, replace the socket with the UART device, for example
`/dev/ttyACM0` on Linux, and follow the first-run guide's wiring and OpenOCD
instructions. On macOS, use the corresponding `/dev/cu.*` device. The tool
saves the link in `session.json`; keep running subsequent commands from the
same directory. ATR is a boot event, not a command to repeat before each load.

### Build And Load An Existing Application

Start with the functional example that exercises the APDU API:

```sh
cd rustlets/tests
RUSTLET_TARGET=thumbv6m-none-eabi cargo run build-fae getting_started_test
cd ../..

target/debug/apdu_tool --progress gp deploy \
  A0000047504F5320 \
  rustlets/tests/getting_started_test/build/rustlet_getting_started_test.fae \
  A0000047504F5320
target/debug/apdu_tool select A0000047504F5320
target/debug/apdu_tool raw 00:04:00:00:00:03
```

The last command returns `10 11 12` and success status `9000`.
`gp deploy` loads the package, installs an instance and makes it selectable;
`select` activates the instance. The kernel still validates the FAE even when
the devkit uses permissive management authorization.

Use unused test AIDs when deploying another application. Loading a FAE does
not imply that an existing package or its persistent instances are replaced.
For repeated experiments, delete your test instances first and then their
package with `gp delete --aid AID`, before redeploying. Deletion discards their
persistent state; do not delete unrelated applications or the devkit root SD.
Restarting physical hardware alone does not clear its persistent registry.

### Create Your Own Rustlet

Copy the template alongside the runtime so its relative dependency remains
valid:

```sh
cp -R rustlets/rustlet_template rustlets/my_rustlet
```

In the copy, change the package name in `Cargo.toml` to `my_rustlet` and edit
`src/main.rs`. The template enables the runtime crate's `runtime` feature,
which supplies the Rustlet entry point, allocator and panic handler. Keep
that feature enabled. The minimal application below can replace `src/main.rs`.

Build only this application:

```sh
cd rustlets/my_rustlet
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..

target/debug/apdu_tool --progress gp deploy \
  A0000047504F5370 rustlets/my_rustlet/build/my_rustlet.fae A0000047504F5370
target/debug/apdu_tool select A0000047504F5370
target/debug/apdu_tool raw 00:00:00:00:00:00
```

The minimal application accepts instruction `00` and returns `9000`.
The AIDs here are local experiment identifiers. The template's `cargo build-fae`
alias runs its host-side `xtask`; this differs from the test workspace's
`cargo run build-fae <name>` command. Always set `RUSTLET_TARGET`: the template's
default is not Pico 1. See the [template README](../rustlets/rustlet_template/README.md)
for its directory layout.

## Minimal Rustlet

```rust
#![no_std]
#![no_main]

use rustlet_runtime::{declare_rustlet, Apdu, ApduStatus, Rustlet, RustletCtx};

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct MyRustlet;

declare_rustlet!(MyRustlet);

impl Rustlet for MyRustlet {
    fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
        let apdu = Apdu::new(ctx);
        match apdu.ins() {
            0x00 => apdu.accept(),
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}
```

This is the current normal shape:

- one Rust state object;
- one declaration macro;
- one `process_apdu()` entry point;
- optional persistent fields serialized by the runtime.

## Declaring The Rustlet

The normal declaration macro is:

```rust
declare_rustlet!(MyRustlet);
declare_rustlet!(MyRustlet, 2048usize);
declare_rustlet!(MyRustlet, 2048usize, install_custom);
```

The forms mean:

- default heap, implicit install;
- explicit heap, implicit install;
- explicit heap, explicit install function.

`declare_app!` is an alias for `declare_rustlet!`; application code should use
`declare_rustlet!`.

The macro's size argument controls the heap backing store. The execution stack
is a separate FAE footer requirement: `build-fae` defaults to 2048 bytes and
accepts `--stack-size`. The kernel uses the encoded size, in 32-byte units,
without imposing the default as a maximum. Choose enough stack for the runtime
and your handlers; activation requires RAM for the rounded combined stack and
writable-data block.

## The `Rustlet` Trait

The core trait is defined in
[rt.rs](../rustlets/rustlet_runtime/src/rt.rs).

Today it exposes:

- `process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus`
- `load_state(&mut self, state: &[u8]) -> Result<(), ApduStatus>`
- `save_state(&self, out: &mut [u8]) -> Result<usize, ApduStatus>`

With `declare_rustlet!`, implement `process_apdu()` and derive
`serde::{Serialize, Deserialize}`. The macro wraps the application in
`PersistentRustlet<T>`, whose load/save methods use postcard. They do not
delegate to overrides of the application's `Rustlet::load_state()` and
`Rustlet::save_state()`. Customize the serialized representation through serde;
do not assume those trait overrides replace the macro's persistence path.

The bare trait defaults only accept empty input and save zero bytes. They are
not themselves the automatic postcard implementation.

## Installation

The Rustlet must implement `Default`, including when an explicit install
function is provided: the generated load adapter reconstructs it with
`Default` before restoring serialized state. Keep the serde derives shown in
the minimal example as well.

If installation needs parameters or custom construction logic, use an explicit
install function:

```rust
fn install(ctx: &mut RustletCtx) -> Result<MyRustlet, ApduStatus> {
    let _ = ctx.version();
    Ok(MyRustlet {})
}

declare_rustlet!(MyRustlet, 1024usize, install);
```

The install function runs inside the Rustlet runtime. It returns the initial
Rust object whose persistent representation will be restored for later APDUs.

## Parsing GP Install Data

When one Rustlet uses a custom install function, it should not parse the raw
`INSTALL [for install]` APDU payload by hand.

The Oxide SE runtime exposes one small helper module:

- [gp.rs](../rustlets/rustlet_runtime/src/gp.rs)

The two entry points to know are:

- `gp::parse_install_for_install_ctx(&RustletCtx)`
- `gp::parse_install_for_install_data(&[u8])`

They decode the current GlobalPlatform envelope used by the kernel:

1. `package AID`
2. `applet AID`
3. `instance AID`
4. `privileges`
5. `install parameters`
6. `install token` (the LV must be present even when empty)

That outer structure is an `LV` sequence, not a flat application payload.
Reading `ctx` as if it directly contained only application bytes is therefore
incorrect.

Installation fragment for an ordinary Rustlet (add its `Rustlet`
implementation as in the minimal example):

```rust
use rustlet_runtime::{declare_rustlet, gp, ApduStatus, Rustlet, RustletCtx};

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct CounterRustlet {
    initial_counter: u8,
}

fn install(ctx: &mut RustletCtx) -> Result<CounterRustlet, ApduStatus> {
    let install = gp::parse_install_for_install_ctx(ctx)
        .map_err(|_| ApduStatus::wrong_data())?;
    let initial_counter = install.install_parameters.first().copied().unwrap_or(0);

    Ok(CounterRustlet { initial_counter })
}

declare_rustlet!(CounterRustlet, 1024usize, install);
```

This is the right level of abstraction for ordinary Rustlets:

- let the runtime parse the GP `LV` envelope;
- read only `install.install_parameters` for your application payload;
- ignore the administrative fields unless your application genuinely needs
  them.

The current regression examples using this helper are:

- [state_test/src/main.rs](../rustlets/tests/state_test/src/main.rs)
- [serialization_test/src/main.rs](../rustlets/tests/serialization_test/src/main.rs)

## BER-TLV Helper

The same runtime module also exposes:

- `gp::BerTlvReader`

This helper is intentionally small:

- it reads one BER-TLV stream sequentially;
- it validates tag and length structure;
- it rejects unsupported forms such as indefinite length;
- it does not allocate.

Typical usage:

```rust
use rustlet_runtime::gp::{BerTlvReader, DecodeError};

fn read_first_tag(data: &[u8]) -> Result<Option<(u32, &[u8])>, DecodeError> {
    let mut reader = BerTlvReader::new(data);
    match reader.next_tlv()? {
        Some(tlv) => Ok(Some((tlv.tag, tlv.value))),
        None => Ok(None),
    }
}
```

For an ordinary Rustlet, this is useful when `install_parameters` themselves
use one TLV structure agreed with the host toolchain.

For a Security Domain Rustlet, this becomes even more relevant, because
GlobalPlatform expects BER-TLV content in some administrative payloads,
especially for Security-Domain-specific configuration carried through install
parameters. In that case, the recommended shape is:

1. parse the outer `INSTALL [for install]` envelope with
   `gp::parse_install_for_install_ctx(ctx)`;
2. extract `install.install_parameters`;
3. iterate over those bytes with `gp::BerTlvReader`.

Minimal illustration:

```rust
use rustlet_runtime::{gp, ApduStatus, RustletCtx};

fn parse_sd_install_data(ctx: &RustletCtx) -> Result<(), ApduStatus> {
    let install = gp::parse_install_for_install_ctx(ctx)
        .map_err(|_| ApduStatus::wrong_data())?;

    let mut tlvs = gp::BerTlvReader::new(install.install_parameters);
    while let Some(tlv) = tlvs.next_tlv().map_err(|_| ApduStatus::wrong_data())? {
        match tlv.tag {
            0xC9 => {
                let _application_specific = tlv.value;
            }
            _ => {}
        }
    }
    Ok(())
}
```

This guide stops there on purpose. The full administrative meaning of those
tags belongs to the Security Domain framework, which is documented separately.

## APDU Programming Model

The Rustlet-side APDU API is intentionally typed. It is documented in
[apdu.rs](../rustlets/rustlet_runtime/src/apdu.rs).

The main object is:

- `Apdu<Command>`
- `Apdu<Receiving>`
- `Apdu<Sending>`

The intent is:

- create `Apdu::new(ctx)` when command processing starts;
- inspect the header in `Command`;
- move to `Receiving` only if the command really has incoming data;
- move to `Sending` only if the command really produces outgoing data.

Example:

```rust
fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
    let apdu = Apdu::new(ctx);
    match apdu.ins() {
        0x02 => {
            apdu.as_receiving().accept_and_send(&[0xAA, 0xBB, 0xCC])
        }
        0x04 => apdu.as_sending().send(&[0x11, 0x22, 0x33, 0x44]),
        _ => apdu.reject(ApduStatus::instruction_not_supported()),
    }
}
```

This is the preferred current API. A Rustlet should not manipulate the raw APDU
shared buffer directly unless the framework leaves no better option.

`Receiving::data()` borrows the incoming bytes; do not retain that borrow
while consuming the session to write a response. `send()` and
`accept_and_send()` copy their supplied slice into the shared output buffer.
For an in-place response, save `rx.data().len()`, consume reception with
`rx.as_sending()`, then call `send_with()`. The transition preserves the payload
bytes and resets only the logical response length. The previous input borrow
cannot cross that transition. The echo handler in `getting_started_test` uses
this path without an intermediate buffer.
For generated output, `Sending::send_with()` writes directly into that buffer
and avoids a separate response array. Return the number of bytes produced;
the current short-APDU limit is `APDU_PAYLOAD_LENGTH_MAX` (255 bytes), even
though the physical buffer has 256 bytes.

## `RustletCtx`

`RustletCtx` is the shared ABI region between kernel and Rustlet.

For an ordinary Rustlet, it is mainly used to:

- construct the typed `Apdu`;
- access the ABI version;
- access the crypto provider;
- access persistence staging indirectly through the runtime.

The Rustlet should treat `RustletCtx` as framework-owned shared state, not as a
general-purpose raw buffer.

## Persistence

The runtime treats the serialized representation of an ordinary Rustlet as the
authoritative state between APDUs. After a normal handler return, it serializes
the instance, destroys the in-memory object, and the kernel scrubs the complete
Rustlet heap. The next APDU reconstructs the object and loads that serialized
state.

If serialization fails, the runtime terminates the invocation with the failure
status. The kernel abandons that call's staged state and retires its runtime;
reselecting reconstructs the last committed state. The failing invocation must
not retain an object in a heap that is subsequently scrubbed. Panic and allocator
failure likewise return through the termination SVC without a second mutable
borrow of the active context.

Current practical rules:

- serializable Rustlets should derive `serde::Serialize` and
  `serde::Deserialize`;
- postcard is the current default serialization backend;
- fields excluded from serialization with serde attributes are transient only
  within the current APDU execution. They are reconstructed from their default
  value for the next APDU and must not be used for cross-command state;
- a Rustlet Security Domain is the explicit exception to this ordinary-Rustlet
  lifecycle: its non-serialized secure-channel session remains resident while
  the Security Domain is active and is cleared when the channel or loaded
  Security Domain is torn down.

The persistence backing store is still evolving, but the Rustlet-side object
model is already in place.

## Crypto

The runtime exposes card-side cryptographic services through `ctx.crypto()`.

The public API includes typed `Cipher` and `Mac`, random generation, P-256
key generation and ECDH, HKDF-SHA256 and X9.63-SHA256 derivation. Availability
and errors still depend on the kernel service and target configuration.

Current implementation limits matter when choosing an API:

- `Cipher::finish()` performs a complete operation; `Cipher::update()` always
  returns `CryptoError::Unsupported`.
- `Mac::update()` copies its input into a Rustlet-owned buffer capped at 256
  bytes. It is not a streaming kernel operation. `CryptoProvider::compute_mac()`
  accepts an existing input slice for a single operation without this
  accumulation buffer.
- Requesting random bytes is not by itself evidence of a cryptographically
  qualified entropy source on a particular board or emulator.

Those services are kernel-mediated. The Rustlet uses them through the runtime
API, not by linking a separate crypto stack of its own into the kernel address
space.

## API Reference

The reference is maintained as Rustdoc in the
[rustlet_runtime crate](../rustlets/rustlet_runtime/src/lib.rs). Its entry page
organizes application, APDU, persistence, crypto, Security Domain and low-level
integration APIs. Public items describe buffer ownership, memory costs,
lifecycle, errors and implementation limits. Missing public documentation is
a compilation error; the documentation check also rejects warnings and broken
links. These checks enforce coverage, not a formal proof of contract accuracy.

Generate and open the current reference from the repository root:

```sh
cargo doc -p rustlet_runtime --features runtime --no-deps --open
```

The generated entry page is `target/doc/rustlet_runtime/index.html`.
The `runtime` feature is essential: without it, the main application trait,
declaration macros and Security Domain runtime are omitted. Generated HTML
is a local build artifact, not a published API website.

Source entry points corresponding to the reference:

| Subject | Source and current role |
| --- | --- |
| Entry macros and feature gates | [lib.rs](../rustlets/rustlet_runtime/src/lib.rs) |
| Application lifecycle and postcard wrapper | [rt.rs](../rustlets/rustlet_runtime/src/rt.rs) |
| Typed APDU sessions | [apdu.rs](../rustlets/rustlet_runtime/src/apdu.rs) |
| Context, status values and buffer limits | [abi.rs](../rustlets/rustlet_runtime/src/abi.rs) |
| Cryptographic services | [crypto.rs](../rustlets/rustlet_runtime/src/crypto.rs) |
| GP install envelope and BER-TLV | [gp.rs](../rustlets/rustlet_runtime/src/gp.rs) |
| Security Domain extension | [security_domain.rs](../rustlets/rustlet_runtime/src/security_domain.rs) |
| Low-level syscall contract | [syscall_abi.rs](../rustlets/rustlet_runtime/src/syscall_abi.rs) and [syscall.rs](../rustlets/rustlet_runtime/src/syscall.rs) |
| Future streaming persistence adapters | [persistence.rs](../rustlets/rustlet_runtime/src/persistence.rs); these placeholders are not the active postcard persistence path |

For a Rustlet acting as a Security Domain, use the
[Security Domain API reference map](security.domain.developper.guide.md#api-reference).
It distinguishes kernel-invoked policy/protocol hooks from the SD-only SCP03
key service and from cryptographic services shared with ordinary Rustlets.

### Check And Package The Reference

```sh
sh scripts/check_rustlet_docs.sh
```

This runs host unit tests and executable/compile-fail doctests with the default
features, checks the declaration examples and APDU application for Pico 1, then
builds the complete reference with `runtime` enabled. The embedded check uses
nightly `rust-src`, as does `build-fae`. Host tests do not emulate SVC services;
QEMU validation remains separate.

The checked reference is at
`target/rustlet-reference/doc/rustlet_runtime/index.html`. The script prints a
fresh `target/rustlet-reference/site.*` directory containing a static site with
`api/development/rustlet_runtime/index.html`. An optional version argument
replaces `development`; use the actual public release tag when building an
approved release snapshot. The artifact records its source commit and whether
tracked files were modified. A release name on a dirty development tree is not
proof that it matches the released code.

The [reference workflow](../.github/workflows/rustlet-reference.yml) checks the
same script and archives the static site under the commit identity. It does
not deploy Pages. For publication, generate it from the reviewed public
snapshot and copy the complete `api/<version>/` subtree into the site's
versioned API directory, preserving earlier versions and Rustdoc's asset/source
directories. Add the release link to the site index and retain `.nojekyll` when
using branch-based GitHub Pages. Publish that site through its normal release
process. No hosted API URL is assumed until that deployment exists.

Cipher initialization consumes `Cipher<Uninitialized>` and returns
`Cipher<CipherReady<'key>>`. The ready state borrows the original key and IV;
Rust rejects their mutation or destruction before the last use of that session.
`finish` consumes the session even when the operation fails. Abandoning a
session releases its borrows without a kernel call. There is no key/IV copy or
heap allocation, and the provider retains no cipher pointers between calls.

Custom backends implement the atomic
`CryptoBackend::cipher_do_final(&CipherReady<'_>, input, output)` operation
instead of the former `setup`/`do_final` pair. Its configuration is borrowed for
the duration of that call only. The usual `Cipher::new(...).init(...).finish(...)`
application sequence is unchanged; explicit ready-state type annotations must
use `CipherReady<'_>` instead of the MAC/key-agreement marker `Ready`.

## Automated Validation

The [test applications](../rustlets/tests) provide functional examples. For a
repository test application, Pico 1 QEMU checks include:

```sh
cargo run test rustlet raspi-pico1 getting_started_test --on qemu
cargo run test rustlet_all raspi-pico1 --on qemu
```

These test commands construct their own test kernel images. They supplement
the dynamic devkit workflow above; they are not the edit/build/load loop for
your own application. A successful build alone does not validate execution
on QEMU or physical hardware.

## What This Guide Deliberately Does Not Cover

This guide does not describe:

- Security Domain authority;
- SCP03 session handling;
- management APDUs such as `INSTALL`, `DELETE`, or `GET DATA` as administrative
  operations;
- the `sddispatch` framework call.

Those topics belong to the dedicated Security Domain guide:

- [security.domain.developper.guide.md](security.domain.developper.guide.md)
