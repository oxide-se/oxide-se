# Rustlet Security Domain Getting Started

This guide follows
[Security Domain Getting Started](security.domain.getting.started.md). There,
you used the reference implementation as an administrator. Here, you take the
checked-in `simple_security_domain`, turn it into your own delegated SCP03 S16
authority, and validate it on the same Pico1 with `apdu-tool`.

This is an implementation exercise, not a request to reimplement cryptographic
primitives. The runtime's reusable `scp03::S16Session` owns S16 derivation,
authentication, secure messaging and replay state; your Security Domain owns
capability discovery, delegated-command routing, key identity and management
policy. Each checkpoint names an observable invariant. Use the
[Security Domain developer guide](security.domain.developper.guide.md) for the
API contracts. The checked-in
[`tutorial_scp03_security_domain`](../rustlets/tutorial_scp03_security_domain/src/main.rs)
is the small final result and is tested independently; consult it only when you
want a complete comparison.

> This exercise edits `rustlets/simple_security_domain` in place so that the
> checked-in build configuration can embed it. Make a topic branch first, or
> save your work as a commit if you want to keep the result. The public keys
> used below are development fixtures only.

## What You Will Build

The checked-in skeleton already provides:

- `declare_security_domain!` and the Security Domain FAE profile;
- selectable application behavior;
- separate persistent and session state;
- conservative default hooks that advertise no SCP and reject establishment.

You will add, in order:

1. SCP03 S16 discovery and delegated-command ownership;
2. registry-backed static key selection and S16 session establishment;
3. host authentication and an explicit authenticated state transition;
4. command unwrap and response wrap through the reusable, atomic engine;
5. reset, failure, and management policy that cannot widen kernel authority.

The kernel image deliberately keeps `protocols = []`. A successful result is
therefore proof that your Rustlet, rather than a native kernel SCP03 backend,
established and operated the channel.

## 1. Establish The Neutral Baseline

Build the APDU client, then build the unmodified skeleton as the root Security
Domain:

```bash
cargo build -p apdu_tool
cargo run -- build \
  --config configs/config_rustlet_security_domain_getting_started.toml \
  raspi-pico1
```

The build configuration is intentionally dedicated to this exercise. It embeds
`rustlets/simple_security_domain`, creates instance `A0000047504F5331`, and
provisions SCP03 keyset `version=1,id=3` under that instance.

Create the matching host-side development keyset now. Keeping it beside the
checkout is convenient for this exercise; it is ignored by Git and must not be
used as production key material:

```bash
umask 077
printf '%s\n' \
  'version = 1' \
  'id = 3' \
  'profile = "s16"' \
  'enc = "404142434445464748494A4B4C4D4E4F"' \
  'mac = "505152535455565758595A5B5C5D5E5F"' \
  > getting-started-scp03.toml
```

Flash it and capture the ATR using the two-terminal procedure from the
[previous guide](security.domain.getting.started.md#3-flash-the-pico1-and-capture-its-atr),
then select the instance:

```bash
target/debug/apdu_tool select A0000047504F5331
target/debug/apdu_tool gp get-data card-recognition --format tlv
target/debug/apdu_tool gp get-data card-capabilities --format tlv
target/debug/apdu_tool scp03 open \
  --scp03-profile s16 \
  --security-domain A0000047504F5331 \
  --security-level c-mac+c-enc \
  --keyset getting-started-scp03.toml
```

The neutral checkpoint is:

- SELECT succeeds;
- card recognition remains structurally valid;
- card capabilities returns `6A88` because no secure-channel capability is
  advertised yet;
- `scp03 open` reaches the card and fails on INITIALIZE UPDATE with `6D00`.

That failure is useful: support must appear only after you implement it.

## 2. Design Session State Before Crypto

Extend `Session` in
[`simple_security_domain/src/main.rs`](../rustlets/simple_security_domain/src/main.rs)
with the bounded runtime state, and declare the manifest key identity used by
the exercise:

```rust
use rustlet_runtime::{scp03::{S16Keyset, S16Session}, SecurityLevel};

const KEYSET: S16Keyset = S16Keyset {
    default_version: 1,
    resolved_id: 3,
};

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct Session {
    commands: u32,
    scp03: S16Session,
}
```

`S16Session` contains only fixed-size session data and has a documented
serialized upper bound of 122 bytes, below the runtime's 244-byte rollback
gate. Static keys remain in the manifest and are loaded through the
Security-Domain-only service; they never become source constants. Its
`reset()` method overwrites every derived secret, chain, cryptogram and counter.

Checkpoint:

```bash
cd rustlets/simple_security_domain
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..
```

The FAE must still build and SELECT must still work after reflashing. No SCP03
claim should exist yet. `cargo build-fae` only rebuilds the standalone FAE;
before every reflash in this guide, return to the repository root and rebuild
the firmware that embeds it:

```bash
cargo run -- build \
  --config configs/config_rustlet_security_domain_getting_started.toml \
  raspi-pico1
```

The state-lifetime contract is detailed in
[Persistent, Session And Volatile Working Data](security.domain.developper.guide.md#persistent-session-and-volatile-working-data).

## 3. Advertise Only What You Implement

Implement these `RustletSecurityDomain` hooks next:

- `supports_scp03_s16()` returns `true`;
- `claims_delegated_secure_channel_command()` claims only `80 50 xx xx`
  (INITIALIZE UPDATE) and `84 82 xx 00` (EXTERNAL AUTHENTICATE);
- `current_mac_len()` returns 16 only for the active S16 channel.

The runtime's default `get_data()` implementation already derives recognition
and capability data from `supports_scp03_s16()`. Keep that default unless your
Security Domain needs additional proprietary data objects.

Do not claim S8, the SCP03-33 protocol option, or SCP11. Security level `0x33`
under S16 is exercised later; it is not the SCP03-33 protocol option. Do not use
a catch-all CLA/INS match: an
overbroad claim silently steals commands from normal dispatch.

Add `current_mac_len()` only after establishment is implemented; it will simply
return `state.session.scp03.mac_len()`. The runtime's default delegated-command adapter converts the claimed wire
commands into the typed `initialize_update()` and `external_authenticate()`
views. The required hook shape and discovery objects are shown in
[Secure Channel Establishment](security.domain.developper.guide.md#4-secure-channel-establishment)
and [Administrative Data](security.domain.developper.guide.md#3-administrative-data).

Rebuild and reflash. The discovery checkpoint is now the inverse of the
baseline: the ATR still reports no kernel-native protocol, while GET DATA from
the selected instance advertises SCP03 S16. `scp03 open` should still fail
safely until the next checkpoints are complete.

## 4. Implement INITIALIZE UPDATE

Delegate `initialize_update()` to the bounded S16 engine:

```rust
fn initialize_update(
    state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
    ctx: &mut RustletCtx,
    command: &rustlet_runtime::InitializeUpdate<'_>,
    out: &mut [u8],
) -> Result<usize, ApduStatus> {
    state.session.scp03.initialize_update(ctx, command, KEYSET, out)
}
```

The engine implements this fail-closed sequence:

1. require the S16 host-challenge length;
2. accept wire P2/key identifier `0` as the GlobalPlatform wildcard and ask
   the runtime to resolve it under requested version `1`; the provisioned
   keyset has identifier `3`, which the response reports;
3. load ENC and MAC static keys with
   `RuntimeSyscall::SecurityDomainLoadScp03Key` through the runtime wrapper;
4. generate or define the card challenge according to your profile;
5. derive session ENC, MAC, and R-MAC keys with the typed crypto provider;
6. compute card and expected host cryptograms;
7. fill the caller-provided response buffer;
8. publish the `initialized` state only after every preceding step succeeds.

Never compile static key bytes into the Rustlet. The manifest owns this
tutorial's static keys; the runtime checks that the selected Security Domain is
allowed to load them. Avoid storing `RustletCtx`, a crypto provider, or borrowed
APDU slices in state.

The reusable engine is the reviewed implementation of those mechanical steps;
your code still chooses the key identity and owns the hook. The developer guide
explains the flow under
[Secure Channel Establishment](security.domain.developper.guide.md#4-secure-channel-establishment).

Checkpoint: after rebuilding the FAE and the embedding firmware, select
`...5331` and send INITIALIZE UPDATE with the deterministic 16-byte host
challenge `00..0F`:

```bash
target/debug/apdu_tool raw \
  80:50:01:00:10:00:000102030405060708090A0B0C0D0E0F
```

It returns 44 response bytes followed by `9000`. Protected management remains
unavailable because the host has not been authenticated.

## 5. Authenticate The Host Atomically

Delegate `external_authenticate()` and expose the authenticated state:

```rust
fn external_authenticate(
    state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
    ctx: &mut RustletCtx,
    command: &rustlet_runtime::ExternalAuthenticate<'_>,
) -> Result<SecurityLevel, ApduStatus> {
    state.session.scp03.external_authenticate(ctx, command)
}

fn current_security_level(
    state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
) -> SecurityLevel {
    state.session.scp03.security_level()
}

fn secure_channel_open(
    state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
) -> bool {
    state.session.scp03.is_open()
}

fn current_mac_len(
    state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
) -> usize {
    state.session.scp03.mac_len()
}
```

The engine performs this order:

1. require the `initialized` state, CLA `84`, P2 `00`, and exact S16 length;
2. reject unsupported security-level bits;
3. compute the initial C-MAC over the command header and host cryptogram;
4. compare both the expected host cryptogram and received C-MAC in constant
   time;
5. only then store the security level, initial command/response chains, and
   authenticated state.

`secure_channel_open()` and `current_security_level()` must be projections of
that state, not independent flags. Any authentication failure must leave no
open channel and must not advance a chain or counter.

After rebuilding, reflashing, capturing the ATR, and selecting `...5331`, the
establishment checkpoint is:

```bash
target/debug/apdu_tool scp03 open \
  --scp03-profile s16 \
  --security-domain A0000047504F5331 \
  --security-level c-mac+c-enc \
  --keyset getting-started-scp03.toml
target/debug/apdu_tool scp03 inspect
```

Both commands must succeed. Protected commands will not be correct until the
secure-messaging hooks are implemented.

## 6. Implement Secure Messaging

Delegate `unwrap_command()`, `wrap_response()` and reset using the in-place
buffers provided by the runtime:

```rust
fn unwrap_command(
    state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
    ctx: &mut RustletCtx,
    command: &rustlet_runtime::WrappedCommand<'_>,
    out: &mut [u8],
) -> Result<usize, ApduStatus> {
    state.session.scp03.unwrap_command(ctx, command, out)
}

fn wrap_response(
    state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
    ctx: &mut RustletCtx,
    response: &rustlet_runtime::PlainResponse<'_>,
    out: &mut [u8],
) -> Result<usize, ApduStatus> {
    state.session.scp03.wrap_response(ctx, response, out)
}

fn reset_secure_channel(
    state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
) {
    state.session.scp03.reset();
}
```

For each protected command, the engine:

- verify C-MAC before decrypting or dispatching plaintext;
- derive the command ICV from the session encryption counter;
- validate ISO/IEC 7816-4 padding after decryption;
- advance command state only after verification succeeds.

For each protected response, it:

- encrypt response data only when the negotiated level requests R-ENC;
- compute R-MAC over the exact protected response representation;
- keep response counters and chains independent from command state;
- reject insufficient output space rather than truncating.

Failed MAC, bad padding, replay, malformed length, or counter overflow do not
publish partially advanced state: the engine works on local chain/counter
copies and commits them only after complete success. The algorithms and buffer
contracts are under
[Secure Messaging](security.domain.developper.guide.md#5-secure-messaging).

At this checkpoint, the following protected read must return `9000`:

```bash
target/debug/apdu_tool scp03 close
target/debug/apdu_tool scp03 open \
  --scp03-profile s16 \
  --security-domain A0000047504F5331 \
  --security-level c-mac+c-enc+r-mac+r-enc \
  --keyset getting-started-scp03.toml
target/debug/apdu_tool gp get-data card-recognition --format tlv
```

This second level deliberately exercises command MAC/encryption and response
MAC/encryption. A successful `c-mac+c-enc` session alone does not call the
R-MAC/R-ENC part of `wrap_response()`.

Then close the host session, reset the Pico1 without erasing it, capture a new
ATR, and prove that a fresh SCP03 session opens while the old live session does
not survive reset.

## 7. Add Management Policy Without Escalation

Review the management-family defaults before installing applications through
your implementation. For this root-bootstrap exercise, no policy override is
required: the runtime defaults are conservative and the kernel grants the root
bootstrap instance the modeled administrative privileges. Their effective
policy is:

- accept reads needed for discovery and status;
- accept load/install only for descendants owned by this instance;
- accept key mutation only under an authenticated profile that permits it;
- reject deletion or lifecycle changes you have not deliberately modeled.

The kernel always enforces ancestry, installed privilege bits, lifecycle, and
its protocol matrix first. Your hook may narrow that decision but must never
try to widen it. See
[Privileges And Policy](security.domain.developper.guide.md#6-privileges-and-policy)
and [Keys And Key Management](security.domain.developper.guide.md#7-keys-and-key-management).

Keep `process_apdu()` small. It is the selected application's ordinary APDU
surface, not the place to parse protected GlobalPlatform management commands;
those arrive through the `RustletSecurityDomain` hooks.

## 8. Validate The Complete Path On Pico1

Rebuild and reflash your final implementation, capture the ATR, select the
root, and open SCP03 as above. Then deploy the Rustlet built in
`rustlets.getting.started.md` under your Security Domain. Rebuild its FAE first
so this checkpoint does not depend on an artifact left by the previous guide:

```bash
cd rustlets/my_first_rustlet
RUSTLET_TARGET=thumbv6m-none-eabi cargo build-fae
cd ../..

target/debug/apdu_tool --progress gp deploy \
  A0000047504F5321 \
  rustlets/my_first_rustlet/build/my_first_rustlet.fae \
  A0000047504F5322 \
  --security-domain A0000047504F5331
target/debug/apdu_tool gp get-status applications --aid A0000047504F5322
target/debug/apdu_tool select A0000047504F5322
target/debug/apdu_tool raw 00:04:00:00:00:02
target/debug/apdu_tool raw 00:08:00:00:04:04:DE:AD:BE:EF
```

The acceptance criteria are:

- deployment ends with `9000`;
- GET STATUS names `A0000047504F5331` as the parent;
- the two Rustlet calls return `CA FE` and `DE AD BE EF`;
- after `close`, reset, a new ATR, and a new SCP03 open, the installed Rustlet
  is still present.

The interactive `apdu-tool` flow intentionally stops at these observable
positive checks: it does not expose a supported mode for editing and replaying
an already protected packet. Wrong-key, modified-MAC, invalid-padding, replay,
counter and non-advancement cases belong to the automated Security Domain
campaign below, where the exact protected bytes and expected state are under
test control.

Run the focused campaign against the checked-in final tutorial implementation:

```bash
cargo run -- test gp_tutorial_scp03_security_domain \
  raspi-pico1 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 \
  --allow-destructive
```

It exercises S16 establishment, wrong static host keys, bad host
authentication, a modified C-MAC,
valid C-MAC with invalid ISO9797-M2 padding, C-MAC/C-ENC management, key
rotation, protected installation, R-MAC/R-ENC and replay rejection. Success
ends with `TUTORIAL-SCP03-SECURITY-DOMAIN-DONE ... total=31`. The runtime unit
test also checks the 244-byte serialization gate and counter-overflow
non-advancement:

```bash
cargo test --manifest-path rustlets/rustlet_runtime/Cargo.toml \
  --features runtime scp03::tests
```

For a regression oracle independent of your code, run the checked-in complete
implementation on the same board:

```bash
cargo run -- test gp_rustlet_security_domain_delegated_scp03 \
  raspi-pico1 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 \
  --allow-destructive
```

Success ends with `RUSTLET-SECURITY-DOMAIN-DELEGATED-SCP03-DONE` and
`total=44`. If the oracle passes but your implementation fails, compare the
first differing establishment or secure-messaging checkpoint instead of
debugging the whole flow at once.

## 9. Know What This Exercise Does Not Solve

This root workflow provisions keys in the firmware manifest. Dynamically
deploying the neutral Security Domain, as demonstrated in the previous guide,
does not automatically provision its first SCP03 keyset. Designing an
authenticated first-key ceremony for a supplementary Rustlet Security Domain
remains separate work; do not solve it by embedding keys in source or accepting
them over a clear APDU.

The resulting implementation is a learning and bring-up Security Domain, not a
production certification claim. Production work must additionally define key
ceremony, diversification, entropy, anti-tearing behavior, lifecycle recovery,
side-channel requirements, zeroization evidence, and the exact GlobalPlatform
profile and test suite being claimed.

## Reference Checklist

Before calling the exercise complete, review:

- [`RustletSecurityDomain` Rustdoc](security.domain.developper.guide.md#api-reference);
- the [kernel/Rustlet dispatch flows](security.domain.developper.guide.md#apdu-processing-flow);
- the [current reference implementation](security.domain.developper.guide.md#current-reference-implementation);
- the [current framework boundaries](security.domain.developper.guide.md#current-boundaries).

The implementation should be explainable from those contracts without relying
on undocumented `complete_security_domain` behavior.
