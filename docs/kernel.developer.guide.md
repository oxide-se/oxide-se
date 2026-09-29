# Kernel Developer Guide

This guide describes the current kernel-side Rustlet execution model in
`kernel/firmware`.

It focuses on the boundary between:

- the APDU transport and secure-channel loop in `kernel/firmware`;
- the shared services hosted in `oxi_core`;
- the standalone FAE images embedded into the kernel;
- the Rustlet runtime ABI used by those images.

## Scope

The current design is still an incremental GlobalPlatform implementation.

It now has a kernel-managed object registry, explicit Security Domain
authorities, SCP03/SCP11 secure-channel profiles, dynamic package loading, and
selected-Rustlet isolation. It does not yet implement the complete
GlobalPlatform lifecycle matrix, multi-channel model, or production-grade
registry/key-store policy.

What it does implement is a complete end-to-end path for:

- embedding one or more privileged Rustlet FAEs into the kernel image;
- selecting a Rustlet by AID;
- loading and relocating that FAE through the XiPFS startup path;
- executing the Rustlet in a distinct non-privileged context;
- routing later clear or protected APDUs to the selected Rustlet through a
  stable ABI;
- recovering cleanly from normal return, `exit`, `panic`, and MPU
  faults.

The important ownership rule is still:

- `kernel/firmware` owns transport, `SELECT`, deferred `GET RESPONSE`, and the
  selected Rustlet slot;
- `kernel/firmware/src/secure_channel.rs` owns the secure-channel APDU
  façade: SCP03/SCP11 establishment APDUs are consumed there, protected
  commands are unwrapped before dispatch, and protected responses are wrapped
  during completion;
- the selected Rustlet owns only its command semantics once selected.

There is also a deliberately separate, statically composed kernel-local path:

- `kernel/firmware/src/kernel_main_app.rs` owns the typed hook chains used by
  privileged `KernelAppModule` extensions;
- each selected module lives in its own file under
  `kernel/firmware/src/kernel_main_app/` and is part of the image TCB;
- APDU filters are one possible hook, not the definition of a module. Modules
  may instead observe kernel or Rustlet lifecycle events.

## Build and Embedding Pipeline

The current pipeline is explicit on purpose.

1. Each Rustlet is built as an independent FAE image.
2. `xtask` builds those FAEs before building `kernel/firmware`.
3. `kernel/firmware/build.rs` exports the generated FAE paths through
   environment variables.
4. `kernel/firmware/src/embedded_apps.rs` embeds the resulting files through
   Rust-native byte inclusion based on the selected build manifest.
5. At first initialization, the generated predeployment plan inserts package,
   instance, Security Domain, and key objects into the kernel-managed object
   registry.

Kernel application modules use a shorter parallel pipeline:

1. `[kernel-image].kernel-app-modules` carries an ordered list of names.
2. `xtask` validates only generic syntax and duplicates, then forwards that
   ordered list to the firmware build.
3. `kernel/firmware/build.rs` resolves every name through the single registry
   in `kernel/firmware/src/kernel_app_modules_registry.inc.rs`.
4. The build script generates one static slice per hook type in `OUT_DIR`.
   Only modules that implement a hook occur in that hook's slice.
5. `kernel_main_app.rs` walks those slices at the corresponding lifecycle
   points. There is no runtime registration, allocation, symbol lookup, or
   mutable module table.

The TOML order is the priority order for every filtering chain: the first APDU
filter that claims a command handles it. Observer hooks run in the same order.

Important current implementation details:

- embedded FAEs are aligned on 2 KiB boundaries in flash;
- the object registry is fixed-capacity in RAM while the firmware runs, and
  targets with a persistence area rebuild it from the latest valid persistent
  `BOSS` block at boot;
- recovery skips the complete extent of a structurally bounded block even if
  its CRC is invalid: an interrupted object's payload cannot supply another
  `BOSS`. Recycling programs and verifies zero magic words at every recognizable
  inner page header before retiring the outer header. It erases only the sectors
  required by the replacement, not the entire retired object. Live objects and
  the current registry remain protected; recycling cannot start inside an old
  block whose header survives;
- live registry objects occupy stable runtime slots. Deletion leaves a
  tombstone instead of compacting later objects, and the next insertion may
  reuse the first tombstone;
- selected applications, selected Rustlet Security Domains, the active
  Security Domain, and exceptionally displaced contexts retain slot numbers rather
  than copied AIDs or object payloads. Every such optional reference must be
  cleared or consumed before its slot can be reused;
- embedded package code remains compile-time data selected by the manifest,
  while dynamically loaded packages can be committed as persistent `C0DE`
  blocks;
- the kernel embeds only the Security Domains and Rustlet packages declared by
  the selected configuration.

The normal build embeds the registry entries declared by the selected build
manifest. The user-facing entry point is `cargo run build --config=...`;
internally, `xtask` forwards that path to Cargo through
`OXIDE_SE_BUILD_CONFIG` because Cargo build scripts do not have their own
command-line option channel.

Trace output is a build/run option, not part of the predeployment manifest.
Use `--trace=none`, `--trace=semihosting`, or `--trace=jtag` on the `cargo run`
xtask command:

- `--trace=none` is the default and compiles kernel `consoleln!` traces as
  no-ops.
- `--trace=semihosting` enables QEMU/debug semihosting console traces.
- `--trace=jtag` enables the target debug trace hook and is currently accepted
  for `raspi-pico1` and `raspi-pico2`.

QEMU runners may still enable semihosting services for test control or
target-provided entropy; `--trace` controls kernel console/debug traces.

For targeted Rustlet debugging, `xtask` either selects an existing
`configs/config_rustlet_*.toml` manifest or generates a small manifest
under `target/xtask/generated-configs`. The important invariant is that
single-Rustlet tests must not remap AIDs: a Rustlet uses the same AIDs in
`test rustlet` and in the full `test rustlet_all` image.

Target tests are selected through `cargo run test <name> [board] [options]`.
`xtask/src/testing/catalog.rs` owns the `TestCatalog`: each entry specifies the
scenario name, description, manifest, supported image/stack options, argument
kind, and required board capabilities. The catalogue drives parsing, help,
and configuration selection; add a scenario there rather than duplicating
command lists in `lib.rs`.

The host test code separates protocol assertions from target execution:

```text
xtask/src/testing/
  mod.rs          command dispatch, campaigns and stack-check scopes
  catalog.rs      scenario descriptions, help and capabilities
  options.rs      argument parsing and validation
  context.rs      explicit build inputs shared by a campaign
  target.rs       image preparation, QEMU lifetime and ATR synchronization
  openocd.rs      owned debugger, hardware programming/reset and serial ordering
  scenarios/
    kernel.rs     core and kernel-module assertions
    gp.rs         management and secure-channel assertions
    rustlets.rs   canonical application scenarios
    persistence.rs  multi-boot registry transactions
```

To add a test, register it in the catalogue, then put its APDU operations and
assertions in the relevant scenario module. Use `target::run_apdu` for a fresh
image/target session; do not assemble a QEMU command or repeat connection and
cleanup code in the scenario. The runner validates the ATR against the effective
manifest before calling the scenario. Errors identify the scenario, board,
backend, elapsed time and stage; APDU transport failures include the command
header without dumping payload secrets. Target output is drained while QEMU
runs and attached to failure reports.

The client distinguishes connection setup (`TARGET_CONNECTION_TIMEOUT`, five
seconds) from firmware initialization before the first ATR byte
(`TARGET_INITIALIZATION_TIMEOUT`, 120 seconds). Predeployment installs and
flash commits can outlast connection setup, notably under Pico1 QEMU. The
`ATR validated after ...s` log records the complete ATR observation time,
including frame-idle detection. This host allowance is not an ISO reset-to-ATR
timing guarantee and does not relax APDU byte deadlines or the 200 ms frame-idle
limit. Both constants live in `xtask/src/lib.rs`.

`BuildContext::with_config` derives another profile without changing the
process environment. Instrumentation and trace settings survive that change.
Only child compilation commands receive the variables consumed by `build.rs`;
disabled options explicitly clear inherited values. Keep source files and
payload inputs unchanged during a campaign. Within that invocation, identical
effective image configurations reuse an immutable image snapshot, not a running
QEMU process. Snapshots cannot be overwritten by a subsequent profile build
and are removed when the campaign ends.

For persistence, keep one `target::FlashFile` owner across boots and call
`target::run_boot`: supply the image only for the initial boot, then `None`
for resets against the same flash file. Target teardown kills and reaps QEMU,
collects its output and removes its socket even after a failed connection or
assertion. Flash-file and image owners also clean up on early returns.

`--on qemu` is the default when the selected board has QEMU support.
Otherwise the default is OpenOCD; an explicit board remains mandatory for
hardware. Without `--serial`, the unique USB serial port is selected at 115200
baud; ambiguous or absent USB links require an explicit choice. A failed QEMU
test never falls back to hardware.
ELF is the default; unsupported formats or stack options are rejected before
building. Stack baseline identifiers use
scenario names independently of CLI syntax; renaming a command must preserve
its measured commits, checkpoints, and limits.

### OpenOCD Execution

**Validation status:** the centralized runner is implemented and covered by
host tests, including mocked reset/serial ordering and failure cleanup.
Its Tcl RPC framing has been checked against OpenOCD without a probe.
On 2026-08-30, `kernel_ping raspi-pico2 --on openocd --allow-destructive`
passed end-to-end with automatic serial selection, OpenOCD HEAD d9b957f35
and a CMSIS-DAP probe: flash programming/verification, ATR and one echo
assertion. `kernel_t0` also passed all four checks, and the `kernel_crypto`
AES-128-CBC benchmark passed with a known vector. The original Pico2 validation also passed the
`fill_random 24` benchmark through the former SDK-style raw-TRNG/PRNG backend;
this is functional validation, not a cryptographic security guarantee.
The default crypto smoke scenario passes on Pico2, with P-256 returned through
one GET RESPONSE using the existing shared APDU buffer.
Other boards/scenarios and hardware failure cleanup still require
validation; successful QEMU runs and builds do not establish it.
The physical acceptance checklist is tracked in
[`TODO.md`](TODO.md#board-porting-and-hardware-validation).

`testing/openocd.rs` controls a private OpenOCD process over its loopback
[Tcl RPC interface](https://openocd.org/doc/html/Tcl-Scripting-API.html).
It uses the installed `openocd` executable, `interface/cmsis-dap.cfg` and the
board catalogue's `openocd_target` script (`target/rp2040.cfg` for Pico1,
`target/rp2350.cfg` for Pico2). The installed OpenOCD must provide that
script and its flash driver. `--probe-serial ID` selects the debug adapter
when several are attached; it does not select the APDU serial port.

With one USB UART bridge attached, the short hardware command is:

```sh
cargo run test kernel_ping raspi-pico2 --on openocd --allow-destructive
```

Without `--serial`, the runner enumerates ports without opening them and
selects the unique USB serial interface at 115200 baud. Bluetooth and platform
console ports are not automatic candidates. On macOS, `cu.*` is preferred over
the matching `tty.*` alias. If several USB interfaces exist, it stops and
lists ports, USB metadata and commands using `--serial` to select one.
An explicit `--serial` bypasses discovery, including for non-USB ports or
another baud rate. USB discovery identifies an adapter, not proof that its
UART is wired to the selected board; ATR/APDU validation still checks that.

The first hardware scenarios to validate are `kernel_ping`, `kernel_t0`,
and `rustlet minimal_valid_test` on a Rustlet-capable board. `kernel_crypto`
and its `--bench` operations also use the same OpenOCD/APDU path; the complete
crypto scenario requires working target entropy. Run the first three in
that order, expecting respectively 34, 4 and 6 successful assertions:

```sh
cargo run test kernel_ping raspi-pico1 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 --allow-destructive
cargo run test kernel_t0 raspi-pico1 --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 --allow-destructive
cargo run test rustlet raspi-pico1 minimal_valid_test --on openocd \
  --serial /dev/cu.usbmodemXXXX:115200 --allow-destructive
```

Replace the serial path with the APDU UART bridge, not a debug-control port.
The shared `apdu_tool` transport also accepts `COM3:115200`, a TCP endpoint
or a Unix socket. Physical serial uses 8 data bits, no parity, one stop bit
and no flow control. No second APDU protocol implementation is introduced.

**Destructive:** each invocation erases the board's declared FLASH range,
including the persistent registry, before programming and verifying the ELF.
Without `--allow-destructive`, the command reports the affected range and
stops before touching the target. Use only a dedicated test device.

The ordered boot contract is:

1. Reset and halt; erase, program, verify; reset and halt again.
2. Open the APDU link and discard stale input while the target is halted.
3. Release reset with `reset run`; never purge the link after this point.
4. Receive and check the ATR, then run the same assertions as under QEMU.
5. Halt the target and stop the owned debugger, including after a test failure.

Builds use `hardware`, not the QEMU configuration, and the image-cache key
includes this distinction. The default trace is `none`; Pico1 and Pico2 can use
`--trace=jtag` through OpenOCD's semihosting support. Hardware rejects
`--trace=semihosting`, which denotes the QEMU build mode.

The internal reset-only path takes no image and issues no erase/program
commands. `kernel_flash` uses this reset-only path to test the block reserved
by `flash-probe` across three complete boots (five checks, validated on Pico2
and Pico1 QEMU). The module reserves the tail before the first registry access;
later or conflicting reservations are rejected. `kernel_registry` uses the
same reset-only path with the normal registry APIs: multi-page Data objects,
write/erase prefix faults, cumulative deletion, recycling under pressure and
repeated recovery. Its disposable registry is limited to 64 KiB of flash. See
the [registry campaign](kernel.getting.started.md#registry-persistence-test)
for the fault model and command details.
Broader GlobalPlatform persistence campaigns remain unavailable on hardware;
so do fault-diagnostic scenarios, FAE images and stack baseline checks/updates.
Adding an OpenOCD script does not by itself promote `board_support`.

Relevant files:

- `kernel/firmware/build.rs`
- `kernel/firmware/src/kernel_app_modules_registry.inc.rs`
- `kernel/firmware/src/kernel_main_app.rs`
- `kernel/firmware/src/kernel_main_app/*.rs`
- `kernel/firmware/src/embedded_apps.rs`
- `kernel/firmware/src/embedded_apps_registry.inc.rs`
- `xtask/src/lib.rs`
- `rustlets/*`

The functional Rustlet scenarios in `xtask/src/testing/scenarios/rustlets.rs` are shared:
`test rustlet` runs one canonical scenario, while
`test rustlet_all` embeds the normal test set and chains those same
scenarios in one QEMU session.
`test gp_all` calls the same GP scenario functions as individual commands,
using a fresh target for each independent scenario. Neither campaign launches
another xtask process.

## Security Domain Profile

The kernel resolves one Security Domain authority for each management command.
The root Security Domain backend is selected by the build manifest, not by
board code. Clear out-of-channel management uses the root Security Domain
authority; protected management uses the Security Domain instance bound to the
active secure-channel session.

The three selectable backends are:

- `NullSecurityDomain`
- `KernelSecurityDomain`
- `RustletSecurityDomainProxy`

The default is still:

- `NullSecurityDomain`

This profile authorizes management operations and does not implement a secure
channel. It is the no-security/debug profile used to keep the embedded Rustlet
flow available without a user-space Security Domain.

For kernel-owned GP/SCP bootstrap work, build with one dedicated manifest:

```sh
cargo run build --config=configs/config_scp03_test.toml
```

This selects:

- `KernelSecurityDomain`
- SCP03 profile `S8`

Use a manifest with `secure_channel.scp03_profile = "S16"` when the build
must exercise the explicit SCP03 S16 profile. The SCP03 profile is only valid
when the manifest enables SCP03 explicitly:

```toml
[secure_channel]
protocols = ["SCP03"]
scp03_profile = "S16"
```

For SCP11 builds, the manifest selects one or more establishment variants
without carrying an SCP03 profile:

```toml
[secure_channel]
protocols = ["SCP11"]
scp11_profiles = ["A", "B", "C"]
```

The implementation then applies one explicit security-level profile:

- SCP03 accepts `EXTERNAL AUTHENTICATE P1=00`, `01`, and `03`. It rejects
  response-protection levels `11`, `13`, and `33`; selected SCP03 responses
  therefore remain plain.
- SCP11a/b/c accept only CRT key-usage qualifier `95=3C`, which selects
  C-MAC/C-ENC/R-MAC/R-ENC. Other GP-defined qualifiers are rejected before
  authentication.
- `BEGIN R-MAC SESSION` (`INS=7A`) and `END R-MAC SESSION` (`INS=78`) are
  deliberately unsupported and return `6D00`. They are optional SCP03
  companion commands and do not apply to SCP11.

Host tests exhaustively validate the selected byte values. The dedicated
`test gp_scp03` and `test gp_scp11a/b/c` campaigns verify representative accepted
and profiled-out values through the firmware APDU boundary.

The ATR reflects that effective build configuration. Oxide SE emits compact
TLV historical bytes ending in:

```text
80 56 09 C1 DE 5E xx yy 73 80 00 00
```

`09 C1 DE 5E` identifies Oxide SE, `xx` is the OS version byte (`10`, meaning
1.0 beta, in the current tree), and `yy` summarizes the root Security Domain
posture plus enabled SCP03/SCP11 profiles. The ISO `73 80 00 00` Card
Capabilities object is intentionally minimal: it only announces selection by
full DF name/AID, not an ISO file system, extended APDUs, or logical-channel
management.

For a user-space Security Domain backed by one embedded Rustlet Security
Domain, use the Rustlet Security Domain QEMU commands:

```sh
cargo run test gp_rustlet_security_domain_scp03 --elf mps2-an385
cargo run test gp_rustlet_security_domain_scp11a --elf mps2-an385
cargo run test gp_rustlet_security_domain_scp11b --elf mps2-an385
cargo run test gp_rustlet_security_domain_scp11c --elf mps2-an385
```

This selects:

- `RustletSecurityDomainProxy`
- the dedicated Rustlet Security Domain predeployment manifest

The kernel profile routes `INSTALL [for load]`, `LOAD`,
`INSTALL [for install]`, `GET DATA`, `STORE DATA`, `PUT KEY`, `DELETE`, and
secure-channel establishment commands through the same
`SecurityDomainManagement` and `SecurityDomainSecureChannel` traits. Its SCP03
handshake delegates KDF, cryptograms, C-MAC/R-MAC, and C-ENC/R-ENC to the pure
`core::scp03` engine; its SCP11a/b/c handshakes delegate profile-specific
establishment to the shared `core::scp11` / `core::scp11c` code and then reuse
the common secure-messaging path. The S8 and S16 variants are SCP03
secure-channel profiles selected separately from the authority itself. SCP11
builds always use the SCP11 secure-messaging profile implied by the selected
SCP11 establishment variant, and do not carry an `scp03_profile`.

The management policy is authority-based:

- a clear management APDU is interpreted under the root Security Domain
  authority;
- a protected management APDU is interpreted under the Security Domain
  instance bound to the active secure-channel session.

From there, each backend applies its own policy. `NullSecurityDomain` accepts
out-of-channel clear management for bring-up and debug. `KernelSecurityDomain`
rejects that out-of-channel path and only accepts mutating management
operations through a valid secure channel. `test gp_security_domain`
exercises this boundary across the kernel Security Domain SCP03 and SCP11
profiles by rejecting clear mutating management, opening protected sessions,
installing `minimal_valid_test`, selecting it, and then running its minimal
APDU scenario.

The proxy profile routes the same kernel-side management and secure-channel
operations through `sddispatch` into the selected Rustlet Security Domain
instance. The kernel still owns:

- APDU parsing;
- registry insertion and lookup;
- privilege non-escalation checks;
- the active Security Domain context;
- secure-channel attachment to the active Security Domain instance.

The Rustlet Security Domain refines management policy and performs its own
SCP03/SCP11 cryptography through the runtime APIs exposed in
`rustlet_runtime`. The kernel still performs APDU-layer framing, DO parsing,
registry mutation, and transaction publication; the Rustlet Security Domain
answers the policy and cryptographic hooks exposed by `sddispatch`.

Kernel-native SCP03 static communication keys are typed registry objects
owned by a Security Domain. They are declared by the build
manifest or created later through `PUT KEY`, then stored as typed registry
objects attached to the owning Security Domain instance through
`parent_sd_aid`. In the current subset, each object stores raw AES-128 SCP03
`ENC` or `MAC` material keyed by `(key_version, key_id, usage)`, and
`INITIALIZE UPDATE` resolves those objects back into `core::scp03::StaticKeys`
before deriving one session.

This object model is shared by both secure profiles:

- `KernelSecurityDomain` reads its SCP03 static keys from those registry
  objects directly in the kernel;
- `RustletSecurityDomainProxy` exposes runtime syscalls so the Rustlet Security
  Domain instance can load its own SCP03 key material from the same registry.

The key-loading SVC is authorized only while a kernel-owned `sddispatch`
context holds the called SD's registry slot. This compact identity is captured
before entry, so the service does not reborrow the selected SD runtime record
while its invocation owns that record. No AID or key payload is duplicated.
The service resolves keys for the captured slot's owner, independently of the
ambient active-SD cursor. Ordinary `process_apdu` and installation calls carry
no such authority. Context replacement, selection replacement, normal scope
exit and abrupt-exit cleanup all revoke it. The SVC also validates parameter
and output memory against the suspended caller's windows.

The invocation participates in the registry transaction already owned by the
external APDU layer. SVC adapters use the same staged registry services as
native kernel callers; the invocation context does not own another transaction.

The 2026-09-19 Pico2/OpenOCD validation passed 122 checks across the Rustlet SD
SCP03, delegated SCP03, and SCP11a/b/c campaigns. SCP03 tests include denial
from an ordinary SD call, denial from an ordinary Rustlet while the SD remains
resident, and denial after panic recovery. Host tests exercise the same key
request implementation with a called SD different from the ambient active SD,
buffer bounds, selection replacement, normal retirement and abrupt exit.

Compared with `c8dcc3f`, the Pico2 devkit ELF flash span grows from 103168 to
103416 bytes (+248); `.data`, `.bss` and RAM-resident code sizes are unchanged.
The instrumented Rustlet SD SCP03 campaign retains a 3016-byte kernel peak,
with no increase at the 39 common APDU checkpoints. Its historical stack
check still rejects the first SELECT checkpoint (2520 bytes versus the
2376-byte reference from `d2b86a794391`); a separate hardware replay of the
unmodified `c8dcc3f` reproduces that same discrepancy. No baseline was changed
for this work. These are sampled observations, not worst-case interrupt bounds.

`PUT KEY` uses one coherent storage model:

- keys are managed objects in the global registry;
- each key object belongs to one Security Domain instance through
  `parent_sd_aid`;
- identical `(key_version, key_id, usage)` tuples may exist in multiple
  Security Domain subtrees because they are parent-qualified resources;
- session establishment always resolves keys relative to the active Security
  Domain instance, not from a process-global key table.

Both profiles use the root Security Domain AID declared by the selected
predeployment manifest. The default development manifest keeps
`A0000047504F5301`.

At boot, the kernel always creates one technical root Security Domain instance
in the global registry. The root is not implicitly the Issuer Security Domain:
an Issuer exists only when one direct child is declared with
`role = "issuer"`. The selected backend defines how the technical root behaves:

- `NullSecurityDomain` acts as a debug/development root authority. It
  owns a root administrative identity in the registry, serves the same minimal
  `GET DATA` administrative view as the kernel-native profile, but does not
  implement secure-channel establishment.
- `KernelSecurityDomain` acts as a kernel-native root Security Domain
  profile. It bootstraps the root administrative-state object and consumes any
  initial SCP03 key objects explicitly declared for that instance in the build
  manifest.
- `RustletSecurityDomainProxy` bootstraps one root Rustlet Security Domain
  instance in that same registry. The proxy remains the kernel-side authority,
  but the selected Rustlet Security Domain instance owns its higher-level
  policy and SCP03 state.

The kernel uses one build-time mechanism for the initial administrative
topology:

- choose the backend, root package/instance AIDs, instance install bytes, and
  pre-installed objects in one
  manifest;
- keep [config.toml](../config.toml) for
  the empty development image;
- use `cargo run build --config=...` for richer
  topologies.

The manifest format is structured around `package.*` and `instance.*`
sections. The minimal development image looks like this:

```toml
[root.package]
name = "NullSecurityDomain"
aid = "A0:00:00:47:50:4F:53:01"

[root.instance]
aid = "A0:00:00:47:50:4F:53:01"
install_bytes = "FF:FF:FF"
```

Initial keys are owned by the Security Domain section in which they are
declared. The current key type is the AES-128 material used by SCP03:

```toml
[[root.keys]]
type = "Scp03Static"
version = 1
id = 3
usage = "Enc"
material = "40:41:42:43:44:45:46:47:48:49:4A:4B:4C:4D:4E:4F"

[[root.keys]]
type = "Scp03Static"
version = 1
id = 3
usage = "Mac"
material = "50:51:52:53:54:55:56:57:58:59:5A:5B:5C:5D:5E:5F"
```

The same `[[security_domains.keys]]` form attaches initial keys to a
supplementary Security Domain. Images that do not declare keys do not receive
fallback development keys from the firmware.

For a rustlet package loaded inside one Security Domain, the package is
selected by path and each declared instance carries one explicit AID plus its
installation payload:

```toml
[[root.packages]]
path = "./rustlets/tests/minimal_valid_test"

[[root.packages.instances]]
aid = "A0:00:00:47:50:4F:53:16"
install_bytes = ""
```

Supplementary Security Domains use the same package/instance structure and
name their parent instance explicitly:

```toml
[[security_domains]]

[security_domains.parent]
aid = "A0:00:00:47:50:4F:53:01"

[security_domains.package]
name = "NullSecurityDomain"
aid = "A0:00:00:47:50:4F:53:02"

[security_domains.instance]
aid = "A0:00:00:47:50:4F:53:03"
install_bytes = "80:00:00"

[[security_domains.packages]]
path = "./rustlets/tests/minimal_valid_test"

[[security_domains.packages.instances]]
aid = "A0:00:00:47:50:4F:53:27"
install_bytes = ""
```

The dedicated regression command validates that this child Security Domain and
its contained instance are installed during first-boot initialization, and
that the child cannot escape its registry subtree:

```bash
cargo run test gp_predeployment mps2-an385
```

The practical bootstrap rule is:

- the technical root is the only Security Domain recorded with
  `parent_sd_aid = None`;
- zero or one direct child may be marked `role = "issuer"`; absence means that
  the composition has no distinct Issuer Security Domain, while a second
  declaration is a configuration error;
- every other Security Domain or applet instance is created under its declared
  Security Domain and therefore receives that instance as `parent_sd_aid`;
- manifest order is irrelevant: the generated plan installs the root, the
  optional Issuer, then all remaining domains in parent-before-child order.

This is also the rule used by `PUT KEY`:

- a clear `PUT KEY` is authorized, or rejected, by the root Security Domain;
- a protected `PUT KEY` is authorized, or rejected, by the Security Domain
  instance bound to the secure channel;
- the resulting key objects are inserted under that authority instance;
- later `INITIALIZE UPDATE` lookups resolve against that same parent-qualified
  scope.

## Runtime Ownership Model

The runtime is split into a few small layers with different
responsibilities.

### 1. Byte transport and T=0 manager

`kernel/firmware/src/main.rs` owns the APDU loop through the abstract
`TransportLayer` interface.

The current stack starts with two explicit layers:

- `kernel/firmware/src/transport_layer.rs`
- `kernel/firmware/src/apdu_manager.rs`

`TransportLayer` owns only byte I/O:

- `send_byte`
- `receive_byte`

The current concrete backends are:

- `SerialTransport` for the normal UART path;
- `SimulatedTransport` for scripted APDU runs;
- `CurrentTransport` as the runtime-selected sum type.

`T0ApduManager<T>` is built on top of one `TransportLayer` instance and is
responsible for:

- ATR emission;
- reading the APDU header;
- retaining only deferred-response metadata, leaving the response bytes in the
  shared APDU payload, and emitting `61xx`;
- recognizing and serving `GET RESPONSE`;
- emitting procedure bytes;
- handling pure-outgoing `6Cxx`;
- emitting final `SW1/SW2`.

The selected Rustlet never owns the transport directly.

`kernel/firmware/src/kernel_main_app.rs` sits next to this loop on purpose. It
does not own transport either. Before conventional kernel dispatch, the loop
offers each command to the statically selected APDU-filter slice. The first
filter that claims the command returns its final status. If no filter claims
it, a `global-platform` image continues through normal management or selected
Rustlet dispatch, while a `kernel-only` image returns instruction-not-supported.

GlobalPlatform management handlers retain explicit non-inlined call boundaries.
Their temporary state must not become part of the long-lived APDU loop frame:
that frame remains on MSP while a selected Rustlet runs on PSP and invokes
kernel services through SVC. Separate source functions alone do not establish
this stack boundary under release LTO.

This behavior is selected by `[kernel-image].mode`; it is not an embedded-
Rustlet boolean. Kernel application modules may also be present in a
`global-platform` image, for example to measure stack use while the ordinary
GlobalPlatform and Rustlet paths remain active.

### 2. APDU protocol-layer composition

Above the base `T0ApduManager`, the kernel uses a separate protocol
boundary defined in `kernel/firmware/src/apdu_layer.rs`.

The central trait is:

- `ApduLayer`

Its job is deliberately narrow:

- emit ATR when relevant;
- receive one `ApduCommand`;
- complete one `ApduCompletion`.

This is the composition point for protocol wrappers above the base
`T=0` manager. At the time of writing, the stack instantiated in
`main.rs` is:

1. `CurrentTransport`
2. `T0ApduManager<CurrentTransport>`
3. `PassthroughApduLayer<_>`
4. `SecureChannelLayer<_>`
5. `TracingApduLayer<_>`

The two wrapper layers are intentionally small:

- `TracingApduLayer` logs APDU-layer transitions for scripted runs;
- `SecureChannelLayer` consumes SCP03 and SCP11a/b/c establishment APDUs,
  calls the active `SecurityDomainSecureChannel`, separates the raw protected
  command payload from its trailing C-MAC, and emits protected response data
  followed by R-MAC when secure messaging is active.

`SecureChannelLayer` is profile-neutral at the APDU-wrapper boundary. It
recognizes the GlobalPlatform establishment command families:

- `INITIALIZE UPDATE` and `EXTERNAL AUTHENTICATE` for SCP03;
- `PERFORM SECURITY OPERATION`, `INTERNAL AUTHENTICATE`, and
  profile-specific `MUTUAL AUTHENTICATE` forms for SCP11a/b/c.

For each protected command, the layer snapshots whether the authenticated
session requires response protection before dispatching the clear command.
That boolean is stored in the current `ApduCommand` and consumed during
completion; it cannot leak into the next APDU because it has the same lifetime
as the command. This ordering is an ABI invariant for a Rustlet-backed
Security Domain: querying its session state uses `sddispatch` and therefore
reuses the shared APDU page, so the kernel must not query that state again
after the selected application has produced its response.

SCP11 establishment parameters are bound before session derivation:

- the common parser rejects reserved SCP parameter bits and requires tag `84`
  exactly when parameter bit `b3` includes identities in `SharedInfo`;
- `P1`/`P2` select the ECKA key version and identifier owned by the active
  Security Domain; unsupported selectors are never replaced implicitly;
- SIN/SDIN for SCP11a/b and Card Group ID for SCP11c come from the active
  Security Domain, not from host-controlled CRT fields;
- `SecureChannelLayer` reassembles PSO command blocks selected by `P1.b8`
  before delegating the verified certificate to either backend. The current
  bounded development profile accepts 256 certificate bytes and rejects
  intermediate certificate chains selected by `P2.b8` with `6A86`.

The selected Security Domain owns the profile-specific state machine, keys,
cryptograms, replay counters, MAC chain, and encryption policy. The APDU layer
owns only the boundary transformation:

- establishment APDUs are consumed and completed before generic dispatch;
- protected command APDUs are authenticated/decrypted into a logical clear
  command before dispatch;
- protected responses are wrapped during `ApduCompletion`;
- SCP03 clear commands remain clear and are dispatched according to the active
  authority policy;
- while SCP11 secure messaging is active, a clear `SELECT` terminates the
  session and continues normally, whereas any other clear command aborts the
  session and returns `6985`.

Secure-channel failures use one explicit status contract at this boundary:

- `6700` reports an invalid profile-dependent length or a protected field that
  cannot fit its bounded destination;
- `6A80` reports malformed SCP11 CRTs or another malformed command data
  structure;
- `6A86` reports an invalid `P1`/`P2` selector or a deliberately profiled-out
  command option;
- `6A88` reports a referenced SCP03 keyset or SCP11 ECKA/CA key that cannot be
  resolved by the active Security Domain;
- `6600` reports SCP11 certificate verification failure;
- `6300` reports failed SCP03 host authentication;
- `6982` reports a secure-messaging cryptographic failure, including an
  invalid MAC chain, stale receipt, or replay;
- `6985` reports a valid command received in the wrong protocol state, such as
  `EXTERNAL AUTHENTICATE` before `INITIALIZE UPDATE`;
- `6D00` reports an establishment instruction not implemented by the selected
  build profile.

The SCP03 and SCP11 engines calculate candidate MAC chains and encryption
counters locally. They publish those values only after the complete unwrap or
wrap operation succeeds, so malformed APDUs, short output buffers, invalid
padding, and replays cannot partially advance session state. Structural
protected-APDU errors retain an authenticated session so a corrected command
can be sent. A cryptographic secure-messaging error returns `6982`, clears the
session, and makes every subsequent protected command fail with `6985` until a
new establishment sequence completes. Failed host authentication similarly
requires a new `INITIALIZE UPDATE`.

After unwrapping, the dispatcher applies a protocol-level management matrix
before consulting the selected Security Domain hooks:

- SCP03 and owner-authenticated SCP11a permit the implemented management
  families;
- card-authentication-only SCP11b permits read-only `GET DATA`, but no registry
  mutation;
- owner-authenticated SCP11c forbids `PUT KEY`, `SET STATUS`, and deletion of
  key objects, while allowing its other implemented management families;
- SCP11c `ANY_AUTH` is limited to `GET DATA` because the current profile does
  not implement the `BF20` authorization object.

This first gate is not overridable. Hierarchy checks, privileges, and
`SecurityDomainManagement` hooks are still evaluated for every accepted
command, so a native or Rustlet-backed backend may further restrict a request
but may never widen the protocol matrix. The dispatcher reads the active
kernel-owned session binding for this gate; it must not call a Rustlet
Security Domain's `session_state()` after unwrapping because that call reuses
the shared APDU page.

There is one deliberate fallback for supplementary protocols. A protocol
enabled by the build manifest is always recognized and filtered by the kernel
matrix above. If no compiled profile claims an establishment header, the active
Rustlet Security Domain may claim it through
`CLAIM_DELEGATED_SECURE_CHANNEL`, consume the raw establishment command through
`HANDLE_DELEGATED_SECURE_CHANNEL`, and own the resulting session policy. The
kernel records that ownership without pretending to know a protocol number.
Its protected-payload framing and memory bounds still apply, and registry reachability,
privilege non-escalation, lifecycle guards, and every management-family hook
remain mandatory. Only the unknown protocol's establishment, cryptographic
state, and profile-specific authorization matrix are delegated.

The regression command
`cargo run test gp_rustlet_security_domain_delegated_scp03 mps2-an385`
builds with `secure_channel.protocols = []`: the ATR advertises no kernel SCP
profile, while `complete_security_domain` claims SCP03 and passes the S8, S16,
`0x33`, key-rotation, replay, and protected-install scenarios. Native engine
entry points are constant stubs in this build profile, allowing release
dead-code elimination to remove the SCP03/SCP11 engines from `kernel.elf`; the
Rustlet FAE remains the sole SCP implementation in that image.

The layer must preserve the kernel zero-copy discipline. Protected bytes are
received in the transport-owned APDU buffer. Temporary authenticated strings,
clear payloads, and response MAC bytes use explicit kernel scratch buffers with
APDU-sized bounds, not unbounded stack arrays. After a successful unwrap, the
transport APDU buffer is rewritten in place with the logical clear payload that
management handlers or a selected Rustlet will see.

The important design rule is:

- higher protocol layers should be expressed as `ApduLayer`
  implementations;
- they should not need to know the concrete `TransportApdu` type.

### 3. APDU command and completion boundary

`ApduLayer` does not expose `TransportApdu` directly.

Instead it uses:

- `ApduCommand`
- `ApduCompletion`

`ApduCommand` is the APDU-layer view of the current command. It exposes:

- the APDU header;
- lightweight header accessors;
- `as_apdu()` to derive the kernel-side `SEApdu` view.

It also carries layer-private, per-command metadata such as the response
protection decision captured before application dispatch. Higher layers do not
expose that metadata to application code.

`ApduCompletion` groups:

- the command being completed;
- the final `ApduStatus`.

This split prevents the kernel dispatcher from depending on the
transport-owned APDU representation. The dispatcher sees:

- one command object on the way in;
- one completion object on the way out.

### 4. Selection path

`SELECT` is recognized before generic dispatch.

The kernel:

1. receives the command data as an AID;
2. resolves the visible instance and package objects in the kernel registry;
3. loads the embedded FAE image referenced by the package object;
4. executes the Rustlet `start()` entry point in isolated mode;
5. validates the returned descriptor;
6. stores the resulting selected context.

If the AID is unknown, the kernel returns `6A82`.

Semantic rule:

- `SELECT` establishes the selected execution context;
- it does not call `install()`.

`install()` is called later only if the routed APDU uses
`INS = E6`.

### 5. FAE loading and activation

`kernel/firmware/src/fae_runtime.rs` owns the activation boundary.

The kernel enters the FAE at offset `0`. The RT0 selected by the Rustlet
producer is part of that image and remains responsible for its internal
startup and relocation work.

The current activation path is:

1. `load(fae)` validates the public FAE footer, including CRC, ISA, ABI
   profile/version and declared writable-RAM and stack requirements;
2. the kernel reserves application memory and derives an explicit layout:
   - executable flash window;
   - one power-of-two writable RAM block containing the execution stack first,
     followed immediately by relocated data and the Rustlet heap;
3. the kernel asks `oxi_core::core::isolation` to build an MPU plan for
   that layout;
4. `call_start()` enters the FAE at offset `0` through the isolation layer,
   with the application data base supplied as `app_gp`. The RT0 executes
   unprivileged under the Rustlet MPU plan, performs relocation and starts
   the application;
5. subsequent `call_handler()` invocations also enter through the isolation
   layer.

#### Public ABI and private RT0 metadata

The security boundary includes the RT0 on the untrusted Rustlet side from
its first instruction. The producer may choose or replace it, including
with arbitrary machine code. Kernel isolation must therefore hold without
assuming that the RT0 validates its own inputs or follows a particular
relocation algorithm. This applies to Security Domain Rustlets as well as
application Rustlets.

The kernel validates the fields it interprets and the operations it performs:
public footer parsing, memory-size arithmetic and allocation, isolation
configuration, and arguments crossing the syscall boundary. CRC and CPU/ABI
compatibility checks do not establish that the executable behaves safely.

Private section sizes, internal entry offsets and relocation tables are
interpreted by the selected RT0, not by the kernel. A malformed private table
may corrupt the Rustlet's own writable memory or cause an isolation fault;
the kernel must contain prohibited accesses and handle the fault through
the normal isolated-execution path. Private RT0 validation is not a kernel
security precondition.

Additional bounds and overflow checks inside a supplied RT0 are an optional
robustness and diagnostic tradeoff against startup size and execution cost.
They are not required of every Rustlet RT0. Malformed-input tests at the
kernel boundary should exercise fields the kernel actually consumes and
verify containment of faulty or hostile startup code; they must not make
the kernel depend on a specific private RT0 representation.

Activation returns `6A84` when the required Rustlet RAM or kernel-side heap
allocator metadata cannot be allocated. A recovered hardware fault
is identified internally as `6F01`; panic and watchdog termination remain `6F00`.
For GP command dispatch, runtime errors become `6400`; `INSTALL` retains
`6A84`, while `SELECT` reports unavailable activation as `6985`. Invalid startup
descriptors and unsupported isolation configurations also retain `6985`.
A failure to allocate memory inside a running Rustlet is not automatically
translated into `6A84`.

The kernel stores only the minimum state needed to re-enter the
application later:

- `app_gp`;
- the returned `state` pointer;
- a validated kernel-owned snapshot of the install/process/SD entry addresses;
- the Rustlet memory layout and MPU plan.

### 6. Isolated execution

Rustlets execute as isolated unprivileged application sessions.

`oxi_core::core::isolation` owns the generic execution-session
model:

- session state for the active Rustlet call;
- MPU plan programming;
- distinction between `start` and `handler` calls;
- return-value policy for normal and faulty exits;
- runtime exit hook wiring.

The board module selects its CPU implementation through a `cpu` module alias.
`target/mod.rs` uses that alias as `app_target_profile`; no runtime dispatch or
trait object is involved. `kernel/core/build.rs` emits exactly one architectural
cfg (`oxide_se_target_armv6m`, `oxide_se_target_armv7m`, or
`oxide_se_target_armv8m`) so incompatible assembly is not compiled.

- `armv6m_profile.rs` owns Thumb-1 entry/return, PMSAv6 and HardFault recovery.
- `armv7m_profile.rs` owns PMSAv7 and the external MPU stack guard.
- `armv8m_profile.rs` owns PMSAv8 and MSPLIM/PSPLIM. Its MPU has no NoAccess
  encoding: requests for it fail rather than silently granting privileged RW.
- `common_arm_m_profile.rs` owns the identical exception-frame/entry layouts,
  SVC immediate decoding, barriers and RAM-XN window programming. Compile-time
  assertions preserve the offsets consumed by assembly.
- `common_arm_m_profile/mainline.rs` shares the identical v7-M/v8-M Mainline
  exception machinery. ARMv6-M keeps its distinct exception path.

The selected profile and these shared mechanisms provide:

- `SVC` dispatch;
- `MemManage` dispatch;
- entry into isolated application context;
- return to the kernel;
- the 512-byte shared ABI region, mapped read/write and execute-never.

Board modules retain clocks, UART, flash, RNG and `MEMORY_LAYOUT`. CPU profiles
never import a named board. The target facade derives stack, boot ABI and RAM-XN
windows from that layout; the shared NX helper receives an explicit borrowed
window list and statically selected MPU operations, with no heap allocation.
Architectural SysTick is also implemented once in `common_arm_m_profile.rs`;
each board supplies only the effective core frequency through
`timer_clock_hz()`. Kernel code installs the single periodic callback with
`core::timer::set_periodic_handler()`. The callback starts as a non-preemptible
top-half and may call `core::timer::begin_bottom_half()` once its shared-state
updates are complete, allowing higher-priority interrupts to preempt the
remaining work. The dispatcher always restores interrupt delivery on return.
Oxide SE configures this callback at 100 ms. Independent saturating counters
emit T=0 NULL bytes every ten ticks while an APDU is being processed and expire
an active Rustlet after one hundred ticks. The T=0 path arms NULL delivery only
after all currently expected host bytes have arrived; every real response byte
clears that state immediately before touching the transport. Rustlet entry and
the common return/fault cleanup respectively arm and clear the watchdog.

SysTick intentionally remains below SVC priority. Consequently this first
watchdog is best-effort: neither its timeout nor NULL cadence advances during a
long syscall. Direct Rustlet execution is recoverable through the same redirect
used by MPU and CPU faults; the timer entry restores the kernel static base and
execution MPU phase before running Rust code. Flash backends that suspend XIP
must preserve and mask interrupts across that exact interval. A pending tick is
served only after XIP and the previous PRIMASK state have been restored.
The architectural encodings are checked in `armv8m_mpu.rs` by host tests.
MSPLIM guards kernel stack growth on v8-M; a direct memory write below the stack
is not the same test. The v8-M stack-guard diagnostic deliberately crosses
MSPLIM. The fault-containment policy below also covers synchronous UsageFault classes.

Pico2's `kernel/native/raspi-pico2/link.ld` reserves the last 16 KiB of RAM for
`.critical.kernel.fct`, including RAM-executed flash-programming routines:

- `0x20000000..0x2000c000`: 48 KiB mutable RAM, privileged RW/XN in region 6
  during kernel execution. The 8-KiB kernel stack starts at the RAM base;
  `.data`, `.bss`, allocator metadata, heap and Rustlet RAM remain below this end.
- `0x2000c000..0x20010000`: executable RAM reservation, excluded from the heap
  and NX mapping. The boot code copies `.critical.kernel.fct` here before use.

The linker asserts that both areas fit. `__ram_end` follows `.bss`, not the
executable section; the allocator stops at the mutable/executable boundary.
The 16-KiB reservation must match `PICO2_EXECUTABLE_RAM_SIZE` in `target/mod.rs`.
It is a reserved capacity, not the current code size.

PMSAv8 does not use the overlapping-region priority rule of PMSAv7. Before
installing kernel NX, `armv8m_profile` disables overlapping application regions.
During kernel execution, attempted user RAM mappings are deferred. Immediately
before user entry/resume, the isolation layer removes kernel NX and restores
the gate and application mappings from the existing isolation plan. There is
no second MPU-plan snapshot or per-transition allocation. A failed NX transition
terminates execution rather than continuing without protection.

`cargo run test kernel_ram_nx raspi-pico2 --on openocd --allow-destructive`
validates this on hardware: OpenOCD vector catch must stop at MemManage with
IACCVIOL, privileged MSP context, and stacked PC at a RAM `BX LR` instruction.
An APDU timeout or an unrelated HardFault is not success. Semihosting services
the core diagnostic's startup messages, but the verdict uses fault registers,
not console text. Flash, crypto and minimal Rustlet tests additionally check
that the executable tail and user transitions remain usable. This does not
establish complete Rustlet fault recovery.

`cargo run test kernel_stack_guard raspi-pico2 --on openocd --allow-destructive`
independently checks MSPLIM enforcement. The diagnostic saves the boot limit
in r2, raises MSPLIM to MSP and executes a PUSH. OpenOCD stops at the
UsageFault entry before handler stack use, checking STKOF alone
(`CFSR=00100000`, `HFSR=00000000`), privileged MSP context and the original
limit equal to the stack base. Kernel overflow remains fatal; this test does
not claim recovery or execution of a diagnostic handler on an exhausted stack.
The core-test build tracks the native-startup fingerprint so edits to its
external vector/startup object trigger a relink.

The [profile integration validation report](reports/arm-profile-integration-2026-08-31.md)
records tested targets, stack measurements and the remaining hardware checks.

Pico2 UART output waits for UARTFR.BUSY to clear before every 32nd byte,
without an artificial delay. Only the synchronous kernel transport writes
UARTDR; BUSY clears after the final stop bit. Each write checks TXFF at bit 5;
bit 6 is RXFF and cannot provide transmit backpressure. All 34 hardware ping
assertions through 255 bytes pass with this policy, including unfragmented
GET RESPONSE. Crypto diagnostics also retrieve their complete short response
without a bridge-specific chunk limit.

The current execution mode for a Rustlet is:

- thread mode;
- non-privileged;
- `PSP` for the Rustlet execution stack;
- MPU enabled with privileged default mapping still available to the
  kernel;
- `MSP` and privileged state restored on kernel return.

The return path is deliberately mediated:

- a normal Rustlet return does not jump directly back into privileged
  kernel code;
- Rustlet runtime code raises the reserved return `SVC` from its FAE image;
- the entry/exception trampolines and kernel-resume code reside in kernel
  flash `.text`; the shared RAM ABI page contains data only;
- `SVC`, `exit`, `panic`, and recoverable `MemManage` faults all
  converge toward the same kernel-resume mechanism.

### Rust memory-safety boundaries

`oxi_core` rejects implicit unsafe operations inside unsafe functions. Protocol,
validation and encoding modules without direct raw-memory operations forbid
unsafe code. This includes the safe flash/serial/MPU facades: their hardware
operations remain in the selected target backend, not in these facades.

The loader constructs `AppExecution` through an unsafe `from_raw_parts` boundary
that owns the proof of image, ABI, stack validity and resource lifetime. Its
private fields and borrowed isolation plan prevent safe code from substituting
arbitrary addresses or a different plan at entry. The token stays on its owner
core; it neither copies Rustlet RAM nor retains Rust references into a stack
while the Rustlet writes it. MPU mappings and permissions are unchanged.

`syscall::with_app_allocator` retains the allocator-state borrow for a synchronous
invocation and rejects nested publication. Its private guard retires the pointer
on normal/fault return or host unwinding. Kernel heap metadata has a separate
short exclusive-access scope, refusing reentry rather than spinning in an
interrupt. ARMv6-M uses the owner core's IRQ mask where compare-exchange is not
available. This remains a single-owner-core runtime, not a multicore scheduler.

Allocation and deallocation traverse the existing bit-tree iteratively, without
an auxiliary traversal buffer. Deallocation validates the complete path to an
allocated block before mutation, rejecting wrong rounded sizes, interior or
foreign addresses, and double frees. The tree establishes rounded block size,
not the exact original Rust Layout or authority to free another owner's block;
SVC allocation remains confined to the current Rustlet heap.

MMIO descriptor construction explicitly carries the selected board's raw-address
and register-protocol proof. Pico flash programming accepts RAM-resident sources
only, rejecting XIP-backed sources instead of copying a page to MSP. The Pico2
RNG guard owns access to its resident state. Volatile accesses still remain at
assembly-facing session/exception storage and secure erasure boundaries; these
retain their documented execution and lifetime obligations.

Rustlet crypto syscalls borrow memory through a scope tied to the suspended
invocation. Parameter records are aligned, range-checked snapshots restricted
to ABI types with integer and raw-pointer fields. Empty buffers are represented
by canonical empty slices, including when the ABI pointer is null. No returned
slice can outlive its scope borrow. Simultaneous input/output views are checked
for overlap before any references are created; ECDH/KDF outputs and keypair
outputs must be disjoint. AES stages overlapping input with a raw memmove before
borrowing output alone, and skips staging when the addresses coincide. MAC
publishes its small tag only after input consumption. These paths add neither
a resident scratch buffer nor heap allocation. Scope construction still carries
the explicit unsafe obligation that the active windows are live, initialized,
exclusive to the syscall, and owned by a suspended Rustlet.
The APDU outgoing-length syscall rejects lengths above the payload limit before
changing transport state. Its void ABI ignores invalid requests rather than
passing untrusted values to the transport's programming-error panic.

## Rustlet Memory Model

The current Rustlet memory model is intentionally simple and bounded by
the Cortex-M MPU constraints.

### Target RAM policy

Board-level memory budgets are declared as `MEMORY_LAYOUT` constants in
the target implementation files:

- `kernel/core/src/core/target/mps2_an385.rs`
- `kernel/core/src/core/target/olimex_stm32_h405.rs`
- `kernel/core/src/core/target/b_l475e_iot01a.rs`
- `kernel/core/src/core/target/raspi_pico.rs`
- `kernel/core/src/core/target/raspi_pico2.rs`

The core runtime consumes these constants directly. `xtask` reads the same
constants from the target source files for host-side diagnostics, so
heap/stack sizing and layout validation share the same target values.

Each entry defines:

- RAM base and size;
- FLASH base and size;
- minimum kernel heap size;
- kernel stack size.

`xtask` generates the native ELF and bootable FAE board linker wrappers from
`MEMORY_LAYOUT`. Native ELF wrappers include
`kernel/native/generic-cortex-m/link.ld`, except for the Pico ports, which use
their dedicated native linker scripts. Legacy bootable FAE wrappers include
`kernel/bootable/generic-cortex-m/link.ld`; **FAE kernel images are no longer supported**. The retained `--fae` option
is deprecated and emits a warning on stderr before a kernel build, including
when a cached image is reused. Use the default native ELF format (`--elf`).
Rustlet FAE images remain supported.
Both layouts place the kernel stack first, then a 32-byte boot ABI slot, then
the firmware RAM window.
The kernel heap is not a fixed linker section anymore; it is carved from the
remaining RAM at runtime.

When changing RAM, FLASH, or `kernel_stack_size`, update only the board
`MEMORY_LAYOUT`. The generated linker wrapper will carry the corresponding
`PROVIDE(__STACK_SIZE_CPU0 = ...)`, `RAM`, and `FLASH` values. If those values
were ever to diverge, the kernel and startup code would disagree on the boot
ABI address, and early SVC forwarding could fail before the kernel syscall
table is initialized. The host-side `xtask` test suite checks every known board
against its generated linker wrappers; run `cargo test -p xtask --lib` after
changing a target memory layout.

Test commands that accept `--check_stack` derive a complete manifest from the
selected source manifest, add both `kernel-stack-monitor` and
`rustlet-stack-monitor`, and write the resulting input under
`target/xtask/generated-configs`. The firmware is then built through the normal
manifest path; no module-selection environment override is involved. The same
observer runs over QEMU and OpenOCD transports.

The kernel monitor initialization hook checks the linker bounds and sampled
MSP, then paints only the unused words below that MSP before the main loop.
Its post-APDU hook scans only the previously initialized prefix and records a
monotonic maximum; it never forms a Rust slice over live stack frames. Atomic
scalar counters retain the observations, and its APDU filter exposes the value.
The command fails above the smaller of the target's declared stack size and
the 6144-byte project budget, or if no
kernel measurement can be obtained. This applies to the
Rustlet campaigns and the dedicated SCP11 and Rustlet-backed SCP03 Security
Domain campaigns; the floor is a regression budget, not a target to consume.

Software AES and CMAC construction first validates and borrows a cipher-sized
key, then uses the library's typed constructor. This keeps fallible results
small instead of transporting expanded cipher/MAC states through `Result`
temporaries. CBC, ECB, CMAC and SCP03 KDF share this rule; buffer validation and
the external cryptographic implementations are unchanged. Avoid substituting
`new_from_slice` without inspecting release stack usage.

With these construction paths and the management-handler boundaries,
`rustlet_all raspi-pico1 --check_stack` measured 3520 bytes of kernel stack and
1600 bytes of Rustlet stack under QEMU on 2026-09-09, with 102 assertions passing.
The prior same-toolchain kernel measurement was 6704 bytes. The physical Pico1
stack reservation remains 7168 bytes and the regression budget remains 6144.
This scenario does not bound every boot, interrupt or SCP11 path. Subsequent
[Pico1 hardware validation and timing comparisons](kernel.getting.started.md#pico1-hardware-validation-september-2026)
completed on 2026-09-19. These dated measurements describe earlier sources;
the [diagnostic qualification](kernel.getting.started.md#diagnostic-and-startup-qualification-september-2026)
records the later safety audit.

The subsequent active-session representation change measured 3424 bytes of
kernel stack in the same Pico1 QEMU Rustlet campaign. It reads the call kind,
fault return value and individual MPU regions separately, rather than copying
the complete session for every query and transition. These measurements do not
change either the physical reservation or the regression budget.

On physical Pico2 hardware through OpenOCD, the same optimized sources passed
ten stack-enabled campaigns on 2026-09-09: `rustlet_all`, SCP03 S8/S16,
SCP11a/b/c, and the five Rustlet Security Domain secure-channel variants.
`rustlet_all` measured 3336 bytes of kernel stack and 1520 bytes of Rustlet
stack. The largest kernel value was 5096 bytes in SCP11b/c, leaving 1048 bytes
under the 6144-byte budget (Pico2 reserves 8192 bytes physically). The largest
Rustlet value was 1936 bytes in delegated SCP03, leaving 112 bytes of its
2048-byte reservation. All 398 assertions passed; these are observed scenario
maxima, not bounds for untested paths. Only the kernel measurements participate
in versioned regression checks; Rustlet measurements remain informational.

The monitor query is the debug-only `GET DATA DF71` command. When that module
is selected, its secure-channel observation hook lets the probe observe an
active SCP11 session without treating it as the clear application command
that would normally abort that session. The exception and measurement code
are absent from images that do not select the module.

The `rustlet-stack-monitor` module paints the selected Rustlet stack
window immediately before userland entry, records its high-water mark after
return or fault recovery, and exposes the maximum through `GET DATA DF72`.
Both observer hooks are `unsafe fn(AppMemoryWindow)`: the loader must provide
an initialized, exclusive, inactive allocation and retain it until the observer
finishes. The after hook runs before stack scrubbing. No stack borrow survives
Rustlet execution.
When the campaign executes a Rustlet, `--check_stack` reports this second
measurement as well. These diagnostics are independent from mandatory
MSPLIM/PSPLIM and MPU guard policy: those mechanisms bound a stack, while the
modules measure its observed use.

The same command also compares the observed high-watermark checkpoints against
the versioned references in
[`xtask/stack-baselines.toml`](../xtask/stack-baselines.toml). A checkpoint is
recorded only when one tested functionality raises the consumed-stack maximum;
later labels on the same plateau are not duplicated. Baselines are qualified by
command, board, image format, execution environment, optional Rustlet scenario,
and monitor profile.
The current baseline file contains only `apdu-observer-v2` campaigns. The
profile remains part of the identity so differently instrumented binaries
cannot accidentally be compared if another profile is introduced later.

All 15 existing QEMU identities were measured against commit `a73b48e6f80b`;
12 references were refreshed. The three mps2 kernel SCP11 references retain
their historical values until interrupt headroom is qualified. Hardware references retain their measured
commits until the corresponding boards are replayed. The field
`rustlet_high_watermark` is informational only: it records an observed Rustlet
maximum, not a regression ceiling. Kernel and Rustlet stacks are never added.
See the [stack baseline audit](kernel.getting.started.md#stack-baseline-audit).
Physical allocations and the global kernel budget remain unchanged.

The comparison policy is intentionally asymmetric:

- `--check_stack` fails when a known kernel checkpoint grows, when a new
  checkpoint exceeds the previous campaign maximum;
- Rustlet high-water marks remain visible but do not participate in regression
  comparisons or the kernel budget; their physical isolation limits still apply;
- `--check_stack` reports a lower height as a gain without rewriting the
  reference;
- when no matching baseline exists, `--check_stack` warns and still applies
  the absolute stack budget, but does not fail merely because the reference is
  missing;
- `--update_stack_baseline` deliberately does not compare against the previous
  reference. It validates the measurement and absolute budget, then replaces
  the campaign with the new checkpoints and measured `HEAD` commit. Reviewing
  that change is the explicit act of accepting an increase or decrease;
- baseline updates require a clean tracked worktree, so the recorded commit
  identifies the exact measured sources.

The target catalogue distinguishes maturity from the validated runner:

- `mps2-an385`: `Rustlet`, with QEMU validation;
- `olimex-stm32-h405`: `Rustlet`, with QEMU validation;
- `raspi-pico1`: `Rustlet`, with QEMU validation and a persistent flash
  oracle;
- `raspi-pico2`: `Rustlet`, with OpenOCD hardware validation; QEMU support
  is not currently claimed;
- `b-l475e-iot01a`: `BuildOnly`, with no execution runner currently claimed.

Pico2 hardware validation covers Rustlet execution, dynamic application
loading and persistence across reboot, and Rustlet-backed Security Domains.
This does not claim that every Security Domain deployment path has been
qualified, including dynamic loading of a new Security Domain Rustlet.

Consequently, `cargo run test rustlet_all` without a board runs every target
whose level is `Rustlet` and whose `qemu_support` flag is true. Supplying a
board selects that target; use `--on openocd --allow-destructive` for a
connected Pico board and its UART bridge.

Use this command before running expensive QEMU campaigns:

```bash
cargo run dump_kernel_layout --elf mps2-an385 minimal
```

It prints the ELF allocated-section footprint, the kernel stack, the effective
firmware RAM footprint, the
derived kernel heap metadata/heap partition, embedded Rustlet FAE sizes,
and explicit overflow diagnostics when the image exceeds the selected
board's memory budget.

For investigation of the unsupported legacy kernel FAE path, the deprecated
`dump_kernel_layout --fae` mode instead reports the packaged FAE footer. Its post-packaging build gate validates the final FAE
against the selected target
before writing a fresh stamp or reusing a cached image. If the image does
not fit, generation fails with the full layout report instead of allowing a
later QEMU or hardware boot crash due to a known layout overflow. Passing this
layout check does not validate the legacy startup path.

### Kernel RAM layout

The current kernel RAM layout is deliberately linear and target-driven:

```text
RAM base
  [ kernel stack ]
  [ boot ABI, 32 bytes ]
  [ native firmware .data + .bss ]
  [ kernel allocator metadata ]
  [ kernel heap ]
  [ board-specific RAM-executed code reservation, on Pico ]
RAM end
```

The stack is placed at the beginning of RAM. This makes stack underflow
diagnostics simpler on Cortex-M targets: the MPU guard can protect the
large address window immediately below RAM instead of consuming an
additional in-RAM guard slot.

The boot ABI is a tiny fixed region used by the boot/startup code to pass
exception and periodic-timer forwarding hooks to the loaded firmware. It is intentionally
outside the shared Rustlet ABI region. Native ELF kernels also use this slot:
reset clears all 32 bytes before RAM initialization, and core initialization
publishes forwarding hooks before enabling interrupts. It belongs to the
kernel image layout, not to one selected Rustlet.

In native ELF kernels, the writable firmware sections start immediately after
the boot ABI; `__ram_end` bounds their initialized footprint. Historical linker
names such as `__fae_ram_start` are also used by this native path and do not
imply a FAE kernel image. Pico linker scripts reserve RAM-executed code outside
the mutable data/heap window. Pico2's total production RAM budget remains
64 KiB, including that reservation, both stacks and Rustlet allocations.

For the legacy bootable FAE kernel, the corresponding footprint is not just
the footer `ram` field. Its loader must also
reserve RAM for:

- relocated GOT data;
- ROM data copied into RAM;
- normal writable RAM.

`xtask` therefore validates the FAE footprint as `got + rom.ram + ram`.
This is the same budget the runtime startup path consumes.

The kernel heap starts after the writable firmware footprint, but its metadata
also needs RAM. This creates a small fixed-point problem: the metadata size
depends on the heap it describes, while the heap starts after the metadata.
The allocator solves this by deterministic convergence:

1. align the first free byte after the writable firmware footprint;
2. reserve a candidate metadata size;
3. place the heap after that candidate metadata block;
4. compute the exact metadata size needed for that heap window;
5. repeat until the reserved metadata block covers the required size.

The stopping condition is:

```text
required_metadata_len <= reserved_metadata_len
```

This is intentionally not strict equality. Moving the heap start can change
the virtual buddy-tree alignment, so exact equality can oscillate. The
kernel only needs the reserved metadata window to be large enough for the
heap it will manage.

The same partitioning algorithm exists in two places:

- `kernel/core/src/core/allocator.rs`, used by the kernel at boot;
- `xtask/src/lib.rs`, used by host-side image validation and layout dumps.

Keep these two implementations behaviorally identical. If they diverge,
the build report can claim an image is valid while the kernel fails to
initialize its heap, or the reverse.

Historical minimal bootable-FAE `mps2-an385` example (not a current native ELF
size reference; use the layout command for the selected image):

```text
kernel stack       0x20000000..0x20002c00 11 KiB
boot ABI           0x20002c00..0x20002c20 32 B
FAE runtime window 0x20002c20..0x20005db0 12688 B
kernel heap meta   0x20005db0..0x200061b0 1 KiB
kernel heap        0x200061b0..0x20008000 7760 B
kernel heap min    6 KiB
```

### Region packing

`oxi_core::core::isolation` currently packs executable text and keeps writable
RAM in one allocator-aligned MPU region:

- flash text covers exclusively owned 256-byte pages;
- PMSAv6/v7 uses at most five power-of-two code regions with eight subregions
  each, including overlapping nominal regions with identical RX permissions;
- PMSAv8 uses one exact base/limit code region without placement padding;
- one power-of-two RW/XN region covers the complete Rustlet RAM block;
- the first `stack_size` bytes, as declared by the FAE footer, are the
  downward-growing execution stack;
- relocated data and heap occupy the remainder immediately above the stack;
- one 512-byte data-only shared ABI region (RW/XN) in MPU region 0.

For PMSAv6/v7, `mpu_cover::Cover` selects the interval extending furthest from
the first uncovered byte. At each power-of-two size, only the aligned region
containing that byte is considered. Only complete subregions inside the owned
window are enabled. This is a minimum-cardinality interval cover; it uses no
heap allocation. Disabled subregions are not deny rules: no enabled region may
expose foreign pages, including when nominal region windows overlap.

Before dynamic LOAD, `mpu_cover_require_padding_for(address, size)` evaluates
four placements: unchanged, a 256-byte suffix, a 256-byte prefix, or both.
It minimizes added flash bytes, preferring a suffix at equal cost. The prefix
is an erased gap excluded from the mapping; the suffix belongs to the C0DE
block. Allocation reevaluates the geometry at each actual candidate address,
including recycled space. An impossible placement is rejected before writing.
The pre-padding gap may subsequently be reused independently because it grants
no access to the package.

The complete C0DE block is readable and executable in the Rustlet phase: its
12-byte header, exact FAE payload, erased rounding/padding and final 8-byte
CRC64. The reserved total length includes optional post-padding, while the
payload length and SHA-256 still describe only the received FAE. Padding bytes
remain `0xFF`; the trailing CRC is metadata, not padding. Reset recovery and GC
retain the complete owning extent. Software pointer checks retain the exact
FAE slice, and handler validation additionally excludes its footer.

Every 256-byte-aligned owning block through 74,240 bytes (72.5 KiB), before
optional padding, has a five-region placement. Some 74,496-byte blocks do not.
This is a coverage guarantee, not a new GP transfer-size limit: LOAD retains
its existing 64-KiB payload limit. Embedded packages retain their dedicated
aligned static storage. RAM permissions, the shared gate and the kernel-phase
execute-never transitions are unchanged.

The allocator rounds `stack_size + writable_ram_size` up to a power of two and
aligns the block to its size, respecting the target MPU minimum region size.
The data base and initial SP are at the upper
stack boundary. The same stack window is passed to entry, stack-limit handling,
scrubbing and the stack monitor. There is no kernel-wide 2048-byte stack ceiling.
FAE 1.0 encodes requests in 32-byte units (at most 65535 units); actual
activation also requires a sufficiently large aligned free RAM block. A package
may be loaded into flash even when its stack cannot currently be allocated;
activation then fails without creating an instance. The separate writable-data
capacity check remains in effect.

A Rustlet must declare at least one 32-byte stack unit. The privileged entry
SVC prepares a basic hardware exception frame at `stack_top - 32` and returns
directly to unprivileged Thread mode using PSP. Hardware unstacking leaves PSP
at the declared stack top. A custom rt0 can then move PSP before using more
stack; the standard Rust runtime needs a larger stack. A zero requirement is
rejected during FAE validation, including the final LOAD check.

The application budget is currently:

- MPU region 0 for the 512-byte shared ABI buffer (RW, execute-never);
- MPU regions 1 through 6 for Rustlet text/RAM/stack while Rustlet code runs;
- MPU region 6 recycled for kernel RAM execute-never protection while kernel
  code runs, when the selected target can express the protected RAM window as
  one MPU region;
- MPU region 7 reserved for the kernel stack-overflow guard.

If the Rustlet does not fit, loading fails. The isolation planner returns a
structured diagnostic containing the required and available region counts,
plus the original text/RAM windows and each window's slot contribution, rather
than crashing.

The `kernel_integrity` F3 / F-02 scenario uses a disposable image with a
64-KiB registry area. It dynamically loads the probe Rustlet between two
root-owned data markers and tests:

- readable owned header, code and trailer;
- syscall acceptance inside the exact FAE and `PermissionDenied` outside it,
  with untouched output on rejection;
- CPU faults immediately before/after the owning block and on both foreign
  markers, followed by successful execution of an unrelated Rustlet;
- the same checks after observed sector recycling, reset, deletion and reload
  at a new placement, then another reset.

This scenario passed on Pico1/QEMU (543 checks) and Pico2/OpenOCD (511 checks).
Both runs observed 25 sector erases during pressure. These results distinguish
emulated PMSAv6 subregions from physical PMSAv8 base/limit protection; MPS2's
PMSAv7 backend was compiled but not executed in this campaign. The broader
`kernel_integrity` command still reports incomplete coverage for its remaining
unimplemented finding groups and the outstanding multi-SD portion of F1.

The `kernel_sd_authority_integrity` scenario exercises a kernel parent with
one kernel child and one Rustlet SD child, plus a kernel grandchild. All SDs
are predeployed. The build orders parents before children regardless of manifest
order. Bootstrap provisions each SD's configured keys immediately after creating
it, before installing its children. Explicit keys replace inherited keys of the
same identity; descendants inherit that effective keyset.

The scenario checks each child's own registry mutations, rejected
sibling/parent selection and deletion, rejected foreign-owner `INSTALL [for
load]`, and independent DATA values under the same tag. Reboots preserve flash
and verify that both branches and the parent's marker survived. A failed SELECT
must preserve the current session; a successful parent-to-child SELECT must
invalidate it even though the root and Rustlet child share identical static keys.
The kernel child overrides its inherited keys; authentication to its grandchild
checks that those overrides propagate, including after reboot.
This tests kernel-enforced scope, not a general authentication policy for
user-defined Rustlet SDs. Cross-SD key-export probes remain separate F1 work.

Run it with `cargo run -- test kernel_sd_authority_integrity raspi-pico1 --on qemu`
or `cargo run -- test kernel_sd_authority_integrity raspi-pico2 --on openocd --allow-destructive`.
It is also included in the F-05 group of `kernel_integrity`. All 94 checks
passed on Pico1/QEMU and Pico2/OpenOCD.

The F-04 shared-page regression also runs independently as
`cargo run -- test kernel_gate_integrity raspi-pico1 --on qemu` or
`cargo run -- test kernel_gate_integrity raspi-pico2 --on openocd --allow-destructive`.
It uses disposable flash and dynamically loads the diagnostic Rustlet. Four
byte patterns cross the former trampoline boundary at payload lengths 246,
247 and 255, followed by a short command. Every incoming and outgoing byte is
checked. A second probe fills all 256 physical data bytes and checks adjacent
serialization storage and control fields. Host tests additionally surround
the 512-byte context with canaries. Existing probes require an NX fault from
the shared page, reject privileged launch through application SVC 0, and check
an unrelated application's response after the fault without rebooting.
This regression passed on Pico1/QEMU (106 checks) and Pico2/OpenOCD
(90 checks); totals include architecture-dependent LOAD block counts. It changes
no production gate layout or permissions.

The F4 / F-03 serialized-state regression runs independently with
`cargo run -- test kernel_state_integrity raspi-pico1 --on qemu` or
`cargo run -- test kernel_state_integrity raspi-pico2 --on openocd --allow-destructive`.
It is also part of `kernel_integrity`; the other F4 / F-03 containment cases
remain pending. The shared state's raw length byte is untrusted even though
the safe Rustlet setter bounds it. `StateSlice::try_as_bytes` and
`RustletCtx::try_state_bytes` return `None` above the 244-byte capacity without
truncation, allocation or copying.

Every handler return reacquires the exclusive gate lease and validates this
length before constructing the returned-state view. Invalid state clears the
control and payload halves and produces `6700` with `returned_normally=false`,
using the existing invocation teardown and registry rollback paths. This
boundary is common to ordinary handlers and Security Domain dispatch. Registry
state borrows independently validate the length and retain their exclusive
lease, preventing mutation between validation and use. Trusted convenience
accessors remain available; they must not be used to validate raw ABI input.

The regression accepts a 244-byte state, then forges lengths 245 and 255 while
attempting to replace a committed counter. It checks rejection, an unrelated
successful APDU without reboot, the unchanged counter after reselection, and
its durability after reboot. State-length rejection scrubs the staged output
before normal APDU completion; that path currently sends the staged length of
zero bytes followed by the error status, never the proposed response. Host tests check all 256 possible raw length bytes,
the leased return boundary, and clearing on rejection. The target regression passed on
Pico1/QEMU (102 checks) and Pico2/OpenOCD (86 checks), including LOAD and reboot.
These state-length tests do not establish containment of other application faults.

The independent `kernel_svc_integrity` scenario covers unknown SVCs 254 and
255 on the same backends and with the same destructive-flash option as
`kernel_state_integrity`. Both are included in `kernel_integrity`. The probe
stages a modified persistent counter and a response, executes the unknown SVC,
and must never resume after it. The host requires `6F00` without response data,
a successful unrelated APDU before reboot, and the original counter after
reselection and reboot. This scenario passed on Pico1/QEMU (102 checks) and
Pico2/OpenOCD (86 checks), including the architecture-dependent LOAD sequence.

Both ARM dispatchers pass the saved EXC_RETURN to a common rejection path.
Only an unprivileged Thread/PSP origin with a stacked Thread-mode xPSR and an
active isolated session is recoverable. An unknown privileged/kernel SVC
remains a fatal kernel error. An application violation notifies the existing
exit observer with `UnknownSyscall`, records an abnormal return and requests
the normal kernel-resume redirect. The observer retires authority, cancels
staged output and clears the gate; existing teardown and rollback apply.
The MPU configuration is unchanged. `kernel_invstate_integrity` exercises a
branch to code with the Thumb bit clear, checks the fault cause and `6F01`,
and applies the same output, liveness and rollback assertions. It passed on
Pico1/QEMU (104 checks, ARMv6-M HardFault) and Pico2/OpenOCD (88 checks,
INVSTATE). Stack-fault containment is implemented separately and exercised by
`kernel_stack_entry_integrity`.
Mainline MemManage, BusFault, UsageFault and escalated HardFault share one
fault classification policy. Recovery requires all of the following:

- the isolation phase identifies Rustlet execution and an isolated call is active;
- hardware EXC_RETURN identifies a basic Thread/PSP frame, with unprivileged CONTROL;
- the captured causes are synchronous instruction/access faults or supported
  stacking, unstacking and stack-limit faults;
- HFSR contains no vector-fetch or unrelated debug fault.

This includes UNDEFINSTR, INVSTATE, INVPC, NOCP, UNALIGNED and DIVBYZERO,
precise instruction/data bus errors, and PSP stack failures. Division by zero
trapping is enabled. Normal unaligned byte-buffer accesses retain their existing
behavior; instructions that architecturally require alignment still fault.
A standalone Rustlet BKPT debug event without an attached debugger has its own
strict HFSR/DFSR classification. Debugger interception is not a recovered exception.

Recovery abandons the application; it never retries the failed instruction or
unstack operation. The native HardFault vector preserves the saved kernel MSP.
Incomplete PSP frames, frames rejected during exception return and extended FP
frames are not read for diagnostics. A fresh MSP frame returns through the
existing abnormal-exit cleanup, authority retirement, output cancellation and
rollback path. ARMv6-M similarly requires an active unprivileged Thread/PSP
origin and never reads the unproven fault frame.

Kernel faults, including SVC execution on behalf of a Rustlet, remain fatal.
An active application alone is insufficient attribution. Imprecise bus errors,
unknown status bits, vector-fetch faults, cross-security-state returns and
nested Handler faults remain fatal. Lazy floating-point faults and extended frames are outside the current
basic-frame runtime contract and remain fatal; this is not floating-point
context-switch support. NMI and unexpected debug/PendSV exceptions have explicit
fatal vectors; Pico2 SecureFault is fatal in the current single-security-state
runtime. A future TrustZone split needs its own security-state recovery contract.

Validation is split into independent scenarios:

- `kernel_stack_entry_integrity` moves PSP below its limit or outside its mapping
  immediately before SVC. Pico2 reports STKOF and MSTKERR with HFSR clear.
- `kernel_cpu_exception_integrity` executes undefined, alignment, coprocessor
  and division probes. On Pico2, it also forces UsageFault escalation to
  HardFault, a failed PSP unstack and an inconsistent exception return (INVPC).
  The test-only integrity module supplies the return-corruption SVC; production
  images do not install it. The scenario checks the exact fault registers,
  `6F01`, output cancellation, another application's APDU without reboot, and
  durable rollback after reboot. It passed 118 checks on Pico1/QEMU and 141 on
  Pico2/OpenOCD. Pico1 reports its synthetic HardFault cause; unsupported
  Mainline instruction encodings do not prove a separate ARMv6-M fault class.
- `kernel_cpu_fatal_integrity` exercises privileged instruction faults, a real
  Pico2 bus error, bus-error unstacking (UNSTKERR) and an invalid return (INVPC).
  The latter two use a privileged PSP with no active Rustlet, proving that PSP
  alone does not authorize recovery. OpenOCD checks the exception, CFSR, HFSR
  and privilege before resuming to the fatal diagnostic. Pico1 requires a
  HardFault diagnostic and termination at BKPT, never a timeout as evidence.

The pure classifier tests reject kernel, nested, ambiguous and unsupported FP
contexts. They cover flags that cannot all be produced safely with the current
MPU mappings, and are not a substitute for hardware fault injection. Rustlet
IBUSERR/PRECISERR/UNSTKERR, lazy FP and imprecise bus errors are not claimed as
physically exercised by these scenarios.

The `kernel_output_integrity` scenario covers untrusted outgoing APDU lengths.
The void SET_OUTGOING_LENGTH ABI ignores values above 255, preserving the
previous phase, length and payload; it does not abort the application or
return an error status. A valid length implicitly starts output, and a repeated
SET_OUTGOING resets the staged length. The kernel unit test exercises the real
SVC with lengths 256..511 and the 16-bit, 32-bit and host-word maxima, before
output and after lengths 0, 2 and 255. The target scenario checks actual wire
responses for invalid lengths 256, 65535 and the target-word maximum and valid
lengths 0 and 255 in four output phases, followed by an unrelated application
APDU without reboot. It passed on Pico1/QEMU and Pico2/OpenOCD (165 checks
each).

The `kernel_apdu_order_integrity` scenario exercises incoming/output ordering
through raw SVCs and the runtime wrapper. Once output starts, an incoming request
returns zero without reading the transport or changing the prepared response.
The authoritative guard uses kernel-owned transport state, not writable shared
flags. Repeated input before output reuses the received payload; empty input
emits no procedure byte. Valid output lengths can still implicitly start output,
and repeated output declarations reset its length. The scenario checks these
transitions at empty, small and maximum payload lengths and sends an unrelated
application APDU after every case without reboot. Host tests also verify that
rejected input does not consume the next command header.

### Diagnostic and startup safety boundaries

The startup contracts here describe native ELF kernels. The legacy bootable-FAE
kernel path is no longer supported; Rustlet FAE loading remains supported and
is independent.

Diagnostics are opt-in kernel modules and remain part of the privileged TCB.
Their APDU logic does not gain permission to fabricate Rust references merely
because an image is intended for testing.

| Boundary | Necessary operation and obligation |
| --- | --- |
| Kernel watermark | Read MSP and access linker-owned stack words through raw volatile operations. Paint only below the current frame, scan only the previously initialized prefix, and reject inconsistent bounds. Never borrow live stack frames as a Rust slice. Atomic scalar counters need no `static mut`. |
| Rustlet watermark | The loader's unsafe observer contract supplies an initialized, exclusively owned, inactive stack before entry and after return, including faults. Observers finish before scrubbing. No Rust reference crosses execution. |
| Flash diagnostics | A short raw view reads a successfully reserved, mapped flash sector. Page and torn-erase scratch remain resident under checked `KernelCell` loans. Validate the complete sector before reading it; no IRQ or other core may run this diagnostic. |
| SRAM experiment | The opt-in RP2350 experiment owns its external scratch, SRAM power switch and cycle counter under one operation guard. Physical reads, MMIO, barriers and the aligned scratch reinterpretation remain unsafe. These experimental external ranges are not part of the production 64 KiB allocation. |
| Fault injection | A deliberate invalid load/store, undefined instruction or NX branch is expressed in assembly. Invalid or trapping accesses do not meet Rust volatile-pointer contracts. These tests intentionally terminate the application; they are not safe memory-access examples. |
| C runtime shims | `memcpy` and `memset` retain explicit unsafe C ABI contracts: valid byte ranges, exclusive writable destination and non-overlap for copying. Linker symbols name storage; taking a symbol address does not validate a later dereference. |
| Native ELF reset and relocation | Assembly establishes MSP, masks IRQs, installs VTOR and clears the reserved boot ABI before copying data and clearing BSS. Linker assertions enforce word-sized copy ranges, stack alignment and existing RAM/flash bounds. Rust starts only after those invariants hold. |
| Exception transitions | Assembly owns EXC_RETURN, CONTROL, PSP/MSP and the register-save protocol. Every call into Rust keeps MSP eight-byte aligned; a 12-byte redirect record occupies a 16-byte call frame. No mapping or permission change follows from the diagnostic cleanup. |

Pico1 fatal kernel exits execute `BKPT #0`, after an optional trace message.
The default Pico QEMU run terminates on this breakpoint when reached from
HardFault (observed as SIGABRT); this is a fatal stop, not a successful test
exit. A debugger can intercept the breakpoint. If execution is resumed, the
kernel remains in a halt loop. Successful test completion retains the explicit
emulator exit service. Recoverable Rustlet faults still return their status
word and do not take this kernel-fatal path. The Pico1 stack-guard regression
requires both its fault diagnostic and termination after the breakpoint.

Pico2 fatal faults retain the halt-loop policy. With traces enabled, the fatal
path reports the exception class, execution origin, EXC_RETURN and CONTROL;
the fatal handler adds the available fault registers and stacked PC/LR only
when the frame is usable. Native HardFault fallback reports register values
and stack addresses without reading the interrupted stack. Its semihosting
calls are compiled out with `trace=none`; traced Pico2 output checks for an
attached debugger before BKPT. OpenOCD must have semihosting enabled, as the
`--trace=jtag` runner does. Text fragments are sent directly without allocating
another buffer. Recoverable Rustlet faults use stored diagnostics without
semihosting calls in the recovery path. The Pico2 RAM-NX hardware test verifies the fault first, then
resumes the fatal handler and checks its diagnostic and halt message.

Fault reporting must not cause another memory fault while inspecting a failed
stack. Mainline profiles suppress stacked PC/LR on stacking, unstacking,
lazy-state or stack-limit errors. The ARMv6-M HardFault path cannot establish
frame completeness from CFSR and reports PC/LR as unavailable. Fatal native startup
fallbacks report SP addresses and fault registers without dereferencing the
interrupted stack: their emergency MSP reset can itself overwrite that frame.
A fatal kernel stack fault can still prevent the handler from running at all;
external debugger observation is required for that case.

The raw SVC frame contract is different: successful SVC exception entry supplies
an initialized basic frame, and dispatch runs with the application suspended.
The supported profiles do not use floating-point extended frames. Stack
watermarks are measurements for exercised paths, not proofs of a worst-case
bound, and `scripts/stack_dump.py` provides debugger frame estimates rather than
an alternative watermark.

### Execute-never phase transitions

Rustlet text is executable only while the processor is running the
unprivileged Rustlet thread. The isolation layer keeps one immutable MPU plan
per loaded Rustlet, then varies only the `XN` bit of its text regions:

- before entering the Rustlet thread, its text regions are restored to
  read-only executable mappings;
- on every Rustlet-originated SVC or recoverable MemManage entry, the
  trampoline reprograms those same regions as read-only execute-never before
  dispatching any Rust kernel code;
- a syscall that resumes the Rustlet restores execution immediately before
  exception return;
- `exit`, panic, fault recovery, and normal completion keep the text regions
  execute-never while control returns to the kernel;
- after the session ends, the last Rustlet text mapping remains explicitly
  read-only and execute-never rather than falling back to the privileged
  default map.

This transition consumes no additional MPU region. Text XN changes are invoked
directly by the exception trampolines before their Rust dispatchers and read a
compact bitmask of the active text-region numbers.

The active session owns a plan whose contents remain immutable until cleanup.
Publication writes that plan and the fault return value before setting the
scalar call-kind marker; retirement clears the marker. Only the owning core
publishes or retires a session. Interrupt observers may read it, while fault and
watchdog handlers request a redirect and defer retirement to resume cleanup.
These volatile accesses describe a single-core interrupt protocol, not a
multicore synchronization mechanism.

Restoring phase-dependent MPU mappings and cleaning up the session read one
region at a time from this owned plan. They do not borrow mutable static storage
or take a complete stack snapshot. Queries for activity, call kind and fault
status read only their respective scalar metadata. Initial MPU programming
borrows its caller's plan, avoiding another by-value copy.

The kernel also recycles the last MPU region slots for phase-dependent RAM
execute-never mappings. When the selected target exposes representable mutable
RAM windows, those slots are enabled as `Privileged RW + XN` while the kernel is
running. Immediately before entering unprivileged Rustlet code, the isolation
layer disables those kernel mappings and restores any overwritten Rustlet
text/RAM mappings if the active Rustlet plan uses them. This prevents kernel
control-flow bugs from branching into RAM data such as Rustlet stacks, Rustlet
heap/data blocks, registry state, APDU buffers, or other mutable kernel data
without permanently reducing the Rustlet MPU budget.

On ordinary strict-power-of-two targets such as `mps2-an385`, one recycled
region covers the complete RAM window. Pico splits its low mutable RAM into two
strict MPU windows, 32 KiB plus 16 KiB, while `.critical.kernel.fct` is placed
outside those windows in SRAM for XIP-performance and flash-safety reasons. The
`cargo run test kernel_ram_nx <board>` regression validates the positive case by
attempting to execute a RAM-resident instruction while the kernel is active; a
supported target must fault before that instruction returns.

MPU region 7 is deliberately not recycled in the same way. It remains the
kernel stack guard because exception and fault entry can return to privileged
code through MSP at any point during Rustlet execution.

The current vector tables do not install recoverable external IRQ or SysTick
handlers while a Rustlet runs. Any future interrupt path that returns to a
Rustlet must join this same XN/X transition protocol. On ARMv6-M targets such
as Pico, recoverable Rustlet MPU faults are routed through HardFault because
there is no separate MemManage exception; fatal HardFaults remain
bootstrap-owned reporting paths.

### Heap allocation

Heap allocation is handled by the buddy/pruning allocator in
`kernel/core/src/core/allocator.rs`. The same allocator implementation backs both
the kernel heap and each Rustlet heap, but the backing storage is different
for each case.

The allocator works with two separate regions:

- a heap region that stores user data;
- a metadata region that stores the buddy tree outside the managed heap.

Important invariants:

- allocator metadata is never stored inside the heap it manages;
- heap corruption may damage user data, but should not directly corrupt
  allocator bookkeeping;
- every allocation is rounded up to an integer number of 8-byte granules;
- every supported alignment must be a power-of-two multiple of 8;
- deallocation relies on the `Layout` passed back by Rust, so the
  allocator does not write per-allocation headers into the heap.

The `kernel_dealloc_integrity` scenario (also included in `kernel_integrity`)
validates hostile DEALLOC calls through the real Rustlet SVC boundary. Its
twelve cases cover an oversized range, an oversized block, misaligned and
interior addresses, an undersized block, null, address overflow, an invalid
Layout alignment, a repeated free before reuse, and frees of the entire gate
or either aligned 256-byte half. The gate cases use valid layouts, so rejection
must enforce heap ownership. They check both payload canaries and control words,
and ensure subsequent allocations cannot reuse the gate. Each case runs twice,
checks live contents and non-overlapping allocations, exercises subsequent
allocate/free operations, and requires an unrelated Rustlet APDU to succeed
without reboot.
The host test `untrusted_free_rejects_wrong_blocks_without_changing_metadata`
additionally checks that rejected frees leave the metadata unchanged.
DEALLOC returns no rejection status; the embedded assertions therefore check
its effects. These checks do not detect a stale pointer after the same block
has been legitimately reallocated, or prevent an application from freeing
its own live allocation with a matching layout.

The tree is virtual and may be larger than the physical heap. Nodes outside
the physical heap window are pruned and marked unavailable. This allows the
allocator to support non-power-of-two heap sizes and heap bases that are
only granule-aligned.

This matters for the kernel/Rustlet split:

- the kernel heap metadata is placed in the free RAM tail immediately
  before the kernel heap;
- each Rustlet heap bytes live in the Rustlet RAM allocation;
- each Rustlet allocator metadata block lives in kernel-owned
  selected-application state;
- the kernel resets and selects that allocator state before entering a
  Rustlet handler.

### Shared region and entry

The first MPU region maps exactly 512 bytes for the shared APDU and serialized
state buffers. It contains no instructions and is mapped RW, execute-never.

ARMv6-M and ARMv7-M/v8-M enter through a kernel `SVC 0` site. The exception
handler checks both the exception return mode (kernel Thread mode using MSP)
and the stacked PC against that exact call site before interpreting the
kernel-owned entry descriptor. It prepares the Rustlet's basic exception frame,
loads its static base, selects unprivileged Thread mode and returns through
`EXC_RETURN = 0xFFFFFFFD`. Execution starts directly at the FAE entry point.
An application-issued `SVC 0` cannot take this privileged path.

The kernel continuation remains on MSP for normal return, explicit exit,
watchdog termination and fault recovery. No entry trampoline is copied into
the exchange page, so all 256 payload bytes remain available without code/data
collision. The length field still limits each request to 255 bytes.

## Shared ABI

`rustlets/rustlet_runtime` defines the kernel/Rustlet ABI.

The current ABI is intentionally smaller than the earlier
`SelectionContext` / `ApduCommand` / `ApduResponse` model.

Today the important shared types are:

- `ABI_VERSION`;
- `RustletApduHeader`;
- `RustletCtx`;
- `ApduStatus`;
- `RustletHeapRegion`;
- `SelectedAppVtable`;
- `SelectedAppDescriptor`.

### `RustletCtx`

The current shared APDU contract is centered on one fixed-size
`RustletCtx`. Its binary layout is part of the kernel/Rustlet ABI and must not
be changed casually.

The shared page is exactly 512 bytes:

- bytes `0x000..0x100`: control/secondary buffer;
- bytes `0x100..0x200`: APDU payload buffer.

The control/secondary half contains:

- `abi_version`;
- five command/status bytes, interpreted as `CLA INS P1 P2 P3` on entry and
  `SW1 SW2 00 00 00` on return;
- flags;
- one short-APDU data-length byte;
- one serialized-state length byte;
- 244 bytes of serialized-state storage.

The APDU payload half is physically 256 bytes long, but the useful payload
limit is 255 bytes in this ABI version because the length field is one byte.
Do not treat the physical 256-byte reservation as an extended-APDU mechanism.

Its semantics are:

- before `set_outgoing()`, the payload is the incoming command data;
- after `set_outgoing()`, the same payload buffer becomes the outgoing
  response area;
- at the end of execution, the Rustlet writes its status word into
  `SW1/SW2`.

The shared payload is modeled as one directional `RustletCtx` buffer rather
than separate `ApduCommand` and `ApduResponse` structures.

The control/secondary half also has a kernel-side implementation role. Before
entering a Rustlet, secure-channel or dispatch code may use that half as an
explicit scratch area for bounded APDU-sized transformations. The invariant is
strict: every Rustlet entry path must reset and reinitialize the control half
before user code observes it. This prevents decrypted data, MAC material,
serialized state, or stale status bytes from leaking across calls.

### Zero-copy ownership rules

Zero-copy in this kernel is primarily a stack- and RAM-usage rule. It does not
mean that every type owns a different payload array, and it does not forbid a
copy when an algorithm genuinely requires stable, non-overlapping input and
output.

The firmware APDU path has one physical 256-byte payload store. It is the APDU
half of the gate-region `RustletCtx`:

- `TransportApdu` owns the T=0 session metadata, but its payload pointer refers
  to that shared store;
- `ApduCommand`, `Apdu`, and `RunningSEApdu` are temporary views over the same
  command and must not retain payload slices after the current operation;
- the active Rustlet receives that same store as `RustletCtx::data`;
- the incoming-to-outgoing transition changes the logical meaning and length
  of the bytes; it does not allocate a response buffer.

The bridge helpers are alias-aware. Staging an already received command only
publishes its header and length when the source is the shared APDU store.
Likewise, returning a Rustlet response updates the transport's outgoing state
without copying when source and destination are the same store.

A T=0 response deferred through `61xx` remains in that store until the final
`GET RESPONSE` chunk is sent; `PendingResponse` contains only offset, length,
and completion status. Secure-channel establishment follows the same rule for
a Rustlet-backed Security Domain: SDDISPATCH publishes its response directly
in the shared payload and returns only its length. Native Security Domains use
the explicit auxiliary scratch and copy once into the payload because they do
not execute through the shared Rustlet ABI.

The first 256-byte half of `RustletCtx` has two mutually exclusive roles:

- while kernel protocol code is running, it may be borrowed as bounded
  secondary scratch;
- immediately before Rustlet entry, it contains only the initialized ABI
  control fields and the selected instance's serialized state.

No Rustlet entry may occur while kernel scratch data remains in that half.
`SharedRustletCtx::stage_state_from_registry()` is the mandatory ownership
transition: it clears the complete control half, restores `ABI_VERSION`, then
copies only the selected object's current serialized state. The APDU payload
length is published only after the payload is valid. Unused APDU-tail bytes are
zeroed before entry. Normal T=0 completion scrubs the payload store, while
panic, explicit exit, and recovered fault paths scrub the complete shared page.

### Secondary-buffer ownership phases

The secondary half has exactly one logical owner at a time. Its bytes have no
stable meaning outside the current phase:

1. **Kernel transform scratch.** Before a native Security Domain or ordinary
   Rustlet is entered, secure-messaging code may use all 256 bytes as temporary
   plaintext, ciphertext, authenticated Amendment D framing, or another bounded
   APDU transform result. SCP03 authenticates the command header and protected
   APDU as separate slices, so it does not build a second contiguous CMAC input
   there. The final CMAC value uses the dedicated 16-byte MAC scratch.
2. **ABI input.** `stage_state_from_registry()` ends transform ownership,
   clears all 256 bytes, publishes the ABI version, and copies the serialized
   state read from the registry. Command staging then publishes
   `CLA INS P1 P2 P3`, flags, and the incoming APDU length. From this point
   until return, kernel protocol code must not borrow the half as scratch.
3. **Rustlet execution.** The Rustlet reads its deserialization input through
   `state_bytes()`. It may replace those bytes with a new serialized state and
   publish the new state length. The same rule applies to an ordinary Rustlet
   and to a Rustlet Security Domain entered through SDDISPATCH.
4. **Returned state pending publication.** After a normal return, the control
   half contains `SW1/SW2`, response flags and the newly serialized state.
   `save_selected_instance_state()` or
   `save_selected_security_domain_state()` copies the declared state bytes into
   the polymorphic registry, then synchronously publishes the new persistent
   registry image. The control half is the source of that transaction, not the
   Flash page-programming buffer, and must not be reused until the copy
   completes.
5. **Released and scrubbed.** Once returned state has been copied and the
   persistent registry has been published, the serialized-state capacity is
   overwritten. Normal T=0 completion overwrites the shared APDU payload after
   its last response byte, or after the final `GET RESPONSE` chunk for a
   deferred response. For an ordinary Rustlet, the runtime has also destroyed
   the in-memory instance and the kernel overwrites its complete heap; its stack
   is overwritten after the stack observer runs. Abrupt return paths clear the
   complete shared page, so no state or cryptographic intermediate is accepted
   from a failed Rustlet call.

For a Rustlet Security Domain, “serialized state” excludes the active SCP
session. Derived keys, expected cryptograms, receipts, MAC chains, counters,
and staged handshake bytes live in a `#[serde(skip)]` field of the loaded
Rustlet value. They remain available across consecutive SDDISPATCH calls while
that value is loaded, but they are absent from both the secondary-buffer state
view and the persistent registry. `reset_secure_channel()` explicitly
overwrites that field; unloading is not used as a substitute for zeroization.
The active Rustlet Security Domain remains loaded in its dedicated firmware
slot while an ordinary selected Rustlet occupies the application slot, so
`unwrap`, application dispatch, and `wrap` share one live volatile session
without registry round-trips.

Rustlet-backed secure-channel operations need one additional constraint:
SDDISPATCH itself takes ownership of both halves of `RustletCtx`. A slice into
either half cannot survive such a call. Data that must remain stable across
SDDISPATCH therefore lives in the explicitly named static proxy/auxiliary
scratch, never in a stack array and never in the secondary half. SCP11 also
uses the auxiliary scratch when its authenticated input must be contiguous.

### Scoped access and ownership phases

The firmware represents the preceding ownership phases with the Rust typestate
pattern. Phase markers are zero-sized `PhantomData` parameters and therefore
have no runtime representation:

- secure messaging consumes
  `SecondaryBuffer<SecondaryAvailable>` to obtain
  `SecondaryBuffer<SecondaryCryptoScratch>`, then releases it only after the
  transform result has been consumed;
- a Rustlet handler call consumes
  `SharedRustletCall<AbiInput>`, stages a command to produce
  `SharedRustletCall<AbiReady>`, and obtains
  `SharedRustletCall<ReturnedState>` only after `invoke_app()` returns.

The transaction types are not `Copy` or `Clone`, and each transition consumes
the previous value. A checked access token supplements these ordering rules:
the payload and control half can be acquired separately, while an ABI call
requires both. Acquiring an occupied region is a kernel programming error and
is rejected before constructing a reference. The access map occupies one byte;
it does not contain APDU data. Firmware access belongs to the kernel owner
core, and interrupt handlers must not acquire protocol buffers.

`TransportApdu` retains its payload reservation while it can expose slices.
Releasing it requires an exclusive borrow of the transport object, so earlier
slices cannot survive that transition. `SharedRustletCtx` is a non-copyable
address descriptor constructed at the unsafe loader boundary. Its methods
acquire the whole page; returned byte views retain their reservation and bound
their slices to the view's lifetime. They no longer return `'static` slices.
The proxy, auxiliary, MAC and management scratch buffers remain resident and
use guarded access; certificate-chain storage retains its contents between
commands under the same access discipline.

Rustlet entry consumes the kernel page reservation and delegates access to the
ABI without retaining a kernel reference to its bytes. Synchronous APDU SVCs
temporarily borrow this delegated page, and normal return restores kernel
access. The invocation context is installed only within a closure retaining
the live transport and image. Abrupt exit retires invocation authority, drains
transport I/O and scrubs the shared page under a temporary ABI reservation.
The unsafe ABI boundary still requires a suspended Rustlet, valid memory and
the runtime's lending contract; suspension alone is not an aliasing proof.

SDDISPATCH requests whose input already occupies the payload use an encoding
plan containing offsets and small header fields. Parsing borrows end before
the encoder receives its sole mutable payload view. Segments move directly to
their final positions with `copy_within`, in an order checked before mutation.
Cyclic field permutations use a 32-byte position bitmap and one temporary byte;
they do not allocate a second data buffer. External
input uses ordinary disjoint slice copies. GET DATA responses produced by a
Rustlet SD are published by length, without copying the shared payload onto
itself. No extra payload buffer or heap allocation is introduced.

Long-lived secure-channel session material belongs to the selected Security
Domain's session state. Temporary secure-messaging values belong to explicit,
APDU-bounded kernel scratch storage whose lifetime ends before another
transformation or Rustlet-SD dispatch can reuse the shared page. In particular:

- do not place APDU-sized arrays in a kernel stack frame;
- do not retain a slice into the shared page across a call that can dispatch a
  Rustlet Security Domain;
- if input and output overlap unsafely, use one documented scratch region and
  copy back into the shared APDU store as soon as the transformation completes;
- preserve a management payload only when an authorization hook can republish
  the shared page;
- keep `unsafe` limited to constructing views over the statically reserved gate
  region or single-thread-owned scratch; protocol code should consume ordinary
  bounded slices.

Copies are therefore expected only at explicit ownership boundaries: T=0
pending responses, transforms that cannot safely operate in place, payloads
parked across Rustlet-SD calls, and persistence/registry storage. A new copy on
the hot APDU path should identify which of these lifetimes requires it and must
not be implemented as an APDU-sized local stack array.

### Descriptor boundary

The selected application is still represented through:

- a `repr(C)` descriptor;
- a `repr(C)` vtable;
- explicit kernel entry and return routines.

It is intentionally **not** represented as a native Rust trait object
across the kernel/application boundary.

That would be incorrect for this design because kernel and FAE are
separate binaries with separate relocation contexts and distinct runtime
state requirements.

Preserve this rule while evolving the ABI.

The loader reads descriptor and vtable storage as integer ABI words, never as
Rust function-pointer values or static references into writable application RAM.
Before each read it checks alignment and containment in the owned data allocation.
Heap geometry must be aligned, bounded and disjoint from the known descriptor,
vtable and state prefix. Handler words must be Thumb addresses within the actual
FAE image before its public footer, not merely somewhere in the rounded MPU text
region. Any such address is accepted; there is no symbol-name allowlist or
producer-specific function table. Compile-time layout assertions keep this
decoder tied to the public C ABI.
These checks do not prove that an address denotes a well-behaved function or that
opaque application state satisfies a Rust type: untrusted execution remains
confined by the existing isolation boundary.

`LoadedFae` keeps its geometry and checked descriptor private. Safe dispatch
selects an install, process or SD handler from that image's kernel snapshot; it
cannot substitute an arbitrary PC or state pointer. Startup may be attempted
only once per loaded allocation, including when it fails. Later application writes to
its original descriptor or vtables cannot change that snapshot. The snapshot
contains only addresses and lengths, with no duplicate APDU or serialized state.
Allocation owners erase and free the image RAM and allocator metadata on normal
retirement as well as failed activation paths. Invocation scopes keep those owners
alive until the allocator binding and SVC context are retired.

On the Rustlet side, unsafe startup carries the one-shot relocated-image and
owner-core contract. Handler entry is the explicit raw-pointer boundary; it
borrows only the runtime state and shared context supplied by the ABI. Panic and
allocation failure send their status through the termination SVC without
reborrowing a globally published context. Failed state serialization also takes
terminal exit: it cannot publish a partial snapshot as a normal handler return or
leave a live instance pointing into a heap that the kernel will scrub. A faulted
SD is retired whether it was entered through SDDISPATCH or ordinary process_apdu;
its former session cannot authorize a subsequent call.

Both firmware crate roots and the Rustlet runtime deny implicit unsafe operations
inside unsafe functions. The descriptor validator, registry model, GP status
mapping, persistence codec and syscall ABI definitions forbid unsafe code. These
lints constrain future edits; they do not certify the remaining ABI, allocation
or hardware contracts.


## Selected-Application Dispatch

Once a Rustlet is selected, later APDUs are routed through
`kernel/firmware/src/selected_app.rs`.

The current dispatch rule is:

- `INS = E6` routes to `install`;
- every other command routes to `process_apdu`.

Before the call, the kernel stages the logical APDU into the shared
`RustletCtx`. If the command arrived through secure messaging, the
`SecureChannelLayer` has already verified and unwrapped it; selected-app code
does not parse the external payload-and-MAC framing itself.

After the call, the kernel:

- reads `SW1/SW2` from the shared buffer;
- publishes the outgoing length in the transport-owned APDU session; the
  alias-aware bridge copies bytes only if a non-shared backing is used;
- lets `SecureChannelLayer` protect the response data, append R-MAC when
  required, and authenticate the actual status word if the command was protected;
- resumes the normal `T=0` completion path.

This is an ownership boundary, not normally a payload-copy boundary:

- the transport session and T=0 state remain kernel-owned;
- the firmware transport payload and `RustletCtx::data` normally alias the
  same gate-region storage;
- host-based unit tests may use independent backing storage, so bridge helpers
  retain an alias-aware copy fallback.

The current object composition around one command is therefore:

1. `ApduLayer` yields one `ApduCommand`;
2. the dispatcher derives one kernel-side `Apdu` view from that command;
3. the selected-app bridge may derive one `RunningSEApdu` view while a
   Rustlet call is active;
4. Rustlet code sees the shared `RustletCtx` through the common
   `SEApdu` trait;
5. command completion returns through one `ApduCompletion`.

The kernel has three distinct APDU-facing object families:

- transport-owned session state (`TransportApdu`);
- APDU-layer command/completion objects (`ApduCommand`,
  `ApduCompletion`);
- card-side command-processing views (`Apdu`, `RunningSEApdu`,
  `RustletCtx` through `SEApdu`).

Keep these roles distinct when extending the code.

## Exit and Fault Handling

Application exits are centralized in `oxi_core::core::isolation`.

The main exit classes are:

- normal handler return through the runtime `handler_return` syscall;
- explicit `exit(sw1, sw2)`;
- `panic`;
- attributable CPU isolation faults, including supported stack/return failures.

The current flow is:

1. the target backend captures the machine event (`SVC` or CPU fault);
2. `core::isolation` computes the kernel-visible return semantics;
3. an optional kernel-side observer is notified;
4. the target backend resumes the kernel through the common resume path.

Normal handler return, explicit exit, and panic all use the single
`RETURN_TO_KERNEL` runtime syscall. Its return-kind argument distinguishes a
normal completion from an early exit; there is no separate exit syscall or
second kernel handler.

`kernel/firmware/src/selected_app.rs` observes those exit events and:

- drain and discard an unread T=0 incoming phase after advertising the
  procedure byte;
- discard a staged outgoing response without sending bytes; only normal
  completion emits an outgoing procedure byte, so abort must not inject
  unframed zero bytes;
- clear the complete shared `RustletCtx` page after explicit exit, panic, or
  recoverable fault;
- log memory-fault diagnostics;
- keep APDU completion policy in the kernel.

These rules are deliberately independent of Rustlet behavior. An interrupted
Rustlet cannot leave unread transport bytes or command, response, status, and
serialized-state bytes in the shared page for the next invocation. Normal
handler returns keep the page only until the kernel has consumed the response
and persisted the instance state.

Fatal CPU faults still stop the system instead of borrowing a Rustlet recovery
context.

### CPU fault recovery and failed exception returns

Recovery means aborting an attributable Rustlet invocation, never repairing its
CPU state or retrying the failed instruction. Kernel faults remain fatal, even
when a Rustlet call is active or PSP happens to be selected. The common Mainline
policy in `kernel/core/src/core/target/fault_policy.rs` requires the recorded
Rustlet execution phase, an active isolated call, unprivileged `CONTROL`, a basic
Thread/PSP `EXC_RETURN` (`0xFFFFFFFD`) and only supported fault-status bits.
Ambiguous, nested, extended floating-point and cross-security-state contexts
are rejected. These checks do not require reading the application stack.

Two Pico2 cases need particular care:

- **MUNSTKERR** is a MemManage failure while restoring registers from the
  exception frame. The frame being restored is not a trustworthy diagnostic
  source. Dereferencing PSP to print a stacked PC can fault again; returning
  through that PSP can repeat the failed unstack.
- **INVPC** is a UsageFault raised when exception-return integrity checks fail.
  It is not simply an ordinary invalid code address: the requested return and
  saved execution state can be inconsistent. The runtime must not assume that
  the rejected frame describes a valid resumable Thread context.

These events occur at the handler-to-Thread boundary. The instruction performing
exception return belongs to a handler, but that alone does not establish which
execution context is responsible. Conversely, PSP or an active Rustlet alone
cannot justify recovery. Only the combined attribution above permits abandoning
an application; an invalid `EXC_RETURN` outside the supported value remains fatal.
For architectural definitions, see the fault and exception-return sections of
the [Armv8-M Architecture Reference Manual](https://documentation-service.arm.com/static/5f8efff7f86e16515cdbe5f9).

The Mainline implementation follows this order:

1. Preserve the hardware exception-return value and the kernel MSP context;
   capture CFSR/HFSR and any valid fault-address registers.
2. Suppress stacked PC/LR reads for stacking, unstacking, stack-limit, lazy-state
   and INVPC errors. `fault_frame_registers` applies this rule before any frame
   dereference. Classify the captured origin and causes independently of PSP
   contents; unsupported cases enter the fatal path.
3. For an attributable Rustlet fault, clear the captured sticky status bits with
   write-one-to-clear writes. Record an isolation fault and invoke the existing
   exit observer, which retires authority and cancels staged output/state.
4. Request the existing kernel-resume redirect. `oxi_core_resume_with_redirect`
   selects privileged execution, builds a fresh basic frame on MSP and returns
   through `0xFFFFFFF9` to the kernel continuation. It never unpacks or patches
   the failed application frame. Normal abnormal-exit teardown and rollback
   then complete, and the APDU reports `6F01`.

`kernel_cpu_exception_integrity` physically exercises MUNSTKERR and INVPC on
Pico2/OpenOCD using a test-only return-corruption SVC. It checks fault registers,
`6F01`, discarded output, another application's APDU without reboot, and durable
rollback after reboot. `kernel_cpu_fatal_integrity` checks privileged PSP
UNSTKERR (the BusFault counterpart) and INVPC remain fatal. These are distinct
positive and negative controls, not evidence that every CPU fault combination
has been injected. Rustlet IBUSERR/PRECISERR/UNSTKERR and unsupported FP cases
retain the coverage limitations documented in the integrity campaign above.

This recovery assumes the kernel stack and saved continuation remain usable.
A damaged kernel stack can prevent fault handling itself; the current fatal
policy is a halt on Pico2 and a terminal breakpoint on Pico1, not a guaranteed
reboot or recovery from arbitrary kernel corruption.

## Syscall and Allocator Integration

The Rustlet-facing syscall numbers live in
`rustlets/rustlet_runtime::syscall_abi`.

On the kernel side:

- `oxi_core::core::syscall` owns the registration table and builtin
  bindings;
- the selected CPU profile owns the `SVC` trap and machine dispatch, sharing
  the Mainline implementation between ARMv7-M and ARMv8-M;
- `core::isolation` installs the runtime hooks needed for `handler_return`
  and mediated Rustlet exit handling.

The current builtin syscall set includes:

- enter application mode;
- Rustlet handler return / explicit exit;
- heap allocate;
- heap deallocate.

APDU-specific syscalls are registered by `kernel/firmware/src/selected_app.rs`
from the same shared ABI constants.

The allocator state used by a Rustlet is selected by the kernel before
entering that Rustlet handler.

Important current invariant:

- Rustlet allocator metadata is kernel-owned selected-app state, while the
  Rustlet heap bytes remain inside the Rustlet RAM allocation.

### Validating untrusted SVC arguments

Validation follows the argument contract rather than interpreting every register
as a pointer. The complete production binding set is covered as follows:

| SVC family | Validation boundary |
| --- | --- |
| Enter application (0) | Only the privileged entry site supplies a kernel-owned entry descriptor; a Rustlet cannot use it to enter privileged execution. |
| Return (1) | Return kind must match the active call phase. A bootstrap descriptor remains an integer until the loader validates it with `fae_descriptor`. |
| Allocate / deallocate (3/4) | Checked `Layout` and active Rustlet allocator; deallocation validates allocation ownership and size using kernel-owned metadata. |
| APDU phase / length (6..8) | Kernel-owned transport phase, shared-page lease and bounded output length; no caller-supplied buffer pointer. |
| Cipher, random, MAC, SD key, EC keypair, ECDH, HKDF, X9.63 (9..16) | `syscall_memory::Memory::request<T>` validates and snapshots a complete aligned parameter record. Scoped buffer methods validate each payload and its access mode. SD key access additionally requires invocation authority. |

`Params` restricts snapshots to ABI records whose initialized field bit patterns
are valid Rust values. Reserved fields in SD-key, EC-keypair and ECDH records must
be zero; the common request boundary rejects nonzero values with
`PermissionDenied` before service execution. Algorithms, lengths and authority
remain service-specific checks. Only the small parameter record is copied;
payloads stay in their original storage and no resident validation buffer is
introduced.

`read` and `write` enforce readable and writable windows. `write_pair`,
`read_pair_write` and `buffers` validate simultaneous ranges and reject forbidden
aliases before constructing Rust references. Empty buffers are canonical empty
slices without dereferencing the supplied address. A nonempty range must fit in
one backing window with checked arithmetic and a Rust-representable length.

Aliasing policy deliberately differs by operation. Cipher consumes key/IV before
staging input with overlap-safe copying; identical input/output addresses avoid
that copy. MAC publishes its tag only after consuming input, so its output may
overlap input. ECDH and KDF outputs must be disjoint from live input borrows, and
the two keypair outputs must be disjoint. Validation failures leave outputs
unchanged; this does not promise unchanged output after an algorithm has started
and later fails, for example on invalid decryption padding.

`kernel_abi_integrity` is the F5 target campaign. It exercises malformed record
addresses for all eight services, invalid inner buffers, read-only destinations,
forbidden aliases, reserved fields and legal empty/in-place operations. Every
case checks the result and a subsequent unrelated APDU without reboot. The SD
key calls made by its ordinary Rustlet must fail the authority gate; separate
host tests reach the same record boundary with actual SD authority established.
Host tests also shorten every record type through every truncated size. The
on-target descriptor diagnostic applies synthetic words to the production
validator, including SD vtables and code boundaries; it is not a campaign of
loading independently corrupted FAE files. Existing loading and crypto scenarios
provide positive integration controls. The F5 campaign passes on Pico1/QEMU
and Pico2/OpenOCD (78 SVC cases each, plus descriptor and management checks).

## Kernel-Local Application Path

`KernelAppModule` is the common abstraction for optional privileged extensions
that are statically linked into one kernel image. It is intentionally separate
from the Rustlet ABI: modules run in privileged mode, belong to the TCB, and
are selected only when a new kernel image is built.

The trait currently requires one boot-phase entry point:

```rust
pub(crate) trait KernelAppModule {
    fn initialize();
}
```

`initialize()` runs after core initialization and before the main APDU loop.
It is not a reset handler. Event integration is explicit and typed rather than
represented by optional trait methods. The generated image contains distinct
slices for:

- module initializers;
- APDU filters;
- post-APDU observers;
- pre- and post-Rustlet hooks;
- clear-command secure-session preservation predicates.

Keeping a slice per hook means a module that does not implement an event adds
no default call to that event path. It also keeps filter contracts separate
from observer contracts. APDU filters expose a read-only recognition function
and a processing function; recognition order is exactly the module order in
the TOML.

Pre- and post-Rustlet hooks have unsafe call contracts: an `AppMemoryWindow`
contains bounds, not proof that the stack is inactive and exclusively owned.
The loader supplies that proof at the call site. Ordinary APDU and initializer
hooks do not inherit permission to access raw stack memory.

For example:

```toml
[kernel-image]
mode = "kernel-only"
kernel-app-modules = ["ping", "t0-test"]
```

maps `ping` directly to
`kernel/firmware/src/kernel_main_app/ping.rs` and `t0-test` to
`kernel/firmware/src/kernel_main_app/t0_test.rs` through
`kernel_app_modules_registry.inc.rs`. The build script rejects any name absent
from that registry and generates slices in the declared order.

To add a module:

1. create its source file under `kernel/firmware/src/kernel_main_app/`;
2. implement `KernelAppModule` explicitly and define only the hook functions
   it actually needs;
3. add one name/module/path/hook declaration to
   `kernel_app_modules_registry.inc.rs`;
4. select the name in the relevant image manifests.

Neither `xtask`, the central dispatcher, nor a list of per-module `cfg` names
needs another edit. The current registry includes `ping`, `t0-test`, `timer-test`,
`crypto-self-test`, `flash-probe`, `registry-test`, `kernel-stack-monitor`, and
`rustlet-stack-monitor`, plus the opt-in `sram-fingerprint` experiment.

## Current Limitations

Several limits are still intentional at this stage:

- only one selected Rustlet context is modeled at a time;
- the kernel-managed object registry is still fixed-capacity in RAM, even when
  it is recovered from and published back to persistent flash;
- the transport loop still owns deferred response and `GET RESPONSE`;
- the ABI remains fixed-size and buffer-oriented.

## Practical Rules for Kernel Work

When extending this area, keep the following rules in mind.

- Do not move `SELECT` ownership out of the kernel.
- Do not move `GET RESPONSE` ownership out of the transport loop.
- Do not replace the ABI boundary with a native Rust trait object.
- Do not rewrite the XiPFS startup path just to simplify the current
  Rustlet activation model.
- Treat the kernel/Rustlet boundary as a real ABI boundary: version it,
  validate it, and keep it explicit.
- Keep the transport hot path in `kernel/firmware/src/main.rs` short and free
  of unrelated work.
- Keep byte I/O concerns in `TransportLayer`, not in protocol wrappers.
- Keep `T=0` completion rules in `T0ApduManager`, not in the dispatcher.
- Add future secure-messaging or tracing features as `ApduLayer`
  wrappers, not as ad-hoc branches inside `main.rs`.
- Keep SCP03 and SCP11 profile differences behind `SecurityDomainSecureChannel`
  and the shared `SecureChannelLayer`; do not add one APDU wrapper per SCP
  profile unless the APDU boundary itself genuinely changes.
- Do not leak `TransportApdu` back across the `ApduLayer` boundary.
- Do not stage protected or clear APDU payload mirrors on the kernel stack;
  use the transport APDU buffer and explicit bounded scratch regions.
- Keep each `KernelAppModule` local to one source file and declare only its
  real hooks in the central registry.
- Treat TOML module order as executable priority, especially for filters.
- Do not add dynamic registration or mutable hook tables to this path.
- Treat the gate region as a security-sensitive object, even though its
  current protection is still a draft compromise.

## Work Tracking

Keep open work in [`TODO.md`](TODO.md). Do not add local TODO lists to this
guide; it should describe the current architecture, invariants, and supported
workflows.

### Pico2 RAM envelope and SRAM experiment

OxideSE is globally limited to 64 KiB of RAM on Pico2, including stacks,
globals, allocator and RAM-executed code. The last 16 KiB of this envelope
is reserved for executable kernel routines; the mutable region ends at
0x2000C000. Remaining physical SRAM is reserved for a future host OS.
The opt-in [SRAM repeatability experiment](sram-fingerprint-experiment.md)
reads an explicitly selected bank outside this envelope without extending
Rustlet MPU permissions.

## Scoped registry and Security Domain access

Resident registry, selected-instance and persistence objects are owned by
`KernelCell`. Its read guards permit nested reads; its write guards exclude all
other loans. Returned object and byte views retain their guard, so their Rust
references cannot outlive the reservation. Conflicting acquisition fails before
a reference is constructed. The storage remains in place; guards carry only a
pointer and a reservation. Construction is an explicit unsafe boundary: firmware
access must stay on the privileged owner core and out of interrupt handlers.
Host acquisition uses atomic compare/exchange; non-Send values still require
their owning thread. These checks do not establish cross-core firmware support.

Operations release registry and selection loans before replacement, rollback
or publication can revisit those objects. The registry state copied into a
Rustlet's shared page is borrowed inside a preparation callback which finishes
before entry, allowing that Rustlet's synchronous services to mutate the staged
registry. The key-loading SVC uses the captured invocation identity rather than
reborrowing the running instance. Persistence scratch regions are borrowed
separately, only while encoding or programming their contents. Snapshot
publication reads the resident reference table entry by entry instead of copying
the complete table to the kernel stack. DELETE retains only object identifiers,
not a copied object payload.

The null authority and Rustlet proxy are stateless operation-local values. The
native cryptographic engine remains resident behind an exclusive guard. Temporary
management authority uses a scope which restores its enclosing authority on
normal return, error and host unwinding. Native engine reentry is rejected.
Session retirement revokes the binding immediately; if an operation still owns
the native engine, that guard scrubs its secrets before releasing the loan.
Changing administrative instance also unloads resident SD heaps without invoking
a hook on the retired identity. Subsequent activation restores administrative
state from the registry and requires a fresh secure channel.

Nested registry operations retain savepoints, not long-lived mutable registry
references. Their guards abandon staged changes on unwinding; an operation that
opened its own transaction also closes it on that path. Rustlet faults return
through the existing isolation/abort protocol, rather than relying on Rust
unwinding in firmware. None of these scoped-access rules changes flash atomicity,
MPU permissions, or the normal-rejection qualification issue described below.

## Registry failure propagation

Registry mutations return `RegistryResult` with separate causes for missing
references, authority denial, invalid state/data, exhausted capacity, an
undersized output buffer, and persistent-memory failure. Allocation failure is
not inferred from a rejected mutation: the slot allocator and flash-span
allocator report capacity explicitly. Flash erase/program failures and invalid
persistent records retain the persistence diagnosis through BOSS publication.

The GP boundary maps these causes using the current command's error table;
Appendix D of the manual lists the implemented statuses and required overlaps.
Missing DATA objects use `6A88`, including after deletion. Privilege and subtree
refusals use `6982`; lifecycle and dependency constraints retain `6985`.
Rustlet Security Domain proxies preserve explicit SW values, and the secure
channel layer normalizes GP execution/memory failures on its early-return paths
as well as the central dispatcher. Response protection uses the resulting SW.

`RegistryApduLayer` opens the RAM transaction after command reception, before
secure-channel establishment/unwrap, and finalizes it after response wrapping
but before any response bytes or status are emitted. Creation, replacement,
deletion, key inheritance and serialized Rustlet state update the same staged
registry. They do not publish a BOSS individually. A dirty transaction attempts
one publication even when a Rustlet has no changed state to serialize; an
identical persistent snapshot does not produce another BOSS.

The registry journals the previous contents of each touched slot at an operation
savepoint. New slots need no object backup. Existing objects use fallible heap
storage allocated before mutation; secret-bearing buffers are separately
allocated and scrubbed on commit as well as rollback. This avoids a second
fixed-capacity registry in RAM. Compound services use the same savepoint
mechanism, including native SD installation together with inherited SCP03 keys.
Capacity failure restores the whole operation. Final publication failure
restores the APDU's old RAM slots and retains the previous durable BOSS;
resident Rustlet heaps and secure-channel session bindings are retired.
Selection may need to be re-established after an abandoned deletion or a
publication failure; runtime handles must never refer to reused slots.

The dispatcher explicitly abandons a rejected GP management operation's staged
changes. Secure-channel establishment, unwrap and wrap are outside that operation
savepoint, so an error SW does not globally roll back protocol evolution. An
ordinary Rustlet's normally returned error SW likewise retains its serialized
state; abnormal return or failed state saving abandons its call's changes.
If final publication fails after response wrapping, the prepared response is
discarded, the session is retired and an unprotected persistence-error status
is returned. The peer must establish a new secure channel.

An abnormal SD hook return marks the complete APDU for abandonment, unloads
its resident heap and retires the secure-channel binding without calling the
faulted SD again. The response discards partial data and preserves the fault
status, without secure-channel protection. The old authenticated session is
rejected; a newly selected SD must establish a fresh channel. An ordinary
error SW does not trigger this retirement. Any response-protection failure,
including a crash inside the wrap hook, securely clears the APDU payload and
resets its output metadata before returning the error status alone.
For any SD hook crash, finalization abandons the entire
APDU transaction, including an application's already serialized state, without
publishing the BOSS. Resident participants are unloaded so they cannot restore
the discarded state on a subsequent command. This is an explicit SD-crash
abort, not a rule inferred from an error SW.

**Open qualification issue:** registry rollback alone does not restore the
Rust object of a resident Rustlet SD after a normally returned management
rejection. Its abandoned persistent counter can reappear on a later call.
Restoring persistent fields while preserving legitimate volatile session
progress remains a separate task. The private
`config_rustlet_sd_transaction_test.toml` campaign keeps this failing check,
then independently exercises crash retirement under SCP03-03 and SCP03-33,
publication failure after response wrapping, and reboot recovery.
Pico2 OpenOCD validation on 2026-09-22 passed both crash cases (32 checks),
publication/reboot recovery (14 checks), and the ordinary Rustlet SD SCP03
regression (44 checks). Late response-hook crash tests passed 25 additional checks: no response data,
immediate reboot before recovery APDUs, live rollback, old-session rejection,
and subsequent successful persistence. The immediate-reboot test reproduced
an application-state commit before the late-abort fix and passes with it.
The four SD/application crash combinations are checked through persistent
counters after immediate reboot (30 further checks for no crash, application
crash alone, and both crashes; SD-only crash is covered above). Application
crash alone retains the SD's unwrap/wrap progress. An SD crash retains neither
participant's changes from the failing APDU. A successful local savepoint
cannot revoke the global abort latch. The host kernel suite passed 157 tests. The complete
fault campaign still reports failure for the normal-rejection issue above.
The Pico2 devkit build has 92472 bytes of `text`, 14904 of `data` and 4376
of `bss`: +872 bytes of flash content and +4 bytes of static RAM versus the
2026-09-21 build (91600/14904/4372); RAM-resident code remains 40 bytes.

Pending `INSTALL [for load]` / `LOAD` packages remain unreachable until the
final block validates size, hash and CRC. Publication of other APDU participants
protects the reserved LOAD span and temporarily preserves its partial page.
Abandoning a load therefore cannot make its package visible. A failed final
APDU publication also cancels any pending LOAD context. Flash payloads
referenced by the staged view or an undo record are protected against recycling;
a full protection table conservatively protects additional space rather than
omitting a live range.

`PUT KEY` validates all entries before mutation, including key identifiers,
lengths and SCP11 scalar/point validity, then uses the common operation
savepoint. This remains atomicity within one APDU; it does not introduce a
protocol for staging keys across several PUT KEY APDUs. KCV verification and
DEK wrapping remain separate profile work.

Host tests cover SD creation failing midway through inherited-key allocation,
final publication failure of the whole SD/key graph, restoration of replaced,
inserted and deleted slots, preservation of protocol changes outside an
abandoned management operation, and a dirty transaction without Rustlet state
changes. The registry hardware campaign also injects failure at the SD/key
BOSS, checks absence before and after reboot, then installs successfully and
checks the complete graph after another reboot.

Validation on 2026-09-17 passed `gp_cli_load` with 489 checks on both Pico1
QEMU and Pico2 OpenOCD. Kernel unit tests cover malformed later entries,
capacity failure after an earlier insertion, and publication failure after
replacement or creation. CLI transport tests cover interrupted deployment,
full final blocks, the 256-block limit, and invalidation of persisted SCP11
state on transport or response-verification failure.

The earlier typed-error and PUT KEY change, relative to `943d623`, had the
following devkit ELF flash spans (registry storage excluded):

| Target | Before (bytes) | After (bytes) | Difference |
| --- | ---: | ---: | ---: |
| MPS2-AN385 | 85,732 | 86,508 | +776 |
| Pico1 | 106,356 | 107,180 | +824 |
| Pico2 | 102,392 | 103,168 | +776 |

Those earlier measurements had unchanged static RAM and a 2912-byte SCP03 S8
kernel stack peak. Their specialized key undo records have since been replaced
by the shared registry journal described above.

For the APDU transaction refactoring, relative to `50cc5e5`, the Pico2 devkit
flash span is 106388 bytes versus 103416 (+2972). Static `.data` grows by 16
bytes; `.bss` and RAM-resident code are unchanged. Temporary heap cost depends
on the touched slots and nested operation savepoints; it is additional to
those static figures. A publication during an unfinished LOAD also temporarily
preserves one logical flash page (256 bytes on Pico2). This step increases
flash footprint; sharing rollback machinery alone has not yet produced a net
size reduction. The global 64 KiB Pico2 RAM limit and MPU mappings are unchanged.

The 2026-09-19 Pico2/OpenOCD campaigns passed 1498 `kernel_registry` checks
(including the SD/inherited-key publication failure), 71 `gp_registry` checks,
122 Rustlet SD SCP03/delegated/SCP11a/b/c checks, 199 `gp_persistence` checks,
and 1562 `dyn_rustlet` checks: 3452 functional checks in total. Workspace host
tests and strict Clippy passed; the kernel library now has 154 passing tests.

The instrumented Rustlet SD SCP03 campaign passed its 44 functional checks.
Across its 44 common checkpoints, measured kernel stack deltas versus
`50cc5e5` range from -256 to +32 bytes. The peak grows from 3016 to 3048 bytes;
the first SELECT drops from 2520 to 2264. `--check_stack` still exits with a
regression warning (the first is EXTERNAL AUTHENTICATE, 2984 versus the old
2952-byte reference). No stack baseline was updated. Rustlet stack accounting
remains separate, and these observed peaks are not worst-case bounds.




### Pico2 random generation

The production backend is `raspi_pico2_random.rs`. It keeps the RP2350 TRNG's
von Neumann conditioning, repeated-bit, CRNGT and autocorrelation checks
active. It uses oscillator chain 1 and a 200-cycle sampling interval. Register
semantics come from the [RP2350 datasheet, section 12.12](https://datasheets.raspberrypi.com/rp2350/rp2350-datasheet.pdf).
The [Embassy driver](https://github.com/embassy-rs/embassy/blob/main/embassy-rp/src/trng.rs)
also uses 200 cycles and reports that shorter intervals can fail when the CPU
sleeps. This backend polls rather than sleeping during acquisition.

A health error takes precedence over a simultaneous valid indication. The
entire attempt is discarded and the peripheral reset with the same checks
active. Acquisition permits at most eight attempts, at most 1,000,000 polls
per attempt and 1,000 reset-handshake polls. A timeout fails immediately;
these are iteration bounds, not a wall-clock latency promise. Configuration
readback, all-zero/all-one checks and a consecutive 192-bit block comparison
provide additional catastrophic-failure detection. They do not estimate
min-entropy. No health-test bypass is used for recovery.

`crypto/hmac_drbg.rs` implements HMAC-DRBG/SHA-256 Update, Instantiate, Reseed
and Generate from [NIST SP 800-90A Rev. 1, section 10.1.2](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf).
The internal API has no personalization or additional input. SHA-256 and
HMAC-SHA-256 were already linked for FAE verification and HKDF. The new
mechanism reuses RustCrypto HMAC rather than implementing a new MAC.

The first nonempty request consumes two checked 24-byte blocks as entropy
input and a separate 24-byte nonce block. Each later request, and each further
1024-byte output chunk, requires two new checked blocks before generation.
To claim 256-bit strength, those 48-byte entropy inputs must contain at least
256 bits of entropy, and the initial nonce at least 128 bits. **Byte counts,
health checks and the conditioner do not establish those bounds.** Hardware
source characterization remains required; SRAM fingerprint experiments do
not qualify the TRNG. The generator's post-generation update protects prior
outputs under the standard mechanism's assumptions; fresh reseeding supports
recovery from state disclosure only when the new entropy is unknown to the
attacker. Kernel/Rustlet isolation remains a separate necessary assumption.

One non-reentrant guard owns the peripheral and state. Reentry refuses the
request without modifying the interrupted owner's state. On collection or
generation failure the complete output, including previously filled chunks,
is cleared; owned seed/state buffers are scrubbed and the source is stopped.
The backend then refuses requests until reboot. Initialization is idempotent
and cannot clear this latch. There is no raw-entropy, reset or seed-selection
syscall. Rustlet `RandomData` objects are facades over the same kernel service;
constructing one does not initialize a new kernel generator. DRBG state is
neither cloned nor serialized into the registry.

Tests include 45 NIST CAVP vectors across three reseed modes, injected register
failures, bounded retries, output cancellation, fresh-entropy requirements
and reentry refusal. Target scenarios exercise repeated public requests and
forbidden accesses to the RP2350 TRNG EHR and bypass registers from a Rustlet,
followed by a successful RNG syscall. These tests establish functional
behavior and isolation on tested targets, not certification or a statistical
proof of cryptographic security. No MPU mapping or permission change is part
of this backend replacement.

Validation on 2026-09-17 passed the 73 core unit tests, workspace tests,
strict workspace Clippy, Pico1 QEMU Rustlet crypto/isolation scenarios, and
Pico2 OpenOCD kernel crypto (19 checks), Rustlet crypto (46), isolation (29),
SCP03 S8 (52) and Rustlet Security Domain SCP03 (39) scenarios.

For the same devkit configuration, relative to commit `bfe08ae`, the ELF flash
load span changes as follows; these spans exclude registry storage:

| Target | Before (bytes) | After (bytes) | Difference |
| --- | ---: | ---: | ---: |
| MPS2-AN385 | 85,732 | 85,732 | 0 |
| Pico1 | 106,356 | 106,356 | 0 |
| Pico2 | 101,812 | 102,392 | +580 |

Pico2 `.bss` grows from 4,316 to 4,372 bytes (+56); `.data` remains 14,888
bytes and RAM-resident code remains 40 bytes. RNG state grows from 48 to 104
bytes. The 64 KiB total RAM limit and MPU layout are unchanged. The measured
SCP03 S8 kernel stack peak remains 2,912 bytes before and after; the new
Rustlet crypto scenario reaches 3,344 bytes of kernel stack, with its Rustlet
stack measured separately. These are scenario peaks, not universal bounds.

A single first 255-byte RNG APDU measured 31 ms before and 40 ms after the
change, including serial transport. Subsequent 255-byte requests in the new
kernel scenario measured 34.871--35.065 ms; 16-byte requests measured
13.359--13.603 ms. These host observations include transport and scheduling,
and do not isolate generator execution time or provide worst-case bounds.
