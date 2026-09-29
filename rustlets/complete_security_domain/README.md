# Complete Security Domain

`CompleteSecurityDomain` is a privileged Rustlet used to demonstrate that a
Security Domain can own a secure-channel implementation in application space.
It is not limited to authorizing kernel operations: the kernel proxy forwards
SCP establishment and secure-messaging operations to this Rustlet.

The SCP03 example deliberately includes security level `33`:

- command encryption (`C-ENC`);
- command authentication (`C-MAC`);
- response encryption (`R-ENC`);
- response authentication (`R-MAC`).

`KernelSecurityDomain` does not select SCP03 level `33`. Loading this Rustlet
Security Domain therefore illustrates the intended extension model: when a
deployment needs a protocol fragment that the kernel profile does not provide,
implement it in a Security Domain Rustlet and load that Security Domain rather
than adding a proprietary path to the kernel.

The same model can host future GlobalPlatform Supplementary Security Domains.
This keeps optional or deployment-specific protocol policy in the application
environment instead of making internal, proprietary kernel implementations the
only extension mechanism, as is common in Java Card ecosystems.

## Validation

The Oxide SE QEMU campaign exercises SCP03 S16 at security level `33`,
including encrypted commands, encrypted and authenticated responses, and replay
rejection:

```text
cargo run test gp_rustlet_security_domain_scp03 mps2-an385
```

The campaign also checks that the SD key-loading SVC is denied outside
`sddispatch`, including from this SD's ordinary `process_apdu` and from an
ordinary Rustlet while the SD remains resident. Diagnostic instruction `0A`
returns `9000` only when the SVC reports `PermissionDenied` and leaves its
output buffer untouched; otherwise it returns `6F00`. It never returns key
material. The test repeats the check after recovering from a Rustlet panic.

The host-side SCP03 vector tests also reproduce the public Samsung
OpenSCP-Java AES-128/S16 exchange. Samsung selects `EXTERNAL AUTHENTICATE`
security level `33` and currently publishes no equivalent `11` or `13`
scenario. The Samsung transcript is independent regression evidence, not a
GlobalPlatform certification vector.

### Transaction diagnostics

The test SD exposes `INS 0B` to enable/reset three persistent one-byte counters
and `INS 0C` to return them as three big-endian `u32` values: operation, unwrap,
and wrap. Counters remain dormant in normal scenarios. After enabling the
probe, diagnostic GET DATA hooks `EF00`, `EF01`, and `EF02` increment the
operation counter and respectively succeed, reject, or panic.

`configs/config_rustlet_sd_transaction_test.toml` combines this SD with the
private kernel registry-test module. Its `A0/P1=12` command stages a DATA mutation
and calls the diagnostic SD hook inside a management savepoint. `P1=14` also
arms a final BOSS write failure. These are disposable-image qualification
commands, not production management interfaces. No key material is exposed.

With the transaction probe enabled, a five-byte plaintext response ending in
`D3 91 A7 5E` makes the response hook write a partial output and then panic.
The `minimal_valid_test` fixture produces that response with INS `0D` after
incrementing its persistent counter; INS `0E` reads the counter. The campaign
checks status-only failure, an immediate reboot before any recovery APDU,
rollback in RAM, rejection of the old channel, and a later successful commit.

`0B` with P1=1 also makes response protection panic on an application crash
status. The minimal fixture increments then panics with INS `0F`; INS `10`
increments and returns normally without triggering the SD diagnostic. Together
these commands exercise all four SD/application crash combinations, including
preservation of SD protocol progress when only the application crashes.
