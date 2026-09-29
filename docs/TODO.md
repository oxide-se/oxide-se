# TODO

This file tracks open technical work for the current implementation. Design
history belongs in the lab journal. Remove completed items instead of keeping
checked entries; retain only pending work and the context needed to complete it.

## Stack Budgets And Regression Validation

Required:

- [ ] Qualify kernel stack headroom including periodic interrupt paths before
  lowering the three mps2 kernel SCP11 references. Pico1 fixed-seed tests still
  varied with SysTick enabled; the tested variation disappeared when SysTick
  was disabled under GDB, and a controlled interrupt reproduced deeper stack
  use. Measure the complete timer callback at deep crypto frames, including
  NULL emission and watchdog paths. Do not replace a worst-case analysis with
  the largest sampled value or treat stable stack usage as a constant-time proof.
- [x] Refresh Pico2 hardware stack baselines on the current firmware. Repeated
  measurements retain the largest value observed at each checkpoint, plus a
  24-byte kernel interrupt-frame margin. Kernel and Rustlet maxima remain
  separate; the largest retained kernel reference is 5480 bytes.
- [x] Refresh Pico1 QEMU stack baselines on the current firmware. Each campaign
  has one measured run plus a 24-byte kernel interrupt-frame margin; the largest
  retained kernel reference is 5576 bytes. These are QEMU references, not
  hardware measurements.
- [ ] Refresh hardware stack baselines for the remaining supported boards. Keep
  existing measurements until their replacement is validated on the
  corresponding board; QEMU results must not replace hardware references.

Keep kernel and Rustlet measurements separate in `xtask/stack-baselines.toml`.
Preserve the 6144-byte kernel budget and each target's smaller physical limits.
See [the stack validation guide](kernel.getting.started.md#stack-baseline-audit).

Possible Improvements:

- Add measured identities for newer campaigns as their stack instrumentation
  becomes supported. Absence of a baseline is not evidence of a regression-free
  campaign.

## Security Domain And Secure Channel

Required:

- [ ] Add ISO/IEC 7816-4 / GlobalPlatform logical-channel support after the
  beta, including `MANAGE CHANNEL` and independent per-channel application
  selection and secure-channel state. Multiple logical channels are planned,
  not deliberately excluded from the oXiDe SE profile.

Possible Improvements:

- Extend Rustlet Security Domain QEMU coverage so every management hook has
  positive and negative tests where the hook has one meaningful policy branch.
- Add Rustlet-SD-authorized dynamic `LOAD` scenarios beyond the current
  kernel-authorized persistence path.
- Add richer lifecycle-management flows on top of the current package,
  instance, Security Domain, and key state guards.
- Refine certification-grade key-purpose and key-diversification policy on top
  of the current GP-style SCP03 key object model.
- Add optional key-information and Security-Domain metadata fields beyond the
  current `GET DATA 0066/0067` and mandatory `GET STATUS` records.

## Rustlet Fault Isolation

Possible Improvements:

- Extend hardware fault-injection coverage to Rustlet instruction/data bus errors
  and bus-error unstacking without weakening production MPU permissions.
  Keep imprecise bus errors, unsupported floating-point contexts and ambiguous
  exception origins fatal; any future recovery needs an explicit ownership and
  attribution contract.

## SCP03/SCP11

Possible Improvements:

- Account for long-running SVC execution in Rustlet watchdog and T=0 NULL
  timing. The initial low-priority SysTick design deliberately does not
  preempt SVC handlers, notably slow asymmetric crypto on Pico1.

- Validate secure-channel operations against official GlobalPlatform
  certification vectors if such vectors become available to the project.
- Import the remaining reusable Samsung OpenSCP-Java references: SCP11a
  P-256/AES-128 S8, P-256/AES-192 S8, P-256/AES-256 S8, P-384/AES-128 S8,
  Brainpool-P256/AES-128 S8, GP-certificate P-256/AES-128 S8, SCP11c
  P-256/AES-128 S8, and the X.509/GP certificate-bundle `GET DATA` cases.
  Record explicitly that the current Samsung suite provides no SCP11b vector.
- Decide whether deployment manifests should prefer SCP03 S16, SCP11, or a
  dual SCP03+SCP11 protocol set once production policy is ready.
- Define diversification policy for static Security Domain key material,
  separately from SCP03 session-key derivation.
- Support additional SCP11 algorithm and curve variants beyond the current
  P-256/AES development profile.
- Generalize certificate-chain handling beyond the embedded-CA development
  profile if production deployment needs a fuller GP PKI model.
- Map currently modeled but unused privilege families to kernel operations when
  those operations exist: `Trusted Path`, `Token Verification`, `Global Lock`,
  `Final Application`, `Global Service`, `Receipt Generation`,
  `Ciphered Load File Data Block`, `Contactless Activation`,
  `Contactless Self-Activation`, `DAP Verification`,
  `Mandated DAP Verification`, `Card Lock`, `Card Terminate`, `Card Reset`,
  and `CVM Management`.

## Rustlet Isolation And MPU Packing

Possible Improvements:

- Extend kernel RAM-XN coverage to future targets whose mutable RAM cannot be
  represented as one or two strict MPU windows.
- Distinguish executable Rustlet code from read-only Rustlet metadata only if a
  future threat model requires metadata to be XN instead of merely RX.

## Board Porting And Hardware Validation

Required:

- [ ] Complete entropy-source qualification of the Pico2 checked-TRNG /
  HMAC-DRBG backend under a software attacker controlling APDU contents/timing,
  arbitrary Rustlets and a subordinate SD Rustlet. The replacement enables
  hardware health checks, bounds waits/retries, requires fresh entropy before
  every request, and removes splitmix64/xoroshiro128**. Its NIST vectors and
  fault/isolation tests do not establish a source min-entropy bound. Measure
  pre-DRBG source behavior across sampling settings, devices, restarts and
  software activity; justify the entropy credited to seed and nonce inputs.
  SRAM fingerprint stability provides no TRNG qualification. Keep raw-source
  acquisition diagnostics out of production images.

Possible Improvements:

- Extend the hardware campaigns validated on Pico2 to other supported boards,
  including persistence across reset without reflashing and fault observation;
  record hardware-specific stack baselines for each validated campaign.
- Map each maturity level to reproducible validation commands before
  `qemu_support` or `board_support` is enabled.

## Documentation Cleanup

Possible Improvements (deferred):

- Review Rustdoc coverage of internal public `kernel` / `core` interfaces,
  especially around the secure-channel boundary and registry authority model,
  and document any remaining gaps. This is deferred work, separate from the
  Rustlet and Rustlet Security Domain API reference already documented.

## Persistent Registry And Flash Backend

Required:

- [ ] Qualify electrical interruptions during sector erase and brownout recovery.
  The ordinary Pico1/Pico2 power cycles and deterministic write/erase-prefix images
  do not establish those behaviors. The earlier `kernel_flash` two-marker
  campaign covers complete resets on Pico2 and Pico1 QEMU. Keep explicit
  destructive-test consent; back up data unless the user explicitly waives it.

Possible Improvements:

- Extend erase fault models beyond the deterministic erased-prefix/original-
  suffix pattern. Physical erase interruption, arbitrary partially erased bits
  and brownouts need separate evidence; an injected durable image is not an
  electrical fault qualification.
- Define and implement a syscall API through which an authorized Rustlet can
  read, write, replace, and remove AID-qualified registry `Data` objects
  without exposing kernel-managed `Key` semantics. Specify the associated
  Security Domain access checks and the atomicity/transaction model for
  multi-page or multi-call mutations, including interruption, rollback, and
  power-loss behavior.
- Use DMA where the target can provide it to optimize flash programming and CRC
  calculation for persistent registry blocks.
- Optimize flash-space management beyond the current first-fit append/recycle
  strategy, including compaction policy, wear distribution, and stronger
  fault-injection coverage.

### Atomicity of compound management mutations

- [ ] Implement explicit persistent and session state scopes for Rustlets and
  Rustlet Security Domains, following the shared-gate design recorded in the
  laboratory journal on 2026-09-26. Persistent state follows the applicable
  transaction's commit/rollback; session state survives that rollback while
  its session remains valid and is discarded at session termination or reset.
  Preserve the existing distinction between a rejected SD management operation
  and an ordinary Rustlet's normally returned error status.
  Serialize both scopes successively through the same gate, with a preparation
  service for persistent state and kernel-managed storage of serialized session
  state in the inactive Rustlet heap, without another permanent buffer or live
  cross-invocation pointers. Restore abandoned persistent fields of resident
  Rustlet SDs without losing legitimate secure-channel progress. Until this is
  implemented, registry rollback alone can leave the resident SD object able
  to reintroduce abandoned state; this remains an accepted current limitation.
  Close this item only when normal-rejection restoration and the complete fault
  campaign pass, including crash retirement, protected-response publication
  failure, and reboot recovery. The remaining issue and existing regression
  coverage are described in [the kernel developer guide](kernel.developer.guide.md).
  Reproduce with `cargo run --offline test gp_rustlet_security_domain_scp03
  raspi-pico2 --on openocd --config configs/config_rustlet_sd_transaction_test.toml
  --serial <port>:115200 --allow-destructive`.

## INSTALL [for load] / LOAD

Possible Improvements:

- Use DMA where the target can provide it for large `LOAD` writes, hash/CRC
  calculation, and flash programming.
- Complete the remaining KCV/wrapping and segmented STORE DATA work when
  their command profiles are defined; see [the apdu-tool roadmap](../tools/apdu-tool/docs/TODO.md).

## Porting Pico-2

Possible Improvements:

- Replace the software-based SHA-256 implementation with the hardware SHA-256
  accelerator on the Pico 2. This would reduce CPU cycles spent on hashing and
  improve efficiency.
- Use spinlocks to protect hardware peripherals such as the TRNG if concurrent
  execution or similar use cases are introduced.

## FAE Tooling Roadmap Scope

Track private RT0 relocation-metadata bounds and arithmetic, completion of
malformed-input coverage, and legacy/XiPFS equivalence tests in
[the upstream roadmap](../tooling/build-fae/TODO.md). Changes belong in the
build-fae repository and require separate validation for each affected ABI.
