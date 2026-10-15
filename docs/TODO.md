# TODO

This file tracks open technical work for the current implementation. Design
history belongs in the lab journal. Remove completed items instead of keeping
checked entries; retain only pending work and the context needed to complete it.

## Stack Budgets And Regression Validation

Required:

- [ ] Qualify stack headroom on paths that are actually interruptible. The
  2026-10-14 sampled envelopes are accepted references, not worst-case proofs.
  SysTick cannot preempt SVC; Pico flash command-mode sections mask interrupts.
  Restrict deep-frame timer analysis to Thread-mode kernel paths with interrupts
  enabled, and include the complete callback there. Do not inject an impossible
  timer preemption inside SVC or masked flash operations.
- [ ] Qualify the complete SD Rustlet's small observed stack headroom: 1968–1976/2048
  bytes on Pico1 SCP03 and 1888/2048 on mps2 SCP03. Include exception entry at
  deep live frames; sampled watermarks are not a worst-case proof.
- [ ] Establish a dedicated `sd-transactions` stack reference after qualification.
  The rollback fixture must not reuse the ordinary SCP03 campaign's baseline.
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

- [ ] Define and implement an authenticated first-key provisioning ceremony for
  a dynamically created supplementary Rustlet Security Domain. Dynamic
  `LOAD`/`INSTALL` can currently register and select the child, but no supported
  flow gives that new authority its initial SCP03 keyset; consequently it
  cannot safely become an operational SCP03 authority. Closing this item
  requires an explicit bootstrap trust model and authorizer, proof that the
  child cannot amplify its parent's authority, atomic key-object publication
  with rollback and power-loss behavior, replay/downgrade protection, and an
  `apdu-tool` workflow that never exposes clear keys in process arguments or
  logs. Add positive and negative end-to-end tests on physical Pico1 covering
  successful provisioning, wrong authority, interrupted provisioning,
  duplicate/replayed provisioning, reset, and subsequent SCP03 establishment
  under the child. Embedding keys in the Rustlet or accepting an unauthenticated
  clear first-key APDU is not an acceptable workaround.
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

Required:

- [ ] Extend F-08 redirect interrupt injection to physical MPU-equipped boards.
  QEMU results exercise exception handling but do not qualify physical interrupt
  timing, deep crypto/flash timer stack usage, NMI or multicore behavior.

Possible Improvements:

- Extend hardware fault-injection coverage to Rustlet instruction/data bus errors
  and bus-error unstacking without weakening production MPU permissions.
  Keep imprecise bus errors, unsupported floating-point contexts and ambiguous
  exception origins fatal; any future recovery needs an explicit ownership and
  attribution contract.

## SCP03/SCP11

Possible Improvements:

- Qualify the crypto/flash anticipation budgets in `core/operation_timing.rs`
  on each board and flash part. NULL deadlines now use a hardware counter
  and transport-owned window, including Rustlet SD UNWRAP/WRAP. Operations
  individually exceeding one NULL interval (notably P-256 on slow Pico1)
  need internal progress points or splitting; preflight alone cannot cover them.

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

- [ ] Deferred: complete entropy-source qualification of the Pico2 checked-TRNG /
  HMAC-DRBG backend under a software attacker controlling APDU contents/timing,
  arbitrary Rustlets and a subordinate SD Rustlet. The replacement enables
  hardware health checks, bounds waits/retries, requires fresh entropy before
  every request, and removes splitmix64/xoroshiro128**. Its NIST vectors and
  fault/isolation tests do not establish a source min-entropy bound. Measure
  pre-DRBG source behavior across sampling settings, devices, restarts and
  software activity; justify the entropy credited to seed and nonce inputs.
  SRAM fingerprint stability provides no TRNG qualification. Keep raw-source
  acquisition diagnostics out of production images. This qualification requires
  measurement resources beyond the current software regression campaigns.

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
