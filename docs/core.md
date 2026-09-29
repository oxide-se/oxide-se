# Oxide SE Core Notes

This document captures the current role of `oxi_core` inside the
workspace and the service boundaries that are expected to stabilize
first.

## Scope

`oxi_core` is a reusable embedded library crate.

Its role is to provide:

- target-oriented early initialization;
- runtime initialization and shutdown support;
- minimal semihosting support;
- minimal serial I/O services;
- runtime allocation services for Rust `alloc`;
- low-level flash page services;
- low-level cryptographic services and target dispatch.

`oxi_core` is intentionally low-level. It should expose small and
stable service boundaries, while keeping board-specific details hidden
behind target implementations.

It is currently consumed by:

- `kernel/firmware`, the production firmware crate;
- `core_test`, the QEMU-oriented embedded test firmware crate.

## Current Structure

The current `kernel/core/src/` layout is:

- `lib.rs`: crate root exporting the reusable embedded library
- `core/mod.rs`: top-level wiring and public runtime-facing API
- `core/runtime.rs`: runtime initialization and shutdown
- `core/semihosting.rs`: semihosting helpers
- `core/serial.rs`: byte-oriented serial API
- `core/syscall.rs`: architecture-facing syscall facade
- `core/allocator.rs`: buddy allocator with an external bit-tree
- `core/isolation.rs`: owned execution sessions and MPU transition policy
- `core/crypto.rs`: low-level crypto facade and target/software routing
- `core/flash.rs`: flash service API
- `core/mpu.rs`: low-level MPU facade
- `core/target/`: board-specific implementations

For the practical sequence used to add a new board target, see
[`newboard.porting.guide.md`](newboard.porting.guide.md).

Application-facing firmware entry points belong to their firmware crates.
Each firmware crate provides an exported `start()` symbol and
delegates initialization and shutdown to `oxi_core`.

## Entry and Shutdown Model

Native ELF startup establishes MSP, masks interrupts, initializes the reserved
boot ABI and RAM sections, then calls the exported `start()` symbol owned by
the firmware crate. The legacy bootable kernel FAE mode is no longer supported; its `--fae` option
is deprecated. Rustlet FAE loading remains supported.

The current model is:

1. firmware `start()` calls `oxi_core::core::initialize()`;
2. the firmware runs its own `main` logic;
3. the firmware terminates through `oxi_core::core::shutdown(exit_code)`.

The same shutdown path is also used by Rust panics inside the embedded
runtime.

Current target behavior is:

- on QEMU-supported paths, request emulator exit via semihosting;
- otherwise, emit `tbd` on the serial line and freeze in a spin loop.

## Serial API

The current serial service is deliberately minimal and synchronous.

Public surface:

- `send_byte(byte: u8)`
- `receive_byte() -> u8`

Current assumptions:

- polling-based operation;
- no buffering;
- no interrupt-driven API;
- no DMA-facing abstraction yet.

This is sufficient for the APDU transport path used by `kernel/firmware`.

## Syscall Boundary

The syscall boundary separates three responsibilities:

- `oxi_core::core::syscall` owns handler registration and the builtin runtime
  services;
- the selected CPU profile owns exception entry, machine context preservation
  and dispatch, with shared code for the Mainline profiles;
- `rustlets/rustlet_runtime` defines the shared ABI and emits application-side
  calls. Firmware modules register services such as APDU processing and crypto.

This keeps machine transitions in the target layer and service policy in the
kernel modules that own it. The shared ABI must evolve consistently on both
sides of the boundary.

For the integration and execution contracts, see
[Syscall and Allocator Integration](kernel.developer.guide.md#syscall-and-allocator-integration).
The authoritative syscall numbers, register arguments, return kinds and
parameter records are documented alongside `RuntimeSyscall` in
[`syscall_abi.rs`](../rustlets/rustlet_runtime/src/syscall_abi.rs).

## Semihosting

Semihosting is a dedicated debug and development channel,
distinct from the APDU serial link.

Current uses include:

- debug output under QEMU;
- selected development-only host services, such as the QEMU-side
  entropy path.

This channel is convenient for bring-up and testing, but it is not part
of any security boundary and should not be confused with a hardened
production path.

## Allocator

The buddy allocator keeps its bit-tree metadata outside the managed heap and
walks it iteratively, without a recursive traversal buffer. Kernel heap and
metadata share the remaining mutable RAM after the firmware sections, subject
to the board's `MEMORY_LAYOUT` and RAM-code reservation. There is no fixed
8 KiB heap reservation. Rustlet allocator metadata stays kernel-owned while
the corresponding heap bytes belong to the Rustlet allocation.

Exclusive allocator access rejects reentry. Deallocation validates the path
to an allocated block before changing the tree; it cannot establish the exact
original Rust `Layout` or ownership of an arbitrary pointer solely from the
rounded block size.

## Memory-Safety Boundaries

Safe facades and pure validation/encoding modules forbid unsafe code where
their contracts allow it. Raw storage, allocator initialization, exception ABI,
linker symbols and hardware access still require explicit unsafe obligations.
The owner-core and IRQ exclusion rules are part of those obligations, not
multicore guarantees supplied by the borrow checker.

`AppExecution` binds validated execution resources to a borrowed isolation
plan. Allocator publication is scoped to the synchronous invocation;
syscall-buffer borrows last only while the relevant Rustlet is suspended.
These contracts preserve resident buffers without
additional payload copies or a whole-stack Rust borrow. See the
[kernel safety boundaries](kernel.developer.guide.md#rust-memory-safety-boundaries)
and [diagnostic contracts](kernel.developer.guide.md#diagnostic-and-startup-safety-boundaries)
for the remaining proof obligations.

## Crypto Service

The crypto layer is intentionally kept low-level and buffer-oriented.

Current responsibilities include:

- AES key loading through an opaque `AesKey`;
- AES-CBC encrypt/decrypt fallback;
- AES-CMAC fallback;
- SCP03-specific KDF support;
- entropy routing between target hardware and the QEMU development path.

The target policy is:

- use hardware support when a credible target backend exists;
- otherwise use the software fallback where appropriate;
- fail explicitly for entropy if no credible source is available.

## Flash Service

The low-level flash service is exposed at a page-oriented logical level,
not at the raw flash-controller level.

Flash remains directly readable through normal memory addressing. The
core service does not need to wrap reads into page-copying helpers.

### Intended Public API

The first public API is built around logical pages:

- `write_page(page_addr, page_buf)`
- `flush_page(page_addr)`
- `write_page_atomic(page_addr, page_buf)`
- `logical_page_size()`

Expected contract:

- `page_addr` is aligned on the logical page size;
- `page_buf` has exactly one logical page of data;
- `write_page` is non-atomic and best-effort;
- `flush_page` upgrades pending work for that page to
  all-or-nothing-except-power-loss semantics;
- `write_page_atomic` guarantees that, after boot-time recovery, either
  the previous page contents or the new page contents are preserved, but
  never a validated mixed state.

Backend note:

- a purely synchronous backend may treat `write_page` as an implicit
  flush and implement `flush_page` as a no-op.

Backend availability is target-specific; unsupported targets return
`Unsupported`.

### Recovery

Recovery from interrupted atomic writes is an internal core concern.
There is no need to expose a public `resume_*` API.

In the current implementation, recovery is triggered when the flash
service is first used. This keeps normal QEMU bring-up working while the
flash-controller path itself is still hardware-oriented.

### Minimal Metadata Direction

The current metadata direction for the first STM32L4-oriented atomic
scheme is deliberately small:

- `magic`
- logical page address or `0xFFFF_FFFF` for empty
- shadow checksum or `0xFFFF_FFFF` for empty
- `sequence_number`

If `magic` is missing, the core initializes the metadata page before
using the service.

### First Target Strategy

For the current STM32L475 direction, the first implementation uses only
flash `bank 2` as the managed region:

- total managed bank size: `512 KiB`
- reserved tail area: `16 * 2 KiB = 32 KiB`
- usable logical space: `480 KiB`

The last `16` pages of `bank 2` are reserved:

- the last `8` pages are rolling metadata pages;
- the preceding `8` pages are their associated rolling shadow pages.

The metadata/shadow pairing is:

- `-1 -> -9`
- `-2 -> -10`
- `...`
- `-8 -> -16`

The rolling metadata pages reduce the flash stress on any single page by
a factor of eight compared with a single fixed metadata page.

Selection policy:

- each metadata page carries a `sequence_number`;
- the next atomic write reuses the metadata slot with the smallest
  sequence number;
- the latest metadata slot is the one with the greatest sequence
  number;
- metadata is not invalidated after a successful atomic write.

Atomic-write policy:

- the selected shadow page is programmed with the desired post-write
  page image;
- that shadow is fully verified before metadata is written;
- metadata records the target page and the CRC of the shadow image;
- the target page is then erased and reprogrammed from the caller
  buffer.

Recovery policy:

- at flash-service startup, the implementation examines only the latest
  metadata slot;
- if that slot is empty, there is no recovery work;
- if the target page already matches the associated shadow page, the
  previous atomic write is considered complete;
- otherwise the target page is rewritten from the shadow image;
- old metadata entries remain as rolling history until reused.

Operational policy:

- `write_page` is currently synchronous on STM32L475 and performs an
  erase plus full page programming;
- `flush_page` is currently a no-op on STM32L475;
- `write_page_atomic` uses shadow-copying plus rolling metadata;
- the metadata page is not erased again after a successful commit, which
  removes one metadata burn per atomic write cycle;
- the implementation does not rely on `1 -> 0` rewrites as a software
  contract.

## Design Rule

The public core API should stay stable, small, and logical.
Target-specific constraints such as:

- erase granularity;
- program granularity;
- read-while-write limitations;
- need for RAM-resident routines;
- optional `1 -> 0` rewrite optimizations

should remain implementation details of the target backend whenever
possible.
