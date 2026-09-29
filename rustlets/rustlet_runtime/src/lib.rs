#![deny(unsafe_op_in_unsafe_fn)]
#![no_std]
#![deny(missing_docs)]
#![cfg_attr(feature = "runtime", feature(alloc_error_handler))]

//! Application and Security Domain API for oXiDe SE Rustlets.
//!
//! # Start here
//!
//! | Task | API |
//! | --- | --- |
//! | Declare an application and its heap | `declare_rustlet!`, `Rustlet` |
//! | Receive commands and produce responses | [`Apdu`], [`ApduStatus`] |
//! | Decode installation parameters without allocation | [`gp::parse_install_for_install_ctx`] |
//! | Encrypt, authenticate or derive keys | [`CryptoProvider`], [`Cipher`], [`Mac`], [`KeyAgreement`] |
//! | Generate random data | [`RandomData`] |
//! | Implement management and secure-channel policy | `RustletSecurityDomain`, `declare_security_domain!` |
//! | Integrate an ABI or runtime | [`RustletCtx`], [`syscall_abi`], [`syscall`], `rt` |
//!
//! Application entry points require the **`runtime` feature** and the repository's
//! nightly toolchain. Without it, shared types and parsers remain available for
//! kernel and host tooling, but the allocator, entry macros and application
//! traits are absent. Enable it when generating the complete reference.
//!
//! # Lifecycle and persistence
//!
//! A `no_std`, `no_main` Rustlet is packaged as an FAE and loaded into a running
//! devkit. Pico 1 uses `thumbv6m-none-eabi`. The declaration macro requires
//! `Default`, [`serde::Serialize`] and [`serde::Deserialize`], even with a custom
//! installer. Installation creates the initial object; ordinary APDU calls
//! reconstruct it and restore postcard state. On normal return the runtime
//! serializes it, drops it, and the kernel scrubs its heap. Serialization errors
//! abandon the invocation's staged state. The wrapper does **not** call the
//! application's custom `load_state`/`save_state` overrides.
//!
//! Use serde attributes to choose persistent fields. Skipped fields are
//! reconstructed for every ordinary invocation. Security Domains are different:
//! their active secure-channel session may remain resident and should be excluded
//! from serialization. [`persistence`] contains future streaming adapters, not
//! the active postcard persistence implementation.
//!
//! # Memory and execution boundaries
//!
//! The shared context is [`APDU_SHARED_REGION_SIZE`] bytes: a control/state half
//! and one APDU buffer reused for input and output. Payloads are limited to
//! [`APDU_PAYLOAD_LENGTH_MAX`] bytes and serialized state to
//! [`STATE_BUFFER_CAPACITY`] bytes. Borrow input only during its processing
//! phase; [`Apdu::send_with`] generates output directly in shared storage.
//! The macro's heap size and the FAE's stack requirement are independent.
//! Neither Rust ownership nor successful QEMU execution establishes hardware
//! isolation: Pico 1 has no MPU.
//!
//! Crypto services enter the kernel synchronously. Availability and random-source
//! quality depend on the target. [`Cipher::update`] is unimplemented;
//! [`Mac::update`] buffers up to 256 bytes. Prefer [`CryptoProvider::compute_mac`]
//! for an already assembled message. Key wrappers are copyable values, not
//! automatically zeroizing secret containers; avoid unnecessary copies and logs.
//!
//! # Reference scope
//!
//! The typed APIs above are the application interface. Public descriptor,
//! syscall and `rt` items also serve separately compiled kernel/runtime glue;
//! their visibility is not an invitation to bypass the typed API. Raw records
//! carry no Rust lifetime proof. Read their contracts before integration.
//! The kernel checks address ranges and authority at each service boundary.
//! Host builds support parser and data-model tests; they do not emulate SVCs.
//!
//! Examples involving services must run inside a Rustlet. Pure parser examples
//! are executable host doctests. Feature-gated entry examples are checked on
//! the embedded target by the documentation validation script.

#![cfg_attr(
    feature = "runtime",
    doc = "\n## Runtime entry points\n\nSee [`Rustlet`], [`declare_rustlet!`], [`RustletSecurityDomain`],\n[`declare_security_domain!`] and [`rt`] for the feature-gated lifecycle API."
)]
#[cfg(feature = "runtime")]
extern crate alloc;

mod abi;
mod apdu;
mod crypto;
pub mod gp;
pub mod persistence;
#[cfg(feature = "runtime")]
mod security_domain;
pub mod syscall;
pub mod syscall_abi;
mod syscall_backend;

pub use abi::*;
pub use apdu::*;
pub use crypto::*;
pub use persistence::{PersistenceError, StateReader, StateWriter};
#[cfg(feature = "runtime")]
pub use security_domain::*;
pub use serde;
pub use syscall_abi::{
    CryptoCipherDoFinalParams, CryptoEcCurve, CryptoEcGenerateKeypairParams,
    CryptoEcdhDoFinalParams, CryptoErrorCode, CryptoHkdfSha256Params, CryptoMacDoFinalParams,
    CryptoMacOperation, CryptoRandomGenerateParams, CryptoX963Sha256Params, RuntimeReturnKind,
    RuntimeSyscall, Scp03LoadKeyParams, SyscallNumber, SyscallWord,
};

#[cfg(feature = "runtime")]
pub mod rt;

#[cfg(feature = "runtime")]
pub use rt::{PostcardState, Rustlet};

#[cfg(feature = "runtime")]
#[macro_export]
/// Declares a Rustlet entry point and its private heap.
///
/// The generated entry point exposes only the lifecycle handlers consumed by the
/// kernel. Persistent state is loaded and saved inside the Rustlet runtime
/// around `install` and `process_apdu`.
///
/// Forms: `declare_rustlet!(T)`, `declare_rustlet!(T, heap_bytes)`, or
/// `declare_rustlet!(T, heap_bytes, install_fn)`. The default heap is 768 bytes;
/// it must fit the boxed application and its allocations. This does not size
/// the stack. Use exactly one declaration per image.
///
/// `T` must implement [`Rustlet`], `Default`, [`serde::Serialize`] and
/// [`serde::Deserialize`]. The custom installer has signature
/// `fn(&mut RustletCtx) -> Result<T, ApduStatus>`; an error rejects installation.
/// `Default` is still required to reconstruct subsequent calls. The generated
/// postcard wrapper owns persistence; custom trait load/save overrides are not
/// delegated to. No APDU/context borrow may escape a handler.
macro_rules! declare_rustlet {
    // --- Public API Overloads ---

    // Default overload: use implicit install with a default heap size (768 bytes).
    ($app_ty:ty) => {
        $crate::declare_rustlet!(@implicit $app_ty, 768usize);
    };

    // Custom heap size overload with implicit install.
    ($app_ty:ty, $heap_size:expr) => {
        $crate::declare_rustlet!(@implicit $app_ty, $heap_size);
    };

    // Fully explicit overload: custom heap size and custom install function.
    ($app_ty:ty, $heap_size:expr, $install_fn:path) => {
        $crate::declare_rustlet!(@explicit $app_ty, $heap_size, $install_fn);
    };

    // --- Internal Implementation Detail: Implicit Installation ---
    (@implicit $app_ty:ty, $heap_size:expr) => {
        #[doc(hidden)]
        /// Internal adapter for apps implementing Default for installation.
        fn __oxide_se_implicit_install(ctx: &mut $crate::RustletCtx) -> core::result::Result<$app_ty, $crate::ApduStatus> {
            <$app_ty as $crate::rt::DeclareAppWithoutInstallRequiresDefault>::implicit_install(
                ctx,
            )
        }

        $crate::declare_rustlet!(@explicit $app_ty, $heap_size, __oxide_se_implicit_install);
    };

    // --- Internal Implementation Detail: The Core Entry Point ---
    (@explicit $app_ty:ty, $heap_size:expr, $install_fn:path) => {
        extern crate alloc;

        #[doc(hidden)]
        static __OXIDE_SE_RUSTLET_HEAP_STORAGE: $crate::rt::RustletHeapStorage<{ $heap_size }> =
            $crate::rt::RustletHeapStorage::new();

        #[doc(hidden)]
        /// Bridges the typed install function with the boxed trait object required by the runtime.
        fn __oxide_se_install_adapter(
            ctx: &mut $crate::RustletCtx,
        ) -> core::result::Result<$crate::rt::RuntimeInstance, $crate::ApduStatus> {
            let instance: $app_ty = $install_fn(ctx)?;
            Ok($crate::rt::RuntimeInstance::App(alloc::boxed::Box::new(
                $crate::rt::PersistentRustlet::new(instance),
            )))
        }

        #[doc(hidden)]
        fn __oxide_se_load_adapter(
            _ctx: &mut $crate::RustletCtx,
        ) -> core::result::Result<$crate::rt::RuntimeInstance, $crate::ApduStatus>
        where
            $app_ty: core::default::Default,
        {
            let instance = <$app_ty as core::default::Default>::default();
            Ok($crate::rt::RuntimeInstance::App(alloc::boxed::Box::new(
                $crate::rt::PersistentRustlet::new(instance),
            )))
        }

        #[unsafe(no_mangle)]
        #[doc(hidden)]
        /// Low-level entry point called by the Kernel.
        /// Initializes the allocator with the local storage and starts the Rustlet runtime.
        /// # Safety
        /// Called once by the kernel with this image's GP and exclusive memory
        /// established; no previous runtime instance or handler may be active.
        pub unsafe extern "C" fn start(buffer: *mut $crate::RustletCtx) -> ! {
            // SAFETY: the kernel entry contract and private static heap establish
            // the runtime startup obligations for this relocated image.
            unsafe {
                $crate::rt::start(
                    __oxide_se_install_adapter,
                    __oxide_se_load_adapter,
                    buffer,
                    __OXIDE_SE_RUSTLET_HEAP_STORAGE.as_mut_ptr(),
                    $heap_size,
                )
            }
        }
    };
}

#[cfg(feature = "runtime")]
#[macro_export]
/// Alias for `declare_rustlet!` to maintain compatibility with legacy "app" terminology.
macro_rules! declare_app {
    ($($tt:tt)*) => {
        $crate::declare_rustlet!($($tt)*);
    };
}

#[cfg(feature = "runtime")]
#[macro_export]
/// Declares a Rustlet that can also act as a user-land Security Domain.
///
/// The concrete type must implement both [`Rustlet`] and
/// [`RustletSecurityDomain`]. It remains a normal selectable Rustlet through
/// `process_apdu`, while the kernel can also call the generated Security
/// Domain vtable through a proxy.
///
/// Accepts the same heap and installer forms as [`declare_rustlet!`], with the
/// same `Default` and serde requirements. Adds persistent administrative metadata
/// to the serialized application state, reducing its available state capacity.
/// Secure-channel session fields should be skipped by serde and cleared by
/// `reset_secure_channel`. The active SD object can remain resident between
/// calls; its administrative role does not confer CPU privilege. The kernel's
/// proxy remains responsible for ownership and privilege checks.
macro_rules! declare_security_domain {
    // Default overload: use implicit install with a default heap size (768 bytes).
    ($app_ty:ty) => {
        $crate::declare_security_domain!(@implicit $app_ty, 768usize);
    };

    // Custom heap size overload with implicit install.
    ($app_ty:ty, $heap_size:expr) => {
        $crate::declare_security_domain!(@implicit $app_ty, $heap_size);
    };

    // Fully explicit overload: custom heap size and custom install function.
    ($app_ty:ty, $heap_size:expr, $install_fn:path) => {
        $crate::declare_security_domain!(@explicit $app_ty, $heap_size, $install_fn);
    };

    (@implicit $app_ty:ty, $heap_size:expr) => {
        #[doc(hidden)]
        fn __oxide_se_implicit_install(ctx: &mut $crate::RustletCtx) -> core::result::Result<$app_ty, $crate::ApduStatus> {
            <$app_ty as $crate::rt::DeclareAppWithoutInstallRequiresDefault>::implicit_install(
                ctx,
            )
        }

        $crate::declare_security_domain!(@explicit $app_ty, $heap_size, __oxide_se_implicit_install);
    };

    (@explicit $app_ty:ty, $heap_size:expr, $install_fn:path) => {
        extern crate alloc;

        #[doc(hidden)]
        static __OXIDE_SE_RUSTLET_HEAP_STORAGE: $crate::rt::RustletHeapStorage<{ $heap_size }> =
            $crate::rt::RustletHeapStorage::new();

        #[doc(hidden)]
        fn __oxide_se_install_adapter(
            ctx: &mut $crate::RustletCtx,
        ) -> core::result::Result<$crate::rt::RuntimeInstance, $crate::ApduStatus> {
            fn __oxide_se_assert_security_domain<T: $crate::RustletSecurityDomain>() {}
            __oxide_se_assert_security_domain::<$app_ty>();
            let instance: $app_ty = $install_fn(ctx)?;
            let mut instance = $crate::rt::PersistentSecurityDomain::new(instance);
            instance.initialize_from_install_apdu(ctx)?;
            Ok($crate::rt::RuntimeInstance::SecurityDomain(
                alloc::boxed::Box::new(instance),
            ))
        }

        #[doc(hidden)]
        fn __oxide_se_load_adapter(
            _ctx: &mut $crate::RustletCtx,
        ) -> core::result::Result<$crate::rt::RuntimeInstance, $crate::ApduStatus>
        where
            $app_ty: core::default::Default,
        {
            fn __oxide_se_assert_security_domain<T: $crate::RustletSecurityDomain>() {}
            __oxide_se_assert_security_domain::<$app_ty>();
            let instance = <$app_ty as core::default::Default>::default();
            Ok($crate::rt::RuntimeInstance::SecurityDomain(
                alloc::boxed::Box::new($crate::rt::PersistentSecurityDomain::new(instance)),
            ))
        }

        #[unsafe(no_mangle)]
        #[doc(hidden)]
        /// # Safety
        /// Called once by the kernel with this image's GP and exclusive memory
        /// established; no previous runtime instance or handler may be active.
        pub unsafe extern "C" fn start(buffer: *mut $crate::RustletCtx) -> ! {
            // SAFETY: the kernel entry contract and private static heap establish
            // the runtime startup obligations for this relocated image.
            unsafe {
                $crate::rt::start_security_domain(
                    __oxide_se_install_adapter,
                    __oxide_se_load_adapter,
                    buffer,
                    __OXIDE_SE_RUSTLET_HEAP_STORAGE.as_mut_ptr(),
                    $heap_size,
                )
            }
        }
    };
}
