//! Raw SVC wrappers for kernel/runtime integration.
//!
//! These functions do not grant authority by themselves. They act on the active
//! invocation and its shared page, and must not be used as host-side emulation.
//! On non-ARM hosts the backend supplies placeholder return values, not real
//! services; terminal calls spin. Use the typed application API instead.
//!
//! Parameter records borrow no memory at the type level: pointed-to inputs and
//! writable outputs must remain valid for the synchronous call. The kernel
//! validates ranges, alignment and authority as described by [`crate::syscall_abi`].
//! Do not fabricate aliasing Rust references merely because the raw ABI permits
//! some overlapping buffers. Return values of crypto wrappers are encoded words,
//! not `Result`; decode the error flag before consuming lengths or booleans.

/// Low-level synchronous runtime services. Prefer the typed application API.
pub mod runtime {
    /// Bootstrap publication of the runtime descriptor.
    pub mod descriptor_return {
        /// Transfer control to the kernel; never return or unwind destructors.
        /// Invoke only at the matching runtime lifecycle boundary.
        pub fn trigger(descriptor: *const crate::SelectedAppDescriptor) -> ! {
            crate::syscall_backend::svc_3::<{ crate::syscall_abi::RETURN_TO_KERNEL }>(
                descriptor as usize,
                0,
                crate::syscall_abi::RuntimeReturnKind::Descriptor.word(),
            );
            loop {
                core::hint::spin_loop();
            }
        }
    }

    /// Terminal invocation exit without unwinding.
    pub mod exit {
        /// Transfer control to the kernel; never return or unwind destructors.
        /// Invoke only at the matching runtime lifecycle boundary.
        pub fn trigger(status: crate::ApduStatus) -> ! {
            crate::syscall_backend::svc_3::<{ crate::syscall_abi::RETURN_TO_KERNEL }>(
                status.sw1 as usize,
                status.sw2 as usize,
                crate::syscall_abi::RuntimeReturnKind::Exit.word(),
            );
            loop {
                core::hint::spin_loop();
            }
        }
    }

    /// Normal handler completion protocol.
    pub mod handler_return {
        /// Transfer control to the kernel; never return or unwind destructors.
        /// Invoke only at the matching runtime lifecycle boundary.
        pub fn trigger(status: crate::ApduStatus) -> ! {
            crate::syscall_backend::svc_3::<{ crate::syscall_abi::RETURN_TO_KERNEL }>(
                status.sw1 as usize,
                status.sw2 as usize,
                crate::syscall_abi::RuntimeReturnKind::HandlerReturn.word(),
            );
            loop {
                core::hint::spin_loop();
            }
        }
    }

    /// Panic-to-status termination adapter.
    pub mod panic {
        /// Transfer control to the kernel; never return or unwind destructors.
        /// Invoke only at the matching runtime lifecycle boundary.
        pub fn trigger() -> ! {
            super::exit::trigger(crate::ApduStatus::internal_error())
        }
    }

    /// Active Rustlet heap allocation services.
    pub mod allocator {
        use core::alloc::Layout;

        /// Allocate from the current Rustlet heap; return null on failure.
        /// The returned storage is uninitialized and exclusively owned by the caller
        /// until deallocated with the same layout. Does not allocate from the host.
        pub fn alloc(layout: Layout) -> *mut u8 {
            crate::syscall_backend::svc_2::<{ crate::syscall_abi::ALLOC }>(
                layout.size(),
                layout.align(),
            ) as *mut u8
        }

        /// # Safety
        ///
        /// `ptr` and `layout` must describe a live allocation previously
        /// returned by `alloc` for the current Rustlet heap.
        pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
            crate::syscall_backend::svc_3::<{ crate::syscall_abi::DEALLOC }>(
                ptr as usize,
                layout.size(),
                layout.align(),
            )
        }
    }

    /// APDU phase changes for runtime integration.
    pub mod apdu {
        /// Receive command bytes into the active shared page.
        pub mod set_incoming_and_receive {
            /// Receive incoming bytes and return their count in the active shared page.
            /// Repeated input reuses the payload; after output starts this returns
            /// zero without modifying the response or reading the transport.
            pub fn trigger() -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::APDU_SET_INCOMING_AND_RECEIVE }>(
                    0, 0,
                )
            }
        }

        /// Switch the active page to outgoing response storage.
        pub mod set_outgoing {
            /// Declare output and reset its logical length, preserving payload storage.
            pub fn trigger() {
                let _ = crate::syscall_backend::svc_2::<{ crate::syscall_abi::APDU_SET_OUTGOING }>(
                    0, 0,
                );
            }
        }

        /// Publish the initialized response prefix length.
        pub mod set_outgoing_length {
            /// Publish `len` initialized response bytes; caller must keep len at most 255.
            pub fn trigger(len: usize) {
                let _ = crate::syscall_backend::svc_2::<
                    { crate::syscall_abi::APDU_SET_OUTGOING_LENGTH },
                >(len, 0);
            }
        }
    }

    /// Raw crypto service wrappers; see parameter and range contracts in `crate::syscall_abi`.
    pub mod crypto {
        /// Atomic symmetric encryption/decryption.
        pub mod cipher_do_final {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoCipherDoFinalParams) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_CIPHER_DO_FINAL }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// Kernel random-byte generation.
        pub mod random_generate {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoRandomGenerateParams) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_RANDOM_GENERATE }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// Atomic MAC computation or verification.
        pub mod mac_do_final {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoMacDoFinalParams) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_MAC_DO_FINAL }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// SD-scoped SCP03 key retrieval during SDDISPATCH only.
        pub mod load_scp03_key {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::Scp03LoadKeyParams) -> usize {
                crate::syscall_backend::svc_2::<
                    { crate::syscall_abi::SECURITY_DOMAIN_LOAD_SCP03_KEY },
                >(params as *const _ as usize, 0)
            }
        }

        /// Generate a P-256 key pair.
        pub mod ec_generate_keypair {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoEcGenerateKeypairParams) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_EC_GENERATE_KEYPAIR }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// Compute a raw ECDH secret.
        pub mod ecdh_do_final {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoEcdhDoFinalParams) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_ECDH_DO_FINAL }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// HKDF-SHA256 key derivation.
        pub mod hkdf_sha256 {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoHkdfSha256Params) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_HKDF_SHA256 }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }

        /// X9.63-SHA256 key derivation.
        pub mod x963_sha256 {
            /// Invoke this service synchronously with the supplied raw parameter record.
            /// Pointers must satisfy the record's documented range/lifetime/overlap
            /// contract. Return the ABI-encoded length, boolean or error word.
            pub fn trigger(params: &crate::syscall_abi::CryptoX963Sha256Params) -> usize {
                crate::syscall_backend::svc_2::<{ crate::syscall_abi::CRYPTO_X963_SHA256 }>(
                    params as *const _ as usize,
                    0,
                )
            }
        }
    }
}
