use core::marker::PhantomData;

#[cfg(test)]
#[path = "crypto_tests.rs"]
mod tests;

use crate::syscall_abi::{
    CryptoCipherDoFinalParams, CryptoEcGenerateKeypairParams, CryptoEcdhDoFinalParams,
    CryptoErrorCode, CryptoHkdfSha256Params, CryptoMacDoFinalParams, CryptoMacOperation,
    CryptoRandomGenerateParams, CryptoX963Sha256Params, CRYPTO_RESULT_ERROR_FLAG,
};

const AES_BLOCK_SIZE: usize = 16;
const AES128_KEY_SIZE: usize = 16;
const AES256_KEY_SIZE: usize = 32;
const MAC_TAG_SIZE: usize = 16;
const MAC_INPUT_CAPACITY: usize = 256;
const P256_PRIVATE_KEY_SIZE: usize = 32;
const P256_PUBLIC_KEY_UNCOMPRESSED_SIZE: usize = 65;
const P256_SHARED_SECRET_SIZE: usize = 32;

/// Cipher object has not been configured yet.
pub struct Uninitialized;

/// MAC or key-agreement object has been configured.
/// Cipher sessions instead use [`CipherReady`] to carry borrowed key material.
pub struct Ready;

/// Reserved state marker for future streaming operations; no current public
/// cipher transition creates this state.
pub struct Processing;

/// Symmetric cipher direction.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CipherMode {
    /// Encrypt plaintext into ciphertext.
    Encrypt = 1,
    /// Decrypt ciphertext into plaintext.
    Decrypt = 2,
}

/// Symmetric cipher algorithm.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Algorithm {
    /// AES-128 CBC; 16-byte key/IV and block-aligned input, no padding.
    Aes128CbcNoPadding = 1,
    /// AES-256 CBC; 32-byte key, 16-byte IV and block-aligned input.
    Aes256CbcNoPadding = 2,
    /// AES-128 CBC with `80 00...` padding, including a full block when aligned.
    Aes128CbcIso9797M2 = 3,
    /// AES-256 CBC with `80 00...` padding, including a full block when aligned.
    Aes256CbcIso9797M2 = 4,
    /// AES-128 ECB without padding. The current facade still requires a 16-byte IV.
    Aes128EcbNoPadding = 5,
    /// AES-256 ECB without padding. The current facade still requires a 16-byte IV.
    Aes256EcbNoPadding = 6,
}

/// Message authentication algorithm.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MacAlgorithm {
    /// AES-CMAC with a 16- or 32-byte key and a 16-byte full tag.
    AesCmac = 1,
}

/// Random generator algorithm.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RandomAlgorithm {
    /// Kernel-provided generator; this name does not certify target entropy quality.
    SecureRandom = 1,
}

/// Supported elliptic curves for Rustlet-facing asymmetric crypto.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EcCurve {
    /// NIST P-256 with 32-byte scalars and 65-byte SEC1 uncompressed public keys.
    P256 = 1,
}

/// Error returned by Rustlet-facing crypto operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CryptoError {
    /// Key encoding length does not match the requested algorithm.
    InvalidKeyLength,
    /// Input, IV, expected MAC tag, padding or another buffer shape is invalid.
    InvalidBufferLength,
    /// Output capacity or produced length is invalid for the operation.
    InvalidOutputLength,
    /// Algorithm/service is unavailable, or the returned error code is unknown.
    Unsupported,
    /// The caller lacks authority or a buffer range/overlap fails kernel validation.
    PermissionDenied,
    /// The service/session has not been initialized for this operation.
    NotInitialized,
    /// The requested key or referenced cryptographic object is absent.
    NotFound,
}

/// Fixed-size AES-CMAC authentication tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MacTag(
    /// Full 16-byte AES-CMAC tag in transmission order.
    pub [u8; MAC_TAG_SIZE],
);

impl AsRef<[u8]> for MacTag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl CryptoError {
    /// Decode the low byte of a kernel error code; unknown values map to Unsupported.
    /// Strip the ABI error flag before calling; this does not decode success values.
    pub const fn from_code(code: usize) -> Self {
        match code as u8 {
            value if value == CryptoErrorCode::InvalidKeyLength as u8 => Self::InvalidKeyLength,
            value if value == CryptoErrorCode::InvalidBufferLength as u8 => {
                Self::InvalidBufferLength
            }
            value if value == CryptoErrorCode::InvalidOutputLength as u8 => {
                Self::InvalidOutputLength
            }
            value if value == CryptoErrorCode::PermissionDenied as u8 => Self::PermissionDenied,
            value if value == CryptoErrorCode::NotInitialized as u8 => Self::NotInitialized,
            value if value == CryptoErrorCode::NotFound as u8 => Self::NotFound,
            _ => Self::Unsupported,
        }
    }
}

/// Backend used by typed cipher sessions.
///
/// Runtime code normally uses the internal syscall backend. Tests may provide a
/// local backend to exercise the typestate API without entering the kernel.
pub trait CryptoBackend {
    /// Execute one complete operation with borrowed, validated cipher parameters.
    ///
    /// Key/IV loans last through this synchronous call only. Implementations must
    /// not retain their addresses. Safe implementations cannot store the borrowed
    /// references in a longer-lived backend. Return the produced prefix length
    /// or a service error; do not publish output after an error.
    fn cipher_do_final(
        &mut self,
        parameters: &CipherReady<'_>,
        input: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError>;

    /// Compute one complete MAC operation.
    fn mac_compute(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        output: &mut [u8; MAC_TAG_SIZE],
    ) -> Result<(), CryptoError>;

    /// Verify one complete MAC operation using kernel-side comparison.
    fn mac_verify(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        expected_tag: &[u8],
    ) -> Result<bool, CryptoError>;
}

/// Kernel-backed crypto provider returned by [`crate::RustletCtx::crypto`].
///
/// Calls are synchronous and do not allocate Rustlet heap buffers. Input/output
/// slices remain borrowed through each call. Range validation and errors come
/// from the active kernel; a host build does not emulate these services.
///
/// The provider retains no cipher key/IV addresses. A ready [`Cipher`] owns
/// those Rust borrows and lends them to one atomic operation.
pub struct CryptoProvider {
    backend: SyscallCryptoBackend,
}

impl CryptoProvider {
    pub(crate) const fn new() -> Self {
        Self {
            backend: SyscallCryptoBackend::new(),
        }
    }

    /// Derive key material with the ANSI X9.63 SHA-256 KDF.
    /// Writes into `output` and returns the produced byte count. Inputs are
    /// borrowed only for this call; output must not overlap them at the ABI
    /// boundary. Kernel input/capacity errors are returned as `CryptoError`.
    pub fn derive_x963_sha256(
        &mut self,
        shared_secret: &[u8],
        shared_info: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        self.x963_sha256(shared_secret, shared_info, output)
    }

    /// Compute a MAC over one already assembled message.
    ///
    /// This one-shot form avoids the 256-byte accumulation buffer carried by
    /// [`Mac`]. It is useful when a Rustlet already owns a contiguous message,
    /// especially on targets with small application stacks. AES-CMAC accepts
    /// 16- or 32-byte keys and returns a full 16-byte tag. Invalid key lengths
    /// fail before entering the kernel; range/service errors propagate.
    pub fn compute_mac(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
    ) -> Result<MacTag, CryptoError> {
        let mut tag = [0u8; MAC_TAG_SIZE];
        self.backend.mac_compute(key, algorithm, input, &mut tag)?;
        Ok(MacTag(tag))
    }

    fn ec_generate_keypair(
        &mut self,
        curve: EcCurve,
        private_key: &mut [u8; P256_PRIVATE_KEY_SIZE],
        public_key: &mut [u8; P256_PUBLIC_KEY_UNCOMPRESSED_SIZE],
    ) -> Result<(), CryptoError> {
        let params = CryptoEcGenerateKeypairParams {
            curve: curve as u8,
            reserved0: 0,
            reserved1: 0,
            reserved2: 0,
            private_key_ptr: private_key.as_mut_ptr(),
            private_key_capacity: private_key.len(),
            public_key_ptr: public_key.as_mut_ptr(),
            public_key_capacity: public_key.len(),
        };
        let result = crate::syscall::runtime::crypto::ec_generate_keypair::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(())
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }

    fn ecdh_do_final(
        &mut self,
        curve: EcCurve,
        private_key: &[u8; P256_PRIVATE_KEY_SIZE],
        peer_public_key: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        let params = CryptoEcdhDoFinalParams {
            curve: curve as u8,
            reserved0: 0,
            reserved1: 0,
            reserved2: 0,
            private_key_ptr: private_key.as_ptr(),
            private_key_len: private_key.len(),
            peer_public_key_ptr: peer_public_key.as_ptr(),
            peer_public_key_len: peer_public_key.len(),
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = crate::syscall::runtime::crypto::ecdh_do_final::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(result)
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }

    fn hkdf_sha256(
        &mut self,
        ikm: &[u8],
        salt: &[u8],
        info: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        let params = CryptoHkdfSha256Params {
            ikm_ptr: ikm.as_ptr(),
            ikm_len: ikm.len(),
            salt_ptr: salt.as_ptr(),
            salt_len: salt.len(),
            info_ptr: info.as_ptr(),
            info_len: info.len(),
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = crate::syscall::runtime::crypto::hkdf_sha256::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(result)
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }

    fn x963_sha256(
        &mut self,
        shared_secret: &[u8],
        shared_info: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        let params = CryptoX963Sha256Params {
            shared_secret_ptr: shared_secret.as_ptr(),
            shared_secret_len: shared_secret.len(),
            shared_info_ptr: shared_info.as_ptr(),
            shared_info_len: shared_info.len(),
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = crate::syscall::runtime::crypto::x963_sha256::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(result)
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }
}

impl CryptoBackend for CryptoProvider {
    fn cipher_do_final(
        &mut self,
        parameters: &CipherReady<'_>,
        input: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        self.backend.cipher_do_final(parameters, input, output)
    }

    fn mac_compute(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        output: &mut [u8; MAC_TAG_SIZE],
    ) -> Result<(), CryptoError> {
        self.backend.mac_compute(key, algorithm, input, output)
    }

    fn mac_verify(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        expected_tag: &[u8],
    ) -> Result<bool, CryptoError> {
        self.backend.mac_verify(key, algorithm, input, expected_tag)
    }
}

struct SyscallCryptoBackend;

impl SyscallCryptoBackend {
    const fn new() -> Self {
        Self
    }
}

impl CryptoBackend for SyscallCryptoBackend {
    fn cipher_do_final(
        &mut self,
        parameters: &CipherReady<'_>,
        input: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        // Raw addresses exist only in this synchronous ABI record. The borrowed
        // state keeps key/IV storage alive and immutable throughout the SVC.
        let params = CryptoCipherDoFinalParams {
            algorithm: parameters.algorithm as u8,
            mode: parameters.mode as u8,
            key_ptr: parameters.key.as_ptr(),
            key_len: parameters.key.len(),
            iv_ptr: parameters.iv.as_ptr(),
            iv_len: parameters.iv.len(),
            input_ptr: input.as_ptr(),
            input_len: input.len(),
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = crate::syscall::runtime::crypto::cipher_do_final::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(result)
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }

    fn mac_compute(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        output: &mut [u8; MAC_TAG_SIZE],
    ) -> Result<(), CryptoError> {
        if !mac_key_len_matches_algorithm(key.len(), algorithm) {
            return Err(CryptoError::InvalidKeyLength);
        }

        let params = CryptoMacDoFinalParams {
            algorithm: algorithm as u8,
            operation: CryptoMacOperation::Compute as u8,
            key_ptr: key.as_ptr(),
            key_len: key.len(),
            input_ptr: input.as_ptr(),
            input_len: input.len(),
            expected_tag_ptr: core::ptr::null(),
            expected_tag_len: 0,
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let result = crate::syscall::runtime::crypto::mac_do_final::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            if result == MAC_TAG_SIZE {
                Ok(())
            } else {
                Err(CryptoError::InvalidOutputLength)
            }
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }

    fn mac_verify(
        &mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
        input: &[u8],
        expected_tag: &[u8],
    ) -> Result<bool, CryptoError> {
        if !mac_key_len_matches_algorithm(key.len(), algorithm) {
            return Err(CryptoError::InvalidKeyLength);
        }

        let params = CryptoMacDoFinalParams {
            algorithm: algorithm as u8,
            operation: CryptoMacOperation::Verify as u8,
            key_ptr: key.as_ptr(),
            key_len: key.len(),
            input_ptr: input.as_ptr(),
            input_len: input.len(),
            expected_tag_ptr: expected_tag.as_ptr(),
            expected_tag_len: expected_tag.len(),
            output_ptr: core::ptr::null_mut(),
            output_capacity: 0,
        };
        let result = crate::syscall::runtime::crypto::mac_do_final::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(result != 0)
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }
}

fn key_len_matches_algorithm(len: usize, algorithm: Algorithm) -> bool {
    match algorithm {
        Algorithm::Aes128CbcNoPadding | Algorithm::Aes128CbcIso9797M2 => len == AES128_KEY_SIZE,
        Algorithm::Aes256CbcNoPadding | Algorithm::Aes256CbcIso9797M2 => len == AES256_KEY_SIZE,
        Algorithm::Aes128EcbNoPadding => len == AES128_KEY_SIZE,
        Algorithm::Aes256EcbNoPadding => len == AES256_KEY_SIZE,
    }
}

fn mac_key_len_matches_algorithm(len: usize, algorithm: MacAlgorithm) -> bool {
    match algorithm {
        MacAlgorithm::AesCmac => len == AES128_KEY_SIZE || len == AES256_KEY_SIZE,
    }
}

/// Random-data facade using a synchronous kernel service.
/// No Rustlet heap allocation is made. Availability and entropy quality depend
/// on the board/backend; QEMU success is not cryptographic qualification.
pub struct RandomData {
    algorithm: RandomAlgorithm,
}

impl RandomData {
    /// Construct the facade without checking kernel availability or consuming
    /// entropy. The current constructor always succeeds.
    pub fn get_instance(algorithm: RandomAlgorithm) -> Result<Self, CryptoError> {
        Ok(Self { algorithm })
    }

    /// Fill the complete output buffer or return the kernel error.
    /// Do not consume output on error; no rollback of partial writes is promised.
    pub fn generate_data(&mut self, output: &mut [u8]) -> Result<(), CryptoError> {
        // The kernel validates that the destination is writable Rustlet memory.
        let params = CryptoRandomGenerateParams {
            algorithm: self.algorithm as u8,
            output_ptr: output.as_mut_ptr(),
            output_len: output.len(),
        };
        let result = crate::syscall::runtime::crypto::random_generate::trigger(&params);
        if result & CRYPTO_RESULT_ERROR_FLAG == 0 {
            Ok(())
        } else {
            Err(CryptoError::from_code(result & !CRYPTO_RESULT_ERROR_FLAG))
        }
    }
}

/// Validated cipher state borrowing key and IV without copying.
///
/// Created by [`Cipher::init`]. The key length matches the algorithm; the IV
/// is exactly 16 bytes, including for ECB to preserve the current ABI contract.
/// This state carries actual Rust references. A backend only borrows the record
/// for one atomic operation.
///
/// A backend cannot extend an input loan into its own longer-lived storage:
///
/// ```compile_fail
/// use rustlet_runtime::CipherReady;
/// fn retain<'backend>(saved: &mut Option<&'backend [u8]>, params: &CipherReady<'_>) {
///     *saved = Some(params.key());
/// }
/// ```
pub struct CipherReady<'key> {
    key: &'key [u8],
    iv: &'key [u8; AES_BLOCK_SIZE],
    mode: CipherMode,
    algorithm: Algorithm,
}

impl CipherReady<'_> {
    /// Borrow the validated key for the current backend call.
    pub fn key(&self) -> &[u8] {
        self.key
    }

    /// Borrow the 16-byte IV for the current backend call.
    pub fn iv(&self) -> &[u8; AES_BLOCK_SIZE] {
        self.iv
    }

    /// Return the requested encryption/decryption direction.
    pub fn mode(&self) -> CipherMode {
        self.mode
    }

    /// Return the algorithm whose key length was checked during initialization.
    pub fn algorithm(&self) -> Algorithm {
        self.algorithm
    }
}

/// Typestate cipher session with exclusive access to its backend.
///
/// `Cipher<Uninitialized>` contains no key/IV storage. Initialization consumes
/// it and produces `Cipher<CipherReady<'key>>`, borrowing those bytes through
/// finalization or abandonment. Backend and key lifetimes are independent, so
/// a long-lived provider can process successive short-lived keys.
///
/// No key/IV copy, heap allocation or runtime initialization flag is needed.
/// [`Cipher::finish`] consumes the ready session on both success and error.
/// Dropping an unfinished session releases its loans without a kernel call.
pub struct Cipher<'backend, State> {
    backend: &'backend mut dyn CryptoBackend,
    state: State,
}

impl<'backend> Cipher<'backend, Uninitialized> {
    /// Exclusively borrow a backend for an unconfigured session.
    #[inline(always)]
    pub fn new(backend: &'backend mut dyn CryptoBackend) -> Self {
        Self {
            backend,
            state: Uninitialized,
        }
    }

    /// Validate and borrow a key/IV, consuming the uninitialized session.
    ///
    /// The IV must be 16 bytes even for ECB (otherwise InvalidBufferLength);
    /// the key must match the algorithm (otherwise InvalidKeyLength).
    /// Validation makes no backend call. Both arrays remain immutably borrowed
    /// while the returned session can still be used.
    ///
    /// The compiler rejects expired or mutated key material and reuse of a
    /// consumed session. These examples compile-check the actual public API:
    ///
    /// ```compile_fail,E0597
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// let iv = [0; 16];
    /// let ready;
    /// {
    ///     let key = [0; 16];
    ///     ready = Cipher::new(&mut provider)
    ///     .init(&key, &iv, CipherMode::Encrypt, Algorithm::Aes128CbcNoPadding)
    ///     .unwrap();
    /// }
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ```
    ///
    /// ```compile_fail,E0597
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// let key = [0; 16];
    /// let ready;
    /// {
    ///     let iv = [0; 16];
    ///     ready = Cipher::new(&mut provider)
    ///     .init(&key, &iv, CipherMode::Encrypt, Algorithm::Aes128CbcNoPadding)
    ///     .unwrap();
    /// }
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ```
    ///
    /// ```compile_fail,E0506
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// let mut key = [0; 16];
    /// let iv = [0; 16];
    /// let ready = Cipher::new(&mut provider)
    ///     .init(&key, &iv, CipherMode::Encrypt, Algorithm::Aes128CbcNoPadding)
    ///     .unwrap();
    /// key[0] = 1;
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ```
    ///
    /// ```compile_fail,E0506
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// let key = [0; 16];
    /// let mut iv = [0; 16];
    /// let ready = Cipher::new(&mut provider)
    ///     .init(&key, &iv, CipherMode::Encrypt, Algorithm::Aes128CbcNoPadding)
    ///     .unwrap();
    /// iv[0] = 1;
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ```
    ///
    /// ```compile_fail,E0382
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// let key = [0; 16];
    /// let iv = [0; 16];
    /// let ready = Cipher::new(&mut provider)
    ///     .init(&key, &iv, CipherMode::Encrypt, Algorithm::Aes128CbcNoPadding)
    ///     .unwrap();
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ready.finish(&[0; 16], &mut [0; 16]);
    /// ```
    ///
    /// ```compile_fail,E0599
    /// use rustlet_runtime::{Algorithm, Cipher, CipherMode, RustletCtx};
    /// let mut ctx = RustletCtx::new();
    /// let mut provider = ctx.crypto();
    /// Cipher::new(&mut provider).finish(&[0; 16], &mut [0; 16]);
    /// ```
    // Keep the borrowed transition in its caller so the optimizer can eliminate
    // aggregate Result/session temporaries on ARMv6-M.
    #[inline(always)]
    pub fn init<'key>(
        self,
        key: &'key [u8],
        iv: &'key [u8],
        mode: CipherMode,
        algorithm: Algorithm,
    ) -> Result<Cipher<'backend, CipherReady<'key>>, CryptoError> {
        let iv = iv
            .try_into()
            .map_err(|_| CryptoError::InvalidBufferLength)?;
        if !key_len_matches_algorithm(key.len(), algorithm) {
            return Err(CryptoError::InvalidKeyLength);
        }
        Ok(Cipher {
            backend: self.backend,
            state: CipherReady {
                key,
                iv,
                mode,
                algorithm,
            },
        })
    }
}

/// Typestate MAC session.
///
/// Data is accumulated Rustlet-side with `update`. The kernel sees only one
/// final MAC syscall when `compute` or `verify` consumes the ready session.
/// Owns a 256-byte message buffer and a 32-byte key buffer inline; moving the
/// typestate may copy them. Use `CryptoProvider::compute_mac` when the message
/// already exists. There is no heap allocation or automatic zeroizing Drop.
pub struct Mac<'a, State> {
    backend: &'a mut dyn CryptoBackend,
    key: [u8; AES256_KEY_SIZE],
    key_len: usize,
    algorithm: MacAlgorithm,
    input: [u8; MAC_INPUT_CAPACITY],
    input_len: usize,
    _state: PhantomData<State>,
}

impl<'a> Mac<'a, Uninitialized> {
    /// Create a new unconfigured MAC session.
    pub fn new(backend: &'a mut dyn CryptoBackend) -> Self {
        Self {
            backend,
            key: [0; AES256_KEY_SIZE],
            key_len: 0,
            algorithm: MacAlgorithm::AesCmac,
            input: [0; MAC_INPUT_CAPACITY],
            input_len: 0,
            _state: PhantomData,
        }
    }

    /// Copy a 16- or 32-byte key into this session and reset its message length.
    /// Other key lengths return `InvalidKeyLength`; the key borrow then ends.
    pub fn init(
        mut self,
        key: &[u8],
        algorithm: MacAlgorithm,
    ) -> Result<Mac<'a, Ready>, CryptoError> {
        if !mac_key_len_matches_algorithm(key.len(), algorithm) {
            return Err(CryptoError::InvalidKeyLength);
        }

        self.key[..key.len()].copy_from_slice(key);
        Ok(Mac {
            backend: self.backend,
            key: self.key,
            key_len: key.len(),
            algorithm,
            input: self.input,
            input_len: 0,
            _state: PhantomData,
        })
    }
}

impl Mac<'_, Ready> {
    /// Copy bytes into the inline message accumulator.
    /// More than 256 total bytes returns `InvalidBufferLength` without changing
    /// the accumulated prefix. This does not call a streaming kernel service.
    pub fn update(&mut self, data: &[u8]) -> Result<(), CryptoError> {
        let Some(end) = self.input_len.checked_add(data.len()) else {
            return Err(CryptoError::InvalidBufferLength);
        };
        if end > self.input.len() {
            return Err(CryptoError::InvalidBufferLength);
        }

        self.input[self.input_len..end].copy_from_slice(data);
        self.input_len = end;
        Ok(())
    }

    /// Finalize the MAC and return the computed tag.
    pub fn compute(self) -> Result<MacTag, CryptoError> {
        let mut tag = [0u8; MAC_TAG_SIZE];
        self.backend.mac_compute(
            &self.key[..self.key_len],
            self.algorithm,
            &self.input[..self.input_len],
            &mut tag,
        )?;
        Ok(MacTag(tag))
    }

    /// Finalize the MAC and compare the tag in the kernel.
    /// The expected tag must be the complete 16-byte AES-CMAC tag.
    /// `Ok(false)` is an authentication mismatch, not a service error.
    /// Invalid tag lengths and kernel failures return `Err`; the session is
    /// consumed on every outcome.
    pub fn verify(self, expected_tag: &[u8]) -> Result<bool, CryptoError> {
        self.backend.mac_verify(
            &self.key[..self.key_len],
            self.algorithm,
            &self.input[..self.input_len],
            expected_tag,
        )
    }
}

impl Cipher<'_, CipherReady<'_>> {
    /// Always return `Unsupported` without reading input or changing output.
    /// The ready session remains available for `finish`; streaming is not implemented.
    pub fn update(&mut self, _input: &[u8], _output: &mut [u8]) -> Result<usize, CryptoError> {
        Err(CryptoError::Unsupported)
    }

    /// Complete one cipher operation and consume the ready session on any outcome.
    /// Return the produced prefix length. No-padding input must be block aligned;
    /// padded encryption needs room for the added block/padding. Kernel errors
    /// include invalid input/padding, insufficient output and denied ranges.
    /// Do not use partially written output on failure.
    #[inline(always)]
    pub fn finish(self, input: &[u8], output: &mut [u8]) -> Result<usize, CryptoError> {
        self.backend.cipher_do_final(&self.state, input, output)
    }
}

/// Fixed-size Rustlet-owned P-256 private key.
/// Stores a big-endian scalar inline. `Copy` and `Debug` can duplicate/expose
/// secrets; this type has no zeroizing Drop and performs no scalar validation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EcPrivateKey {
    curve: EcCurve,
    bytes: [u8; P256_PRIVATE_KEY_SIZE],
}

impl EcPrivateKey {
    /// Build a P-256 private key wrapper from raw scalar bytes.
    pub const fn p256_from_bytes(bytes: [u8; P256_PRIVATE_KEY_SIZE]) -> Self {
        Self {
            curve: EcCurve::P256,
            bytes,
        }
    }

    /// Return the encoded private key bytes.
    pub fn as_bytes(&self) -> &[u8; P256_PRIVATE_KEY_SIZE] {
        &self.bytes
    }

    /// Return the curve carried by this key.
    pub fn curve(&self) -> EcCurve {
        self.curve
    }
}

/// Fixed-size Rustlet-owned P-256 public key encoded as SEC1 uncompressed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EcPublicKey {
    curve: EcCurve,
    bytes: [u8; P256_PUBLIC_KEY_UNCOMPRESSED_SIZE],
}

impl EcPublicKey {
    /// Return the SEC1 public key bytes.
    pub fn as_bytes(&self) -> &[u8; P256_PUBLIC_KEY_UNCOMPRESSED_SIZE] {
        &self.bytes
    }

    /// Return the curve carried by this key.
    pub fn curve(&self) -> EcCurve {
        self.curve
    }
}

/// Freshly generated EC key pair kept entirely in Rustlet memory.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EcKeyPair {
    private_key: EcPrivateKey,
    public_key: EcPublicKey,
}

impl EcKeyPair {
    /// Generate a new key pair for the requested curve.
    pub fn generate(crypto: &mut CryptoProvider, curve: EcCurve) -> Result<Self, CryptoError> {
        match curve {
            EcCurve::P256 => {
                let mut private = [0u8; P256_PRIVATE_KEY_SIZE];
                let mut public = [0u8; P256_PUBLIC_KEY_UNCOMPRESSED_SIZE];
                crypto.ec_generate_keypair(curve, &mut private, &mut public)?;
                Ok(Self {
                    private_key: EcPrivateKey {
                        curve,
                        bytes: private,
                    },
                    public_key: EcPublicKey {
                        curve,
                        bytes: public,
                    },
                })
            }
        }
    }

    /// Return the private key.
    pub fn private_key(&self) -> EcPrivateKey {
        self.private_key
    }

    /// Return the public key.
    pub fn public_key(&self) -> EcPublicKey {
        self.public_key
    }
}

/// Java Card-style key agreement object backed by one atomic kernel syscall.
pub struct KeyAgreement<'a, State> {
    crypto: &'a mut CryptoProvider,
    curve: EcCurve,
    private_key: [u8; P256_PRIVATE_KEY_SIZE],
    _state: PhantomData<State>,
}

impl<'a> KeyAgreement<'a, Uninitialized> {
    /// Create a new unconfigured key agreement object.
    pub fn new(crypto: &'a mut CryptoProvider) -> Self {
        Self {
            crypto,
            curve: EcCurve::P256,
            private_key: [0; P256_PRIVATE_KEY_SIZE],
            _state: PhantomData,
        }
    }

    /// Copy the 32-byte scalar into this object without validating it yet.
    /// The input borrow ends immediately. Invalid scalars are rejected by the
    /// kernel when an agreement is performed.
    pub fn init(
        mut self,
        private_key: &EcPrivateKey,
    ) -> Result<KeyAgreement<'a, Ready>, CryptoError> {
        self.curve = private_key.curve();
        self.private_key.copy_from_slice(private_key.as_bytes());
        Ok(KeyAgreement {
            crypto: self.crypto,
            curve: self.curve,
            private_key: self.private_key,
            _state: PhantomData,
        })
    }
}

impl KeyAgreement<'_, Ready> {
    /// Derive the 32-byte raw P-256 shared secret into caller storage.
    /// Output needs at least 32 bytes; the peer is a 65-byte SEC1 uncompressed
    /// point validated by the kernel. Return the produced length or a kernel
    /// error. Inputs and output must not overlap at the ABI boundary.
    /// The ready object can perform another agreement; this is not a KDF.
    pub fn generate_secret(
        &mut self,
        peer_public_key: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        if output.len() < P256_SHARED_SECRET_SIZE {
            return Err(CryptoError::InvalidOutputLength);
        }
        self.crypto
            .ecdh_do_final(self.curve, &self.private_key, peer_public_key, output)
    }

    /// Perform ECDH, then HKDF-SHA256 into caller storage; return its byte count.
    /// Uses a temporary 32-byte shared-secret array and two synchronous syscalls.
    /// The temporary is filled with zero after HKDF returns, but this is not a
    /// guaranteed volatile erasure. Salt/info are borrowed for this call.
    /// Errors from either step propagate; do not consume output on failure.
    pub fn derive_hkdf_sha256(
        &mut self,
        peer_public_key: &[u8],
        salt: &[u8],
        info: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        let mut shared_secret = [0u8; P256_SHARED_SECRET_SIZE];
        let shared_len = self.generate_secret(peer_public_key, &mut shared_secret)?;
        let result = self
            .crypto
            .hkdf_sha256(&shared_secret[..shared_len], salt, info, output);
        shared_secret.fill(0);
        result
    }
}
