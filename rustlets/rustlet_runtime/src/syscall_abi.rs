#![forbid(unsafe_code)]

//! Rustlet syscall ABI.
//!
//! Crypto parameter records must be naturally aligned and wholly readable in
//! the active Rustlet's text, data, stack or shared page. The kernel snapshots
//! each record before writing any output. Buffers must remain in those windows;
//! outputs may only name writable data, stack or shared memory. Empty buffers
//! may use a null pointer and never cause a raw memory access.
//!
//! AES input/output buffers may coincide or partially overlap: input is staged
//! into output before one in-place transform, with no copy for identical base
//! addresses. Key and IV are consumed before output is modified. MAC output may
//! overlap input because publication follows computation. ECDH and KDF outputs
//! must be disjoint from all input buffers; keypair outputs must be mutually
//! disjoint. Invalid ranges, alignment or forbidden overlaps are rejected with
//! PermissionDenied before creating memory references. Reserved fields in SD-key,
//! EC-keypair and ECDH records must be zero; nonzero values are rejected with
//! PermissionDenied before the service touches its output.

/// Machine word used for Rustlet SVC arguments and return registers.
pub type SyscallWord = usize;

/// Immediate value encoded in the ARM `svc #imm8` instruction.
pub type SyscallNumber = u8;

/// Runtime-owned Rustlet syscall numbers.
///
/// The same values are used by the Rustlet runtime wrappers and by the kernel
/// syscall dispatch table. Keep all numbering changes in this enum so both
/// sides evolve together.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeSyscall {
    /// Enter app mode from kernel code.
    ///
    /// Kernel-side gate only.
    ///
    /// Inputs:
    /// - `r0`: kernel-owned entry descriptor at the authenticated kernel call site.
    ///
    /// The CPU profile recognizes this call only from the exact privileged
    /// entry site, builds a PSP exception frame and returns to user Thread mode.
    /// An invocation from a Rustlet follows ordinary syscall dispatch and
    /// cannot launch an application or acquire privileges.
    EnterApp = 0,

    /// Return from a Rustlet handler, explicit Rustlet exit, or bootstrap.
    ///
    /// Inputs:
    /// - `r0`: status `SW1`, or descriptor pointer for bootstrap returns.
    /// - `r1`: status `SW2`, or unused for bootstrap returns.
    /// - `r2`: [`RuntimeReturnKind`] discriminant.
    ///
    /// Returns:
    /// - `r0`: kernel-side acknowledgement only; the app does not resume.
    /// - `r1`: reserved.
    ReturnToKernel = 1,

    /// Allocate memory from the currently active Rustlet heap.
    ///
    /// Inputs:
    /// - `r0`: requested allocation size in bytes.
    /// - `r1`: requested alignment in bytes.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: allocated pointer, or `0` on failure.
    /// - `r1`: reserved.
    Alloc = 3,

    /// Free memory previously allocated from the active Rustlet heap.
    ///
    /// Inputs:
    /// - `r0`: pointer to free.
    /// - `r1`: allocation size in bytes.
    /// - `r2`: allocation alignment in bytes.
    ///
    /// Returns:
    /// - `r0`: currently unused, always `0`.
    /// - `r1`: reserved.
    Dealloc = 4,

    /// Receive the incoming APDU payload for the active command.
    ///
    /// Inputs:
    /// - `r0`: unused.
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: number of incoming bytes received.
    /// - `r1`: reserved.
    ///
    /// Repeated input reuses the payload. After output starts, returns zero
    /// without reading the transport or modifying the prepared response.
    ApduSetIncomingAndReceive = 6,

    /// Declare that the current APDU has an outgoing phase.
    ///
    /// Inputs:
    /// - `r0`: unused.
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: current requested `Le` value.
    /// - `r1`: reserved.
    ApduSetOutgoing = 7,

    /// Declare the outgoing APDU payload length.
    ///
    /// Inputs:
    /// - `r0`: outgoing payload length in bytes.
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: currently unused, always `0`.
    /// - `r1`: reserved.
    ApduSetOutgoingLength = 8,

    /// Run one symmetric cipher `doFinal` operation.
    ///
    /// All parameter pointers must target either the shared APDU page or the
    /// active Rustlet RAM windows validated by the kernel.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoCipherDoFinalParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: produced byte length on success, otherwise
    ///   [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoCipherDoFinal = 9,

    /// Fill a Rustlet-owned output buffer with random bytes.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoRandomGenerateParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: `0` on success, otherwise [`CRYPTO_RESULT_ERROR_FLAG`] ORed
    ///   with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoRandomGenerate = 10,

    /// Run one message authentication `doFinal` operation.
    ///
    /// This is an application-facing MAC service. SCP03 secure channel MACs are
    /// a separate kernel protocol concern.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoMacDoFinalParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: produced tag length for compute, `1` or `0` for verify,
    ///   otherwise [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a
    ///   [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoMacDoFinal = 11,

    /// Load one SCP03 static key object owned by the SD invoked by SDDISPATCH.
    ///
    /// The kernel grants this service only for the duration of its SDDISPATCH
    /// call. Ordinary process_apdu and install calls, including those of a
    /// Security Domain Rustlet, receive PermissionDenied. The caller cannot
    /// supply an owner AID or inherit authority from a selected SD.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`Scp03LoadKeyParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: loaded byte length on success, otherwise
    ///   [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    SecurityDomainLoadScp03Key = 12,

    /// Generate one fresh EC key pair for the requested curve.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoEcGenerateKeypairParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: `0` on success, otherwise [`CRYPTO_RESULT_ERROR_FLAG`] ORed
    ///   with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoEcGenerateKeypair = 13,

    /// Compute one EC Diffie-Hellman shared secret.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoEcdhDoFinalParams`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: produced shared secret byte length on success, otherwise
    ///   [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoEcdhDoFinal = 14,

    /// Derive one output key from caller-provided input keying material using HKDF-SHA256.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoHkdfSha256Params`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: produced output byte length on success, otherwise
    ///   [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoHkdfSha256 = 15,

    /// Derive key material with the ANSI X9.63 SHA-256 KDF used by SCP11.
    ///
    /// Inputs:
    /// - `r0`: pointer to [`CryptoX963Sha256Params`].
    /// - `r1`: unused.
    /// - `r2`: unused.
    ///
    /// Returns:
    /// - `r0`: produced output byte length on success, otherwise
    ///   [`CRYPTO_RESULT_ERROR_FLAG`] ORed with a [`CryptoErrorCode`] value.
    /// - `r1`: reserved.
    CryptoX963Sha256 = 16,
}

impl RuntimeSyscall {
    /// Return the immediate byte to encode in the SVC instruction.
    pub const fn number(self) -> SyscallNumber {
        self as SyscallNumber
    }
}

/// Kind value passed in `r2` to [`RuntimeSyscall::ReturnToKernel`].
#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeReturnKind {
    /// Normal handler return; `r0/r1` contain `SW1/SW2`.
    HandlerReturn = 0,
    /// Explicit Rustlet exit; `r0/r1` contain `SW1/SW2`.
    Exit = 1,
    /// Bootstrap return; `r0` contains the selected-app descriptor pointer.
    Descriptor = 2,
}

impl RuntimeReturnKind {
    /// Encode this discriminant in a machine-word register.
    pub const fn word(self) -> SyscallWord {
        self as SyscallWord
    }

    /// Decode 0 as HandlerReturn and 1 as Exit; all other words become Descriptor.
    /// This compatibility decoder does not reject unknown values.
    pub const fn from_word(word: SyscallWord) -> Self {
        match word {
            0 => Self::HandlerReturn,
            1 => Self::Exit,
            _ => Self::Descriptor,
        }
    }
}

/// SVC immediate for [`RuntimeSyscall::EnterApp`].
pub const ENTER_APP: SyscallNumber = RuntimeSyscall::EnterApp.number();
/// SVC immediate for [`RuntimeSyscall::ReturnToKernel`].
pub const RETURN_TO_KERNEL: SyscallNumber = RuntimeSyscall::ReturnToKernel.number();
/// SVC immediate for [`RuntimeSyscall::Alloc`].
pub const ALLOC: SyscallNumber = RuntimeSyscall::Alloc.number();
/// SVC immediate for [`RuntimeSyscall::Dealloc`].
pub const DEALLOC: SyscallNumber = RuntimeSyscall::Dealloc.number();
/// SVC immediate for [`RuntimeSyscall::ApduSetIncomingAndReceive`].
pub const APDU_SET_INCOMING_AND_RECEIVE: SyscallNumber =
    RuntimeSyscall::ApduSetIncomingAndReceive.number();
/// SVC immediate for [`RuntimeSyscall::ApduSetOutgoing`].
pub const APDU_SET_OUTGOING: SyscallNumber = RuntimeSyscall::ApduSetOutgoing.number();
/// SVC immediate for [`RuntimeSyscall::ApduSetOutgoingLength`].
pub const APDU_SET_OUTGOING_LENGTH: SyscallNumber = RuntimeSyscall::ApduSetOutgoingLength.number();
/// SVC immediate for [`RuntimeSyscall::CryptoCipherDoFinal`].
pub const CRYPTO_CIPHER_DO_FINAL: SyscallNumber = RuntimeSyscall::CryptoCipherDoFinal.number();
/// SVC immediate for [`RuntimeSyscall::CryptoRandomGenerate`].
pub const CRYPTO_RANDOM_GENERATE: SyscallNumber = RuntimeSyscall::CryptoRandomGenerate.number();
/// SVC immediate for [`RuntimeSyscall::CryptoMacDoFinal`].
pub const CRYPTO_MAC_DO_FINAL: SyscallNumber = RuntimeSyscall::CryptoMacDoFinal.number();
/// SVC immediate for [`RuntimeSyscall::SecurityDomainLoadScp03Key`].
pub const SECURITY_DOMAIN_LOAD_SCP03_KEY: SyscallNumber =
    RuntimeSyscall::SecurityDomainLoadScp03Key.number();
/// SVC immediate for [`RuntimeSyscall::CryptoEcGenerateKeypair`].
pub const CRYPTO_EC_GENERATE_KEYPAIR: SyscallNumber =
    RuntimeSyscall::CryptoEcGenerateKeypair.number();
/// SVC immediate for [`RuntimeSyscall::CryptoEcdhDoFinal`].
pub const CRYPTO_ECDH_DO_FINAL: SyscallNumber = RuntimeSyscall::CryptoEcdhDoFinal.number();
/// SVC immediate for [`RuntimeSyscall::CryptoHkdfSha256`].
pub const CRYPTO_HKDF_SHA256: SyscallNumber = RuntimeSyscall::CryptoHkdfSha256.number();
/// SVC immediate for [`RuntimeSyscall::CryptoX963Sha256`].
pub const CRYPTO_X963_SHA256: SyscallNumber = RuntimeSyscall::CryptoX963Sha256.number();

/// High-bit marker distinguishing a crypto error code from a success value.
pub const CRYPTO_RESULT_ERROR_FLAG: SyscallWord = 1usize << (usize::BITS - 1);

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Low-byte service error encoded alongside [`CRYPTO_RESULT_ERROR_FLAG`].
pub enum CryptoErrorCode {
    /// Key length does not match the algorithm.
    InvalidKeyLength = 1,
    /// Input, expected MAC tag, padding or parameter-buffer shape is invalid.
    InvalidBufferLength = 2,
    /// Output capacity or produced length is invalid.
    InvalidOutputLength = 3,
    /// Requested service or algorithm is unavailable.
    Unsupported = 4,
    /// Authority or memory-range/overlap validation failed.
    PermissionDenied = 5,
    /// Operation requires initialization that has not occurred.
    NotInitialized = 6,
    /// Referenced key or object is absent.
    NotFound = 7,
}

impl CryptoErrorCode {
    /// Encode this discriminant in a machine-word register.
    pub const fn word(self) -> SyscallWord {
        self as SyscallWord
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Atomic cipher request for [`RuntimeSyscall::CryptoCipherDoFinal`].
/// Key and IV are read before output changes; input/output may overlap under
/// the module contract. Output capacity must include any encryption padding.
pub struct CryptoCipherDoFinalParams {
    /// [`crate::Algorithm`] discriminant.
    pub algorithm: u8,
    /// [`crate::CipherMode`] discriminant.
    pub mode: u8,
    /// Pointer to the key bytes.
    pub key_ptr: *const u8,
    /// Key length in bytes.
    pub key_len: usize,
    /// Pointer to the IV bytes.
    pub iv_ptr: *const u8,
    /// IV length in bytes.
    pub iv_len: usize,
    /// Pointer to input bytes.
    pub input_ptr: *const u8,
    /// Input length in bytes.
    pub input_len: usize,
    /// Pointer to the output buffer.
    pub output_ptr: *mut u8,
    /// Output capacity in bytes.
    pub output_capacity: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Random request; fill exactly `output_len` writable bytes on success.
pub struct CryptoRandomGenerateParams {
    /// [`crate::RandomAlgorithm`] discriminant.
    pub algorithm: u8,
    /// Pointer to the output buffer.
    pub output_ptr: *mut u8,
    /// Output length in bytes.
    pub output_len: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Key retrieval request under the currently invoked SD's authority.
/// Usage selects the key role. Output remains caller-owned; no owner AID can
/// be supplied. Ordinary APDU/install calls are denied.
pub struct Scp03LoadKeyParams {
    /// Requested key set version.
    pub key_version: u8,
    /// Requested key identifier.
    pub key_id: u8,
    /// Requested key usage.
    pub usage: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved: u8,
    /// Pointer to the output buffer.
    pub output_ptr: *mut u8,
    /// Output capacity in bytes.
    pub output_capacity: usize,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Curve discriminant used in raw asymmetric service records.
pub enum CryptoEcCurve {
    /// NIST P-256, 32-byte big-endian scalar and 65-byte SEC1 public point.
    P256 = 1,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Key-generation request with mutually disjoint writable output ranges.
/// P-256 requires exactly 32 private and 65 public output bytes.
pub struct CryptoEcGenerateKeypairParams {
    /// [`CryptoEcCurve`] discriminant.
    pub curve: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved0: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved1: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved2: u8,
    /// Pointer to the private key output buffer.
    pub private_key_ptr: *mut u8,
    /// Output capacity in bytes for the private key.
    pub private_key_capacity: usize,
    /// Pointer to the public key output buffer.
    pub public_key_ptr: *mut u8,
    /// Output capacity in bytes for the public key.
    pub public_key_capacity: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// ECDH request; output must be disjoint from both key inputs.
/// P-256 consumes a 32-byte scalar and 65-byte SEC1 point and produces 32 bytes.
pub struct CryptoEcdhDoFinalParams {
    /// [`CryptoEcCurve`] discriminant.
    pub curve: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved0: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved1: u8,
    /// Reserved for future extensions. Must be zero.
    pub reserved2: u8,
    /// Pointer to the private key bytes.
    pub private_key_ptr: *const u8,
    /// Private key length in bytes.
    pub private_key_len: usize,
    /// Pointer to the peer public key bytes.
    pub peer_public_key_ptr: *const u8,
    /// Peer public key length in bytes.
    pub peer_public_key_len: usize,
    /// Pointer to the output shared secret buffer.
    pub output_ptr: *mut u8,
    /// Output capacity in bytes.
    pub output_capacity: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// HKDF-SHA256 request; output must be disjoint from IKM, salt and info.
/// The requested output length is `output_capacity`; empty salt/info are allowed.
pub struct CryptoHkdfSha256Params {
    /// Pointer to the input keying material.
    pub ikm_ptr: *const u8,
    /// Input keying material length in bytes.
    pub ikm_len: usize,
    /// Pointer to the optional salt bytes.
    pub salt_ptr: *const u8,
    /// Salt length in bytes.
    pub salt_len: usize,
    /// Pointer to the optional info/context bytes.
    pub info_ptr: *const u8,
    /// Info/context length in bytes.
    pub info_len: usize,
    /// Pointer to the output buffer.
    pub output_ptr: *mut u8,
    /// Output capacity in bytes.
    pub output_capacity: usize,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// X9.63-SHA256 request; output must be disjoint from both input ranges.
/// The requested output length is `output_capacity`.
pub struct CryptoX963Sha256Params {
    /// Pointer to the shared secret bytes.
    pub shared_secret_ptr: *const u8,
    /// Shared secret length in bytes.
    pub shared_secret_len: usize,
    /// Pointer to the shared info/context bytes.
    pub shared_info_ptr: *const u8,
    /// Shared info/context length in bytes.
    pub shared_info_len: usize,
    /// Pointer to the output buffer.
    pub output_ptr: *mut u8,
    /// Output capacity in bytes.
    pub output_capacity: usize,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Operation selector for [`CryptoMacDoFinalParams`].
pub enum CryptoMacOperation {
    /// Write a full tag to the output buffer and return its length.
    Compute = 1,
    /// Compare an expected tag; return 1 for match or 0 for mismatch.
    Verify = 2,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Atomic MAC request; AES-CMAC uses a 16- or 32-byte key.
/// Compute writes a full 16-byte tag after consuming input, permitting overlap.
/// Verify reads the expected tag and uses the kernel comparison; unused buffer
/// fields should be null/zero. Verify requires the complete 16-byte tag.
pub struct CryptoMacDoFinalParams {
    /// [`crate::MacAlgorithm`] discriminant.
    pub algorithm: u8,
    /// [`CryptoMacOperation`] discriminant.
    pub operation: u8,
    /// Pointer to the key bytes.
    pub key_ptr: *const u8,
    /// Key length in bytes.
    pub key_len: usize,
    /// Pointer to authenticated input bytes.
    pub input_ptr: *const u8,
    /// Authenticated input length in bytes.
    pub input_len: usize,
    /// Pointer to expected tag bytes for verify operations.
    pub expected_tag_ptr: *const u8,
    /// Expected tag length in bytes.
    pub expected_tag_len: usize,
    /// Pointer to output tag bytes for compute operations.
    pub output_ptr: *mut u8,
    /// Output tag capacity in bytes.
    pub output_capacity: usize,
}
