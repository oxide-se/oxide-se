//! Typed RPC codecs and clients. The kernel transports bytes and never decodes Postcard.
//! Calls are synchronous and non-nested. Addressing an AID leaves APDU selection
//! unchanged. Each invocation starts with a default callee Session and discards it
//! on return or failure, even for consecutive calls to the same AID. Successful
//! persistent changes participate in the caller's transaction.

use crate::{Aid, ApduStatus, RustletCtx};
use serde::{de::DeserializeOwned, Serialize};

/// Maximum encoded request, excluding the kernel's 17-byte caller identity.
pub const REQUEST_CAPACITY: usize = 238;
/// Maximum encoded response.
pub const RESPONSE_CAPACITY: usize = 255;

/// Failure to encode, transport, dispatch or decode an RPC.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The request or response does not fit its bounded buffer.
    Capacity,
    /// Invalid Postcard data or incompatible response type.
    Codec,
    /// Kernel transport failure or remote APDU-style status word.
    Remote(usize),
    /// SVC execution is unavailable on the host.
    Unsupported,
}

/// Encode and invoke a typed request without heap allocation.
///
/// Uses one 255-byte stack buffer, copied into the callee gateway by the kernel.
/// The response replaces the request. Returned values own their data, so no
/// reference can escape the temporary buffer. Host calls return `Unsupported`.
pub fn call<Q: Serialize, R: DeserializeOwned>(target: Aid, request: &Q) -> Result<R, Error> {
    let mut bytes = [0u8; RESPONSE_CAPACITY];
    let len = crate::postcard::to_slice(request, &mut bytes[..REQUEST_CAPACITY])
        .map_err(|_| Error::Capacity)?
        .len();
    let params = crate::syscall_abi::RpcCallParams {
        target,
        buffer: bytes.as_mut_ptr(),
        request_len: len,
        capacity: bytes.len(),
    };
    #[cfg(not(target_arch = "arm"))]
    {
        let _ = params;
        Err(Error::Unsupported)
    }
    #[cfg(target_arch = "arm")]
    {
        // SAFETY: params and its exclusive buffer stay live across the synchronous call.
        let result = unsafe { invoke(&params) };
        if result & crate::syscall_abi::RPC_ERROR != 0 {
            return Err(Error::Remote(result & !crate::syscall_abi::RPC_ERROR));
        }
        let response = bytes.get(..result).ok_or(Error::Capacity)?;
        let (value, rest) = crate::postcard::take_from_bytes(response).map_err(|_| Error::Codec)?;
        if !rest.is_empty() {
            return Err(Error::Codec);
        }
        Ok(value)
    }
}

// Save every callee-saved register on the caller's private stack. The kernel can
// resume at the instruction after SVC using a fresh basic exception frame;
// this epilogue restores the original registers and return address. 40 bytes
// preserve the mandatory eight-byte stack alignment on both M0+ and mainline.
#[cfg(target_arch = "arm")]
#[unsafe(naked)]
unsafe extern "C" fn invoke(_params: *const crate::syscall_abi::RpcCallParams) -> usize {
    core::arch::naked_asm!(
        "push {{r4-r7, lr}}",
        "mov r4, r8", "mov r5, r9", "mov r6, r10", "mov r7, r11",
        "push {{r4-r7}}", "sub sp, #4",
        "svc {number}",
        "add sp, #4", "pop {{r4-r7}}",
        "mov r8, r4", "mov r9, r5", "mov r10, r6", "mov r11, r7",
        "pop {{r4-r7}}", "pop {{r1}}", "bx r1",
        number = const crate::syscall_abi::RuntimeSyscall::RpcCall as u8,
    );
}

/// Decode the kernel identity prefix and an owned typed request.
/// Only call from `process_rpc`; ordinary APDU bytes carry no caller authority.
pub fn request<Q: DeserializeOwned>(ctx: &RustletCtx) -> Result<(Aid, Q), ApduStatus> {
    let bytes = ctx.incoming_data();
    if bytes.len() < 17 || bytes[0] == 0 || bytes[0] > 16 {
        return Err(ApduStatus::wrong_data());
    }
    let caller = Aid::new(&bytes[1..1 + bytes[0] as usize]);
    let (value, rest) =
        crate::postcard::take_from_bytes(&bytes[17..]).map_err(|_| ApduStatus::wrong_data())?;
    if !rest.is_empty() {
        return Err(ApduStatus::wrong_data());
    }
    Ok((caller, value))
}

/// Encode a response directly into the callee gateway, without transport APDU SVCs.
pub fn respond<R: Serialize>(ctx: &mut RustletCtx, response: &R) -> ApduStatus {
    match crate::postcard::to_slice(response, &mut ctx.data[..RESPONSE_CAPACITY]) {
        Ok(bytes) => {
            let len = bytes.len();
            ctx.declare_outgoing_length(len);
            ApduStatus::success()
        }
        Err(_) => ApduStatus::wrong_length(),
    }
}

/// Declare a typed client, a server trait and its Postcard dispatcher.
///
/// Methods are numbered in declaration order. Changing their order or types
/// requires a version change. Interface identifiers and versions are checked by
/// the Rustlet dispatcher only. Service methods receive the kernel's caller AID.
///
/// ```
/// rustlet_runtime::rpc_interface! {
///     pub mod counter, id = 42, version = 1 {
///         fn add(value: u32) -> u32;
///         fn value() -> u32;
///     }
/// }
/// ```
#[macro_export]
macro_rules! rpc_interface {
    ($vis:vis mod $name:ident, id = $id:expr, version = $version:literal {
        $(fn $method:ident($($arg:ident: $ty:ty),*) -> $ret:ty;)*
    }) => {
        #[allow(missing_docs)]
        $vis mod $name {
            use $crate::{Aid, ApduStatus, RustletCtx};
            use $crate::serde as __serde;
            #[allow(non_camel_case_types)]
            #[derive($crate::serde::Serialize, $crate::serde::Deserialize)]
            #[serde(crate = "__serde")]
            enum Request { $($method { $($arg: $ty),* }),* }
            pub trait Service { $(fn $method(&mut self, caller: &Aid, $($arg: $ty),*) -> $ret;)* }
            pub struct Client { target: Aid }
            impl Client {
                pub const fn new(target: Aid) -> Self { Self { target } }
                $(pub fn $method(&self, $($arg: $ty),*) -> Result<$ret, $crate::rpc::Error> {
                    $crate::rpc::call(self.target, &($id as u32, $version as u16, Request::$method { $($arg),* }))
                })*
            }
            pub fn dispatch(service: &mut impl Service, ctx: &mut RustletCtx) -> ApduStatus {
                let (caller, (id, version, request)) = match $crate::rpc::request::<(u32, u16, Request)>(ctx) {
                    Ok(value) => value, Err(status) => return status,
                };
                if id != $id || version != $version { return ApduStatus::instruction_not_supported(); }
                match request { $(Request::$method { $($arg),* } => {
                    let result = service.$method(&caller, $($arg),*);
                    $crate::rpc::respond(ctx, &result)
                }),* }
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    crate::rpc_interface! {
        pub mod example, id = 42, version = 1 {
            fn add(value: u32) -> u32;
        }
    }
    struct Service(u32);
    impl example::Service for Service {
        fn add(&mut self, caller: &Aid, value: u32) -> u32 {
            assert_eq!(caller.as_slice(), &[1, 2, 3, 4, 5]);
            self.0 += value;
            self.0
        }
    }
    #[test]
    fn typed_dispatch_validates_schema_identity_and_roundtrips_postcard() {
        let mut ctx = RustletCtx::new();
        let mut request = [0; 32];
        request[0] = 5;
        request[1..6].copy_from_slice(&[1, 2, 3, 4, 5]);
        // Wire tuple (interface 42, version 1, method discriminant 0, argument 7).
        request[17..21].copy_from_slice(&[42, 1, 0, 7]);
        assert!(ctx.stage_incoming_data(&request[..21]));
        let mut service = Service(10);
        assert_eq!(
            example::dispatch(&mut service, &mut ctx).to_word(),
            ApduStatus::success().to_word()
        );
        assert_eq!(
            crate::postcard::from_bytes::<u32>(ctx.outgoing_data()),
            Ok(17)
        );
        for (offset, byte) in [(0, 17), (17, 43), (18, 2), (19, 1)] {
            let mut invalid = request;
            invalid[offset] = byte;
            ctx.stage_incoming_data(&invalid[..21]);
            assert_ne!(
                example::dispatch(&mut service, &mut ctx).to_word(),
                ApduStatus::success().to_word()
            );
            assert_eq!(service.0, 17);
        }
        ctx.stage_incoming_data(&request[..22]);
        assert_ne!(
            example::dispatch(&mut service, &mut ctx).to_word(),
            ApduStatus::success().to_word()
        );
        assert_eq!(
            example::Client::new(Aid::new(&[1])).add(1),
            Err(Error::Unsupported)
        );
    }
}
