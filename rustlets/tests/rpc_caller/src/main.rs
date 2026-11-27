#![no_std]
#![no_main]
use rpc_shared_interface::{counter, CALLEE};
use rustlet_runtime::{declare_rustlet, Apdu, ApduStatus, Rustlet, RustletCtx, State};
declare_rustlet!(Caller, 384usize);
struct Caller;
impl Rustlet for Caller {
    type Persistent = ();
    type Session = ();
    fn process_apdu(_: &mut State<(), ()>, ctx: &mut RustletCtx) -> ApduStatus {
        let service = counter::Client::new(CALLEE);
        let apdu = Apdu::new(ctx);
        let result = match apdu.ins() {
            0x10 => service.add(7).map(|value| value.to_le_bytes()),
            0x11 => service.value().map(|value| value.to_le_bytes()),
            0x12 => {
                return match service.identity() {
                    Ok(aid) => apdu.as_sending().send(&aid),
                    Err(_) => apdu.reject(ApduStatus::internal_error()),
                }
            }
            0x13 => {
                if service.crash().is_ok() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                service.value().map(|value| value.to_le_bytes())
            }
            0x14 => {
                if service.add(100).is_err() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                panic!("Parent rollback must include the accepted RPC");
            }
            0x15 => {
                if service.fault().is_ok() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                service.value().map(|value| value.to_le_bytes())
            }
            0x16 => {
                return match service.nested() {
                    Ok(true) => apdu.as_sending().send(&[1]),
                    _ => apdu.reject(ApduStatus::internal_error()),
                }
            }
            0x17 => {
                let rx = apdu.as_receiving();
                let mut original = [0u8; 16];
                if rx.data().len() != original.len() {
                    return rx.reject(ApduStatus::wrong_length());
                }
                original.copy_from_slice(rx.data());
                if service.value().is_err() || rx.data() != original {
                    return rx.reject(ApduStatus::internal_error());
                }
                return rx.accept_and_send(&original);
            }
            0x18 => {
                let own = counter::Client::new(rpc_shared_interface::CALLER);
                let missing =
                    counter::Client::new(rustlet_runtime::Aid::from_array([1, 2, 3, 4, 5]));
                if own.value().is_ok() || missing.value().is_ok() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                service.value().map(|value| value.to_le_bytes())
            }
            0x19 => {
                for _ in 0..16 {
                    if service.value().is_err() {
                        return apdu.reject(ApduStatus::internal_error());
                    }
                }
                service.value().map(|value| value.to_le_bytes())
            }
            0x1a => {
                let invalid =
                    rustlet_runtime::rpc::call::<_, u32>(CALLEE, &(0x525043u32, 2u16, 0u8, 1u32));
                if invalid.is_ok() {
                    return apdu.reject(ApduStatus::internal_error());
                }
                service.value().map(|value| value.to_le_bytes())
            }
            _ => return apdu.reject(ApduStatus::instruction_not_supported()),
        };
        match result {
            Ok(bytes) => apdu.as_sending().send(&bytes),
            Err(_) => apdu.reject(ApduStatus::internal_error()),
        }
    }
}
