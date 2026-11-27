#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};
declare_app!(TerminationTestRustlet);

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct TerminationTestRustlet;

impl Rustlet for TerminationTestRustlet {
    type Persistent = Self;
    type Session = ();
    fn process_apdu(
        _state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        let ins = Apdu::new(ctx).ins();

        match ins {
            0x20 => ctx.exit(ApduStatus {
                sw1: 0x91,
                sw2: 0x23,
            }),
            0x22 => panic!("termination test panic"),
            0x24 => ApduStatus::success(),
            0x26 => loop {
                core::hint::spin_loop();
            },
            // The second long call on Pico1 cannot fit in the APDU deadline.
            // A returned Busy/error is a failure: expiration must never resume us.
            0x28 | 0x2a => {
                let mut first = true;
                loop {
                    let mut private = [0; 32];
                    let mut public = [0; 65];
                    let params = rustlet_runtime::CryptoEcGenerateKeypairParams {
                        curve: 1,
                        reserved0: 0,
                        reserved1: 0,
                        reserved2: 0,
                        private_key_ptr: private.as_mut_ptr(),
                        private_key_capacity: 32,
                        public_key_ptr: public.as_mut_ptr(),
                        public_key_capacity: 65,
                    };
                    if rustlet_runtime::syscall::runtime::crypto::ec_generate_keypair::trigger(
                        &params,
                    ) != 0
                    {
                        return ApduStatus {
                            sw1: 0x91,
                            sw2: 0xee,
                        };
                    }
                    if first && ins == 0x2a {
                        let _ = Apdu::new(ctx).as_receiving();
                    }
                    first = false;
                }
            }
            _ => ApduStatus::instruction_not_supported(),
        }
    }
}
