#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_app!(ImplicitDefaultRustlet);

struct ImplicitDefaultRustlet;

impl Rustlet for ImplicitDefaultRustlet {
    type Persistent = ();
    type Session = ();
    fn process_apdu(
        _state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        Apdu::new(ctx).accept()
    }
}
