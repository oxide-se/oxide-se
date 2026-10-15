#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_app!(ImplicitHeapRustlet, 2048usize);

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct ImplicitHeapRustlet;

impl Rustlet for ImplicitHeapRustlet {
    type Persistent = Self;
    type Session = ();
    fn process_apdu(
        _state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        Apdu::new(ctx).accept()
    }
}
