#![no_std]
#![no_main]

use rustlet_runtime::{declare_rustlet, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_rustlet!(TemplateRustlet, 256);

struct TemplateRustlet;

impl Rustlet for TemplateRustlet {
    type Persistent = ();
    type Session = ();
    fn process_apdu(
        _state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            0x00 => apdu.accept(),
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}
