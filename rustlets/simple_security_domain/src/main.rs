#![no_std]
#![no_main]

use rustlet_runtime::{
    declare_security_domain, Aid, Apdu, ApduStatus, Rustlet, RustletCtx, RustletSecurityDomain,
};

declare_security_domain!(SimpleSecurityDomain);

/// Example AID for the minimal Security Domain skeleton.
///
/// This value is the instance AID reserved by the authoring tutorial. It is
/// intentionally distinct from `complete_security_domain` so both crates can
/// coexist in the workspace without colliding.
const SIMPLE_SECURITY_DOMAIN_AID: Aid =
    Aid::from_array([0xA0, 0x00, 0x00, 0x47, 0x50, 0x4F, 0x53, 0x31]);

/// Minimal Security Domain skeleton.
///
/// This Rustlet deliberately relies on the default `RustletSecurityDomain`
/// behavior implemented by the runtime. It is meant to be copied and refined
/// when building a custom user-land Security Domain.
#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct SimpleSecurityDomain;

impl Rustlet for SimpleSecurityDomain {
    type Persistent = Self;
    type Session = Session;
    fn process_apdu(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        state.session.commands = state.session.commands.wrapping_add(1);
        let apdu = Apdu::new(ctx);
        if apdu.is_select() {
            return state.persistent.handle_select(apdu);
        }

        match apdu.ins() {
            0x00 => apdu.accept(),
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}

impl RustletSecurityDomain for SimpleSecurityDomain {
    fn reset_secure_channel(state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>) {
        state.session = Session::default();
    }
}

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct Session {
    commands: u32,
}

impl SimpleSecurityDomain {
    fn handle_select(&mut self, apdu: Apdu<'_, rustlet_runtime::Command>) -> ApduStatus {
        let fci = [
            0x6F,
            0x10,
            0x84,
            SIMPLE_SECURITY_DOMAIN_AID.len,
            SIMPLE_SECURITY_DOMAIN_AID.bytes[0],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[1],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[2],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[3],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[4],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[5],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[6],
            SIMPLE_SECURITY_DOMAIN_AID.bytes[7],
            0xA5,
            0x04,
            0x9F,
            0x65,
            0x01,
            0x01,
        ];
        apdu.as_sending().send(&fci)
    }
}
