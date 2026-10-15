#![no_std]
#![no_main]

use rustlet_runtime::{
    declare_security_domain,
    scp03::{S16Keyset, S16Session},
    Aid, Apdu, ApduStatus, Rustlet, RustletCtx, RustletSecurityDomain, SecurityLevel,
};

declare_security_domain!(TutorialScp03SecurityDomain);

const INSTANCE_AID: Aid = Aid::from_array([0xA0, 0x00, 0x00, 0x47, 0x50, 0x4F, 0x53, 0x31]);
const KEYSET: S16Keyset = S16Keyset {
    default_version: 1,
    resolved_id: 3,
};

/// Final, deliberately small result of the Rustlet Security Domain tutorial.
#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct TutorialScp03SecurityDomain;

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct Session {
    commands: u32,
    scp03: S16Session,
}

impl Rustlet for TutorialScp03SecurityDomain {
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

impl RustletSecurityDomain for TutorialScp03SecurityDomain {
    fn supports_scp03_s16(
        _state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
    ) -> bool {
        true
    }

    fn claims_delegated_secure_channel_command(
        _state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
        header: rustlet_runtime::DelegatedSecureChannelHeader,
    ) -> bool {
        matches!(
            (header.cla, header.ins, header.p2),
            (0x80, 0x50, _) | (0x84, 0x82, 0)
        )
    }

    fn initialize_update(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
        command: &rustlet_runtime::InitializeUpdate<'_>,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        state
            .session
            .scp03
            .initialize_update(ctx, command, KEYSET, out)
    }

    fn external_authenticate(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
        command: &rustlet_runtime::ExternalAuthenticate<'_>,
    ) -> Result<SecurityLevel, ApduStatus> {
        state.session.scp03.external_authenticate(ctx, command)
    }

    fn current_security_level(
        state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
    ) -> SecurityLevel {
        state.session.scp03.security_level()
    }

    fn secure_channel_open(
        state: &rustlet_runtime::State<Self::Persistent, Self::Session>,
    ) -> bool {
        state.session.scp03.is_open()
    }

    fn current_mac_len(state: &rustlet_runtime::State<Self::Persistent, Self::Session>) -> usize {
        state.session.scp03.mac_len()
    }

    fn unwrap_command(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
        command: &rustlet_runtime::WrappedCommand<'_>,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        state.session.scp03.unwrap_command(ctx, command, out)
    }

    fn wrap_response(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
        response: &rustlet_runtime::PlainResponse<'_>,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        state.session.scp03.wrap_response(ctx, response, out)
    }

    fn reset_secure_channel(state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>) {
        state.session.scp03.reset();
    }
}

impl TutorialScp03SecurityDomain {
    fn handle_select(&mut self, apdu: Apdu<'_, rustlet_runtime::Command>) -> ApduStatus {
        let fci = [
            0x6F,
            0x10,
            0x84,
            INSTANCE_AID.len,
            INSTANCE_AID.bytes[0],
            INSTANCE_AID.bytes[1],
            INSTANCE_AID.bytes[2],
            INSTANCE_AID.bytes[3],
            INSTANCE_AID.bytes[4],
            INSTANCE_AID.bytes[5],
            INSTANCE_AID.bytes[6],
            INSTANCE_AID.bytes[7],
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
