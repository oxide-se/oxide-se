#![no_std]
#![no_main]

use rustlet_runtime::{declare_app, gp, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_app!(
    SerializationTestRustlet,
    1024usize,
    install_serialization_test
);

const INS_INCREMENT: u8 = 0x40;
const INS_DUMP: u8 = 0x42;
const INS_FAIL_SAVE: u8 = 0x44;

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct NestedCounters {
    persistent: u8,
}

#[derive(Default, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct SerializationTestRustlet {
    #[serde(skip, default)]
    fail_save: bool,
    persistent: u8,
    nested: NestedCounters,
}

// Force a real snapshot failure after application mutation; the next selection
// must recover the previously committed bytes, without using a scrubbed Box.
impl rustlet_runtime::serde::Serialize for SerializationTestRustlet {
    fn serialize<S: rustlet_runtime::serde::Serializer>(
        &self,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        use rustlet_runtime::serde::ser::{Error, SerializeStruct};
        if self.fail_save {
            return Err(S::Error::custom("injected state save failure"));
        }
        let mut value = serializer.serialize_struct("SerializationTestRustlet", 2)?;
        value.serialize_field("persistent", &self.persistent)?;
        value.serialize_field("nested", &self.nested)?;
        value.end()
    }
}

fn install_serialization_test(
    ctx: &mut RustletCtx,
) -> Result<SerializationTestRustlet, ApduStatus> {
    let mut install_data = [0u8; 4];
    let data_len = gp::parse_install_for_install_ctx(ctx)
        .ok()
        .map(|install| {
            let len = install.install_parameters.len().min(install_data.len());
            install_data[..len].copy_from_slice(&install.install_parameters[..len]);
            len
        })
        .unwrap_or(0);
    let data = &install_data[..data_len];

    Ok(SerializationTestRustlet {
        fail_save: false,
        persistent: data.first().copied().unwrap_or(0),
        nested: NestedCounters {
            persistent: data.get(1).copied().unwrap_or(0),
        },
    })
}

impl Rustlet for SerializationTestRustlet {
    type Persistent = Self;
    type Session = Session;
    fn process_apdu(
        state: &mut rustlet_runtime::State<Self::Persistent, Self::Session>,
        ctx: &mut RustletCtx,
    ) -> ApduStatus {
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            INS_FAIL_SAVE => {
                state.persistent.persistent = 0xee;
                state.persistent.fail_save = true;
                apdu.accept()
            }
            INS_INCREMENT => {
                state.persistent.persistent = state.persistent.persistent.wrapping_add(1);
                state.persistent.nested.persistent =
                    state.persistent.nested.persistent.wrapping_add(1);
                state.session.transient = state.session.transient.wrapping_add(1);
                state.session.nested_transient = state.session.nested_transient.wrapping_add(1);
                apdu.accept()
            }
            INS_DUMP => apdu.as_sending().send(&[
                state.persistent.persistent,
                state.persistent.nested.persistent,
                state.session.transient,
                state.session.nested_transient,
            ]),
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct Session {
    transient: u8,
    nested_transient: u8,
}
