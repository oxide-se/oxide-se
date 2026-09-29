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
    #[serde(skip, default)]
    transient: u8,
}

#[derive(Default, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct SerializationTestRustlet {
    #[serde(skip, default)]
    fail_save: bool,
    persistent: u8,
    nested: NestedCounters,
    #[serde(skip, default)]
    transient: u8,
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
            transient: data.get(3).copied().unwrap_or(0),
        },
        transient: data.get(2).copied().unwrap_or(0),
    })
}

impl Rustlet for SerializationTestRustlet {
    fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            INS_FAIL_SAVE => {
                self.persistent = 0xee;
                self.fail_save = true;
                apdu.accept()
            }
            INS_INCREMENT => {
                self.persistent = self.persistent.wrapping_add(1);
                self.nested.persistent = self.nested.persistent.wrapping_add(1);
                self.transient = self.transient.wrapping_add(1);
                self.nested.transient = self.nested.transient.wrapping_add(1);
                apdu.accept()
            }
            INS_DUMP => apdu.as_sending().send(&[
                self.persistent,
                self.nested.persistent,
                self.transient,
                self.nested.transient,
            ]),
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}
