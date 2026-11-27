include!(concat!(env!("OUT_DIR"), "/firmware_uid.inc.rs"));

/// Returns the 256-bit identifier embedded when this firmware image was built.
pub fn get_firmware_uid() -> &'static [u8; 32] {
    &FIRMWARE_UID
}

// Link-time provider for oxi-core; keep the UID's existing single source.
#[unsafe(no_mangle)]
pub fn oxide_se_firmware_puf() -> &'static [u8; 32] {
    get_firmware_uid()
}

#[cfg(test)]
mod tests {
    use super::{get_firmware_uid, FIRMWARE_UID};

    #[test]
    fn firmware_uid_accessor_returns_the_embedded_value() {
        assert_eq!(get_firmware_uid(), &FIRMWARE_UID);
        assert_eq!(oxi_core::core::get_puf(), get_firmware_uid());
    }
}
