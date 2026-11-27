//! Device-root interface. The current provider is the firmware image UID.
//!
//! This is a development substitute, not a hardware PUF: identical firmware
//! images share this value, and rebuilding with a new UID changes it.

/// Returns the current 256-bit root supplied by the firmware image.
///
/// The provider must retain this value across resets for the lifetime of the
/// persistent image. Target-specific SRAM enrollment/reconstruction is pending.
pub fn get_puf() -> &'static [u8; 32] {
    unsafe extern "Rust" {
        fn oxide_se_firmware_puf() -> &'static [u8; 32];
    }
    // The firmware supplies an immutable, image-lifetime value. A missing
    // provider is a link error, never a zero or randomly generated fallback.
    unsafe { oxide_se_firmware_puf() }
}
