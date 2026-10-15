//! Private, kernel-only primitive timing. No keys or buffers leave the device.
use super::{ApduFilter, KernelAppModule};
use crate::{
    apdu_manager::ApduStatus,
    core::{crypto as c, flash, target},
    kernel_cell::KernelCell,
};
use rustlet_runtime::SEApdu;

const MAX_SAMPLES: usize = 50;
const MAX: usize = 1024;
const INS: u8 = 0x0b;
// Explicit diagnostic sector, reserved before registry initialization.
static AREA: KernelCell<usize> = unsafe { KernelCell::new(0) };
pub(crate) struct Module;
impl KernelAppModule for Module {
    fn initialize() {
        if flash::logical_page_size() == 256 && flash::erase_sector_size() == 4096 {
            if let Ok(area) = flash::reserve_persistence_tail(4096) {
                AREA.set(area.start);
            }
        }
    }
}
pub(crate) const APDU_FILTER: ApduFilter = ApduFilter {
    matches: |a| a.ins() == INS,
    process,
};

// SVC-PERF: svc=all; replay=all; see docs/kernel.developer.guide.md#svc-performance-maintenance.
fn process(apdu: &mut dyn SEApdu) -> ApduStatus {
    let Some((svc, variant)) = decode_selector(apdu.p1()) else {
        return ApduStatus::wrong_data();
    };
    let count = apdu.p2() as usize;
    if !(1..=MAX_SAMPLES).contains(&count) {
        return ApduStatus::wrong_data();
    }
    if apdu.set_incoming_and_receive() != 4 {
        return ApduStatus::wrong_length();
    }
    let n = u16::from_be_bytes(apdu.buffer_mut()[..2].try_into().unwrap()) as usize;
    let out_len = u16::from_be_bytes(apdu.buffer_mut()[2..4].try_into().unwrap()) as usize;
    if !valid(svc, variant, n, out_len) {
        return ApduStatus::wrong_data();
    }
    if svc >= 0xf0 && AREA.get() == 0 {
        return ApduStatus::conditions_not_satisfied();
    }
    let Some(_guard) = crate::time_manager::profile_begin() else {
        return ApduStatus::conditions_not_satisfied();
    };
    let mut input = [0x5a; MAX + 16];
    let mut output = [0u8; MAX + 16];
    let key = c::AesKey::from_bytes(if variant & 8 != 0 {
        &[0x42; 32][..]
    } else {
        &[0x42; 16][..]
    })
    .unwrap();
    let iv = [0x37; 16];
    let mut scalar = [0x13; 32];
    let mut public = [0u8; 65];
    let mut storage = [0u32; MAX_SAMPLES];
    let samples = &mut storage[..count];
    let hz = target::monotonic_hz();
    for (i, sample) in samples.iter_mut().enumerate() {
        if !crate::time_manager::profile_send_null() {
            return ApduStatus { sw1: 0x6f, sw2: 0 };
        }
        // Preparation is excluded from the timed interval. Vary public input
        // patterns and private scalars to avoid measuring one lucky operand.
        input.fill(0x5a ^ i as u8);
        scalar.fill(0x13 + (i % 32) as u8);
        let padded_len = n + 16;
        if svc == 9 && variant & 7 == 5 {
            if c::aes_cbc_encrypt_iso9797_m2(&key, &iv, &input[..n], &mut output[..padded_len])
                .is_err()
            {
                return ApduStatus { sw1: 0x6f, sw2: 0 };
            }
            input[..padded_len].copy_from_slice(&output[..padded_len]);
        }
        if svc >= 0xf0 {
            if flash::erase_sector(AREA.get()).is_err() {
                return ApduStatus { sw1: 0x6f, sw2: 0 };
            }
            if svc == 0xf1 {
                for page in 0..16 {
                    if flash::write_page(AREA.get() + page * 256, &input[..256]).is_err() {
                        return ApduStatus { sw1: 0x6f, sw2: 0 };
                    }
                }
            }
        }
        let (elapsed, ok) = target::with_interrupts_masked(|| {
            let start = target::monotonic_ticks();
            let ok = match svc {
                9 => match variant & 7 {
                    0 => c::aes_cbc_encrypt_in_place(&key, &iv, &mut input[..n]).is_ok(),
                    1 => c::aes_cbc_decrypt_in_place(&key, &iv, &mut input[..n]).is_ok(),
                    2 => c::aes_ecb_encrypt_in_place(&key, &mut input[..n]).is_ok(),
                    3 => c::aes_ecb_decrypt_in_place(&key, &mut input[..n]).is_ok(),
                    4 => c::aes_cbc_encrypt_iso9797_m2_in_place(
                        &key,
                        &iv,
                        &mut input[..padded_len],
                        n,
                    )
                    .is_ok(),
                    5 => {
                        c::aes_cbc_decrypt_iso9797_m2_in_place(&key, &iv, &mut input[..padded_len])
                            .is_ok()
                    }
                    _ => false,
                },
                10 => c::fill_random(&mut output[..n]).is_ok(),
                11 => {
                    c::aes_cmac(&key, &input[..n], (&mut output[..16]).try_into().unwrap()).is_ok()
                }
                13 => {
                    if variant == 0 {
                        c::p256_generate_keypair(&mut scalar, &mut public).is_ok()
                    } else {
                        c::p256_public_from_private(&scalar, &mut public).is_ok()
                    }
                }
                14 => c::p256_ecdh(&scalar, &GENERATOR, &mut output[..32]).is_ok(),
                15 => c::hkdf_sha256(
                    &input[..n],
                    &[0x31; 32],
                    &[0x32; 32],
                    &mut output[..out_len],
                )
                .is_ok(),
                16 => c::x963_sha256_kdf(&input[..n], &[0x32; 32], &mut output[..out_len]).is_ok(),
                0xf0 => flash::write_page(AREA.get(), &input[..256]).is_ok(),
                0xf1 => flash::erase_sector(AREA.get()).is_ok(),
                _ => false,
            };
            (target::monotonic_ticks().wrapping_sub(start), ok)
        });
        // Keep outputs observable across optimizations; never time host/UART work.
        core::hint::black_box((&input, &output, &scalar, &public));
        if !ok || elapsed == 0 || elapsed > i32::MAX as u32 {
            return ApduStatus { sw1: 0x6f, sw2: 0 };
        }
        if svc >= 0xf0 {
            // SAFETY: the module exclusively owns this mapped flash sector.
            let stored = unsafe { core::slice::from_raw_parts(AREA.get() as *const u8, 4096) };
            if (svc == 0xf0 && stored[..256] != input[..256])
                || (svc == 0xf1 && stored.iter().any(|&x| x != 0xff))
            {
                return ApduStatus { sw1: 0x6f, sw2: 0 };
            }
        }
        *sample = elapsed;
    }
    drop(_guard);
    let sum: u64 = samples.iter().map(|&x| x as u64).sum();
    let us = |ticks: u64| (ticks * 1_000_000).div_ceil(hz as u64) as u32;
    apdu.set_outgoing();
    let result = apdu.buffer_mut();
    result[..4].copy_from_slice(&[2, svc, variant, count as u8]);
    for (i, value) in [
        target::core_clock_hz(),
        hz,
        us(*samples.iter().min().unwrap() as u64),
        us(*samples.iter().max().unwrap() as u64),
        (sum * 1_000_000).div_ceil(hz as u64 * count as u64) as u32,
    ]
    .iter()
    .enumerate()
    {
        result[4 + i * 4..8 + i * 4].copy_from_slice(&value.to_be_bytes());
    }
    for (i, sample) in samples.iter().enumerate() {
        result[24 + i * 4..28 + i * 4].copy_from_slice(&sample.to_be_bytes());
    }
    apdu.set_outgoing_length(24 + 4 * count);
    ApduStatus::success()
}
// P1 high nibble: variant; low nibble: compact profiling operation ID.
// SVC-PERF: svc=all; replay=all; see docs/kernel.developer.guide.md#svc-performance-maintenance.
fn decode_selector(p1: u8) -> Option<(u8, u8)> {
    let svc = match p1 & 15 {
        1 => 9,
        2 => 10,
        3 => 11,
        4 => 13,
        5 => 14,
        6 => 15,
        7 => 16,
        8 => 0xf0,
        9 => 0xf1,
        _ => return None,
    };
    Some((svc, p1 >> 4))
}
// SVC-PERF: svc=all; replay=all; see docs/kernel.developer.guide.md#svc-performance-maintenance.
fn valid(svc: u8, variant: u8, n: usize, out: usize) -> bool {
    if n > MAX || out > MAX {
        return false;
    }
    match svc {
        9 => variant & !15 == 0 && variant & 7 <= 5 && n > 0 && n % 16 == 0 && out == 0,
        10 => variant == 0 && n > 0 && out == 0,
        11 => matches!(variant, 0 | 8) && n > 0 && out == 0,
        13 => variant <= 1 && n == 0 && out == 0,
        14 => variant == 0 && n == 0 && out == 0,
        15 | 16 => variant == 0 && n > 0 && out > 0,
        0xf0 | 0xf1 => variant == 0 && n == 0 && out == 0,
        _ => false,
    }
}
const GENERATOR: [u8; 65] = [
    4, 0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47, 0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40,
    0xf2, 0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0, 0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2,
    0x96, 0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b, 0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e,
    0x16, 0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce, 0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf, 0x51,
    0xf5,
];

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn selector_separates_variant_and_operation() {
        assert_eq!(decode_selector(0xd1), Some((9, 13)));
        assert_eq!(decode_selector(0x14), Some((13, 1)));
        assert_eq!(decode_selector(0x07), Some((16, 0)));
        assert_eq!(decode_selector(0x08), Some((240, 0)));
        assert_eq!(decode_selector(0x09), Some((241, 0)));
        assert_eq!(decode_selector(0), None);
        assert_eq!(decode_selector(0xff), None);
    }
    #[test]
    fn validates_before_any_operation_or_flash_access() {
        assert!(valid(9, 13, 1024, 0));
        assert!(!valid(9, 14, 16, 0));
        assert!(!valid(9, 0, 17, 0));
        assert!(!valid(10, 0, 1025, 0));
        assert!(!valid(15, 0, 16, 0));
        assert!(valid(16, 0, 1024, 1024));
        assert!(!valid(14, 1, 0, 0));
        assert!(valid(0xf1, 0, 0, 0));
        assert!(!valid(0xf1, 1, 0, 0));
        assert!(!valid(12, 0, 0, 0));
    }
}
