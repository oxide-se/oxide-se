//! Adversarial ABI requests through the real SVC boundary; no production keys.
use super::raw_svc;
use core::ptr;
use rustlet_runtime::{syscall_abi::*, ApduStatus, RustletCtx};

fn invoke(service: u8, address: usize) -> usize {
    match service {
        9 => raw_svc::<9>(address, 0, 0),
        10 => raw_svc::<10>(address, 0, 0),
        11 => raw_svc::<11>(address, 0, 0),
        12 => raw_svc::<12>(address, 0, 0),
        13 => raw_svc::<13>(address, 0, 0),
        14 => raw_svc::<14>(address, 0, 0),
        15 => raw_svc::<15>(address, 0, 0),
        16 => raw_svc::<16>(address, 0, 0),
        _ => usize::MAX,
    }
}

fn call<T>(service: u8, params: &T) -> usize {
    invoke(service, ptr::from_ref(params) as usize)
}

pub(super) fn run(ctx: &mut RustletCtx, service: u8, case: u8) -> ApduStatus {
    ctx.data.fill(0xa5);
    let passed = if (9..=16).contains(&service) {
        // All eight parameter-bearing services must reject malformed records.
        // SD key lookup here proves the ordinary-call authority gate; the host
        // test additionally reaches record validation under actual SD authority.
        let address = match case {
            0 => 0,
            1 => ctx as *mut RustletCtx as usize + 1,
            2 => usize::MAX & !3,
            3 => ctx as *mut RustletCtx as usize + rustlet_runtime::APDU_SHARED_REGION_SIZE - 4,
            _ => return ApduStatus::wrong_data(),
        };
        invoke(service, address)
            == CRYPTO_RESULT_ERROR_FLAG | CryptoErrorCode::PermissionDenied as usize
    } else if service == 0 {
        rejected_buffer(ctx, case)
    } else if service == 1 {
        return if positive(ctx, case) {
            ApduStatus::success()
        } else {
            ApduStatus::internal_error()
        };
    } else {
        false
    };
    if passed && ctx.data.iter().all(|b| *b == 0xa5) {
        ApduStatus::success()
    } else {
        ApduStatus::internal_error()
    }
}

fn rejected_buffer(ctx: &mut RustletCtx, case: u8) -> bool {
    let base = ctx.data.as_mut_ptr();
    let out = base.wrapping_add(128);
    let invalid = usize::MAX as *mut u8;
    let denied = CRYPTO_RESULT_ERROR_FLAG | CryptoErrorCode::PermissionDenied as usize;
    let result = match case {
        0..=5 => {
            let mut p = CryptoRandomGenerateParams {
                algorithm: 1,
                output_ptr: out,
                output_len: 16,
            };
            match case {
                0 => p.output_ptr = ptr::null_mut(),
                1 => p.output_ptr = invalid,
                2 => p.output_len = usize::MAX,
                3 => {
                    p.output_ptr = (ctx as *mut RustletCtx as usize
                        + rustlet_runtime::APDU_SHARED_REGION_SIZE
                        - 4) as *mut u8;
                }
                4 => p.output_ptr = KEY.as_ptr() as *mut u8,
                _ => p.output_len = isize::MAX as usize + 1,
            }
            call(10, &p)
        }
        6..=10 => {
            let mut p = cipher_params(base, out);
            match case {
                6 => p.key_ptr = invalid,
                7 => p.iv_ptr = ptr::null(),
                8 => p.input_ptr = invalid,
                9 => p.output_ptr = ptr::null_mut(),
                _ => p.output_capacity = usize::MAX,
            }
            call(9, &p)
        }
        11..=14 => {
            let mut p = mac_params(base, out);
            match case {
                11 => p.key_ptr = invalid,
                12 => p.input_ptr = invalid,
                13 => p.output_ptr = invalid,
                _ => {
                    p.operation = 2;
                    p.expected_tag_ptr = invalid;
                    p.expected_tag_len = 16;
                }
            }
            let value = call(11, &p);
            // MAC verify's ABI uses InvalidBufferLength for an invalid tag span.
            if case == 14 {
                return value
                    == CRYPTO_RESULT_ERROR_FLAG | CryptoErrorCode::InvalidBufferLength as usize;
            }
            value
        }
        15..=20 => {
            let mut p = CryptoEcGenerateKeypairParams {
                curve: 1,
                reserved0: 0,
                reserved1: 0,
                reserved2: 0,
                private_key_ptr: base,
                private_key_capacity: 32,
                public_key_ptr: out,
                public_key_capacity: 65,
            };
            match case {
                15 => p.private_key_ptr = invalid,
                16 => p.public_key_ptr = ptr::null_mut(),
                17 => p.public_key_ptr = base,
                18 => p.public_key_ptr = base.wrapping_add(16),
                19 => {
                    p.private_key_ptr = base.wrapping_add(16);
                    p.public_key_ptr = base;
                }
                _ => p.reserved1 = 1,
            }
            call(13, &p)
        }
        21..=26 => {
            let mut p = CryptoEcdhDoFinalParams {
                curve: 1,
                reserved0: 0,
                reserved1: 0,
                reserved2: 0,
                private_key_ptr: base,
                private_key_len: 32,
                peer_public_key_ptr: base.wrapping_add(32),
                peer_public_key_len: 65,
                output_ptr: out,
                output_capacity: 32,
            };
            match case {
                21 => p.private_key_ptr = invalid,
                22 => p.peer_public_key_ptr = invalid,
                23 => p.output_ptr = invalid,
                24 => p.output_ptr = base,
                25 => p.output_ptr = base.wrapping_add(64),
                _ => p.reserved2 = 1,
            }
            call(14, &p)
        }
        27..=33 => {
            let mut p = CryptoHkdfSha256Params {
                ikm_ptr: base,
                ikm_len: 16,
                salt_ptr: base.wrapping_add(16),
                salt_len: 16,
                info_ptr: base.wrapping_add(32),
                info_len: 16,
                output_ptr: out,
                output_capacity: 16,
            };
            match case {
                27 => p.ikm_ptr = invalid,
                28 => p.salt_ptr = invalid,
                29 => p.info_ptr = invalid,
                30 => p.output_ptr = invalid,
                31 => p.output_ptr = base,
                32 => p.output_ptr = base.wrapping_add(16),
                _ => p.output_ptr = base.wrapping_add(32),
            }
            call(15, &p)
        }
        34..=38 => {
            let mut p = CryptoX963Sha256Params {
                shared_secret_ptr: base,
                shared_secret_len: 16,
                shared_info_ptr: base.wrapping_add(16),
                shared_info_len: 16,
                output_ptr: out,
                output_capacity: 16,
            };
            match case {
                34 => p.shared_secret_ptr = invalid,
                35 => p.shared_info_ptr = invalid,
                36 => p.output_ptr = invalid,
                37 => p.output_ptr = base,
                _ => p.output_ptr = base.wrapping_add(16),
            }
            call(16, &p)
        }
        _ => return false,
    };
    result == denied
}

static KEY: [u8; 16] = [0; 16];
static IV: [u8; 16] = [0; 16];
fn cipher_params(input: *const u8, output: *mut u8) -> CryptoCipherDoFinalParams {
    CryptoCipherDoFinalParams {
        algorithm: 1,
        mode: 1,
        key_ptr: KEY.as_ptr(),
        key_len: 16,
        iv_ptr: IV.as_ptr(),
        iv_len: 16,
        input_ptr: input,
        input_len: 16,
        output_ptr: output,
        output_capacity: 16,
    }
}
fn mac_params(input: *const u8, output: *mut u8) -> CryptoMacDoFinalParams {
    CryptoMacDoFinalParams {
        algorithm: 1,
        operation: 1,
        key_ptr: KEY.as_ptr(),
        key_len: 16,
        input_ptr: input,
        input_len: 16,
        expected_tag_ptr: ptr::null(),
        expected_tag_len: 0,
        output_ptr: output,
        output_capacity: 16,
    }
}

fn positive(ctx: &mut RustletCtx, case: u8) -> bool {
    let base = ctx.data.as_mut_ptr();
    match case {
        0 => {
            call(
                10,
                &CryptoRandomGenerateParams {
                    algorithm: 1,
                    output_ptr: usize::MAX as *mut u8,
                    output_len: 0,
                },
            ) == 0
                && ctx.data.iter().all(|b| *b == 0xa5)
        }
        1..=3 => {
            // AES-128 CBC, zero key/IV and zero block: known first ciphertext.
            let (src, dst) = match case {
                1 => (0, 0),
                2 => (0, 4),
                _ => (4, 0),
            };
            ctx.data[..32].fill(0);
            let result = call(
                9,
                &cipher_params(base.wrapping_add(src), base.wrapping_add(dst)),
            );
            result == 16
                && ctx.data[dst..dst + 16]
                    == [
                        0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b, 0x88, 0x4c, 0xfa, 0x59,
                        0xca, 0x34, 0x2b, 0x2e,
                    ]
                && ctx.data[32..].iter().all(|b| *b == 0xa5)
        }
        4 => {
            if call(11, &mac_params(base, base.wrapping_add(128))) != 16 {
                return false;
            }
            let expected: [u8; 16] = ctx.data[128..144].try_into().unwrap();
            call(11, &mac_params(base, base)) == 16 && ctx.data[..16] == expected
        }
        5 => {
            // Empty optional inputs accept null without dereference; shared read
            // ranges also remain legal while output is disjoint.
            call(
                15,
                &CryptoHkdfSha256Params {
                    ikm_ptr: base,
                    ikm_len: 16,
                    salt_ptr: ptr::null(),
                    salt_len: 0,
                    info_ptr: usize::MAX as *const u8,
                    info_len: 0,
                    output_ptr: base.wrapping_add(128),
                    output_capacity: 16,
                },
            ) == 16
        }
        6 => {
            call(
                16,
                &CryptoX963Sha256Params {
                    shared_secret_ptr: base,
                    shared_secret_len: 16,
                    shared_info_ptr: base,
                    shared_info_len: 16,
                    output_ptr: base.wrapping_add(128),
                    output_capacity: 16,
                },
            ) == 16
        }
        _ => false,
    }
}
