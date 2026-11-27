//! Separate AES-CBC keys for the encrypted BOSS body. Reads decrypt only the
//! requested range into the caller's destination; no plaintext BOSS cache.
use oxi_core::core::{
    crypto::{self, AesKey, CryptoResult},
    secure_zero,
};

struct Keys {
    iv: AesKey,
    enc: AesKey,
}

fn derive() -> CryptoResult<Keys> {
    #[cfg(test)]
    let root = &[0x42; 32];
    #[cfg(not(test))]
    let root = oxi_core::core::get_puf();
    let key = |label: &[u8]| {
        let mut bytes = [0; 32];
        let result = crypto::hkdf_sha256(root, b"oXiDe registry BOSS v1", label, &mut bytes)
            .and_then(|()| AesKey::from_bytes(&bytes));
        secure_zero(&mut bytes);
        result
    };
    Ok(Keys {
        iv: key(b"IV/AES-256")?,
        enc: key(b"body/AES-256-CBC")?,
    })
}

#[cfg(not(test))]
static KEYS: crate::kernel_cell::KernelCell<Option<Keys>> =
    unsafe { crate::kernel_cell::KernelCell::new(None) };

fn with_keys<T>(f: impl FnOnce(&Keys) -> CryptoResult<T>) -> CryptoResult<T> {
    #[cfg(test)]
    {
        f(&derive()?)
    }
    #[cfg(not(test))]
    {
        let mut keys = KEYS.borrow_mut();
        if keys.is_none() {
            *keys = Some(derive()?);
        }
        f(keys.as_ref().unwrap())
    }
}

fn iv(keys: &Keys, offset: usize, seed: u64) -> CryptoResult<[u8; 16]> {
    let offset = u32::try_from(offset).map_err(|_| crypto::CryptoError::InvalidBufferLength)?;
    let mut iv = [0; 16];
    iv[..4].copy_from_slice(&0x0001_B055u32.to_le_bytes());
    iv[4..8].copy_from_slice(&offset.to_le_bytes());
    iv[8..].copy_from_slice(&seed.to_le_bytes());
    crypto::aes_ecb_encrypt_in_place(&keys.iv, &mut iv)?;
    Ok(iv)
}

pub(super) fn encrypt(offset: usize, seed: u64, body: &mut [u8]) -> CryptoResult<()> {
    if body.is_empty() || !body.len().is_multiple_of(16) {
        return Err(crypto::CryptoError::InvalidBufferLength);
    }
    with_keys(|keys| {
        let chain = iv(keys, offset, seed)?;
        crypto::aes_cbc_encrypt_in_place(&keys.enc, &chain, body)
    })
}

pub(super) fn read_range(
    offset: usize,
    seed: u64,
    ciphertext: &[u8],
    start: usize,
    out: &mut [u8],
) -> CryptoResult<()> {
    if out.is_empty() {
        return Ok(());
    }
    let position = start / 16 * 16;
    let skip = start % 16;
    let touched = (skip + out.len()).div_ceil(16) * 16;
    if position
        .checked_add(touched)
        .is_none_or(|end| end > ciphertext.len())
    {
        return Err(crypto::CryptoError::InvalidBufferLength);
    }
    with_keys(|keys| {
        let chain = if position == 0 {
            iv(keys, offset, seed)?
        } else {
            ciphertext[position - 16..position].try_into().unwrap()
        };
        crypto::aes_cbc_decrypt_range_into(
            &keys.enc,
            &chain,
            &ciphertext[position..position + touched],
            skip,
            out,
        )
    })
}

pub(super) fn decrypt_in_place(offset: usize, seed: u64, body: &mut [u8]) -> CryptoResult<()> {
    if body.is_empty() || !body.len().is_multiple_of(16) {
        return Err(crypto::CryptoError::InvalidBufferLength);
    }
    with_keys(|keys| {
        let chain = iv(keys, offset, seed)?;
        crypto::aes_cbc_decrypt_in_place(&keys.enc, &chain, body)
    })
}
