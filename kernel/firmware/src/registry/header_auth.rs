//! Address-bound authentication: LOAD header + CRC32, full CMAC otherwise.
//! Only the serialized privileged owner uses the cached key; no payload buffer.
use oxi_core::core::crypto::{self, AesKey, CryptoResult};

#[cfg(not(test))]
static KEY: crate::kernel_cell::KernelCell<Option<AesKey>> =
    unsafe { crate::kernel_cell::KernelCell::new(None) };

// Keep the key derivation scratch from occupying the CMAC caller's frame.
#[inline(never)]
fn derive() -> CryptoResult<AesKey> {
    #[cfg(test)]
    let root = &[0x42; 32];
    #[cfg(not(test))]
    let root = oxi_core::core::get_puf();
    let mut bytes = [0; 32];
    let result = crypto::hkdf_sha256(
        root,
        b"oXiDe registry block v6",
        b"AES-256-CMAC",
        &mut bytes,
    )
    .and_then(|()| AesKey::from_bytes(&bytes));
    oxi_core::core::secure_zero(&mut bytes);
    result
}

pub fn tag(offset: usize, header: &[u8], body: &[u8]) -> CryptoResult<[u8; 16]> {
    tag_split(offset, header, body, &[])
}

/// Same message with a staged first-page body and an immutable XIP tail.
pub fn tag_split(
    offset: usize,
    header: &[u8],
    first: &[u8],
    tail: &[u8],
) -> CryptoResult<[u8; 16]> {
    let offset = u32::try_from(offset).map_err(|_| crypto::CryptoError::InvalidBufferLength)?;
    if header.len() != 16 {
        return Err(crypto::CryptoError::InvalidBufferLength);
    }
    let mut context = [0; 8];
    context[..4].copy_from_slice(&0x0006_0001u32.to_le_bytes());
    context[4..].copy_from_slice(&offset.to_le_bytes());
    let compute = |key: &AesKey| {
        let mut out = [0; 16];
        if super::format::has_body_crc(header) {
            crypto::aes_cmac_parts(key, &[&context, header], &mut out)?;
        } else {
            crypto::aes_cmac_parts(key, &[&context, header, first, tail], &mut out)?;
        }
        Ok(out)
    };
    #[cfg(test)]
    {
        compute(&derive()?)
    }
    #[cfg(not(test))]
    {
        let mut key = KEY.borrow_mut();
        if key.is_none() {
            *key = Some(derive()?);
        }
        compute(key.as_ref().unwrap())
    }
}

pub fn verify(offset: usize, header: &[u8]) -> CryptoResult<bool> {
    verify_inner(offset, header, true)
}

/// Authenticate the extent without touching a LOAD body.
pub fn verify_header(offset: usize, header: &[u8]) -> CryptoResult<bool> {
    verify_inner(offset, header, false)
}

fn verify_inner(offset: usize, header: &[u8], body_required: bool) -> CryptoResult<bool> {
    if header.len() < 32 {
        return Err(crypto::CryptoError::InvalidBufferLength);
    }
    #[cfg(not(test))]
    let page = {
        let area = super::physical::persistence_area();
        let size = super::physical::logical_page_size();
        if size != 0
            && offset.is_multiple_of(size)
            && offset / size < area.page_count
            && area.start.checked_add(offset) == Some(header.as_ptr() as usize)
        {
            Some((offset / size, area.page_count))
        } else {
            None
        }
    };
    #[cfg(not(test))]
    if let Some((index, _)) = page {
        if super::state::USED_PAGES.authenticated(index) {
            return Ok(true);
        }
    }
    let header_valid =
        crypto::constant_time_eq(&tag(offset, &header[..16], &header[32..])?, &header[16..32]);
    let crc_body = super::format::has_body_crc(header);
    let valid = header_valid
        && (!body_required
            || !crc_body
            || super::format::crc32_body(&header[32..])
                == u32::from_le_bytes(header[12..16].try_into().unwrap()));
    // Header-only LOAD validation and failures are deliberately not cached.
    #[cfg(not(test))]
    if valid && (!crc_body || body_required) {
        if let Some((index, _)) = page {
            super::state::USED_PAGES.authenticate(index);
        }
    }
    Ok(valid)
}

/// A complete authenticated block was programmed and verified by the backend.
pub fn remember_publication(offset: usize) {
    #[cfg(not(test))]
    {
        let size = super::physical::logical_page_size();
        let count = super::physical::persistence_area().page_count;
        if size != 0 && offset.is_multiple_of(size) && offset / size < count {
            super::state::USED_PAGES.authenticate(offset / size);
        }
    }
    #[cfg(test)]
    let _ = offset;
}

/// Called BEFORE every program/erase, including failed and diagnostic writes.
pub fn invalidate(address: usize, len: usize) {
    #[cfg(not(test))]
    {
        if len == 0 {
            return;
        }
        let area = super::physical::persistence_area();
        let size = super::physical::logical_page_size();
        let area_end = area
            .start
            .saturating_add(area.page_count.saturating_mul(size));
        let start = address.max(area.start);
        let end = address.saturating_add(len).min(area_end);
        if size == 0 || start >= end {
            return;
        }
        // A body write also invalidates its earlier header. Rejected candidates
        // are included: programming their missing tail can make them valid.
        let Some(bytes) = super::physical::read_area() else {
            super::state::USED_PAGES.invalidate_auth(size, 0, area.page_count * size, |_| None);
            return;
        };
        super::state::USED_PAGES.invalidate_auth(
            size,
            start - area.start,
            end - area.start,
            |offset| super::format::header_total_len(&bytes[offset..offset + 32], size).ok(),
        );
    }
    #[cfg(test)]
    let _ = (address, len);
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    #[test]
    fn staged_first_page_and_flash_tail_authenticate_the_same_message() {
        let body = [0x57; 513];
        let header = [0x39; 16];
        let expected = tag(256, &header, &body).unwrap();
        for split in [0, 1, 16, 224, 513] {
            assert_eq!(
                tag_split(256, &header, &body[..split], &body[split..]).unwrap(),
                expected
            );
        }
    }
}
