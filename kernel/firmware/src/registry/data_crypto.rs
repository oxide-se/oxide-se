//! AES-CBC for Data, state and key bodies. The block CMAC authenticates the
//! metadata, ciphertext and padding before a trusted range reference is exposed.
use super::format::{self, PersistenceFormatError};
use crate::registry::objects::{RegistryError, RegistryResult};
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
        let result = crypto::hkdf_sha256(root, b"oXiDe registry Data v3", label, &mut bytes)
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
// Key derivation owns large temporaries. Release them before using cached keys.
#[cfg(not(test))]
#[inline(never)]
fn initialize_keys(keys: &mut Option<Keys>) -> CryptoResult<()> {
    *keys = Some(derive()?);
    Ok(())
}

fn with_keys<T>(f: impl FnOnce(&Keys) -> CryptoResult<T>) -> CryptoResult<T> {
    #[cfg(test)]
    {
        f(&derive()?)
    }
    #[cfg(not(test))]
    {
        let mut keys = KEYS.borrow_mut();
        if keys.is_none() {
            initialize_keys(&mut keys)?;
        }
        f(keys.as_ref().unwrap())
    }
}

// Reserve BEFORE any attempted encryption, including a subsequently aborted write.
// None means uninitialized; Some(None) means permanently exhausted for this boot.
#[cfg(not(test))]
static SEED: crate::kernel_cell::KernelCell<Option<Option<u64>>> =
    unsafe { crate::kernel_cell::KernelCell::new(None) };
pub(super) fn reserve_seed() -> CryptoResult<u64> {
    #[cfg(test)]
    {
        static SEED: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(1);
        Ok(SEED.fetch_add(1, core::sync::atomic::Ordering::Relaxed))
    }
    #[cfg(not(test))]
    {
        let mut seed = SEED.borrow_mut();
        if seed.is_none() {
            let mut bytes = [0; 8];
            crypto::fill_random(&mut bytes)?;
            *seed = Some(Some(u64::from_le_bytes(bytes)));
        }
        let value = seed
            .unwrap()
            .ok_or(crypto::CryptoError::InvalidBufferLength)?;
        *seed = Some(value.checked_add(1));
        Ok(value)
    }
}
fn iv(keys: &Keys, offset: usize, seed: u64) -> CryptoResult<[u8; 16]> {
    let offset = u32::try_from(offset).map_err(|_| crypto::CryptoError::InvalidBufferLength)?;
    let mut iv = [0; 16];
    iv[..4].copy_from_slice(&0x0003_0001u32.to_le_bytes());
    iv[4..8].copy_from_slice(&offset.to_le_bytes());
    iv[8..].copy_from_slice(&seed.to_le_bytes());
    crypto::aes_ecb_encrypt_in_place(&keys.iv, &mut iv)?;
    Ok(iv)
}
pub(super) fn prepare_header(
    offset: usize,
    len: usize,
    header: &mut [u8],
) -> CryptoResult<[u8; 16]> {
    prepare_header_for(format::ENCRYPTED_DATA_MAGIC, offset, len, header)
}
pub(super) fn prepare_header_for(
    magic: u32,
    offset: usize,
    len: usize,
    header: &mut [u8],
) -> CryptoResult<[u8; 16]> {
    let len = u32::try_from(len).map_err(|_| crypto::CryptoError::InvalidBufferLength)?;
    let seed = reserve_seed()?;
    header[..4].copy_from_slice(&magic.to_le_bytes());
    header[4..8].copy_from_slice(&len.to_le_bytes());
    header[8..16].copy_from_slice(&seed.to_le_bytes());
    with_keys(|keys| iv(keys, offset, seed))
}
pub(super) fn encrypt(iv: &mut [u8; 16], bytes: &mut [u8]) -> CryptoResult<()> {
    if bytes.is_empty() {
        return Ok(());
    }
    with_keys(|keys| crypto::aes_cbc_encrypt_in_place(&keys.enc, iv, bytes))?;
    iv.copy_from_slice(&bytes[bytes.len() - 16..]);
    Ok(())
}

/// Immutable structural flash reference, authenticated on first access. No plaintext.
#[derive(Clone, Copy)]
pub struct DataRef {
    block: &'static [u8],
    offset: usize,
}
impl DataRef {
    /// Structural reference only; the body is authenticated on first use.
    pub(super) fn from_structural(
        area: &'static [u8],
        offset: usize,
        page_size: usize,
    ) -> Result<Self, PersistenceFormatError> {
        let view = format::decode_object_block_trusted(area, offset, page_size)?;
        if !format::is_encrypted_magic(view.magic) {
            return Err(PersistenceFormatError::InvalidBlockMagic);
        }
        Ok(Self {
            block: &area[offset..offset + view.total_len],
            offset,
        })
    }
    pub(super) fn offset(self) -> usize {
        self.offset
    }
    pub(super) fn total_len(self) -> usize {
        self.block.len()
    }
    pub(crate) fn len(self) -> usize {
        u32::from_le_bytes(self.block[4..8].try_into().unwrap()) as usize
    }
    pub(crate) fn authenticate(self) -> RegistryResult {
        super::header_auth::verify(self.offset, self.block)
            .map_err(|_| RegistryError::Persistence)?
            .then_some(())
            .ok_or(RegistryError::Persistence)
    }
    pub(crate) fn read_range(self, start: usize, out: &mut [u8]) -> RegistryResult<usize> {
        self.authenticate()?;
        self.read_range_unchecked(start, out)
    }
    /// Recovery reads only fixed metadata needed to materialize RAM references.
    /// No decision may use this metadata until `authenticate` succeeds.
    pub(super) fn read_range_unchecked(
        self,
        start: usize,
        out: &mut [u8],
    ) -> RegistryResult<usize> {
        if start > self.len() {
            return Err(RegistryError::InvalidData);
        }
        let take = out.len().min(self.len() - start);
        if take == 0 {
            return Ok(0);
        }
        let seed = u64::from_le_bytes(self.block[8..16].try_into().unwrap());
        let result = with_keys(|keys| {
            read(
                keys,
                self.offset,
                seed,
                &self.block[32..],
                start,
                &mut out[..take],
            )
        });
        if result.is_err() {
            secure_zero(&mut out[..take]);
            return Err(RegistryError::Persistence);
        }
        Ok(take)
    }
}

fn read(
    keys: &Keys,
    offset: usize,
    seed: u64,
    ciphertext: &[u8],
    start: usize,
    out: &mut [u8],
) -> CryptoResult<()> {
    let position = start / 16 * 16;
    let chain = if position == 0 {
        iv(keys, offset, seed)?
    } else {
        ciphertext[position - 16..position].try_into().unwrap()
    };
    let skip = start % 16;
    let touched = (skip + out.len()).div_ceil(16) * 16;
    crypto::aes_cbc_decrypt_range_into(
        &keys.enc,
        &chain,
        &ciphertext[position..position + touched],
        skip,
        out,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{boxed::Box, vec};

    fn fixture(len: usize, offset: usize) -> DataRef {
        let plaintext: alloc::vec::Vec<u8> = (0..len).map(|i| (i * 29 + 7) as u8).collect();
        let size = format::object_block_total_len(format::ENCRYPTED_DATA_MAGIC, len, 256).unwrap();
        let mut area = vec![0xff; offset + size];
        format::encode_object_block_at(
            offset,
            format::ENCRYPTED_DATA_MAGIC,
            &plaintext,
            256,
            &mut area[offset..],
        )
        .unwrap();
        format::decode_object_block_at(&area, offset, 256).unwrap();
        if len > 0 {
            assert_ne!(&area[offset + 32..offset + 32 + len], &plaintext);
        }
        DataRef::from_structural(Box::leak(area.into_boxed_slice()), offset, 256).unwrap()
    }

    #[test]
    fn recovered_reference_rejects_corrupted_body_on_first_read() {
        let mut area = vec![0xff; 512];
        format::encode_object_block_at(
            256,
            format::ENCRYPTED_DATA_MAGIC,
            b"secret",
            256,
            &mut area[256..],
        )
        .unwrap();
        area[256 + 32] ^= 1;
        let data = DataRef::from_structural(Box::leak(area.into_boxed_slice()), 256, 256).unwrap();
        let mut out = [0xa5; 6];
        assert_eq!(
            data.read_range(0, &mut out),
            Err(RegistryError::Persistence)
        );
        assert_eq!(out, [0xa5; 6]);
    }

    #[test]
    fn scanner_skips_only_fully_authenticated_data_extent() {
        let data = fixture(244, 0);
        let mut area = vec![0xff; 1024];
        area[..512].copy_from_slice(data.block);
        // A valid-looking BOSS inside a Data body must never become a root.
        format::encode_registry_block_at(256, 99, &[], 256, &mut area[256..]).unwrap();
        format::seal_block(0, &mut area[..512]).unwrap();
        format::encode_registry_block_at(512, 7, &[], 256, &mut area[512..]).unwrap();
        assert_eq!(
            format::find_latest_registry_block(&area, 256)
                .unwrap()
                .unwrap()
                .offset,
            512
        );
        // Rejected header advances only one page and discovers the nested candidate.
        area[16] ^= 1;
        assert_eq!(
            format::find_latest_registry_block(&area, 256)
                .unwrap()
                .unwrap()
                .offset,
            256
        );
    }

    #[test]
    fn extraction_all_alignments_edges_and_eof_without_touching_destination_tail() {
        for len in [0, 1, 15, 16, 17, 208, 209, 216, 217, 244, 256, 4096] {
            let data = fixture(len, 256);
            assert_eq!(data.len(), len);
            for start in
                (0..=len.min(33)).chain([len.saturating_sub(17), len.saturating_sub(1), len])
            {
                for capacity in [0, 1, 15, 16, 17, 31, 32, 63, 244] {
                    let mut output = [0xa5; 244];
                    let expected = (len - start).min(capacity);
                    assert_eq!(
                        data.read_range(start, &mut output[..capacity]),
                        Ok(expected)
                    );
                    for i in 0..expected {
                        assert_eq!(output[i], ((start + i) * 29 + 7) as u8);
                    }
                    assert!(output[expected..].iter().all(|&b| b == 0xa5));
                }
            }
            let mut output = [0xa5; 17];
            assert_eq!(
                data.read_range(len + 1, &mut output),
                Err(RegistryError::InvalidData)
            );
            assert_eq!(output, [0xa5; 17]);
        }
    }

    #[test]
    fn distant_range_does_not_decrypt_or_verify_preceding_body() {
        let data = fixture(4096, 256);
        let keys = derive().unwrap();
        let seed = u64::from_le_bytes(data.block[8..16].try_into().unwrap());
        let mut ciphertext = data.block[32..].to_vec();
        ciphertext[..960].fill(0); // excludes block 960..975, needed as CBC chaining value
        let mut out = [0; 33];
        read(&keys, 256, seed, &ciphertext, 977, &mut out).unwrap();
        for (i, byte) in out.iter().enumerate() {
            assert_eq!(*byte, ((977 + i) * 29 + 7) as u8);
        }
    }

    #[test]
    fn nonce_changes_and_binds_ciphertext_to_address() {
        let first = fixture(244, 256);
        let second = fixture(244, 256);
        assert_ne!(&first.block[8..16], &second.block[8..16]);
        assert_ne!(&first.block[32..288], &second.block[32..288]);
        let keys = derive().unwrap();
        assert_ne!(iv(&keys, 256, 42).unwrap(), iv(&keys, 512, 42).unwrap());
        let mut a = [0; 16];
        let mut b = a;
        crypto::aes_ecb_encrypt_in_place(&keys.enc, &mut a).unwrap();
        crypto::aes_ecb_encrypt_in_place(&keys.iv, &mut b).unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn whole_block_cmac_rejects_changed_metadata_ciphertext_and_torn_body() {
        let first = fixture(244, 256);
        let mut area = vec![0xff; 1024];
        area[256..768].copy_from_slice(first.block);
        assert!(format::decode_object_block_at(&area, 256, 256).is_ok());
        area[256 + 8] ^= 1;
        assert!(matches!(
            format::decode_object_block_at(&area, 256, 256),
            Err(PersistenceFormatError::Authentication)
        ));
        area[256 + 8] ^= 1;
        area[256 + 32] ^= 1;
        assert!(matches!(
            format::decode_object_block_at(&area, 256, 256),
            Err(PersistenceFormatError::Authentication)
        ));
        area[256 + 32] ^= 1;
        for prefix in [0, 1, 15, 16, 17, 31, 32, 33, 255, 256, 287] {
            area[256..768].fill(0xff);
            area[256..256 + prefix].copy_from_slice(&first.block[..prefix]);
            assert!(format::decode_object_block_at(&area, 256, 256).is_err());
        }
    }
}
