//! Immutable object content. Persistent targets retain flash references only.
//! Owned content is reserved for host tests and targets without registry flash.
use super::{
    format,
    objects::{Registry, RegistryError, RegistryResult},
};
use alloc::{rc::Rc, vec::Vec};

pub struct VolatileBytes(Vec<u8>);
impl Drop for VolatileBytes {
    fn drop(&mut self) {
        oxi_core::core::secure_zero(&mut self.0);
    }
}
#[derive(Clone)]
pub enum Content {
    #[cfg(test)]
    Flash {
        bytes: &'static [u8],
        offset: usize,
        total: usize,
    },
    Volatile(Rc<VolatileBytes>),
    Encrypted {
        data: super::data_crypto::DataRef,
        start: usize,
    },
}
impl Content {
    pub fn volatile(bytes: &[u8]) -> Self {
        Self::Volatile(Rc::new(VolatileBytes(bytes.into())))
    }
    #[cfg(not(test))]
    pub(crate) fn volatile_generated(
        len: usize,
        byte: impl FnMut(usize) -> u8,
    ) -> RegistryResult<Self> {
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(len)
            .map_err(|_| RegistryError::Capacity)?;
        bytes.extend((0..len).map(byte));
        Ok(Self::Volatile(Rc::new(VolatileBytes(bytes))))
    }

    pub fn range(&self) -> Option<format::PersistentRange> {
        match self {
            #[cfg(test)]
            Self::Flash { offset, total, .. } => {
                Some(format::PersistentRange::new(*offset, *total))
            }
            Self::Encrypted { data, .. } => Some(format::PersistentRange::new(
                data.offset(),
                data.total_len(),
            )),
            _ => None,
        }
    }
    pub fn len(&self) -> usize {
        match self {
            #[cfg(test)]
            Self::Flash { bytes, .. } => bytes.len(),
            Self::Volatile(bytes) => bytes.0.len(),
            Self::Encrypted { data, start } => data.len() - start,
        }
    }
    pub fn read_range(&self, start: usize, out: &mut [u8]) -> RegistryResult<usize> {
        if start > self.len() {
            return Err(RegistryError::InvalidData);
        }
        let take = out.len().min(self.len() - start);
        match self {
            Self::Encrypted {
                data, start: base, ..
            } => data.read_range(base + start, &mut out[..take]),
            _ => {
                out[..take].copy_from_slice(&self.clear_bytes().unwrap()[start..start + take]);
                Ok(take)
            }
        }
    }
    pub fn clear_bytes(&self) -> Option<&[u8]> {
        match self {
            #[cfg(test)]
            Self::Flash { bytes, .. } => Some(bytes),
            Self::Volatile(bytes) => Some(&bytes.0),
            _ => None,
        }
    }
    /// Neutral serialization must not program another immutable version.
    /// Use existing publication scratch, never a body-sized stack allocation.
    pub fn matches(&self, bytes: &[u8]) -> bool {
        self.matches_generated(bytes.len(), |i| bytes[i])
            .unwrap_or(false)
    }

    /// Compare before reserving flash or materializing a deferred snapshot.
    /// Reuse the existing scratch in bounded chunks; no resident cache is added.
    pub(crate) fn matches_generated(
        &self,
        len: usize,
        mut byte: impl FnMut(usize) -> u8,
    ) -> RegistryResult<bool> {
        if self.len() != len {
            return Ok(false);
        }
        if let Some(clear) = self.clear_bytes() {
            return Ok(clear.iter().enumerate().all(|(i, &value)| value == byte(i)));
        }
        if len == 0 {
            // Even an empty encrypted object must authenticate before reuse.
            return self.read_range(0, &mut []).map(|_| true);
        }
        let mut scratch = super::state::PERSISTENCE_PAYLOAD_BUFFER.borrow_mut();
        let mut start = 0;
        while start < len {
            let take = (len - start).min(scratch.len());
            let out = &mut scratch[..take];
            let read = self.read_range(start, out);
            let equal = read == Ok(take)
                && out
                    .iter()
                    .enumerate()
                    .all(|(i, &value)| value == byte(start + i));
            oxi_core::core::secure_zero(out);
            read?;
            if !equal {
                return Ok(false);
            }
            start += take;
        }
        Ok(true)
    }
    /// Writes the immutable body before its reference is attached to the RAM index.
    /// Recovery constructs Encrypted references separately, without programming flash.
    pub fn store<const N: usize>(
        registry: &Registry<N>,
        magic: u32,
        prefix: &[u8],
        bytes: &[u8],
    ) -> RegistryResult<Self> {
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        let _timing = crate::registry::perf::start(crate::registry::perf::Metric::PrepareObject);
        let Some(area) = super::physical::read_area() else {
            return Ok(Self::volatile(bytes));
        };
        let magic = match magic {
            format::INSTANCE_STATE_BLOCK_MAGIC => format::ENCRYPTED_STATE_MAGIC,
            format::DATA_BLOCK_MAGIC => format::ENCRYPTED_KEY_MAGIC,
            other => other,
        };
        let page_size = super::physical::logical_page_size();
        super::storage::require_writable()?;
        if !super::storage::ensure_persistence_area_initialized(area, page_size) {
            return Err(RegistryError::Persistence);
        }
        let protected = &super::state::USED_PAGES;
        let _count =
            super::payload::build_persistence_protection_for(registry, area, page_size, protected)
                .ok_or(RegistryError::Persistence)?;
        // Align the logical body: reads start after the encrypted metadata and
        // use its last ciphertext block directly as the CBC chaining value.
        let body_start = prefix.len().div_ceil(16) * 16;
        let len = body_start
            .checked_add(bytes.len())
            .ok_or(RegistryError::Capacity)?;
        let total = format::object_block_total_len(magic, len, page_size)
            .map_err(|_| RegistryError::Capacity)?;
        #[cfg(oxide_se_board_raspi_pico)]
        if total > super::state::PERSISTENCE_PAYLOAD_BUFFER_SIZE {
            return Err(RegistryError::Capacity);
        }
        #[cfg(not(oxide_se_board_raspi_pico))]
        if total > super::storage::PERSISTENCE_PAGE_BUFFER_SIZE {
            return Err(RegistryError::Capacity);
        }
        let offset = super::storage::reserve_persistent_span(area, page_size, total, protected)?;
        #[cfg(not(oxide_se_board_raspi_pico))]
        if total > super::state::PERSISTENCE_PAYLOAD_BUFFER_SIZE {
            let result =
                Self::store_large_page(area, offset, total, page_size, magic, prefix, bytes);
            if result.is_err() {
                super::retention::release_unattached(
                    protected,
                    format::PersistentRange::new(offset, total),
                )?;
            }
            return result;
        }
        let mut buffer = super::state::PERSISTENCE_PAYLOAD_BUFFER.borrow_mut();
        let block = &mut buffer[..total];
        block.fill(0xff);
        block[32..32 + prefix.len()].copy_from_slice(prefix);
        block[32 + body_start..32 + len].copy_from_slice(bytes);
        let result = (|| {
            let mut iv = super::data_crypto::prepare_header_for(magic, offset, len, block)
                .map_err(|_| RegistryError::Persistence)?;
            let cipher_end = 32 + len.div_ceil(16) * 16;
            super::data_crypto::encrypt(&mut iv, &mut block[32..cipher_end])
                .map_err(|_| RegistryError::Persistence)?;
            format::seal_block(offset, block).map_err(|_| RegistryError::Persistence)?;
            super::storage::write_persistent_block(offset, block)
        })();
        oxi_core::core::secure_zero(block);
        if let Err(error) = result {
            super::retention::release_unattached(
                protected,
                format::PersistentRange::new(offset, total),
            )?;
            return Err(error);
        }
        super::header_auth::remember_publication(offset);
        let data = super::data_crypto::DataRef::from_structural(area, offset, page_size)
            .map_err(|_| RegistryError::Persistence)?;
        Ok(Self::Encrypted {
            data,
            start: body_start,
        })
    }
    /// Large-page targets reuse the existing physical page scratch. Preserve a
    /// pending LOAD only on that path, as the BOSS publisher already does.
    #[cfg(not(oxide_se_board_raspi_pico))]
    fn store_large_page(
        area: &'static [u8],
        offset: usize,
        total: usize,
        page_size: usize,
        magic: u32,
        prefix: &[u8],
        bytes: &[u8],
    ) -> RegistryResult<Self> {
        let mut saved = Vec::new();
        if super::state::dynamic_package_load_in_progress() {
            saved
                .try_reserve_exact(page_size)
                .map_err(|_| RegistryError::Capacity)?;
            saved.extend_from_slice(&super::storage::PERSISTENCE_PAGE_BUFFER.borrow()[..page_size]);
        }
        let mut scratch = super::storage::PERSISTENCE_PAGE_BUFFER.borrow_mut();
        let block = &mut scratch[..total];
        let start = prefix.len().div_ceil(16) * 16;
        let len = start + bytes.len();
        block.fill(0xff);
        block[32..32 + prefix.len()].copy_from_slice(prefix);
        block[32 + start..32 + len].copy_from_slice(bytes);
        let result = (|| {
            let mut iv = super::data_crypto::prepare_header_for(magic, offset, len, block)
                .map_err(|_| RegistryError::Persistence)?;
            super::data_crypto::encrypt(&mut iv, &mut block[32..32 + len.div_ceil(16) * 16])
                .map_err(|_| RegistryError::Persistence)?;
            format::seal_block(offset, block).map_err(|_| RegistryError::Persistence)?;
            super::storage::write_persistent_block(offset, block)
        })();
        oxi_core::core::secure_zero(block);
        if !saved.is_empty() {
            scratch[..saved.len()].copy_from_slice(&saved);
            oxi_core::core::secure_zero(&mut saved);
        }
        result?;
        super::header_auth::remember_publication(offset);
        let data = super::data_crypto::DataRef::from_structural(area, offset, page_size)
            .map_err(|_| RegistryError::Persistence)?;
        Ok(Self::Encrypted { data, start })
    }
}

#[cfg(test)]
mod encrypted_tests {
    use super::*;
    #[test]
    fn generated_comparison_spans_scratch_and_authenticates_empty_content() {
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        for len in [0, 244, 513, 1025] {
            let bytes: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
            let mut area = alloc::vec![0xff; 2048];
            format::encode_object_block_at(
                256,
                format::ENCRYPTED_DATA_MAGIC,
                &bytes,
                256,
                &mut area[256..],
            )
            .unwrap();
            let area = alloc::boxed::Box::leak(area.into_boxed_slice());
            let data = super::super::data_crypto::DataRef::from_structural(area, 256, 256).unwrap();
            let content = Content::Encrypted { data, start: 0 };
            assert_eq!(content.matches_generated(len, |i| bytes[i]), Ok(true));
            assert_eq!(content.matches_generated(len + 1, |_| 0), Ok(false));
            if len > 0 {
                assert_eq!(
                    content.matches_generated(len, |i| bytes[i] ^ u8::from(i == len - 1)),
                    Ok(false)
                );
            }
        }
    }

    #[test]
    fn encrypted_metadata_prefix_never_leaks_into_range_or_destination_tail() {
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        for (magic, prefix) in [
            (format::ENCRYPTED_STATE_MAGIC, 25usize),
            (format::ENCRYPTED_STATE_MAGIC, 21),
            (format::ENCRYPTED_KEY_MAGIC, 9),
            (format::ENCRYPTED_STATE_MAGIC, 32),
            (format::ENCRYPTED_KEY_MAGIC, 16),
        ] {
            for len in [0usize, 1, 16, 17, 208, 244] {
                let plaintext: Vec<u8> = (0..prefix + len).map(|i| (i % 251) as u8).collect();
                let mut area = alloc::vec![0xff; 1024];
                format::encode_object_block_at(256, magic, &plaintext, 256, &mut area[256..])
                    .unwrap();
                let area = alloc::boxed::Box::leak(area.into_boxed_slice());
                let data =
                    super::super::data_crypto::DataRef::from_structural(area, 256, 256).unwrap();
                let content = Content::Encrypted {
                    data,
                    start: prefix,
                };
                assert!(content.matches(&plaintext[prefix..]));
                for start in 0..=len {
                    let mut out = [0xa5; 33];
                    let take = content.read_range(start, &mut out).unwrap();
                    assert_eq!(take, (len - start).min(33));
                    assert_eq!(
                        &out[..take],
                        &plaintext[prefix + start..prefix + start + take]
                    );
                    assert!(out[take..].iter().all(|byte| *byte == 0xa5));
                }
                let mut out = [0xa5; 3];
                assert_eq!(
                    content.read_range(len + 1, &mut out),
                    Err(RegistryError::InvalidData)
                );
                assert_eq!(out, [0xa5; 3]);
            }
        }
    }
}
