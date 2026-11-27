//! Canonical compact BOSS plaintext, shared by RAM and flash.
//!
//! Only identities, lifecycle and addresses live here. Object metadata is read
//! separately after authenticating its backing block. No pointer is dereferenced
//! by this module. Storage validates addresses against its configured regions.

use super::format::{PersistentAid, PersistentKindWord, PersistentObjectKind};
use super::objects::{RegistryError, RegistryResult};
use rustlet_runtime::Aid;

pub(crate) use super::limits::CAPACITY;
pub(crate) const ENTRY_LEN: usize = 40;
#[cfg(test)]
pub(crate) const MAX_IMAGE_LEN: usize = 8 + CAPACITY * ENTRY_LEN;

/// Non-null 32-bit backing reference. On persistent targets this is an absolute
/// flash address. On targets without persistence this is a RAM slot identifier.
/// The backing store validates the reference before resolving it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Address(core::num::NonZeroU32);

impl Address {
    pub(crate) fn new(raw: u32) -> RegistryResult<Self> {
        core::num::NonZeroU32::new(raw)
            .map(Self)
            .ok_or(RegistryError::InvalidData)
    }

    pub(crate) const fn get(self) -> u32 {
        self.0.get()
    }

    /// Resolve a complete span without wrapping at the top of address space.
    pub(crate) fn offset_in(self, base: u32, len: usize, span: usize) -> RegistryResult<usize> {
        let offset = self
            .get()
            .checked_sub(base)
            .ok_or(RegistryError::InvalidData)? as usize;
        if span == 0
            || offset.checked_add(span).filter(|end| *end <= len).is_none()
            || u64::from(base)
                .checked_add(len as u64)
                .filter(|end| *end <= u64::from(u32::MAX) + 1)
                .is_none()
        {
            return Err(RegistryError::InvalidData);
        }
        Ok(offset)
    }
}

/// Byte representation has no padding and needs no unsafe casts or native
/// endianness assumptions. A transient entry copy costs exactly 40 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub(crate) struct Entry([u8; ENTRY_LEN]);

impl Entry {
    pub(crate) const EMPTY: Self = Self([0; ENTRY_LEN]);

    pub(crate) fn is_empty(&self) -> bool {
        self.0 == [0; ENTRY_LEN]
    }

    pub(crate) fn new(
        object: Aid,
        parent: Aid,
        kind: PersistentKindWord,
        address: Address,
    ) -> RegistryResult<Self> {
        if object.len == 0 || object.len > 16 || parent.len > 16 {
            return Err(RegistryError::InvalidData);
        }
        let mut bytes = [0; ENTRY_LEN];
        bytes[..17].copy_from_slice(&PersistentAid::from_aid(&object).encoded());
        bytes[17..34].copy_from_slice(&PersistentAid::from_aid(&parent).encoded());
        bytes[34..36].copy_from_slice(&kind.raw().to_le_bytes());
        bytes[36..].copy_from_slice(&address.get().to_le_bytes());
        Self::decode(&bytes)
    }

    pub(crate) fn decode(bytes: &[u8]) -> RegistryResult<Self> {
        let bytes: [u8; ENTRY_LEN] = bytes.try_into().map_err(|_| RegistryError::InvalidData)?;
        if bytes == [0; ENTRY_LEN] {
            return Ok(Self::EMPTY);
        }
        for (start, allow_empty) in [(0, false), (17, true)] {
            let len = bytes[start] as usize;
            if len > 16
                || (!allow_empty && len == 0)
                || bytes[start + 1 + len..start + 17].iter().any(|b| *b != 0)
            {
                return Err(RegistryError::InvalidData);
            }
        }
        let word = PersistentKindWord::from_raw(u16::from_le_bytes([bytes[34], bytes[35]]))
            .map_err(|_| RegistryError::InvalidData)?;
        // Every currently implemented family has exactly two lifecycle states,
        // except data, which has none. Reject reserved bits before decisions.
        let max_state = if word.kind() == PersistentObjectKind::Data {
            0
        } else {
            1
        };
        if word.state_bits() > max_state {
            return Err(RegistryError::InvalidData);
        }
        Address::new(u32::from_le_bytes(bytes[36..40].try_into().unwrap()))?;
        Ok(Self(bytes))
    }

    pub(crate) fn object(&self) -> Aid {
        Aid::new(&self.0[1..1 + self.0[0] as usize])
    }

    pub(crate) fn parent(&self) -> Aid {
        Aid::new(&self.0[18..18 + self.0[17] as usize])
    }

    pub(crate) fn kind(&self) -> PersistentKindWord {
        PersistentKindWord::from_raw(u16::from_le_bytes([self.0[34], self.0[35]])).unwrap()
    }

    pub(crate) fn address(&self) -> Address {
        Address::new(u32::from_le_bytes(self.0[36..40].try_into().unwrap())).unwrap()
    }

    pub(crate) fn bytes(&self) -> &[u8; ENTRY_LEN] {
        &self.0
    }

    fn conflicts(&self, other: &Self) -> bool {
        self.kind().kind() == other.kind().kind()
            && self.object() == other.object()
            && (self.parent() == other.parent()
                || !matches!(
                    self.kind().kind(),
                    PersistentObjectKind::Key | PersistentObjectKind::Data
                ))
    }
}

/// The only registry table. The live prefix is already serialized. The length
/// is RAM control, not another persistent count; flash derives it from useful_len.
#[repr(C)]
pub(crate) struct Image<const N: usize = CAPACITY> {
    generation: [u8; 8],
    entries: [Entry; N],
    len: u32,
}

impl<const N: usize> Image<N> {
    pub(crate) const fn new() -> Self {
        Self {
            generation: [0; 8],
            entries: [Entry::EMPTY; N],
            len: 0,
        }
    }

    pub(crate) fn entries(&self) -> &[Entry] {
        &self.entries[..self.len as usize]
    }

    #[cfg(test)]
    pub(crate) fn generation(&self) -> u64 {
        u64::from_le_bytes(self.generation)
    }

    pub(crate) fn set_generation(&mut self, generation: u64) {
        self.generation = generation.to_le_bytes();
    }

    /// Validate the entire incoming authenticated image before replacing RAM.
    /// Quadratic duplicate checks are bounded by 63; they need no second table.
    pub(crate) fn restore(&mut self, bytes: &[u8]) -> RegistryResult {
        if bytes.len() < 8
            || bytes.len() > 8 + N * ENTRY_LEN
            || !(bytes.len() - 8).is_multiple_of(ENTRY_LEN)
        {
            return Err(RegistryError::InvalidData);
        }
        let count = (bytes.len() - 8) / ENTRY_LEN;
        for i in 0..count {
            let entry = Entry::decode(&bytes[8 + i * ENTRY_LEN..8 + (i + 1) * ENTRY_LEN])?;
            for j in 0..i {
                let previous = Entry::decode(&bytes[8 + j * ENTRY_LEN..8 + (j + 1) * ENTRY_LEN])?;
                if !entry.is_empty() && !previous.is_empty() && entry.conflicts(&previous) {
                    return Err(RegistryError::InvalidData);
                }
            }
        }
        self.generation.copy_from_slice(&bytes[..8]);
        for (slot, bytes) in self.entries[..count]
            .iter_mut()
            .zip(bytes[8..].chunks_exact(ENTRY_LEN))
        {
            slot.0.copy_from_slice(bytes);
        }
        self.entries[count..].fill(Entry::EMPTY);
        self.len = count as u32;
        Ok(())
    }

    /// Copy directly into the caller's existing encryption/programming scratch.
    pub(crate) fn encode(&self, out: &mut [u8]) -> RegistryResult<usize> {
        let len = 8 + self.len as usize * ENTRY_LEN;
        if out.len() < len {
            return Err(RegistryError::OutputTooSmall);
        }
        out[..8].copy_from_slice(&self.generation);
        for (entry, out) in self
            .entries()
            .iter()
            .zip(out[8..len].chunks_exact_mut(ENTRY_LEN))
        {
            out.copy_from_slice(entry.bytes());
        }
        Ok(len)
    }

    pub(crate) fn slot(&self, index: usize) -> Option<Entry> {
        self.entries().get(index).copied().filter(|e| !e.is_empty())
    }
    pub(crate) fn write_slot(&mut self, index: usize, entry: Entry) {
        assert!(index < N);
        self.entries[index] = entry;
        self.len = self.len.max(index as u32 + 1);
        while self.len > 0 && self.entries[self.len as usize - 1].is_empty() {
            self.len -= 1;
        }
    }
    pub(crate) fn clear(&mut self) {
        self.entries.fill(Entry::EMPTY);
        self.len = 0;
        self.generation = [0; 8];
    }
}

// Stable on both 32- and 64-bit hosts; never hide pointer-sized fields here.
const _: () = assert!(core::mem::size_of::<Entry>() == 40);
const _: () = assert!(core::mem::size_of::<Image>() == 2532);
const _: () = assert!(core::mem::size_of::<crate::kernel_cell::KernelCell<Image>>() == 2536);

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(id: u8) -> Entry {
        Entry::new(
            Aid::new(&[id]),
            Aid::new(&[1]),
            PersistentKindWord::new(PersistentObjectKind::Data, 0),
            Address::new(0x1000_0100 + u32::from(id) * 256).unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn full_image_has_63_entries_and_exact_plaintext_size() {
        let mut image = Image::<CAPACITY>::new();
        for i in 0..63 {
            image.write_slot(i as usize, entry(i));
        }
        let mut out = [0xa5; MAX_IMAGE_LEN + 1];
        assert_eq!(image.encode(&mut out), Ok(MAX_IMAGE_LEN));
        assert_eq!(out[MAX_IMAGE_LEN], 0xa5);
        let mut restored = Image::<CAPACITY>::new();
        restored.restore(&out[..MAX_IMAGE_LEN]).unwrap();
        assert_eq!(restored.entries(), image.entries());
    }

    #[test]
    fn malformed_restore_preserves_the_whole_view() {
        let mut image = Image::<CAPACITY>::new();
        image.write_slot(0, entry(1));
        image.set_generation(42);
        let mut bytes = [0; 88];
        bytes[..8].copy_from_slice(&99u64.to_le_bytes());
        bytes[8..48].copy_from_slice(entry(2).bytes());
        bytes[48..].copy_from_slice(entry(2).bytes());
        assert_eq!(image.restore(&bytes), Err(RegistryError::InvalidData));
        assert_eq!(image.entries(), &[entry(1)]);
        assert_eq!(image.generation(), 42);
        bytes[48] = 17;
        assert_eq!(image.restore(&bytes), Err(RegistryError::InvalidData));
        assert_eq!(image.entries(), &[entry(1)]);
    }

    #[test]
    fn slots_survive_deletion_and_address_resolution_rejects_wraparound() {
        let mut image = Image::<CAPACITY>::new();
        for i in 1..4 {
            image.write_slot(i as usize - 1, entry(i));
        }
        image.write_slot(1, Entry::EMPTY);
        assert_eq!(image.slot(0), Some(entry(1)));
        assert_eq!(image.slot(1), None);
        assert_eq!(image.slot(2), Some(entry(3)));
        assert_eq!(Address::new(0), Err(RegistryError::InvalidData));
        let address = Address::new(0xffff_ff00).unwrap();
        assert_eq!(address.offset_in(0xffff_fe00, 512, 256), Ok(256));
        assert_eq!(
            address.offset_in(0xffff_fe00, 512, 257),
            Err(RegistryError::InvalidData)
        );
        assert_eq!(
            address.offset_in(0xffff_fe00, 513, 1),
            Err(RegistryError::InvalidData)
        );
    }
}

pub(crate) fn plaintext_entry(bytes: &[u8], slot: usize) -> RegistryResult<Option<Entry>> {
    let Some(start) = slot.checked_mul(ENTRY_LEN).and_then(|n| n.checked_add(8)) else {
        return Ok(None);
    };
    let Some(raw) = bytes.get(start..start + ENTRY_LEN) else {
        return Ok(None);
    };
    Ok(Some(Entry::decode(raw)?).filter(|entry| !entry.is_empty()))
}
