//! Persistent binary format for the kernel object registry.
//!
//! The in-RAM [`crate::registry::objects::Registry`] remains the structure
//! used by the firmware while it runs. This module defines the append-only
//! flash format used to rebuild that registry after boot and to publish a new
//! committed registry after each mutation.
//!
//! The persistence model is deliberately simple:
//! - data/package/state objects are written first;
//! - a new registry block is written only after all referenced objects exist;
//! - BOSS bodies are encrypted and authenticated with the complete stored block;
//!   LOAD keeps header CMAC and body CRC32, with no trailer;
//! - the newest journaled, valid registry block is authoritative.
//!
//! A runtime mutation must stay a single registry delta followed by one BOSS
//! publication. During that publication, the previous BOSS remains the recovery
//! root. Therefore the payload replaced or deleted by that one delta is not
//! recyclable until the new BOSS has been written and authenticated.
//!
//! All multi-byte integers are encoded little-endian. Blocks always start on a
//! flash logical page boundary, and their advertised total size is page-aligned.

use crate::registry::objects::{
    InstanceObjectState, KeyObjectState, KeyObjectType, ManagedObjectKind, ObjectPayload,
    ObjectView, PackageObjectState, SecurityDomainObjectBackend, SecurityDomainObjectState,
};
use rustlet_runtime::Aid;

/// First-page marker used to decide whether the persistence area was already
/// initialized.
///
/// If the first page does not begin with this value, the firmware must treat
/// the registry as unpersonalized and replay the predeployment manifest.
pub const PERSISTENCE_AREA_MAGIC: u64 = 0x6010_B055_6010_B00A;

/// Magic word for registry blocks.
///
/// `B055` reads as "BOSS": the latest valid block with this magic is the boss
/// copy of the registry.
pub const REGISTRY_BLOCK_MAGIC: u32 = 0x600D_B055;

/// Magic word for loaded package-code payload blocks.
pub const PACKAGE_BLOCK_MAGIC: u32 = 0x600D_C0DE;

/// Magic word for generic data/key payload blocks.
pub const DATA_BLOCK_MAGIC: u32 = 0x600D_BA5E;
/// Encrypted Data; state and key bodies have their own encrypted magic words.
pub const ENCRYPTED_DATA_MAGIC: u32 = 0x600D_DA7A;
pub const ENCRYPTED_STATE_MAGIC: u32 = 0x600D_FADE;
pub const ENCRYPTED_KEY_MAGIC: u32 = 0x600D_4B45;
pub(super) fn is_encrypted_magic(magic: u32) -> bool {
    matches!(
        magic,
        ENCRYPTED_DATA_MAGIC | ENCRYPTED_STATE_MAGIC | ENCRYPTED_KEY_MAGIC
    )
}

/// Magic word for serialized Rustlet instance-state payload blocks.
pub const INSTANCE_STATE_BLOCK_MAGIC: u32 = 0x600D_FACE;

const COMMON_HEADER_LEN: usize = 32;
const REGISTRY_HEADER_LEN: usize = 32;
const OBJECT_HEADER_LEN: usize = super::limits::OBJECT_BLOCK_HEADER_LEN;
const AID_ENCODED_LEN: usize = 17;
const SECURITY_DOMAIN_PAYLOAD_HEADER_LEN: usize = AID_ENCODED_LEN + 1 + 3 + 4;
const INSTANCE_PAYLOAD_HEADER_LEN: usize = AID_ENCODED_LEN + 4;
const KEY_PAYLOAD_HEADER_LEN: usize = 1 + 1 + 1 + 1 + 1 + 4;

/// Errors returned while encoding or scanning persistent registry blocks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PersistenceFormatError {
    InvalidAidLength,
    InvalidKind,
    InvalidPageSize,
    InvalidBlockSize,
    InvalidBlockMagic,
    BufferTooSmall,
    Authentication,
    Crypto,
    Truncated,
}

/// Number of bytes before the payload in a persistent object block.
pub const OBJECT_BLOCK_HEADER_LEN: usize = OBJECT_HEADER_LEN;

/// Returns the page-aligned size of an object block for one payload length.
pub fn object_block_total_len(
    magic: u32,
    payload_len: usize,
    page_size: usize,
) -> Result<usize, PersistenceFormatError> {
    validate_page_size(page_size)?;
    if !is_object_magic(magic) {
        return Err(PersistenceFormatError::InvalidBlockMagic);
    }
    let payload_len = if is_encrypted_magic(magic) {
        align_up(payload_len, 16)?
    } else {
        payload_len
    };
    let size = payload_len
        .checked_add(OBJECT_HEADER_LEN)
        .ok_or(PersistenceFormatError::InvalidBlockSize)?;
    align_up(size, page_size)
}

/// Functional family stored in the upper four bits of a persistent kind word.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PersistentObjectKind {
    SecurityDomain = 1,
    Package = 2,
    Instance = 3,
    Key = 4,
    Data = 5,
}

impl PersistentObjectKind {
    fn from_nibble(value: u8) -> Option<Self> {
        match value {
            1 => Some(Self::SecurityDomain),
            2 => Some(Self::Package),
            3 => Some(Self::Instance),
            4 => Some(Self::Key),
            5 => Some(Self::Data),
            _ => None,
        }
    }
}

/// Encodes an object kind plus twelve bits of kind-specific state.
///
/// The high nibble is the object family. The low twelve bits are intentionally
/// interpreted by that family only: privileges stay in Security Domain payloads,
/// package state belongs to packages, and key flags belong to key objects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentKindWord(u16);

impl PersistentKindWord {
    /// Builds a kind word from one object family and twelve state bits.
    pub const fn new(kind: PersistentObjectKind, state_bits: u16) -> Self {
        // Invariant: callers may pass a wider integer, but only the lower
        // twelve bits are persisted as kind-specific state.
        Self(((kind as u16) << 12) | (state_bits & 0x0FFF))
    }

    /// Decodes one persisted raw kind word.
    pub fn from_raw(raw: u16) -> Result<Self, PersistenceFormatError> {
        if PersistentObjectKind::from_nibble((raw >> 12) as u8).is_none() {
            return Err(PersistenceFormatError::InvalidKind);
        }
        Ok(Self(raw))
    }

    /// Returns the object family encoded in the high nibble.
    pub fn kind(self) -> PersistentObjectKind {
        // Invariant: constructors reject unknown high-nibble values.
        PersistentObjectKind::from_nibble((self.0 >> 12) as u8).unwrap()
    }

    /// Returns the kind-specific state bits encoded in the low twelve bits.
    pub const fn state_bits(self) -> u16 {
        self.0 & 0x0FFF
    }

    /// Returns the little-endian raw value stored in flash.
    pub const fn raw(self) -> u16 {
        self.0
    }
}

/// Persistent AID representation used in registry entries.
///
/// Byte 0 is the AID length. Bytes 1..=16 carry the AID value padded with zeroes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentAid {
    encoded: [u8; AID_ENCODED_LEN],
}

impl PersistentAid {
    pub const EMPTY: Self = Self {
        encoded: [0u8; AID_ENCODED_LEN],
    };

    /// Encodes one runtime AID for persistence.
    pub fn from_aid(aid: &Aid) -> Self {
        let mut encoded = [0u8; AID_ENCODED_LEN];
        encoded[0] = aid.len;
        encoded[1..1 + aid.len as usize].copy_from_slice(aid.as_slice());
        Self { encoded }
    }

    /// Decodes a persistent AID from its exact 17-byte representation.
    pub fn from_encoded(encoded: [u8; AID_ENCODED_LEN]) -> Result<Self, PersistenceFormatError> {
        if encoded[0] > 16 {
            return Err(PersistenceFormatError::InvalidAidLength);
        }
        Ok(Self { encoded })
    }

    /// Returns the exact 17 bytes stored in a persistent registry entry.
    pub const fn encoded(self) -> [u8; AID_ENCODED_LEN] {
        self.encoded
    }

    /// Converts the persistent AID back to the runtime representation.
    pub fn as_aid(self) -> Aid {
        Aid::new(&self.encoded[1..1 + self.encoded[0] as usize])
    }
}

/// Names the persistent address space referenced by one registry entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PersistentSpace {
    /// Object stored in the mutable append-only registry flash area.
    RegistryFlash = 0,
    /// Object embedded in immutable firmware/predeployment memory.
    FirmwareImage = 1,
    /// Object stored in another configured persistent backend.
    External = 2,
}

impl PersistentSpace {
    fn from_byte(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::RegistryFlash),
            1 => Some(Self::FirmwareImage),
            2 => Some(Self::External),
            _ => None,
        }
    }
}

/// Portable reference to the bytes associated with one registry entry.
///
/// The reference deliberately avoids storing a raw pointer. `offset` is
/// interpreted relative to the selected [`PersistentSpace`]. This lets a
/// registry entry refer either to an append-only flash object or to an object
/// predeployed in the firmware image without baking CPU pointer width into the
/// on-flash registry format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentRef {
    pub space: PersistentSpace,
    pub flags: u8,
    pub offset: u32,
}

impl PersistentRef {
    pub const ENCODED_LEN: usize = 8;
    pub const EMPTY: Self = Self {
        space: PersistentSpace::RegistryFlash,
        flags: 0,
        offset: 0,
    };

    /// Creates a new persistent reference.
    pub const fn new(space: PersistentSpace, flags: u8, offset: u32) -> Self {
        Self {
            space,
            flags,
            offset,
        }
    }

    /// Encodes the reference in the fixed registry-entry representation.
    pub fn encode(self, out: &mut [u8]) -> Result<(), PersistenceFormatError> {
        if out.len() < Self::ENCODED_LEN {
            return Err(PersistenceFormatError::BufferTooSmall);
        }
        out[0] = self.space as u8;
        out[1] = self.flags;
        out[2] = 0;
        out[3] = 0;
        write_u32_le(&mut out[4..8], self.offset);
        Ok(())
    }

    /// Decodes a fixed-size persistent reference.
    pub fn decode(input: &[u8]) -> Result<Self, PersistenceFormatError> {
        if input.len() < Self::ENCODED_LEN {
            return Err(PersistenceFormatError::Truncated);
        }
        let Some(space) = PersistentSpace::from_byte(input[0]) else {
            return Err(PersistenceFormatError::InvalidBlockSize);
        };
        Ok(Self {
            space,
            flags: input[1],
            offset: read_u32_le(&input[4..8]),
        })
    }
}

/// One fixed-size entry in a persistent registry block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentRegistryEntry {
    pub object_aid: PersistentAid,
    pub parent_sd_aid: PersistentAid,
    pub kind_word: PersistentKindWord,
    pub data_ref: PersistentRef,
}

impl PersistentRegistryEntry {
    pub const ENCODED_LEN: usize = 40;
    pub const EMPTY: Self = Self {
        object_aid: PersistentAid::EMPTY,
        parent_sd_aid: PersistentAid::EMPTY,
        kind_word: PersistentKindWord::new(PersistentObjectKind::Package, 0),
        data_ref: PersistentRef::EMPTY,
    };

    /// Encodes one registry entry.
    pub fn encode(self, out: &mut [u8]) -> Result<(), PersistenceFormatError> {
        if out.len() < Self::ENCODED_LEN {
            return Err(PersistenceFormatError::BufferTooSmall);
        }
        out[..AID_ENCODED_LEN].copy_from_slice(&self.object_aid.encoded());
        out[AID_ENCODED_LEN..AID_ENCODED_LEN * 2].copy_from_slice(&self.parent_sd_aid.encoded());
        write_u16_le(
            &mut out[AID_ENCODED_LEN * 2..AID_ENCODED_LEN * 2 + 2],
            self.kind_word.raw(),
        );
        if self == Self::EMPTY {
            out[..Self::ENCODED_LEN].fill(0);
        } else {
            out[36..40].copy_from_slice(&super::references::address(self.data_ref).to_le_bytes());
        }
        Ok(())
    }

    /// Creates a persistent entry from one live runtime registry object.
    ///
    /// The `data_ref` is supplied by the persistence writer after it has placed
    /// the object payload in the appropriate persistent space. This preserves
    /// the transaction invariant: payload first, registry pointer second.
    pub fn from_registry_object(object: &ObjectView, data_ref: PersistentRef) -> Self {
        Self {
            object_aid: PersistentAid::from_aid(&object.object_aid),
            parent_sd_aid: PersistentAid::from_aid(&object.parent_sd_aid),
            kind_word: PersistentKindWord::new(
                persistent_kind_from_runtime(object.object_kind),
                persistent_state_from_runtime(object),
            ),
            data_ref,
        }
    }

    /// Decodes one registry entry from its fixed-size representation.
    pub fn decode(input: &[u8]) -> Result<Self, PersistenceFormatError> {
        if input.len() < Self::ENCODED_LEN {
            return Err(PersistenceFormatError::Truncated);
        }
        if input[..Self::ENCODED_LEN].iter().all(|b| *b == 0) {
            return Ok(Self::EMPTY);
        }
        let object_aid = read_persistent_aid(&input[..AID_ENCODED_LEN])?;
        let parent_sd_aid = read_persistent_aid(&input[AID_ENCODED_LEN..AID_ENCODED_LEN * 2])?;
        let kind_word = PersistentKindWord::from_raw(read_u16_le(&input[AID_ENCODED_LEN * 2..]))?;
        let data_ref = super::references::reference(read_u32_le(&input[36..40]));
        Ok(Self {
            object_aid,
            parent_sd_aid,
            kind_word,
            data_ref,
        })
    }
}

fn persistent_kind_from_runtime(kind: ManagedObjectKind) -> PersistentObjectKind {
    match kind {
        ManagedObjectKind::SecurityDomain => PersistentObjectKind::SecurityDomain,
        ManagedObjectKind::Package => PersistentObjectKind::Package,
        ManagedObjectKind::Instance => PersistentObjectKind::Instance,
        ManagedObjectKind::Key => PersistentObjectKind::Key,
        ManagedObjectKind::Data => PersistentObjectKind::Data,
    }
}

fn persistent_state_from_runtime(object: &ObjectView) -> u16 {
    match object.payload {
        ObjectPayload::SecurityDomain { object_state, .. } => match object_state {
            SecurityDomainObjectState::Selectable => 0,
            SecurityDomainObjectState::Locked => 1,
        },
        ObjectPayload::Package { package_state, .. } => match package_state {
            PackageObjectState::Loaded => 0,
            PackageObjectState::Locked => 1,
        },
        ObjectPayload::Instance { instance_state, .. } => match instance_state {
            InstanceObjectState::Selectable => 0,
            InstanceObjectState::Locked => 1,
        },
        ObjectPayload::Key { key_state, .. } => match key_state {
            KeyObjectState::Active => 0,
            KeyObjectState::Locked => 1,
        },
        ObjectPayload::Data { .. } | ObjectPayload::FlashData { .. } => 0,
    }
}

pub fn decode_package_state(value: u16) -> Result<PackageObjectState, PersistenceFormatError> {
    match value {
        0 => Ok(PackageObjectState::Loaded),
        1 => Ok(PackageObjectState::Locked),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

pub fn decode_instance_state(value: u16) -> Result<InstanceObjectState, PersistenceFormatError> {
    match value {
        0 => Ok(InstanceObjectState::Selectable),
        1 => Ok(InstanceObjectState::Locked),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

pub fn decode_security_domain_state(
    value: u16,
) -> Result<SecurityDomainObjectState, PersistenceFormatError> {
    match value {
        0 => Ok(SecurityDomainObjectState::Selectable),
        1 => Ok(SecurityDomainObjectState::Locked),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

/// Lightweight view of one valid registry block discovered in flash.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryBlockView<'a> {
    pub offset: usize,
    pub total_len: usize,
    pub mutation_counter: u32,
    pub entry_count: u32,
    ciphertext: &'a [u8],
    seed: u64,
}

impl<'a> RegistryBlockView<'a> {
    /// Decrypts this authenticated BOSS into the caller's existing scratch.
    /// The first eight bytes are the generation, followed by fixed entries.
    pub fn decrypt_into<'b>(&self, out: &'b mut [u8]) -> Result<&'b [u8], PersistenceFormatError> {
        if out.len() < self.ciphertext.len() {
            return Err(PersistenceFormatError::BufferTooSmall);
        }
        let bytes = &mut out[..self.ciphertext.len()];
        bytes.copy_from_slice(self.ciphertext);
        super::boss_crypto::decrypt_in_place(self.offset, self.seed, bytes)
            .map_err(|_| PersistenceFormatError::Crypto)?;
        Ok(bytes)
    }

    /// Decodes the `index`-th registry entry without allocating.
    pub fn entry(&self, index: usize) -> Result<PersistentRegistryEntry, PersistenceFormatError> {
        if index >= self.entry_count as usize {
            return Err(PersistenceFormatError::Truncated);
        }
        let start = index * PersistentRegistryEntry::ENCODED_LEN;
        let mut plaintext = [0u8; PersistentRegistryEntry::ENCODED_LEN];
        let read = super::boss_crypto::read_range(
            self.offset,
            self.seed,
            self.ciphertext,
            8 + start,
            &mut plaintext,
        );
        if read.is_err() {
            oxi_core::core::secure_zero(&mut plaintext);
            return Err(PersistenceFormatError::Crypto);
        }
        let result = PersistentRegistryEntry::decode(&plaintext);
        oxi_core::core::secure_zero(&mut plaintext);
        result
    }
}

/// Lightweight view of one valid object payload block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectBlockView<'a> {
    pub offset: usize,
    pub magic: u32,
    pub total_len: usize,
    pub payload: &'a [u8],
}

/// Zero-copy view of one persisted Security Domain payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentSecurityDomainPayload<'a> {
    pub package_aid: PersistentAid,
    pub backend: SecurityDomainObjectBackend,
    pub privilege_bytes: [u8; 3],
    pub serialized_state: &'a [u8],
}

/// Zero-copy view of one persisted Rustlet instance payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentInstancePayload<'a> {
    pub package_aid: PersistentAid,
    pub serialized_state: &'a [u8],
}

/// Zero-copy view of one persisted key payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentKeyPayload<'a> {
    pub key_type: KeyObjectType,
    pub key_state: KeyObjectState,
    pub key_version: u8,
    pub key_id: u8,
    pub key_usage: u8,
    pub raw_key_bytes: &'a [u8],
}

/// Zero-copy view of one persisted generic data payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentDataPayload<'a> {
    pub bytes: &'a [u8],
}

/// Summary produced by a linear scan of the mutable persistence area.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistenceAreaScan<'a> {
    /// Latest valid registry block, if one was found.
    pub latest_registry: Option<RegistryBlockView<'a>>,
    /// First page-aligned erased offset discovered during the full-area scan.
    ///
    /// If no erased page is found, this is `area.len()`. The future allocator
    /// may still recycle older unreferenced blocks, but an erased page is the
    /// simplest append candidate.
    pub append_offset: usize,
}

/// Page-aligned range occupied by one persistent block.
///
/// The allocator uses protected ranges to avoid recycling the latest registry
/// and objects still referenced by that registry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PersistentRange {
    pub offset: usize,
    pub total_len: usize,
}

impl PersistentRange {
    pub const EMPTY: Self = Self {
        offset: 0,
        total_len: 0,
    };

    /// Creates one range from a page-aligned offset and page-aligned length.
    pub const fn new(offset: usize, total_len: usize) -> Self {
        Self { offset, total_len }
    }

    pub(crate) fn overlaps(self, other: Self) -> bool {
        let self_end = self.offset.saturating_add(self.total_len);
        let other_end = other.offset.saturating_add(other.total_len);
        self.offset < other_end && other.offset < self_end
    }
}

/// Page-aligned allocation returned by the persistent log scanner.
///
/// If `erase_len` is zero, `offset..offset+total_len` is already erased page
/// space. Otherwise the caller must erase `erase_offset..erase_offset+erase_len`
/// sector by sector before programming the first page at `offset`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReusableSpan {
    pub offset: usize,
    pub total_len: usize,
    pub erase_offset: usize,
    pub erase_len: usize,
}

impl ReusableSpan {
    pub const EMPTY: Self = Self {
        offset: 0,
        total_len: 0,
        erase_offset: 0,
        erase_len: 0,
    };

    const fn erased(offset: usize, total_len: usize) -> Self {
        Self {
            offset,
            total_len,
            erase_offset: 0,
            erase_len: 0,
        }
    }

    const fn recycled_sector(offset: usize, total_len: usize, erase_len: usize) -> Self {
        Self {
            offset,
            total_len,
            erase_offset: offset,
            erase_len,
        }
    }

    /// Returns true when the caller must erase sectors before writing.
    pub const fn needs_erase(self) -> bool {
        self.erase_len != 0
    }
}

/// Returns true when the first page carries the persistence-area marker.
pub fn has_persistence_area_marker(area: &[u8]) -> bool {
    area.len() >= 8 && read_u64_le(&area[..8]) == PERSISTENCE_AREA_MAGIC
}

/// Writes the persistence-area marker at the beginning of a page buffer.
pub fn write_persistence_area_marker(page: &mut [u8]) -> Result<(), PersistenceFormatError> {
    if page.len() < 8 {
        return Err(PersistenceFormatError::BufferTooSmall);
    }
    write_u64_le(&mut page[..8], PERSISTENCE_AREA_MAGIC);
    Ok(())
}

/// Computes the reservation size before borrowing the shared programming buffer.
pub fn registry_block_total_len(
    entry_count: usize,
    page_size: usize,
) -> Result<usize, PersistenceFormatError> {
    validate_page_size(page_size)?;
    if page_size < 64 || !page_size.is_multiple_of(16) {
        return Err(PersistenceFormatError::InvalidPageSize);
    }
    let bytes = entry_count
        .checked_mul(PersistentRegistryEntry::ENCODED_LEN)
        .and_then(|len| len.checked_add(REGISTRY_HEADER_LEN + 8))
        .ok_or(PersistenceFormatError::InvalidBlockSize)?;
    align_up(bytes, page_size)
}

/// Encodes a complete registry block into `out`.
///
/// Returns the page-aligned number of bytes that must be written to flash.
pub fn encode_registry_block(
    mutation_counter: u32,
    entries: &[PersistentRegistryEntry],
    page_size: usize,
    out: &mut [u8],
) -> Result<usize, PersistenceFormatError> {
    encode_registry_block_at(0, mutation_counter, entries, page_size, out)
}

pub(crate) fn encode_registry_block_at(
    offset: usize,

    mutation_counter: u32,
    entries: &[PersistentRegistryEntry],
    page_size: usize,
    out: &mut [u8],
) -> Result<usize, PersistenceFormatError> {
    let required = registry_block_total_len(entries.len(), page_size)?;
    if out.len() < required {
        return Err(PersistenceFormatError::BufferTooSmall);
    }
    out[..required].fill(0);
    write_u32_le(&mut out[0..4], REGISTRY_BLOCK_MAGIC);
    let useful_len = entries
        .len()
        .checked_mul(PersistentRegistryEntry::ENCODED_LEN)
        .and_then(|len| len.checked_add(8))
        .and_then(|len| u32::try_from(len).ok())
        .ok_or(PersistenceFormatError::InvalidBlockSize)?;
    write_u32_le(&mut out[4..8], useful_len);
    let seed = super::data_crypto::reserve_seed().map_err(|_| PersistenceFormatError::Crypto)?;
    out[8..16].copy_from_slice(&seed.to_le_bytes());
    out[32..40].copy_from_slice(&(mutation_counter as u64).to_le_bytes());
    let mut cursor = REGISTRY_HEADER_LEN + 8;
    for entry in entries {
        entry.encode(&mut out[cursor..cursor + PersistentRegistryEntry::ENCODED_LEN])?;
        cursor += PersistentRegistryEntry::ENCODED_LEN;
    }
    super::boss_crypto::encrypt(offset, seed, &mut out[32..required])
        .map_err(|_| PersistenceFormatError::Crypto)?;
    seal_block(offset, &mut out[..required])?;
    Ok(required)
}

/// Encodes a package, data/key or serialized-state payload block into `out`.
///
/// Returns the page-aligned number of bytes that must be written to flash.
pub fn encode_object_block(
    magic: u32,
    payload: &[u8],
    page_size: usize,
    out: &mut [u8],
) -> Result<usize, PersistenceFormatError> {
    encode_object_block_at(0, magic, payload, page_size, out)
}

pub(crate) fn encode_object_block_at(
    offset: usize,

    magic: u32,
    payload: &[u8],
    page_size: usize,
    out: &mut [u8],
) -> Result<usize, PersistenceFormatError> {
    validate_page_size(page_size)?;
    if !is_object_magic(magic) {
        return Err(PersistenceFormatError::InvalidBlockMagic);
    }
    let required = object_block_total_len(magic, payload.len(), page_size)?;
    if out.len() < required {
        return Err(PersistenceFormatError::BufferTooSmall);
    }
    fill_erased(&mut out[..required]);
    write_u32_le(&mut out[0..4], magic);
    write_u32_le(&mut out[4..8], required as u32);
    write_u32_le(&mut out[8..12], payload.len() as u32);
    out[12..16].fill(0);
    out[OBJECT_HEADER_LEN..OBJECT_HEADER_LEN + payload.len()].copy_from_slice(payload);
    if is_encrypted_magic(magic) {
        let mut iv = super::data_crypto::prepare_header_for(magic, offset, payload.len(), out)
            .map_err(|_| PersistenceFormatError::Crypto)?;
        let end = OBJECT_HEADER_LEN + align_up(payload.len(), 16)?;
        super::data_crypto::encrypt(&mut iv, &mut out[OBJECT_HEADER_LEN..end])
            .map_err(|_| PersistenceFormatError::Crypto)?;
    }
    seal_block(offset, &mut out[..required])?;
    Ok(required)
}

/// Encodes the kind-specific payload of one runtime registry object.
///
/// The returned magic identifies the persistent block family that must wrap the
/// bytes written into `out`. Registry entries then point to that block through
/// a [`PersistentRef`].
pub fn encode_registry_object_payload(
    object: &ObjectView,
    out: &mut [u8],
) -> Result<(u32, usize), PersistenceFormatError> {
    match object.payload {
        ObjectPayload::SecurityDomain {
            package_aid,
            backend,
            privilege_bytes,
            ref serialized_state,
            serialized_state_len,
            ..
        } => {
            let required = SECURITY_DOMAIN_PAYLOAD_HEADER_LEN + serialized_state_len;
            if out.len() < required {
                return Err(PersistenceFormatError::BufferTooSmall);
            }
            out[..AID_ENCODED_LEN]
                .copy_from_slice(&PersistentAid::from_aid(&package_aid).encoded());
            out[AID_ENCODED_LEN] = encode_security_domain_backend(backend);
            out[AID_ENCODED_LEN + 1..AID_ENCODED_LEN + 4].copy_from_slice(&privilege_bytes);
            write_u32_le(
                &mut out[AID_ENCODED_LEN + 4..AID_ENCODED_LEN + 8],
                serialized_state_len as u32,
            );

            serialized_state
                .read_range(0, &mut out[required - serialized_state_len..required])
                .map_err(|_| PersistenceFormatError::Crypto)?;
            Ok((INSTANCE_STATE_BLOCK_MAGIC, required))
        }
        ObjectPayload::Package { binary_code, .. } => {
            if out.len() < binary_code.len() {
                return Err(PersistenceFormatError::BufferTooSmall);
            }
            out[..binary_code.len()].copy_from_slice(binary_code);
            Ok((PACKAGE_BLOCK_MAGIC, binary_code.len()))
        }
        ObjectPayload::Instance {
            package_aid,
            ref serialized_state,
            serialized_state_len,
            ..
        } => {
            let required = INSTANCE_PAYLOAD_HEADER_LEN + serialized_state_len;
            if out.len() < required {
                return Err(PersistenceFormatError::BufferTooSmall);
            }
            out[..AID_ENCODED_LEN]
                .copy_from_slice(&PersistentAid::from_aid(&package_aid).encoded());
            write_u32_le(
                &mut out[AID_ENCODED_LEN..AID_ENCODED_LEN + 4],
                serialized_state_len as u32,
            );

            serialized_state
                .read_range(0, &mut out[required - serialized_state_len..required])
                .map_err(|_| PersistenceFormatError::Crypto)?;
            Ok((INSTANCE_STATE_BLOCK_MAGIC, required))
        }
        ObjectPayload::Key {
            key_type,
            key_state,
            key_version,
            key_id,
            key_usage,
            ref raw_key_bytes,
            raw_key_len,
        } => {
            let required = KEY_PAYLOAD_HEADER_LEN + raw_key_len;
            if out.len() < required {
                return Err(PersistenceFormatError::BufferTooSmall);
            }
            out[0] = encode_key_type(key_type);
            out[1] = encode_key_state(key_state);
            out[2] = key_version;
            out[3] = key_id;
            out[4] = key_usage;
            write_u32_le(&mut out[5..9], raw_key_len as u32);
            raw_key_bytes
                .read_range(0, &mut out[KEY_PAYLOAD_HEADER_LEN..required])
                .map_err(|_| PersistenceFormatError::Crypto)?;
            Ok((DATA_BLOCK_MAGIC, required))
        }
        ObjectPayload::FlashData { .. } => Err(PersistenceFormatError::InvalidKind),
        ObjectPayload::Data { ref bytes, len } => {
            if out.len() < len {
                return Err(PersistenceFormatError::BufferTooSmall);
            }
            bytes
                .read_range(0, &mut out[..len])
                .map_err(|_| PersistenceFormatError::Crypto)?;
            Ok((ENCRYPTED_DATA_MAGIC, len))
        }
    }
}

/// Decodes bytes previously produced for a Security Domain registry object.
pub fn decode_security_domain_payload(
    input: &[u8],
) -> Result<PersistentSecurityDomainPayload<'_>, PersistenceFormatError> {
    if input.len() < SECURITY_DOMAIN_PAYLOAD_HEADER_LEN {
        return Err(PersistenceFormatError::Truncated);
    }
    let package_aid = read_persistent_aid(&input[..AID_ENCODED_LEN])?;
    let backend = decode_security_domain_backend(input[AID_ENCODED_LEN])?;
    let mut privilege_bytes = [0u8; 3];
    privilege_bytes.copy_from_slice(&input[AID_ENCODED_LEN + 1..AID_ENCODED_LEN + 4]);
    let state_len = read_u32_le(&input[AID_ENCODED_LEN + 4..AID_ENCODED_LEN + 8]) as usize;
    let state_start = SECURITY_DOMAIN_PAYLOAD_HEADER_LEN;
    let state_end = state_start + state_len;
    if state_end > input.len() {
        return Err(PersistenceFormatError::Truncated);
    }
    Ok(PersistentSecurityDomainPayload {
        package_aid,
        backend,
        privilege_bytes,
        serialized_state: &input[state_start..state_end],
    })
}

/// Decodes bytes previously produced for a Rustlet instance registry object.
pub fn decode_instance_payload(
    input: &[u8],
) -> Result<PersistentInstancePayload<'_>, PersistenceFormatError> {
    if input.len() < INSTANCE_PAYLOAD_HEADER_LEN {
        return Err(PersistenceFormatError::Truncated);
    }
    let package_aid = read_persistent_aid(&input[..AID_ENCODED_LEN])?;
    let state_len = read_u32_le(&input[AID_ENCODED_LEN..AID_ENCODED_LEN + 4]) as usize;
    let state_start = INSTANCE_PAYLOAD_HEADER_LEN;
    let state_end = state_start + state_len;
    if state_end > input.len() {
        return Err(PersistenceFormatError::Truncated);
    }
    Ok(PersistentInstancePayload {
        package_aid,
        serialized_state: &input[state_start..state_end],
    })
}

/// Decodes bytes previously produced for a key registry object.
pub fn decode_key_payload(
    input: &[u8],
) -> Result<PersistentKeyPayload<'_>, PersistenceFormatError> {
    if input.len() < KEY_PAYLOAD_HEADER_LEN {
        return Err(PersistenceFormatError::Truncated);
    }
    let key_type = decode_key_type(input[0])?;
    let key_state = decode_key_state(input[1])?;
    let raw_key_len = read_u32_le(&input[5..9]) as usize;
    let raw_key_start = KEY_PAYLOAD_HEADER_LEN;
    let raw_key_end = raw_key_start + raw_key_len;
    if raw_key_end > input.len() {
        return Err(PersistenceFormatError::Truncated);
    }
    Ok(PersistentKeyPayload {
        key_type,
        key_state,
        key_version: input[2],
        key_id: input[3],
        key_usage: input[4],
        raw_key_bytes: &input[raw_key_start..raw_key_end],
    })
}

/// Decodes bytes previously produced for a generic data registry object.
pub fn decode_data_payload(
    input: &[u8],
) -> Result<PersistentDataPayload<'_>, PersistenceFormatError> {
    Ok(PersistentDataPayload { bytes: input })
}

/// Scans one persistence area and returns the latest valid registry block.
pub fn find_latest_registry_block<'a>(
    area: &'a [u8],
    page_size: usize,
) -> Result<Option<RegistryBlockView<'a>>, PersistenceFormatError> {
    Ok(scan_persistence_area(area, page_size)?.latest_registry)
}

/// Scans the mutable persistence area from its first page.
///
/// The diagnostic scan walks the complete circular buffer. Erased pages are
/// valid empty pages, not end markers. A BOSS needs full-block CMAC before its
/// encrypted generation can be decoded; LOAD still needs only header CMAC.
pub fn scan_persistence_area<'a>(
    area: &'a [u8],
    page_size: usize,
) -> Result<PersistenceAreaScan<'a>, PersistenceFormatError> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Scan);
    validate_page_size(page_size)?;
    let mut upper_bound = None;
    loop {
        let mut latest = None;
        let mut first_erased = None;
        let mut offset = 0usize;
        while offset + COMMON_HEADER_LEN <= area.len() {
            if is_erased_page_prefix(&area[offset..]) {
                if first_erased.is_none() {
                    first_erased = Some(offset);
                }
                // Invariant: an erased page marks free space in the circular log,
                // but later pages may still contain older valid blocks after wrap.
                offset += page_size;
                continue;
            }
            let Some((magic, total_len)) = recognized_block_header(area, offset, page_size) else {
                offset += page_size;
                continue;
            };
            if magic == REGISTRY_BLOCK_MAGIC {
                if let Ok(block) = decode_registry_block_trusted(area, offset, page_size) {
                    let rank = (block.mutation_counter, core::cmp::Reverse(block.offset));
                    if upper_bound.map(|bound| rank >= bound).unwrap_or(false) {
                        offset += total_len;
                        continue;
                    }
                    if latest
                        .map(|current: RegistryBlockView<'a>| {
                            block.mutation_counter > current.mutation_counter
                        })
                        .unwrap_or(true)
                    {
                        latest = Some(block);
                    }
                }
            }
            // Authenticated extents cannot hide later candidate headers.
            offset += total_len;
        }
        if let Some(block) = latest {
            if !super::header_auth::verify(
                block.offset,
                &area[block.offset..block.offset + block.total_len],
            )
            .map_err(|_| PersistenceFormatError::Crypto)?
            {
                upper_bound = Some((block.mutation_counter, core::cmp::Reverse(block.offset)));
                continue;
            }
        }
        return Ok(PersistenceAreaScan {
            latest_registry: latest,
            append_offset: first_erased.unwrap_or(area.len()),
        });
    }
}

pub trait Protection {
    fn overlaps(&self, range: PersistentRange) -> bool;
}
impl Protection for [PersistentRange] {
    fn overlaps(&self, range: PersistentRange) -> bool {
        self.iter().any(|r| r.overlaps(range))
    }
}
impl<const N: usize> Protection for [PersistentRange; N] {
    fn overlaps(&self, range: PersistentRange) -> bool {
        self.as_slice().overlaps(range)
    }
}

/// Finds a page-aligned span that can hold a new persistent block.
///
/// The search accepts two kinds of reusable space:
/// - contiguous erased pages;
/// - complete erase sectors that do not overlap any protected range.
///
/// This keeps the circular flash journal compact while preserving the core
/// transaction invariant: the caller must never pass the latest registry nor
/// the payload blocks referenced by it as recyclable ranges.
pub fn find_reusable_span(
    area: &[u8],
    page_size: usize,
    erase_sector_size: usize,
    required_len: usize,
    protected: &(impl Protection + ?Sized),
) -> Result<Option<ReusableSpan>, PersistenceFormatError> {
    find_reusable_span_sized(
        area,
        page_size,
        erase_sector_size,
        |_| Some(required_len),
        protected,
    )
}

/// Finds space with an address-dependent reservation length (package MPU padding).
/// The callback is pure: it returns the complete span or rejects that placement.
/// Geometry is recalculated for every append/erased/recycled candidate.
pub fn find_reusable_span_sized(
    area: &[u8],
    page_size: usize,
    erase_sector_size: usize,
    required_at: impl FnMut(usize) -> Option<usize>,
    protected: &(impl Protection + ?Sized),
) -> Result<Option<ReusableSpan>, PersistenceFormatError> {
    find_reusable_span_sized_from(
        area,
        page_size,
        erase_sector_size,
        0,
        required_at,
        protected,
    )
}

/// One circular fallback traversal, starting just after the current BOSS.
/// Erased space has priority; the first recyclable sector is remembered and
/// used only if the traversal finds no erased placement. The start must be a
/// block boundary; a candidate never wraps across the flash end.
pub fn find_reusable_span_sized_from(
    area: &[u8],
    page_size: usize,
    erase_sector_size: usize,
    start_offset: usize,
    mut required_at: impl FnMut(usize) -> Option<usize>,
    protected: &(impl Protection + ?Sized),
) -> Result<Option<ReusableSpan>, PersistenceFormatError> {
    validate_page_size(page_size)?;
    validate_erase_sector_size(page_size, erase_sector_size)?;
    if start_offset > area.len() || !start_offset.is_multiple_of(page_size) {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    let start = if start_offset == area.len() {
        0
    } else {
        start_offset
    };
    let mut first_recyclable = None;
    if let Some(span) = find_span_in(
        area,
        page_size,
        erase_sector_size,
        start,
        area.len(),
        &mut required_at,
        protected,
        &mut first_recyclable,
    )? {
        return Ok(Some(span));
    }
    if let Some(span) = find_span_in(
        area,
        page_size,
        erase_sector_size,
        0,
        start,
        &mut required_at,
        protected,
        &mut first_recyclable,
    )? {
        return Ok(Some(span));
    }
    Ok(first_recyclable)
}

fn find_span_in(
    area: &[u8],
    page_size: usize,
    erase_sector_size: usize,
    start: usize,
    end: usize,
    required_at: &mut impl FnMut(usize) -> Option<usize>,
    protected: &(impl Protection + ?Sized),
    first_recyclable: &mut Option<ReusableSpan>,
) -> Result<Option<ReusableSpan>, PersistenceFormatError> {
    let mut offset = start;
    while offset + page_size <= end {
        let required = required_at(offset)
            .map(|len| align_up(len, page_size))
            .transpose()?;
        if let Some(required) = required {
            let erased_candidate = PersistentRange::new(offset, required);
            if required <= end - offset
                && erased_span_is_at_least(&area[offset..], page_size, required)
                && !protected.overlaps(erased_candidate)
            {
                return Ok(Some(ReusableSpan::erased(offset, required)));
            }
            if first_recyclable.is_none() && offset.is_multiple_of(erase_sector_size) {
                // Reclaim only complete sectors, never the BOSS or a live
                // object. Keep the first such sector in circular order, but
                // avoid an erase if a later page is already blank.
                let erase_len = align_up(required, erase_sector_size)?;
                if erase_len <= end - offset
                    && recycling_preserves_boundaries(
                        area,
                        page_size,
                        PersistentRange::new(offset, erase_len),
                        protected,
                    )
                {
                    *first_recyclable =
                        Some(ReusableSpan::recycled_sector(offset, required, erase_len));
                }
            }
        }
        offset += page_size;
    }
    Ok(None)
}

// Retire only whole old blocks, but erase only the sectors needed by the new
// allocation. In particular, never start recycling inside a surviving block.
fn recycling_preserves_boundaries(
    area: &[u8],
    page_size: usize,
    erased: PersistentRange,
    protected: &(impl Protection + ?Sized),
) -> bool {
    if protected.overlaps(erased) {
        return false;
    }
    let mut offset = 0;
    while offset < erased.offset + erased.total_len {
        if let Some((_, len)) = recognized_block_header(area, offset, page_size) {
            let block = PersistentRange::new(offset, len);
            if block.overlaps(erased) && (offset < erased.offset || protected.overlaps(block)) {
                return false;
            }
            offset += len;
        } else {
            offset += page_size;
        }
    }
    true
}

/// Neutralizes every recognizable page magic in old blocks touched by recycling.
///
/// `clear_magic` must program and verify a zero magic word without erasing or
/// changing any other byte. Each outer header is retired only after its entire
/// payload has been checked, including pages beyond the proposed erase span.
/// An error must abort recycling before any erase. No extra flash sector is
/// erased to retire a block larger than its replacement.
///
/// The caller must use a span returned by `find_reusable_span` and the same
/// protection set, with no intervening registry mutation.
pub fn neutralize_recycled_blocks<E>(
    area: &[u8],
    page_size: usize,
    span: ReusableSpan,
    mut clear_magic: impl FnMut(usize) -> Result<(), E>,
) -> Result<(), E> {
    let end = span.erase_offset + span.erase_len;
    let mut offset = span.erase_offset;
    while offset < end {
        if let Some((_, len)) = recognized_block_header(area, offset, page_size) {
            // Inspect every page; following a forged inner length could hide
            // another magic. Inner authentication is irrelevant to retirement.
            for inner in (offset + page_size..offset + len).step_by(page_size) {
                let magic = read_u32_le(&area[inner..inner + 4]);
                if magic == REGISTRY_BLOCK_MAGIC || is_object_magic(magic) {
                    clear_magic(inner)?;
                }
            }
            clear_magic(offset)?;
            offset += len;
        } else {
            offset += page_size;
        }
    }
    Ok(())
}

/// Tries to reserve erased pages at one exact append cursor.
///
/// This is the nominal allocation path after boot: the caller keeps the cursor
/// in RAM and avoids rediscovering the same append position by scanning the
/// complete flash area for every block. Returning `None` asks the caller to run
/// the slower circular-GC search.
pub fn erased_span_at(
    area: &[u8],
    page_size: usize,
    required_len: usize,
    offset: usize,
    protected: &(impl Protection + ?Sized),
) -> Result<Option<ReusableSpan>, PersistenceFormatError> {
    validate_page_size(page_size)?;
    let required = align_up(required_len, page_size)?;
    let Some(end) = offset.checked_add(required) else {
        return Ok(None);
    };
    if !offset.is_multiple_of(page_size) || end > area.len() {
        return Ok(None);
    }
    let candidate = PersistentRange::new(offset, required);
    if protected.overlaps(candidate)
        || !erased_span_is_at_least(&area[offset..], page_size, required)
    {
        return Ok(None);
    }
    Ok(Some(ReusableSpan::erased(offset, required)))
}

/// Decodes a registry block at one exact page-aligned offset.
pub fn decode_registry_block_at<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
) -> Result<RegistryBlockView<'a>, PersistenceFormatError> {
    validate_page_size(page_size)?;
    validate_offset(offset, page_size)?;
    let block = checked_block(area, offset, page_size, REGISTRY_BLOCK_MAGIC)?;
    verify_block(offset, block)?;
    decode_registry_block_trusted(area, offset, page_size)
}

/// Only for immutable blocks already validated at recovery or successful publication.
pub(crate) fn decode_registry_block_trusted<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
) -> Result<RegistryBlockView<'a>, PersistenceFormatError> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::DecodeBoss);
    decode_registry_block_internal(area, offset, page_size, None)
}

/// A BOSS published or recovered in this boot already has a trusted generation
/// in runtime state; avoid decrypting its first CBC block for each mutation.
pub(crate) fn decode_registry_block_known<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
    generation: u32,
) -> Result<RegistryBlockView<'a>, PersistenceFormatError> {
    decode_registry_block_internal(area, offset, page_size, Some(generation))
}

/// Authenticate the complete immutable BOSS, then decrypt its useful image in
/// one CBC pass. Unlike the entry API, this does not decrypt generation first.
pub(crate) fn decrypt_registry_image<'b>(
    area: &[u8],
    offset: usize,
    page: usize,
    out: &'b mut [u8],
) -> Result<&'b [u8], PersistenceFormatError> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::DecodeBoss);
    validate_page_size(page)?;
    validate_offset(offset, page)?;
    let block = checked_block(area, offset, page, REGISTRY_BLOCK_MAGIC)?;
    verify_block(offset, block)?;
    let view = decode_registry_block_internal(area, offset, page, Some(0))?;
    let useful = 8 + view.entry_count as usize * PersistentRegistryEntry::ENCODED_LEN;
    let cipher_len = align_up(useful, 16)?;
    if cipher_len > out.len() {
        return Err(PersistenceFormatError::BufferTooSmall);
    }
    super::boss_crypto::read_range(
        offset,
        view.seed,
        view.ciphertext,
        0,
        &mut out[..cipher_len],
    )
    .map_err(|_| PersistenceFormatError::Crypto)?;
    let generation = u64::from_le_bytes(out[..8].try_into().unwrap());
    u32::try_from(generation).map_err(|_| PersistenceFormatError::InvalidBlockSize)?;
    Ok(&out[..useful])
}

fn decode_registry_block_internal<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
    known_generation: Option<u32>,
) -> Result<RegistryBlockView<'a>, PersistenceFormatError> {
    validate_page_size(page_size)?;
    validate_offset(offset, page_size)?;
    let block = checked_block(area, offset, page_size, REGISTRY_BLOCK_MAGIC)?;
    if block.len() < REGISTRY_HEADER_LEN {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    let useful_len = read_u32_le(&block[4..8]) as usize;
    if useful_len < 8
        || !(useful_len - 8).is_multiple_of(PersistentRegistryEntry::ENCODED_LEN)
        || useful_len > block.len() - REGISTRY_HEADER_LEN
    {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    let entry_count = ((useful_len - 8) / PersistentRegistryEntry::ENCODED_LEN) as u32;
    let seed = u64::from_le_bytes(block[8..16].try_into().unwrap());
    let mutation_counter = if let Some(value) = known_generation {
        value
    } else {
        let mut generation = [0u8; 8];
        super::boss_crypto::read_range(offset, seed, &block[32..], 0, &mut generation)
            .map_err(|_| PersistenceFormatError::Crypto)?;
        let decoded = u64::from_le_bytes(generation);
        oxi_core::core::secure_zero(&mut generation);
        u32::try_from(decoded).map_err(|_| PersistenceFormatError::InvalidBlockSize)?
    };
    Ok(RegistryBlockView {
        offset,
        total_len: block.len(),
        mutation_counter,
        entry_count,
        ciphertext: &block[REGISTRY_HEADER_LEN..],
        seed,
    })
}

/// Decodes an object payload block at one exact page-aligned offset.
pub fn decode_object_block_at<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
) -> Result<ObjectBlockView<'a>, PersistenceFormatError> {
    validate_page_size(page_size)?;
    validate_offset(offset, page_size)?;
    let view = decode_object_block_trusted(area, offset, page_size)?;
    verify_block(offset, &area[offset..offset + view.total_len])?;
    Ok(view)
}

/// Only for immutable blocks already validated at recovery or successful publication.
pub(crate) fn decode_object_block_trusted<'a>(
    area: &'a [u8],
    offset: usize,
    page_size: usize,
) -> Result<ObjectBlockView<'a>, PersistenceFormatError> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::DecodeObject);
    validate_page_size(page_size)?;
    validate_offset(offset, page_size)?;
    if offset + COMMON_HEADER_LEN > area.len() {
        return Err(PersistenceFormatError::Truncated);
    }
    let magic = read_u32_le(&area[offset..offset + 4]);
    if !is_object_magic(magic) {
        return Err(PersistenceFormatError::InvalidBlockMagic);
    }
    let block = checked_block(area, offset, page_size, magic)?;
    if block.len() < OBJECT_HEADER_LEN {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    let payload_len = if is_encrypted_magic(magic) {
        align_up(read_u32_le(&block[4..8]) as usize, 16)?
    } else {
        read_u32_le(&block[8..12]) as usize
    };
    if payload_len > block.len() - OBJECT_HEADER_LEN {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    Ok(ObjectBlockView {
        offset,
        magic,
        total_len: block.len(),
        payload: &block[OBJECT_HEADER_LEN..OBJECT_HEADER_LEN + payload_len],
    })
}

/// LOAD uses an authenticated CRC32; BOSS and encrypted objects use full CMAC.
pub(super) fn has_body_crc(header: &[u8]) -> bool {
    read_u32_le(header) == PACKAGE_BLOCK_MAGIC
}

/// Bitwise CRC32, polynomial 0x04C11DB7, initial value zero, no final xor.
#[cfg_attr(
    all(not(test), oxide_se_board_raspi_pico),
    unsafe(link_section = ".critical.kernel.fct")
)]
pub(super) fn crc32_body(bytes: &[u8]) -> u32 {
    let mut crc = 0u32;
    for byte in bytes {
        crc ^= (*byte as u32) << 24;
        for _ in 0..8 {
            crc = if crc & 0x8000_0000 != 0 {
                (crc << 1) ^ 0x04C1_1DB7
            } else {
                crc << 1
            };
        }
    }
    crc
}

/// Seal LOAD's header + body CRC32, or the full CMAC for other objects.
pub(crate) fn seal_block(offset: usize, block: &mut [u8]) -> Result<(), PersistenceFormatError> {
    if block.len() < 32 {
        return Err(PersistenceFormatError::Truncated);
    }
    if has_body_crc(block) {
        let crc = crc32_body(&block[32..]);
        write_u32_le(&mut block[12..16], crc);
    }
    let tag = super::header_auth::tag(offset, &block[..16], &block[32..])
        .map_err(|_| PersistenceFormatError::Crypto)?;
    block[16..32].copy_from_slice(&tag);
    Ok(())
}

fn verify_block(offset: usize, header: &[u8]) -> Result<(), PersistenceFormatError> {
    if !super::header_auth::verify(offset, header).map_err(|_| PersistenceFormatError::Crypto)? {
        return Err(PersistenceFormatError::Authentication);
    }
    Ok(())
}

fn checked_block(
    area: &[u8],
    offset: usize,
    page_size: usize,
    expected_magic: u32,
) -> Result<&[u8], PersistenceFormatError> {
    if offset + COMMON_HEADER_LEN > area.len() {
        return Err(PersistenceFormatError::Truncated);
    }
    let magic = read_u32_le(&area[offset..offset + 4]);
    if magic != expected_magic {
        return Err(PersistenceFormatError::InvalidBlockMagic);
    }
    let total_len = header_total_len(&area[offset..offset + COMMON_HEADER_LEN], page_size)?;
    if total_len < COMMON_HEADER_LEN || !total_len.is_multiple_of(page_size) {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    if total_len > area.len() - offset {
        return Err(PersistenceFormatError::Truncated);
    }
    Ok(&area[offset..offset + total_len])
}

pub(super) fn header_total_len(
    header: &[u8],
    page_size: usize,
) -> Result<usize, PersistenceFormatError> {
    if read_u32_le(&header[..4]) == REGISTRY_BLOCK_MAGIC {
        if page_size < 64 || !page_size.is_multiple_of(16) {
            return Err(PersistenceFormatError::InvalidPageSize);
        }
        let useful_len = read_u32_le(&header[4..8]) as usize;
        if useful_len < 8 || !(useful_len - 8).is_multiple_of(PersistentRegistryEntry::ENCODED_LEN)
        {
            return Err(PersistenceFormatError::InvalidBlockSize);
        }
        return useful_len
            .checked_add(REGISTRY_HEADER_LEN)
            .ok_or(PersistenceFormatError::InvalidBlockSize)
            .and_then(|len| align_up(len, page_size));
    }
    let value = read_u32_le(&header[4..8]) as usize;
    if is_encrypted_magic(read_u32_le(&header[..4])) {
        object_block_total_len(ENCRYPTED_DATA_MAGIC, value, page_size)
    } else {
        Ok(value)
    }
}

fn recognized_block_header(area: &[u8], offset: usize, page_size: usize) -> Option<(u32, usize)> {
    if offset + COMMON_HEADER_LEN > area.len() {
        return None;
    }
    let magic = read_u32_le(&area[offset..offset + 4]);
    if magic != REGISTRY_BLOCK_MAGIC && !is_object_magic(magic) {
        return None;
    }
    let total_len = header_total_len(&area[offset..offset + COMMON_HEADER_LEN], page_size).ok()?;
    if total_len < COMMON_HEADER_LEN || !total_len.is_multiple_of(page_size) {
        return None;
    }
    if total_len > area.len() - offset {
        return None;
    }
    match super::header_auth::verify_header(offset, &area[offset..offset + total_len])
        .map_err(|_| PersistenceFormatError::Crypto)
        .and_then(|valid| {
            if valid {
                Ok(())
            } else {
                Err(PersistenceFormatError::Authentication)
            }
        }) {
        Ok(()) => {}
        Err(PersistenceFormatError::Authentication) => return None,
        Err(_) => panic!("registry header crypto unavailable"),
    }
    Some((magic, total_len))
}

fn read_persistent_aid(input: &[u8]) -> Result<PersistentAid, PersistenceFormatError> {
    if input.len() < AID_ENCODED_LEN {
        return Err(PersistenceFormatError::Truncated);
    }
    let mut encoded = [0u8; AID_ENCODED_LEN];
    encoded.copy_from_slice(&input[..AID_ENCODED_LEN]);
    PersistentAid::from_encoded(encoded)
}

fn validate_page_size(page_size: usize) -> Result<(), PersistenceFormatError> {
    if page_size == 0 || !page_size.is_power_of_two() {
        return Err(PersistenceFormatError::InvalidPageSize);
    }
    Ok(())
}

fn validate_erase_sector_size(
    page_size: usize,
    erase_sector_size: usize,
) -> Result<(), PersistenceFormatError> {
    validate_page_size(erase_sector_size)?;
    if erase_sector_size < page_size || !erase_sector_size.is_multiple_of(page_size) {
        return Err(PersistenceFormatError::InvalidPageSize);
    }
    Ok(())
}

fn validate_offset(offset: usize, page_size: usize) -> Result<(), PersistenceFormatError> {
    if !offset.is_multiple_of(page_size) {
        return Err(PersistenceFormatError::InvalidBlockSize);
    }
    Ok(())
}

fn align_up(value: usize, align: usize) -> Result<usize, PersistenceFormatError> {
    validate_page_size(align)?;
    value
        .checked_add(align - 1)
        .map(|v| v & !(align - 1))
        .ok_or(PersistenceFormatError::InvalidBlockSize)
}

fn is_object_magic(magic: u32) -> bool {
    magic == PACKAGE_BLOCK_MAGIC
        || magic == DATA_BLOCK_MAGIC
        || is_encrypted_magic(magic)
        || magic == INSTANCE_STATE_BLOCK_MAGIC
}

fn is_erased_page_prefix(input: &[u8]) -> bool {
    input.len() < COMMON_HEADER_LEN || input[..COMMON_HEADER_LEN].iter().all(|byte| *byte == 0xFF)
}

fn erased_span_is_at_least(input: &[u8], page_size: usize, required: usize) -> bool {
    let mut total = 0usize;
    while total < required && total + page_size <= input.len() {
        let page = &input[total..total + page_size];
        if !page.iter().all(|byte| *byte == 0xFF) {
            return false;
        }
        total += page_size;
    }
    total >= required
}

pub(super) fn encode_security_domain_backend(backend: SecurityDomainObjectBackend) -> u8 {
    match backend {
        SecurityDomainObjectBackend::NullSecurityDomain => 0,
        SecurityDomainObjectBackend::KernelSecurityDomain => 1,
        SecurityDomainObjectBackend::RustletSecurityDomain => 2,
    }
}

pub(super) fn decode_security_domain_backend(
    value: u8,
) -> Result<SecurityDomainObjectBackend, PersistenceFormatError> {
    match value {
        0 => Ok(SecurityDomainObjectBackend::NullSecurityDomain),
        1 => Ok(SecurityDomainObjectBackend::KernelSecurityDomain),
        2 => Ok(SecurityDomainObjectBackend::RustletSecurityDomain),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

pub(super) fn encode_key_type(key_type: KeyObjectType) -> u8 {
    match key_type {
        KeyObjectType::Scp03Static => 0,
        KeyObjectType::Scp11SdEckaPrivate => 1,
        KeyObjectType::Scp11CaKlocPublic => 2,
    }
}

pub(super) fn encode_key_state(key_state: KeyObjectState) -> u8 {
    match key_state {
        KeyObjectState::Active => 0,
        KeyObjectState::Locked => 1,
    }
}

pub(super) fn decode_key_type(value: u8) -> Result<KeyObjectType, PersistenceFormatError> {
    match value {
        0 => Ok(KeyObjectType::Scp03Static),
        1 => Ok(KeyObjectType::Scp11SdEckaPrivate),
        2 => Ok(KeyObjectType::Scp11CaKlocPublic),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

pub(super) fn decode_key_state(value: u8) -> Result<KeyObjectState, PersistenceFormatError> {
    match value {
        0 => Ok(KeyObjectState::Active),
        1 => Ok(KeyObjectState::Locked),
        _ => Err(PersistenceFormatError::InvalidKind),
    }
}

fn fill_erased(out: &mut [u8]) {
    for byte in out {
        *byte = 0xFF;
    }
}

fn read_u16_le(input: &[u8]) -> u16 {
    u16::from_le_bytes([input[0], input[1]])
}

fn read_u32_le(input: &[u8]) -> u32 {
    u32::from_le_bytes([input[0], input[1], input[2], input[3]])
}

fn read_u64_le(input: &[u8]) -> u64 {
    u64::from_le_bytes([
        input[0], input[1], input[2], input[3], input[4], input[5], input[6], input[7],
    ])
}

fn write_u16_le(out: &mut [u8], value: u16) {
    out[..2].copy_from_slice(&value.to_le_bytes());
}

fn write_u32_le(out: &mut [u8], value: u32) {
    out[..4].copy_from_slice(&value.to_le_bytes());
}

fn write_u64_le(out: &mut [u8], value: u64) {
    out[..8].copy_from_slice(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boss_full_cmac_and_load_crc_preserve_fallback() {
        let mut area = [0xff; 1024];
        encode_registry_block_at(0, 7, &[], 256, &mut area[..256]).unwrap();
        encode_registry_block_at(256, 9, &[], 256, &mut area[256..512]).unwrap();
        encode_registry_block_at(512, 8, &[], 256, &mut area[512..768]).unwrap();
        encode_object_block_at(768, PACKAGE_BLOCK_MAGIC, b"package", 256, &mut area[768..])
            .unwrap();
        assert_eq!(&area[4..8], &8u32.to_le_bytes());
        // Older corrupt bodies do not interfere with the newest intact BOSS.
        area[32] ^= 1;
        assert_eq!(
            find_latest_registry_block(&area, 256)
                .unwrap()
                .unwrap()
                .mutation_counter,
            9
        );
        // Multiple failures fall back by version, independent of physical order.
        area[256 + 32] ^= 1;
        assert!(!super::super::header_auth::verify_header(256, &area[256..512]).unwrap());
        assert!(decode_registry_block_at(&area, 256, 256).is_err());
        assert_eq!(
            find_latest_registry_block(&area, 256)
                .unwrap()
                .unwrap()
                .mutation_counter,
            8
        );
        area[512 + 32] ^= 1;
        assert!(find_latest_registry_block(&area, 256).unwrap().is_none());
        // A LOAD's corrupt body is skipped at scan, rejected before use.
        area[768 + 32] ^= 1;
        assert!(recognized_block_header(&area, 768, 256).is_some());
        assert!(decode_object_block_at(&area, 768, 256).is_err());
        area[768 + 12] ^= 1;
        assert!(recognized_block_header(&area, 768, 256).is_none());
    }

    #[test]
    fn crc32_known_vector_and_boss_header_bounds() {
        assert_eq!(crc32_body(b"123456789"), 0x89A1897F);
        let mut block = [0xff; 256];
        encode_registry_block(7, &[], 256, &mut block).unwrap();
        for byte in 0..32 {
            let mut changed = block;
            changed[byte] ^= 1;
            assert!(decode_registry_block_at(&changed, 0, 256).is_err());
        }
    }

    #[test]
    fn compact_authenticated_page_thresholds() {
        for magic in [DATA_BLOCK_MAGIC, ENCRYPTED_DATA_MAGIC] {
            assert_eq!(object_block_total_len(magic, 224, 256), Ok(256));
            assert_eq!(object_block_total_len(magic, 225, 256), Ok(512));
        }
        assert_eq!(registry_block_total_len(4, 256), Ok(256));
        assert_eq!(registry_block_total_len(5, 256), Ok(256));
        assert_eq!(registry_block_total_len(63, 256), Ok(2560));
        assert_eq!(registry_block_total_len(64, 256), Ok(2816));
        assert_eq!(registry_block_total_len(6, 256), Ok(512));
    }

    #[test]
    fn boss_counter_and_entries_are_ciphertext_and_body_tampering_is_rejected() {
        let item = entry(
            &[0xa1, 0xb2, 0xc3, 0xd4],
            &[0x10],
            PersistentObjectKind::Data,
        );
        let mut block = [0xff; 256];
        encode_registry_block_at(0, 17, &[item], 256, &mut block).unwrap();
        let view = decode_registry_block_at(&block, 0, 256).unwrap();
        assert_eq!(view.mutation_counter, 17);
        assert_eq!(view.entry(0), Ok(item));
        assert_ne!(&block[32..40], &17u64.to_le_bytes());
        let mut encoded = [0u8; PersistentRegistryEntry::ENCODED_LEN];
        item.encode(&mut encoded).unwrap();
        assert_ne!(&block[40..40 + encoded.len()], &encoded);
        for index in [32, 39, 40, 255] {
            let mut altered = block;
            altered[index] ^= 1;
            assert!(decode_registry_block_at(&altered, 0, 256).is_err());
        }
    }
    #[test]
    fn header_cmac_rejects_every_changed_bit_and_transplant() {
        let mut block = [0xff; 256];
        encode_object_block(DATA_BLOCK_MAGIC, b"clear body", 256, &mut block).unwrap();
        for byte in 0..256 {
            for bit in 0..8 {
                let mut changed = block;
                changed[byte] ^= 1 << bit;
                assert!(
                    decode_object_block_at(&changed, 0, 256).is_err(),
                    "byte={byte} bit={bit}"
                );
            }
        }
        let mut area = [0xff; 512];
        area[256..].copy_from_slice(&block);
        assert_eq!(
            decode_object_block_at(&area, 256, 256),
            Err(PersistenceFormatError::Authentication)
        );
    }

    #[test]
    fn body_is_authenticated_and_payload_remains_zero_copy() {
        let mut block = [0xff; 256];
        encode_object_block(DATA_BLOCK_MAGIC, b"clear body", 256, &mut block).unwrap();
        let header: [u8; 32] = block[..32].try_into().unwrap();
        block[32] ^= 1;
        assert_eq!(
            decode_object_block_at(&block, 0, 256),
            Err(PersistenceFormatError::Authentication)
        );
        assert_eq!(&block[..32], &header);
        // Restoring the exact authenticated body is necessary to validate it.
        block[32] ^= 1;
        let view = decode_object_block_at(&block, 0, 256).unwrap();
        assert_eq!(view.payload.as_ptr(), block[32..].as_ptr());
        assert_eq!(&block[..32], &header);
    }

    #[test]
    fn forged_header_length_never_hides_a_later_valid_boss() {
        let mut area = [0xff; 768];
        encode_object_block(DATA_BLOCK_MAGIC, b"x", 256, &mut area).unwrap();
        // A plausible magic and length alone no longer authorise this skip.
        area[4..8].copy_from_slice(&768u32.to_le_bytes());
        encode_registry_block_at(256, 9, &[], 256, &mut area[256..]).unwrap();
        let boss = find_latest_registry_block(&area, 256).unwrap().unwrap();
        assert_eq!(boss.offset, 256);
        assert_eq!(boss.mutation_counter, 9);
    }
    use crate::registry::objects::Registry;
    use std::{vec, vec::Vec};

    const PAGE: usize = 64;
    const SECTOR: usize = PAGE * 4;

    fn aid(bytes: &[u8]) -> Aid {
        Aid::new(bytes)
    }

    fn entry(object: &[u8], parent: &[u8], kind: PersistentObjectKind) -> PersistentRegistryEntry {
        PersistentRegistryEntry {
            object_aid: PersistentAid::from_aid(&aid(object)),
            parent_sd_aid: PersistentAid::from_aid(&aid(parent)),
            kind_word: PersistentKindWord::new(kind, 0x123),
            data_ref: PersistentRef::new(PersistentSpace::RegistryFlash, 0, 0x40),
        }
    }

    #[test]
    fn large_data_payload_survives_encoding_and_torn_blocks_are_rejected() {
        let payload: std::vec::Vec<u8> = (0..32772).map(|i| (i * 17) as u8).collect();
        let mut image = std::vec![0xff; 33024];
        let len = encode_object_block(DATA_BLOCK_MAGIC, &payload, 256, &mut image).unwrap();
        let view = decode_object_block_at(&image, 0, 256).unwrap();
        assert_eq!(decode_data_payload(view.payload).unwrap().bytes, payload);
        for cut in [0, 1, 255, 256, 32768, OBJECT_HEADER_LEN + payload.len() - 1] {
            let mut torn = image.clone();
            torn[cut..].fill(0xff);
            assert!(decode_object_block_at(&torn, 0, 256).is_err());
        }
        // Erased padding is already the expected value; omitting its program
        // operation does not constitute an incomplete stored message.
        assert!(image[OBJECT_HEADER_LEN + payload.len()..len]
            .iter()
            .all(|b| *b == 0xff));
    }

    #[test]
    fn persistent_aid_is_length_prefixed_and_roundtrips() {
        let runtime = aid(&[0xA0, 0x00, 0x00, 0x01]);
        let persistent = PersistentAid::from_aid(&runtime);
        let encoded = persistent.encoded();
        assert_eq!(encoded[0], 4);
        assert_eq!(&encoded[1..5], runtime.as_slice());
        assert_eq!(persistent.as_aid().as_slice(), runtime.as_slice());
    }

    #[test]
    fn persistent_aid_rejects_invalid_length() {
        let mut encoded = [0u8; AID_ENCODED_LEN];
        encoded[0] = 17;
        assert_eq!(
            PersistentAid::from_encoded(encoded),
            Err(PersistenceFormatError::InvalidAidLength)
        );
    }

    #[test]
    fn kind_word_splits_family_and_state_bits() {
        let kind = PersistentKindWord::new(PersistentObjectKind::SecurityDomain, 0xFABC);
        assert_eq!(kind.kind(), PersistentObjectKind::SecurityDomain);
        assert_eq!(kind.state_bits(), 0x0ABC);
        assert_eq!(
            PersistentKindWord::from_raw(0x0123),
            Err(PersistenceFormatError::InvalidKind)
        );
    }

    #[test]
    fn persistent_ref_roundtrips_without_raw_pointer_semantics() {
        let reference = PersistentRef::new(PersistentSpace::FirmwareImage, 0xA5, 0x0102_0304);
        let mut encoded = [0u8; PersistentRef::ENCODED_LEN];
        reference.encode(&mut encoded).unwrap();
        assert_eq!(PersistentRef::decode(&encoded), Ok(reference));
    }

    #[test]
    fn persistence_area_marker_is_explicit() {
        let mut page = [0xFFu8; PAGE];
        assert!(!has_persistence_area_marker(&page));
        write_persistence_area_marker(&mut page).unwrap();
        assert!(has_persistence_area_marker(&page));
    }

    #[test]
    fn registry_entry_roundtrips() {
        let original = entry(&[0x10], &[0x01], PersistentObjectKind::Instance);
        let mut encoded = [0u8; PersistentRegistryEntry::ENCODED_LEN];
        original.encode(&mut encoded).unwrap();
        assert_eq!(PersistentRegistryEntry::decode(&encoded), Ok(original));
    }

    #[test]
    fn runtime_registry_object_maps_to_persistent_entry_header() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .upsert_instance_object(aid(&[0x01]), aid(&[0x02]), aid(&[0x03]), &[0xAA])
            .is_ok());
        let runtime_entry = registry.entries().next().expect("runtime entry");
        let data_ref = PersistentRef::new(PersistentSpace::RegistryFlash, 0, 0x80);
        let persistent = PersistentRegistryEntry::from_registry_object(&runtime_entry, data_ref);

        assert_eq!(persistent.object_aid.as_aid().as_slice(), &[0x02]);
        assert_eq!(persistent.parent_sd_aid.as_aid().as_slice(), &[0x01]);
        assert_eq!(persistent.kind_word.kind(), PersistentObjectKind::Instance);
        assert_eq!(persistent.data_ref, data_ref);
    }

    #[test]
    fn runtime_registry_object_maps_lifecycle_state_bits() {
        let mut registry: Registry<4> = Registry::new();
        let parent = aid(&[0x01]);
        assert!(registry
            .insert_package_object(parent, aid(&[0x10]), aid(&[0x10]), &[0xCA])
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, aid(&[0x20]), aid(&[0x10]), &[0xBB])
            .is_ok());
        assert!(registry
            .upsert_security_domain_object(
                parent,
                aid(&[0x30]),
                aid(&[0x10]),
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF, 0xFF, 0xFF],
                &[0xCC],
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                parent,
                aid(&[0x40]),
                KeyObjectType::Scp03Static,
                KeyObjectState::Locked,
                1,
                1,
                1,
                &[0xDD],
            )
            .is_ok());
        assert!(registry
            .set_package_state(&parent, &aid(&[0x10]), PackageObjectState::Locked)
            .is_ok());
        assert!(registry
            .set_instance_state(&parent, &aid(&[0x20]), InstanceObjectState::Locked)
            .is_ok());
        assert!(registry
            .set_security_domain_state(&parent, &aid(&[0x30]), SecurityDomainObjectState::Locked,)
            .is_ok());

        let data_ref = PersistentRef::new(PersistentSpace::RegistryFlash, 0, 0x80);
        for runtime_entry in registry.entries() {
            let persistent =
                PersistentRegistryEntry::from_registry_object(&runtime_entry, data_ref);
            // Invariant: state bit 1 is the persisted encoding of the minimal
            // locked state for every lifecycle-bearing object family.
            assert_eq!(persistent.kind_word.state_bits(), 1);
        }
    }

    #[test]
    fn runtime_instance_payload_encodes_package_binding_and_state() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .upsert_instance_object(aid(&[0x01]), aid(&[0x02]), aid(&[0x03]), &[0xAA, 0xBB])
            .is_ok());
        let runtime_entry = registry.entries().next().expect("runtime entry");
        let mut payload = [0u8; 64];
        let (magic, len) =
            encode_registry_object_payload(&runtime_entry, &mut payload).expect("encode payload");
        let decoded = decode_instance_payload(&payload[..len]).expect("decode instance payload");
        assert_eq!(magic, INSTANCE_STATE_BLOCK_MAGIC);
        assert_eq!(decoded.package_aid.as_aid().as_slice(), &[0x03]);
        assert_eq!(decoded.serialized_state, &[0xAA, 0xBB]);
    }

    #[test]
    fn runtime_security_domain_payload_keeps_privileges_kernel_side() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .upsert_security_domain_object(
                aid(&[0x01]),
                aid(&[0x02]),
                aid(&[0x03]),
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xA0, 0x12, 0x34],
                &[0xFE]
            )
            .is_ok());
        let runtime_entry = registry.entries().next().expect("runtime entry");
        let mut payload = [0u8; 64];
        let (magic, len) =
            encode_registry_object_payload(&runtime_entry, &mut payload).expect("encode payload");
        let decoded = decode_security_domain_payload(&payload[..len]).expect("decode sd payload");
        assert_eq!(magic, INSTANCE_STATE_BLOCK_MAGIC);
        assert_eq!(decoded.package_aid.as_aid().as_slice(), &[0x03]);
        assert_eq!(
            decoded.backend,
            SecurityDomainObjectBackend::KernelSecurityDomain
        );
        assert_eq!(decoded.privilege_bytes, [0xA0, 0x12, 0x34]);
        assert_eq!(decoded.serialized_state, &[0xFE]);
    }

    #[test]
    fn runtime_key_payload_encodes_metadata_and_raw_key() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                aid(&[0x4B]),
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                7,
                3,
                1,
                &[0xCA, 0xFE]
            )
            .is_ok());
        let runtime_entry = registry.entries().next().expect("runtime entry");
        let mut payload = [0u8; 64];
        let (magic, len) =
            encode_registry_object_payload(&runtime_entry, &mut payload).expect("encode payload");
        let decoded = decode_key_payload(&payload[..len]).expect("decode key payload");
        assert_eq!(magic, DATA_BLOCK_MAGIC);
        assert_eq!(decoded.key_type, KeyObjectType::Scp03Static);
        assert_eq!(decoded.key_state, KeyObjectState::Active);
        assert_eq!(decoded.key_version, 7);
        assert_eq!(decoded.key_id, 3);
        assert_eq!(decoded.key_usage, 1);
        assert_eq!(decoded.raw_key_bytes, &[0xCA, 0xFE]);
    }

    #[test]
    fn runtime_data_payload_encodes_raw_bytes() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .upsert_data_object(
                aid(&[0x01]),
                aid(&[0x44, 0x41, 0x54, 0x41, 0xDF, 0x01]),
                b"persistent-data"
            )
            .is_ok());
        let runtime_entry = registry.entries().next().expect("runtime entry");
        let mut payload = [0u8; 64];
        let (magic, len) =
            encode_registry_object_payload(&runtime_entry, &mut payload).expect("encode payload");
        let decoded = decode_data_payload(&payload[..len]).expect("decode data payload");
        assert_eq!(magic, ENCRYPTED_DATA_MAGIC);
        assert_eq!(decoded.bytes, b"persistent-data");
    }

    #[test]
    fn object_blocks_encode_decode_and_check_authentication() {
        let mut buf = vec![0u8; PAGE * 2];
        let len = encode_object_block(INSTANCE_STATE_BLOCK_MAGIC, &[0xDE, 0xAD], PAGE, &mut buf)
            .expect("encode object");
        assert_eq!(len, PAGE);
        let decoded = decode_object_block_at(&buf, 0, PAGE).expect("decode object");
        assert_eq!(decoded.magic, INSTANCE_STATE_BLOCK_MAGIC);
        assert_eq!(decoded.payload, &[0xDE, 0xAD]);

        buf[OBJECT_HEADER_LEN] ^= 0x01;
        assert_eq!(
            decode_object_block_at(&buf, 0, PAGE).map(|_| ()),
            Err(PersistenceFormatError::Authentication)
        );
    }

    #[test]
    fn package_object_block_exposes_fae_payload_after_persistent_header() {
        let fae = [0xF0, 0x9F, 0xA6, 0x80, 0xFA, 0xE0];
        let mut buf = vec![0u8; PAGE * 2];
        let len =
            encode_object_block(PACKAGE_BLOCK_MAGIC, &fae, PAGE, &mut buf).expect("encode package");
        let decoded = decode_object_block_at(&buf, 0, PAGE).expect("decode package");

        assert_eq!(len, PAGE);
        assert_eq!(decoded.magic, PACKAGE_BLOCK_MAGIC);
        assert_eq!(decoded.payload, fae);
        assert_eq!(decoded.payload.as_ptr(), unsafe {
            buf.as_ptr().add(OBJECT_BLOCK_HEADER_LEN)
        });
    }

    #[test]
    fn complete_image_authenticates_before_decryption_and_checks_scratch() {
        let mut block = [0xff; PAGE];
        encode_registry_block(7, &[], PAGE, &mut block).unwrap();
        let mut scratch = [0x5a; 16];
        assert_eq!(
            decrypt_registry_image(&block, 0, PAGE, &mut scratch).unwrap(),
            7u64.to_le_bytes()
        );
        assert_eq!(
            decrypt_registry_image(&block, 0, PAGE, &mut scratch[..8]),
            Err(PersistenceFormatError::BufferTooSmall)
        );
        scratch.fill(0x5a);
        block[32] ^= 1;
        assert_eq!(
            decrypt_registry_image(&block, 0, PAGE, &mut scratch),
            Err(PersistenceFormatError::Authentication)
        );
        assert_eq!(scratch, [0x5a; 16]);
    }

    #[test]
    fn registry_blocks_encode_decode_and_expose_entries() {
        let entries = [
            entry(&[0x10], &[0x01], PersistentObjectKind::Package),
            entry(&[0x11], &[0x01], PersistentObjectKind::Instance),
        ];
        let mut buf = vec![0u8; PAGE * 4];
        let len = encode_registry_block(7, &entries, PAGE, &mut buf).expect("encode registry");
        assert_eq!(len, PAGE * 2);
        let decoded = decode_registry_block_at(&buf, 0, PAGE).expect("decode registry");
        assert_eq!(decoded.mutation_counter, 7);
        assert_eq!(decoded.entry_count, 2);
        assert_eq!(decoded.entry(0), Ok(entries[0]));
        assert_eq!(decoded.entry(1), Ok(entries[1]));
    }

    #[test]
    fn scanner_returns_highest_valid_mutation_counter() {
        let first_entry = [entry(&[0x10], &[0x01], PersistentObjectKind::Instance)];
        let second_entry = [entry(&[0x20], &[0x01], PersistentObjectKind::Key)];
        let mut area = vec![0xFFu8; PAGE * 6];
        let first_len =
            encode_registry_block_at(0, 1, &first_entry, PAGE, &mut area[0..PAGE * 2]).unwrap();
        let second_len = encode_registry_block_at(
            first_len,
            3,
            &second_entry,
            PAGE,
            &mut area[first_len..first_len + PAGE * 2],
        )
        .unwrap();
        assert_eq!(second_len, PAGE * 2);
        let latest = find_latest_registry_block(&area, PAGE)
            .expect("scan")
            .expect("latest registry");
        assert_eq!(latest.offset, first_len);
        assert_eq!(latest.mutation_counter, 3);
        assert_eq!(latest.entry(0), Ok(second_entry[0]));
    }

    #[test]
    fn padded_package_keeps_exact_payload_and_complete_protected_extent() {
        let mut area = vec![0xFF; PAGE * 5];
        let payload = [0x37; PAGE - OBJECT_HEADER_LEN];
        let nominal = encode_object_block(PACKAGE_BLOCK_MAGIC, &payload, PAGE, &mut area).unwrap();
        assert_eq!(nominal, PAGE);
        let total = nominal + PAGE;
        area[nominal..total].fill(0xFF);
        write_u32_le(&mut area[4..8], total as u32);
        seal_block(0, &mut area[..total]).unwrap();
        let block = decode_object_block_at(&area, 0, PAGE).unwrap();
        assert_eq!(block.payload, payload);
        assert_eq!(block.total_len, total);
        assert!(area[OBJECT_HEADER_LEN + payload.len()..total]
            .iter()
            .all(|b| *b == 0xFF));
        assert_eq!(
            scan_persistence_area(&area, PAGE).unwrap().append_offset,
            total
        );
        let protected = [PersistentRange::new(0, total)];
        assert!(erased_span_at(&area, PAGE, PAGE, PAGE, &protected)
            .unwrap()
            .is_none());
        area[total - 1] ^= 1;
        assert!(decode_object_block_at(&area, 0, PAGE).is_err());
        assert_eq!(
            scan_persistence_area(&area, PAGE).unwrap().append_offset,
            total
        );
    }

    #[test]
    fn address_dependent_reservation_rechecks_erased_and_recycled_candidates() {
        let erased = vec![0xFF; PAGE * 8];
        let protected = [PersistentRange::new(0, PAGE * 2)];
        let span = find_reusable_span_sized(
            &erased,
            PAGE,
            PAGE * 4,
            |offset| {
                if offset == PAGE * 2 {
                    Some(PAGE * 3)
                } else {
                    None
                }
            },
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!((span.offset, span.total_len), (PAGE * 2, PAGE * 3));
        assert!(!span.needs_erase());

        let used = vec![0; PAGE * 12];
        let span = find_reusable_span_sized(
            &used,
            PAGE,
            PAGE * 4,
            |offset| {
                if offset == PAGE * 4 {
                    Some(PAGE * 5)
                } else {
                    None
                }
            },
            &[],
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            (span.offset, span.total_len, span.erase_len),
            (PAGE * 4, PAGE * 5, PAGE * 8)
        );
        assert!(
            find_reusable_span_sized(&erased, PAGE, PAGE * 4, |_| None, &[])
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn area_scan_advances_append_offset_past_objects_and_registry() {
        let entries = [entry(&[0x10], &[0x01], PersistentObjectKind::Instance)];
        let mut area = vec![0xFFu8; PAGE * 8];
        let object_len = encode_object_block_at(
            0,
            DATA_BLOCK_MAGIC,
            &[0xCA, 0xFE],
            PAGE,
            &mut area[..PAGE * 2],
        )
        .unwrap();
        let registry_len = encode_registry_block_at(
            object_len,
            4,
            &entries,
            PAGE,
            &mut area[object_len..object_len + PAGE * 2],
        )
        .unwrap();

        let scan = scan_persistence_area(&area, PAGE).expect("scan");
        assert_eq!(scan.append_offset, object_len + registry_len);
        assert_eq!(
            scan.latest_registry.map(|block| block.mutation_counter),
            Some(4)
        );
    }

    #[test]
    fn reusable_span_can_use_erased_hole_before_later_valid_blocks() {
        let entries = [entry(&[0x10], &[0x01], PersistentObjectKind::Instance)];
        let mut area = vec![0xFFu8; PAGE * 8];
        encode_registry_block_at(PAGE * 4, 1, &entries, PAGE, &mut area[PAGE * 4..PAGE * 6])
            .unwrap();

        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE * 2, &[])
            .expect("search")
            .expect("free span");
        assert_eq!(span, ReusableSpan::erased(0, PAGE * 2));
        assert_eq!(
            find_latest_registry_block(&area, PAGE)
                .expect("scan")
                .map(|block| block.offset),
            Some(PAGE * 4)
        );
    }

    #[test]
    fn reusable_span_never_uses_protected_erased_pages() {
        let area = vec![0xFFu8; PAGE * 4];
        let protected = [PersistentRange::new(0, PAGE)];

        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE, &protected)
            .expect("search")
            .expect("second erased page");
        assert_eq!(span, ReusableSpan::erased(PAGE, PAGE));
    }

    #[test]
    fn circular_allocator_prefers_erased_pages_and_wraps_before_recycling() {
        let mut area = vec![0x00u8; PAGE * 12];
        area[PAGE..PAGE * 2].fill(0xff);
        area[PAGE * 5..PAGE * 6].fill(0xff);
        let protected = [
            PersistentRange::new(0, PAGE),
            PersistentRange::new(PAGE * 4, PAGE),
        ];
        let after_boss = PAGE * 5;
        let first = find_reusable_span_sized_from(
            &area,
            PAGE,
            SECTOR,
            after_boss,
            |_| Some(PAGE),
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!(first, ReusableSpan::erased(PAGE * 5, PAGE));

        area[PAGE * 5..PAGE * 6].fill(0);
        let wrapped = find_reusable_span_sized_from(
            &area,
            PAGE,
            SECTOR,
            after_boss,
            |_| Some(PAGE),
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!(wrapped, ReusableSpan::erased(PAGE, PAGE));

        area[PAGE..PAGE * 2].fill(0);
        let recycled = find_reusable_span_sized_from(
            &area,
            PAGE,
            SECTOR,
            after_boss,
            |_| Some(PAGE),
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            recycled,
            ReusableSpan::recycled_sector(PAGE * 8, PAGE, SECTOR)
        );
    }

    #[test]
    fn circular_allocator_rotates_recycling_after_boss() {
        let area = vec![0x00u8; PAGE * 12];
        let protected = [PersistentRange::new(0, PAGE * 4)];
        let span = find_reusable_span_sized_from(
            &area,
            PAGE,
            SECTOR,
            PAGE * 4,
            |_| Some(PAGE),
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!(span, ReusableSpan::recycled_sector(PAGE * 4, PAGE, SECTOR));

        let protected = [
            PersistentRange::new(0, PAGE * 4),
            PersistentRange::new(PAGE * 8, PAGE * 4),
        ];
        let wrapped = find_reusable_span_sized_from(
            &area,
            PAGE,
            SECTOR,
            PAGE * 8,
            |_| Some(PAGE),
            &protected,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            wrapped,
            ReusableSpan::recycled_sector(PAGE * 4, PAGE, SECTOR)
        );
    }

    #[test]
    fn exact_append_cursor_reserves_erased_pages_without_a_scan() {
        let area = vec![0xFFu8; PAGE * 4];

        let span = erased_span_at(&area, PAGE, PAGE * 2, PAGE, &[])
            .expect("validate cursor")
            .expect("erased pages");

        assert_eq!(span, ReusableSpan::erased(PAGE, PAGE * 2));
    }

    #[test]
    fn exact_append_cursor_rejects_occupied_or_protected_pages() {
        let mut area = vec![0xFFu8; PAGE * 4];
        area[PAGE] = 0;
        assert_eq!(
            erased_span_at(&area, PAGE, PAGE, PAGE, &[]).expect("occupied cursor"),
            None
        );

        area[PAGE] = 0xFF;
        let protected = [PersistentRange::new(PAGE, PAGE)];
        assert_eq!(
            erased_span_at(&area, PAGE, PAGE, PAGE, &protected).expect("protected cursor"),
            None
        );
    }

    #[test]
    fn reusable_span_recycles_complete_unprotected_sector_before_programming() {
        let mut area = vec![0x00u8; PAGE * 8];
        encode_object_block_at(
            0,
            DATA_BLOCK_MAGIC,
            &[0xA5; PAGE * 3],
            PAGE,
            &mut area[..PAGE * 4],
        )
        .unwrap();
        let protected = [PersistentRange::new(PAGE * 4, PAGE)];

        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE * 2, &protected)
            .expect("search")
            .expect("reusable sector");
        assert_eq!(span, ReusableSpan::recycled_sector(0, PAGE * 2, SECTOR));
    }

    #[test]
    fn reusable_span_recycles_unauthenticated_abandoned_load_sector() {
        let mut area = vec![0x00u8; PAGE * 80];
        let block_len = encode_object_block_at(
            0,
            PACKAGE_BLOCK_MAGIC,
            &[0xA5; PAGE * 3],
            PAGE,
            &mut area[..PAGE * 40],
        )
        .unwrap();
        area[block_len - 1] ^= 0x5A;
        assert!(decode_object_block_at(&area, 0, PAGE).is_err());

        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE * 2, &[])
            .expect("search")
            .expect("abandoned C0DE block");
        assert_eq!(span, ReusableSpan::recycled_sector(0, PAGE * 2, SECTOR));
    }

    #[test]
    fn smaller_rewrite_leaves_erased_tail_as_reusable_hole() {
        let entries = [entry(&[0x10], &[0x01], PersistentObjectKind::Instance)];
        let mut area = vec![0xFFu8; PAGE * 8];
        encode_object_block_at(
            0,
            DATA_BLOCK_MAGIC,
            &[0xA5; PAGE * 3],
            PAGE,
            &mut area[..PAGE * 4],
        )
        .unwrap();
        let smaller_len =
            encode_object_block_at(0, DATA_BLOCK_MAGIC, &[0x5A], PAGE, &mut area[..PAGE * 2])
                .unwrap();
        area[smaller_len..PAGE * 4].fill(0xFF);
        encode_registry_block_at(PAGE * 4, 5, &entries, PAGE, &mut area[PAGE * 4..PAGE * 6])
            .unwrap();

        let scan = scan_persistence_area(&area, PAGE).expect("scan");
        assert_eq!(
            scan.latest_registry.map(|block| block.offset),
            Some(PAGE * 4)
        );
        assert_eq!(scan.append_offset, smaller_len);
        let protected = [
            PersistentRange::new(0, smaller_len),
            PersistentRange::new(PAGE * 4, PAGE * 2),
        ];
        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE, &protected)
            .expect("search")
            .expect("tail hole");
        assert_eq!(span, ReusableSpan::erased(smaller_len, PAGE));
    }

    #[test]
    fn invalid_containers_resume_pagewise_and_require_inner_authentication() {
        for magic in [
            PACKAGE_BLOCK_MAGIC,
            DATA_BLOCK_MAGIC,
            INSTANCE_STATE_BLOCK_MAGIC,
        ] {
            let mut area = vec![0xff; PAGE * 10];
            encode_registry_block_at(0, 1, &[], PAGE, &mut area[..PAGE]).unwrap();
            let mut payload = vec![0xff; PAGE * 4];
            encode_registry_block_at(
                PAGE * 3,
                999,
                &[],
                PAGE,
                &mut payload[PAGE - OBJECT_HEADER_LEN..],
            )
            .unwrap();
            let len =
                encode_object_block_at(PAGE, magic, &payload, PAGE, &mut area[PAGE..]).unwrap();
            for invalid in [false, true] {
                if invalid {
                    area[PAGE + 16..PAGE + 32].fill(0xff);
                }
                let scan = scan_persistence_area(&area, PAGE).unwrap();
                assert_eq!(scan.latest_registry.unwrap().mutation_counter, 1);
                if !invalid {
                    assert_eq!(scan.append_offset, PAGE + len);
                }
            }
            // A later legitimate publication must remain reachable.
            encode_registry_block_at(PAGE + len, 2, &[], PAGE, &mut area[PAGE + len..]).unwrap();
            assert_eq!(
                find_latest_registry_block(&area, PAGE)
                    .unwrap()
                    .unwrap()
                    .mutation_counter,
                2
            );
        }
    }

    #[test]
    fn recycling_keeps_authenticated_outer_opaque_during_interruption() {
        let mut area = vec![0x5a; SECTOR * 5];
        let mut payload = vec![0x5a; SECTOR * 2];
        // Include an unauthenticated C0DE and a valid BOSS hidden in its claimed
        // extent. Neutralization must inspect both page starts independently.
        let inner = PAGE - OBJECT_HEADER_LEN;
        payload[inner..inner + 4].copy_from_slice(&PACKAGE_BLOCK_MAGIC.to_le_bytes());
        payload[inner + 4..inner + 8].copy_from_slice(&(SECTOR as u32).to_le_bytes());
        encode_registry_block_at(
            SECTOR,
            999,
            &[],
            PAGE,
            &mut payload[SECTOR - OBJECT_HEADER_LEN..],
        )
        .unwrap();
        let len = encode_object_block(PACKAGE_BLOCK_MAGIC, &payload, PAGE, &mut area).unwrap();
        let live = SECTOR * 3;
        encode_registry_block_at(live, 1, &[], PAGE, &mut area[live..]).unwrap();
        let protected = [PersistentRange::new(live, PAGE)];
        // Use one sector for the new object although the retired block spans three.
        let span = ReusableSpan::recycled_sector(0, PAGE, SECTOR);
        assert_eq!(
            find_reusable_span(&area, PAGE, SECTOR, PAGE, &protected).unwrap(),
            Some(span)
        );
        assert!(recycling_preserves_boundaries(
            &area,
            PAGE,
            PersistentRange::new(0, SECTOR),
            &protected
        ));
        let mut offsets = vec![];
        neutralize_recycled_blocks(&area, PAGE, span, |offset| {
            offsets.push(offset);
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(offsets, [PAGE, SECTOR, 0]);
        // Cut at every programming operation and every byte of its magic word.
        for cut in 0..offsets.len() {
            for bytes in 0..=4 {
                let mut interrupted = area.clone();
                let mut call = 0;
                let result = neutralize_recycled_blocks(&area, PAGE, span, |offset| {
                    let n = if call == cut { bytes } else { 4 };
                    interrupted[offset..offset + n].fill(0);
                    if call == cut {
                        return Err(());
                    }
                    call += 1;
                    Ok(())
                });
                assert!(result.is_err());
                assert_eq!(
                    find_latest_registry_block(&interrupted, PAGE)
                        .unwrap()
                        .unwrap()
                        .mutation_counter,
                    // Authenticated outer extent remains opaque while its
                    // inner headers are neutralized, even with a broken CRC.
                    1
                );
            }
        }
        let original = area.clone();
        neutralize_recycled_blocks(&original, PAGE, span, |offset| {
            area[offset..offset + 4].fill(0);
            Ok::<_, ()>(())
        })
        .unwrap();
        // Prefix-erase model: even loss of the retired outer header cannot expose
        // the old fake BOSS. This is not an electrical erase qualification.
        for cut in 0..=SECTOR {
            let mut interrupted = area.clone();
            interrupted[..cut].fill(0xff);
            assert_eq!(
                find_latest_registry_block(&interrupted, PAGE)
                    .unwrap()
                    .unwrap()
                    .mutation_counter,
                1
            );
        }
        let reused = find_reusable_span(&area, PAGE, SECTOR, PAGE, &protected)
            .unwrap()
            .unwrap();
        assert_eq!(reused, span);
        area[..SECTOR].fill(0xff);
        encode_registry_block_at(0, 2, &[], PAGE, &mut area[..PAGE]).unwrap();
        assert_eq!(
            find_latest_registry_block(&area, PAGE)
                .unwrap()
                .unwrap()
                .mutation_counter,
            2
        );
        // Tail payload bytes survive: no erase was needed beyond the new span.
        assert_eq!(area[len - 1], original[len - 1]);
    }

    #[test]
    fn recycling_rejects_interior_allocations_and_protected_tails() {
        let mut area = vec![0x5a; SECTOR * 4];
        encode_object_block(DATA_BLOCK_MAGIC, &vec![0x5a; SECTOR * 2], PAGE, &mut area).unwrap();
        assert!(!recycling_preserves_boundaries(
            &area,
            PAGE,
            PersistentRange::new(SECTOR, SECTOR),
            &[]
        ));
        assert!(!recycling_preserves_boundaries(
            &area,
            PAGE,
            PersistentRange::new(0, SECTOR),
            &[PersistentRange::new(SECTOR, PAGE)]
        ));
    }

    #[test]
    fn scanner_ignores_corrupted_latest_and_keeps_previous_registry() {
        let first_entry = [entry(&[0x10], &[0x01], PersistentObjectKind::Instance)];
        let second_entry = [entry(&[0x20], &[0x01], PersistentObjectKind::Key)];
        let mut area = vec![0xFFu8; PAGE * 6];
        let first_len =
            encode_registry_block_at(0, 1, &first_entry, PAGE, &mut area[0..PAGE * 2]).unwrap();
        encode_registry_block_at(
            first_len,
            2,
            &second_entry,
            PAGE,
            &mut area[first_len..first_len + PAGE * 2],
        )
        .unwrap();
        area[first_len + REGISTRY_HEADER_LEN] ^= 0x01;

        let latest = find_latest_registry_block(&area, PAGE)
            .expect("scan")
            .expect("previous registry");
        assert_eq!(latest.offset, 0);
        assert_eq!(latest.mutation_counter, 1);
        assert_eq!(latest.entry(0), Ok(first_entry[0]));
    }

    #[test]
    fn every_torn_registry_prefix_recovers_one_complete_graph() {
        // Model programming from erased flash, including a partially programmed
        // byte at each cut. This exercises format/recovery, not electrical faults.
        let old = vec![
            entry(&[0x10], &[0x01], PersistentObjectKind::Package),
            entry(&[0x11], &[0x01], PersistentObjectKind::Instance),
            entry(&[0x12], &[0x01], PersistentObjectKind::Data),
        ];
        let mut loaded = old.clone();
        loaded.push(entry(&[0x20], &[0x01], PersistentObjectKind::Package));
        let mut replaced = old.clone();
        replaced[2].data_ref.offset = 0x800;
        // Cumulative deletion removes package and instance together.
        let deleted = vec![old[2]];
        for next in [loaded, replaced, deleted] {
            let mut base = vec![0xFF; PAGE * 32];
            write_persistence_area_marker(&mut base[..PAGE]).unwrap();
            let old_len = encode_registry_block_at(PAGE, 7, &old, PAGE, &mut base[PAGE..]).unwrap();
            let offset = PAGE + old_len;
            let mut encoded = vec![0xFF; PAGE * 8];
            let len = encode_registry_block_at(offset, 8, &next, PAGE, &mut encoded).unwrap();
            encoded.truncate(len);
            for cut in 0..=len {
                for bits in 0..8 {
                    let mut area = base.clone();
                    area[offset..offset + cut].copy_from_slice(&encoded[..cut]);
                    if cut < len {
                        // Clear only the lowest `bits` that the target byte
                        // would program; all other bits remain erased.
                        let mask = ((1u16 << bits) - 1) as u8;
                        area[offset + cut] = encoded[cut] | !mask;
                    }
                    let committed = area[offset..offset + len] == encoded;
                    let expected = if committed { &next } else { &old };
                    for _ in 0..3 {
                        let scan = scan_persistence_area(&area, PAGE).unwrap();
                        let boss = scan.latest_registry.expect("previous BOSS survives");
                        assert_eq!(boss.mutation_counter, if committed { 8 } else { 7 });
                        let actual: Vec<_> = (0..boss.entry_count as usize)
                            .map(|i| boss.entry(i).unwrap())
                            .collect();
                        assert_eq!(&actual, expected, "cut={cut}, bits={bits}");
                    }
                    // Retry after recovery in fresh space. The torn candidate
                    // cannot supersede the retry or resurrect removed entries.
                    let retry_offset = offset + len;
                    encode_registry_block_at(
                        retry_offset,
                        9,
                        &next,
                        PAGE,
                        &mut area[retry_offset..],
                    )
                    .unwrap();
                    let boss = scan_persistence_area(&area, PAGE)
                        .unwrap()
                        .latest_registry
                        .unwrap();
                    assert_eq!(boss.mutation_counter, 9);
                    assert_eq!(boss.entry_count as usize, next.len());
                    for (i, value) in next.iter().enumerate() {
                        assert_eq!(boss.entry(i), Ok(*value));
                    }
                }
            }
        }
    }

    #[test]
    fn scanner_treats_erased_pages_as_free_space_not_as_end_marker() {
        let entries = [entry(
            &[0x33],
            &[0x01],
            PersistentObjectKind::SecurityDomain,
        )];
        let mut area = vec![0xFFu8; PAGE * 4];
        encode_registry_block_at(PAGE, 9, &entries, PAGE, &mut area[PAGE..PAGE * 3]).unwrap();
        let scan = scan_persistence_area(&area, PAGE).expect("scan");
        assert_eq!(scan.append_offset, 0);
        let latest = scan.latest_registry.expect("registry after erased page");
        assert_eq!(latest.offset, PAGE);
        assert_eq!(latest.mutation_counter, 9);
    }

    #[test]
    fn reusable_span_never_erases_sector_touching_protected_range() {
        let area = vec![0x00u8; SECTOR * 2];
        let protected = [PersistentRange::new(PAGE * 2, PAGE)];

        let span = find_reusable_span(&area, PAGE, SECTOR, PAGE, &protected)
            .expect("search")
            .expect("second sector");
        assert_eq!(span, ReusableSpan::recycled_sector(SECTOR, PAGE, SECTOR));
    }

    #[test]
    fn reusable_span_can_reserve_multiple_recyclable_sectors_for_large_object() {
        let area = vec![0x00u8; SECTOR * 4];
        let protected = [PersistentRange::new(0, SECTOR)];

        let span = find_reusable_span(&area, PAGE, SECTOR, SECTOR + PAGE, &protected)
            .expect("search")
            .expect("two-sector span");
        assert_eq!(
            span,
            ReusableSpan::recycled_sector(SECTOR, SECTOR + PAGE, SECTOR * 2)
        );
    }

    #[test]
    fn scp11_key_types_have_stable_persistent_tags() {
        assert_eq!(encode_key_type(KeyObjectType::Scp11SdEckaPrivate), 1);
        assert_eq!(encode_key_type(KeyObjectType::Scp11CaKlocPublic), 2);
        assert_eq!(decode_key_type(1), Ok(KeyObjectType::Scp11SdEckaPrivate));
        assert_eq!(decode_key_type(2), Ok(KeyObjectType::Scp11CaKlocPublic));
    }
}
