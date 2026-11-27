//! Two-sector append journal for the durable BOSS address.
//! Each eight-byte slot contains a page offset and its bitwise complement. The secondary
//! sector holds one validated address while the primary sector is rotated.

#[cfg(not(test))]
use super::physical;
use super::{format, storage::PERSISTENCE_PAGE_BUFFER};
#[cfg(test)]
#[path = "journal_test_flash.rs"]
mod physical;
use crate::registry::objects::{RegistryError, RegistryResult};

// Each corresponding bit pair is 01 or 10. A monotone erase/program change
// cannot turn a complete entry into a different complete entry. A torn write
// from erased bytes retains 11 pairs until the intended entry is complete.
const ENTRY_LEN: usize = 8;

fn layout() -> Option<(usize, usize, usize)> {
    let (primary, sector) = physical::journal_area()?;
    let page = physical::logical_page_size();
    (page >= ENTRY_LEN && sector.is_multiple_of(page)).then_some((primary, sector, page))
}

fn mapped(address: usize, len: usize) -> &'static [u8] {
    physical::read_journal(address, len).expect("validated journal layout")
}

fn entry(offset: usize) -> Option<[u8; ENTRY_LEN]> {
    let offset = u32::try_from(offset).ok()?;
    let mut bytes = [0xff; ENTRY_LEN];
    bytes[..4].copy_from_slice(&offset.to_le_bytes());
    bytes[4..].copy_from_slice(&(!offset).to_le_bytes());
    Some(bytes)
}

fn decode(bytes: &[u8], data_len: usize, page: usize) -> Option<usize> {
    let offset = u32::from_le_bytes(bytes[..4].try_into().ok()?) as usize;
    let complement = u32::from_le_bytes(bytes[4..8].try_into().ok()?);
    (offset >= page
        && offset < data_len
        && offset.is_multiple_of(page)
        && complement == !(offset as u32))
        .then_some(offset)
}

fn validate<'a>(
    area: &'a [u8],
    page: usize,
    bytes: &[u8],
) -> Option<format::RegistryBlockView<'a>> {
    let offset = decode(bytes, area.len(), page)?;
    format::decode_registry_block_at(area, offset, page).ok()
}

fn write_entry(address: usize, bytes: [u8; ENTRY_LEN], page: usize) -> RegistryResult {
    super::storage::require_writable()?;
    let aligned = address / page * page;
    let within = address - aligned;
    let mut scratch = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    let buffer = &mut scratch[..page];
    buffer.copy_from_slice(mapped(aligned, page));
    if buffer[within..within + ENTRY_LEN] != [0xff; ENTRY_LEN] {
        return Err(RegistryError::Persistence);
    }
    buffer[within..within + ENTRY_LEN].copy_from_slice(&bytes);
    physical::program_page(aligned, buffer).map_err(|_| {
        super::storage::freeze();
        RegistryError::Persistence
    })?;
    (mapped(address, ENTRY_LEN) == bytes)
        .then_some(())
        .ok_or(RegistryError::Persistence)
        .inspect_err(|_| super::storage::freeze())
}

fn erase(address: usize) -> RegistryResult {
    super::storage::require_writable()?;
    // A stale secondary must never coexist with a later acknowledged append.
    // Freeze before unwinding, so rollback/LOAD cleanup cannot release pages.
    physical::erase_sector(address).map_err(|_| {
        super::storage::freeze();
        RegistryError::Persistence
    })
}

pub(crate) fn initialize() -> RegistryResult {
    super::storage::require_writable()?;
    let (primary, sector, _) = layout().ok_or(RegistryError::Persistence)?;
    erase(primary)?;
    erase(primary + sector)
}

/// Recover an interrupted rotation, then try newest journal slots first.
/// A torn or stale slot never makes an unjournaled BOSS authoritative.
pub(crate) fn latest<'a>(
    area: &'a [u8],
    page: usize,
) -> Result<Option<format::RegistryBlockView<'a>>, RegistryError> {
    super::storage::require_writable()?;
    let (primary, sector, _) = layout().ok_or(RegistryError::Persistence)?;
    let secondary = primary + sector;
    let backup = mapped(secondary, sector);
    if backup.iter().any(|byte| *byte != 0xff) {
        if let Some(boss) = validate(area, page, &backup[..ENTRY_LEN]) {
            erase(primary)?;
            write_entry(
                primary,
                entry(boss.offset).ok_or(RegistryError::Persistence)?,
                page,
            )?;
        }
        erase(secondary)?;
    }
    Ok(latest_in(area, page, mapped(primary, sector)))
}

fn latest_in<'a>(
    area: &'a [u8],
    page: usize,
    slots: &[u8],
) -> Option<format::RegistryBlockView<'a>> {
    for index in (0..slots.len() / ENTRY_LEN).rev() {
        let bytes = &slots[index * ENTRY_LEN..(index + 1) * ENTRY_LEN];
        if bytes == [0xff; ENTRY_LEN] {
            continue;
        }
        if let Some(boss) = validate(area, page, bytes) {
            return Some(boss);
        }
    }
    None
}

/// Publish only after the new BOSS has been programmed and read back.
pub(crate) fn append(area: &[u8], page: usize, offset: usize) -> RegistryResult {
    super::storage::require_writable()?;
    let (primary, sector, _) = layout().ok_or(RegistryError::Persistence)?;
    let bytes = entry(offset).ok_or(RegistryError::Persistence)?;
    let slots = mapped(primary, sector);
    if let Some(index) = (0..sector / ENTRY_LEN)
        .find(|index| slots[index * ENTRY_LEN..(index + 1) * ENTRY_LEN] == [0xff; ENTRY_LEN])
    {
        return write_entry(primary + index * ENTRY_LEN, bytes, page);
    }
    let old = latest(area, page)?.ok_or(RegistryError::Persistence)?;
    let secondary = primary + sector;
    write_entry(
        secondary,
        entry(old.offset).ok_or(RegistryError::Persistence)?,
        page,
    )?;
    erase(primary)?;
    write_entry(
        primary,
        entry(old.offset).ok_or(RegistryError::Persistence)?,
        page,
    )?;
    erase(secondary)?;
    write_entry(primary + ENTRY_LEN, bytes, page)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn failed_secondary_erase_blocks_d_until_reset_and_recovery() {
        let _lock = crate::selected_app::tests::reset_registry_test_state();
        let _reset = physical::reset();
        let mut area = [0xff; 1024];
        for (offset, generation) in [(256, 1), (512, 2), (768, 3)] {
            format::encode_registry_block_at(offset, generation, &[], 256, &mut area[offset..])
                .unwrap();
        }
        physical::fill_primary(&entry(256).unwrap()); // Full journal, latest A.
        physical::fault(physical::Fault::Erase(physical::BASE + physical::SECTOR));
        assert_eq!(append(&area, 256, 512), Err(RegistryError::Persistence));
        let interrupted = physical::image();
        assert_eq!(&interrupted[..8], &entry(256).unwrap());
        assert_eq!(
            &interrupted[physical::SECTOR..physical::SECTOR + 8],
            &entry(256).unwrap()
        );
        let calls = physical::calls();
        assert!(super::super::physical::program_page(0, &[0xff; 256]).is_err());
        assert!(super::super::physical::erase_sector(0).is_err());
        // The same cleanup helper is used by failed snapshots, content and LOAD.
        let held = super::super::pages::Pages::new();
        held.reset(256, 1024).unwrap();
        let range = format::PersistentRange::new(256, 256);
        held.reserve(range).unwrap();
        super::super::retention::release_unattached(&held, range).unwrap();
        assert!(held.reserve(range).is_err());

        // A later D must not be acknowledged while stale backup A remains.
        assert_eq!(append(&area, 256, 768), Err(RegistryError::Persistence));
        assert!(latest(&area, 256).is_err());
        assert!(initialize().is_err());
        let pages = super::super::pages::Pages::new();
        assert!(super::super::storage::reserve_persistent_span(&area, 256, 256, &pages).is_err());
        assert_eq!(physical::calls(), calls);
        assert_eq!(physical::image(), interrupted);

        // A reset clears only volatile uncertainty, retaining the physical image.
        super::super::storage::reset_freeze_for_test();
        assert_eq!(latest(&area, 256).unwrap().unwrap().offset, 256);
        append(&area, 256, 768).unwrap();
        super::super::storage::reset_freeze_for_test();
        assert_eq!(latest(&area, 256).unwrap().unwrap().offset, 768);
    }

    #[test]
    fn program_and_postwrite_readback_errors_freeze_journal() {
        let _lock = crate::selected_app::tests::reset_registry_test_state();
        for fault in [physical::Fault::Program, physical::Fault::Readback] {
            let _reset = physical::reset();
            let mut area = [0xff; 768];
            format::encode_registry_block_at(256, 1, &[], 256, &mut area[256..]).unwrap();
            physical::fault(fault);
            assert_eq!(append(&area, 256, 256), Err(RegistryError::Persistence));
            let calls = physical::calls();
            assert_eq!(append(&area, 256, 256), Err(RegistryError::Persistence));
            assert_eq!(physical::calls(), calls);
        }
    }

    #[test]
    fn complement_slots_reject_erased_fields_and_monotone_retargeting() {
        let entries: std::vec::Vec<_> = (256..992 * 256)
            .step_by(256)
            .map(|offset| (offset, entry(offset).unwrap()))
            .collect();
        for (offset, encoded) in &entries {
            assert_eq!(decode(encoded, 992 * 256, 256), Some(*offset));
            let mut incomplete = *encoded;
            incomplete[4..].fill(0xff);
            assert_eq!(decode(&incomplete, 992 * 256, 256), None);
            for (other, target) in &entries {
                if offset != other {
                    assert!(!encoded.iter().zip(target).all(|(a, b)| a & b == *a));
                    assert!(!encoded.iter().zip(target).all(|(a, b)| a & b == *b));
                }
            }
        }
        assert_eq!(decode(&[0xff; 8], 992 * 256, 256), None);
    }

    #[test]
    fn ordered_program_cuts_and_partial_erases_only_recover_the_same_address() {
        for offset in [256, 0x1c00, 0x2fd00, 991 * 256] {
            let encoded = entry(offset).unwrap();
            // Completed prefix, arbitrary partial byte, untouched erased suffix.
            for cut in 0..8 {
                for partial in 0..=255u8 {
                    if partial & encoded[cut] != encoded[cut] {
                        continue;
                    }
                    let mut torn = [0xff; 8];
                    torn[..cut].copy_from_slice(&encoded[..cut]);
                    torn[cut] = partial;
                    if let Some(found) = decode(&torn, 992 * 256, 256) {
                        assert_eq!(found, offset);
                        assert_eq!(torn, encoded);
                    }
                    // Erasing more bits after a torn program cannot retarget it.
                    for i in 0..8 {
                        let mut erased = torn;
                        erased[i] = 0xff;
                        if let Some(found) = decode(&erased, 992 * 256, 256) {
                            assert_eq!(found, offset);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn torn_and_misaligned_addresses_are_not_journal_entries() {
        let encoded = entry(0x1200).unwrap();
        assert_eq!(decode(&encoded, 0x10000, 256), Some(0x1200));
        for index in 0..ENTRY_LEN {
            let mut torn = encoded;
            torn[index] ^= 1;
            assert_eq!(decode(&torn, 0x10000, 256), None);
        }
        assert_eq!(decode(&entry(0x1201).unwrap(), 0x10000, 256), None);
        assert_eq!(decode(&entry(0x10000).unwrap(), 0x10000, 256), None);
    }

    #[test]
    fn newest_invalid_entry_falls_back_without_promoting_unjournaled_boss() {
        let mut area = [0xff; 1024];
        format::encode_registry_block_at(256, 1, &[], 256, &mut area[256..]).unwrap();
        format::encode_registry_block_at(512, 2, &[], 256, &mut area[512..]).unwrap();
        let mut slots = [0xff; 32];
        slots[..8].copy_from_slice(&entry(256).unwrap());
        slots[8..16].copy_from_slice(&entry(512).unwrap());
        slots[13] ^= 1;
        assert_eq!(latest_in(&area, 256, &slots).unwrap().offset, 256);
        slots[8..16].fill(0xff);
        assert_eq!(latest_in(&area, 256, &slots).unwrap().offset, 256);
    }
}
