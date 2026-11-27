//! RAM backing for the compact registry on targets with no persistence area.
//! Entry and snapshot addresses are independent, one-based slot identifiers.
//! A slot can be reused once the current image and every rollback root release it.

use super::{
    image::{Address, Entry, Image, ENTRY_LEN},
    objects::{ObjectPayload, ObjectView, Registry, RegistryError, RegistryResult},
};
use crate::kernel_cell::KernelCell;
use alloc::vec::Vec;

// SAFETY: registry backing stores are used only by the privileged owner core.
// Separate cells let rollback observers read objects while borrowing a snapshot.
// Identity and lifecycle stay in the compact entries, so rollback copies
// only references and the arena does not duplicate the AIDs of every object.
static OBJECTS: KernelCell<Vec<Option<ObjectPayload>>> = unsafe { KernelCell::new(Vec::new()) };
static SNAPSHOTS: KernelCell<Vec<Option<Vec<u8>>>> = unsafe { KernelCell::new(Vec::new()) };

pub(crate) fn enabled() -> bool {
    // Pico images require a valid flash layout. A malformed layout is an error.
    if cfg!(any(oxide_se_board_raspi_pico, oxide_se_board_raspi_pico2)) {
        return false;
    }
    oxi_core::core::target::flash_persistence_area().page_count == 0
}

pub(super) fn clear() {
    OBJECTS.set(Vec::new());
    SNAPSHOTS.set(Vec::new());
}

pub(super) fn store_object(object: &ObjectView) -> RegistryResult<Address> {
    insert(&mut OBJECTS.borrow_mut(), object.payload.clone())
}

pub(super) fn object(entry: Entry) -> RegistryResult<ObjectView> {
    let payload = get(&OBJECTS.borrow(), entry.address())?.clone();
    Ok(ObjectView {
        parent_sd_aid: entry.parent(),
        object_aid: entry.object(),
        object_kind: super::state::runtime_object_kind(entry.kind().kind()),
        payload,
    })
}

pub(super) fn save<const N: usize>(image: &Image<N>) -> RegistryResult<Address> {
    let len = 8 + image.entries().len() * ENTRY_LEN;
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(len)
        .map_err(|_| RegistryError::Capacity)?;
    bytes.resize(len, 0);
    image.encode(&mut bytes)?;
    insert(&mut SNAPSHOTS.borrow_mut(), bytes)
}

pub(super) fn with_snapshot<T>(
    root: Address,
    read: impl FnOnce(&[u8]) -> RegistryResult<T>,
) -> RegistryResult<T> {
    read(get(&SNAPSHOTS.borrow(), root)?)
}

pub(super) fn collect<const N: usize>(registry: &Registry<N>) -> RegistryResult {
    let mut snapshots = SNAPSHOTS.borrow_mut();
    for (index, snapshot) in snapshots.iter_mut().enumerate() {
        let address = slot_address(index)?;
        if registry.current != Some(address)
            && !registry.snapshots.roots().any(|root| root == address)
        {
            *snapshot = None;
        }
    }

    let mut objects = OBJECTS.borrow_mut();
    for (index, object) in objects
        .iter_mut()
        .enumerate()
        .filter(|(_, object)| object.is_some())
    {
        let address = slot_address(index)?;
        let matches = |entry: Entry| !entry.is_empty() && entry.address() == address;
        let current = registry.image.entries().iter().copied().any(matches);
        if current {
            continue;
        }
        let saved = snapshots.iter().flatten().any(|bytes| {
            bytes[8..]
                .chunks_exact(ENTRY_LEN)
                .any(|entry| matches(Entry::decode(entry).expect("valid volatile snapshot entry")))
        });
        if !saved {
            *object = None;
        }
    }
    Ok(())
}

fn insert<T>(slots: &mut Vec<Option<T>>, value: T) -> RegistryResult<Address> {
    if let Some((index, slot)) = slots
        .iter_mut()
        .enumerate()
        .find(|(_, slot)| slot.is_none())
    {
        *slot = Some(value);
        return slot_address(index);
    }
    let address = slot_address(slots.len())?;
    // Avoid doubling the resident slot table on the small flashless heaps.
    slots
        .try_reserve_exact(1)
        .map_err(|_| RegistryError::Capacity)?;
    slots.push(Some(value));
    Ok(address)
}

fn get<T>(slots: &[Option<T>], address: Address) -> RegistryResult<&T> {
    slots
        .get(address.get() as usize - 1)
        .and_then(Option::as_ref)
        .ok_or(RegistryError::InvalidData)
}

fn slot_address(index: usize) -> RegistryResult<Address> {
    let index = u32::try_from(index).map_err(|_| RegistryError::Capacity)?;
    Address::new(index.checked_add(1).ok_or(RegistryError::Capacity)?)
}
