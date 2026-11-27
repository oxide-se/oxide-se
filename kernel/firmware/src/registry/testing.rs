//! Host-only backing store for the same compact image / flash-root state machine.
//! Object records simulate immutable backing storage; snapshots store encoded
//! image bytes. Neither is linked into firmware or part of its RAM budget.
use super::{
    image::{Address, Image},
    objects::{ObjectView, RegistryResult},
};
use std::{cell::RefCell, vec::Vec};
std::thread_local! {
    static OPENS: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    static READS: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    static OBJECTS: RefCell<Vec<ObjectView>> = const { RefCell::new(Vec::new()) };
    static SNAPSHOTS: RefCell<Vec<Vec<u8>>> = const { RefCell::new(Vec::new()) };
}
pub(super) fn store_object(object: ObjectView) -> Address {
    OBJECTS.with(|v| {
        let mut v = v.borrow_mut();
        v.push(object);
        Address::new(0xf000_0000 + v.len() as u32 * 256).unwrap()
    })
}
pub(super) fn object(address: Address) -> Option<ObjectView> {
    OPENS.with(|n| n.set(n.get() + 1));
    let index = address.get().checked_sub(0xf000_0000)? as usize / 256;
    OBJECTS.with(|v| v.borrow().get(index.checked_sub(1)?).cloned())
}
pub(super) fn save<const N: usize>(image: &Image<N>) -> RegistryResult<Address> {
    let mut bytes = std::vec![0; 8 + N * 40];
    let len = image.encode(&mut bytes)?;
    bytes.truncate(len);
    Ok(SNAPSHOTS.with(|v| {
        let mut v = v.borrow_mut();
        v.push(bytes);
        Address::new(0xe000_0000 + v.len() as u32 * 4096).unwrap()
    }))
}
pub(super) fn with_snapshot<T>(
    root: Address,
    f: impl FnOnce(&[u8]) -> RegistryResult<T>,
) -> RegistryResult<T> {
    READS.with(|n| n.set(n.get() + 1));
    SNAPSHOTS.with(|v| f(&v.borrow()[(root.get() - 0xe000_0000) as usize / 4096 - 1]))
}

pub(super) fn take_snapshot_reads() -> usize {
    READS.with(|n| n.replace(0))
}

pub(crate) fn take_object_opens() -> usize {
    OPENS.with(|n| n.replace(0))
}
