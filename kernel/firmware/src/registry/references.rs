//! Conversion at the physical boundary. BOSS entries store absolute addresses.
use super::format::{PersistentRef, PersistentSpace};

pub(super) fn base() -> u32 {
    #[cfg(test)]
    {
        0x1000_0000
    }
    #[cfg(not(test))]
    {
        super::physical::persistence_area().start as u32
    }
}
pub(super) fn address(reference: PersistentRef) -> u32 {
    match reference.space {
        PersistentSpace::RegistryFlash => {
            base().checked_add(reference.offset).expect("flash address")
        }
        _ => reference.offset,
    }
}
pub(super) fn reference(address: u32) -> PersistentRef {
    #[cfg(test)]
    let len = 0x1000_0000;
    #[cfg(not(test))]
    let len = super::physical::persistence_area().page_count * super::physical::logical_page_size();
    if address >= base() && u64::from(address) < u64::from(base()) + len as u64 {
        PersistentRef::new(PersistentSpace::RegistryFlash, 0, address - base())
    } else {
        PersistentRef::new(PersistentSpace::FirmwareImage, 0, address)
    }
}
