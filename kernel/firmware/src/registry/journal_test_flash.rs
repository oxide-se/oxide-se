//! Host-only flash transport for executing the real journal control flow.
//! BOSS encoding/validation remain the production host-test implementations.
use oxi_core::core::flash::{FlashError, FlashResult};
use std::{cell::RefCell, vec, vec::Vec};
pub(super) const BASE: usize = 0x100000;
pub(super) const SECTOR: usize = 4096;
#[derive(Clone, Copy)]
pub(super) enum Fault {
    Erase(usize),
    Program,
    Readback,
}
struct Flash {
    bytes: Vec<u8>,
    fault: Option<Fault>,
    calls: usize,
}
std::thread_local! {
    static FLASH: RefCell<Flash> = RefCell::new(Flash {
        bytes: vec![255; 2 * SECTOR], fault: None, calls: 0,
    });
}
pub(super) struct ResetGuard;
impl Drop for ResetGuard {
    fn drop(&mut self) {
        super::super::storage::reset_freeze_for_test();
    }
}
pub(super) fn reset() -> ResetGuard {
    super::super::storage::reset_freeze_for_test();
    FLASH.with(|f| {
        *f.borrow_mut() = Flash {
            bytes: vec![255; 2 * SECTOR],
            fault: None,
            calls: 0,
        }
    });
    ResetGuard
}
pub(super) fn fault(fault: Fault) {
    FLASH.with(|f| f.borrow_mut().fault = Some(fault));
}
pub(super) fn image() -> Vec<u8> {
    FLASH.with(|f| f.borrow().bytes.clone())
}
pub(super) fn calls() -> usize {
    FLASH.with(|f| f.borrow().calls)
}
pub(super) fn fill_primary(slot: &[u8]) {
    FLASH.with(|f| {
        for bytes in f.borrow_mut().bytes[..SECTOR].chunks_exact_mut(8) {
            bytes.copy_from_slice(slot);
        }
    });
}
pub(super) fn journal_area() -> Option<(usize, usize)> {
    Some((BASE, SECTOR))
}
pub(super) fn logical_page_size() -> usize {
    256
}
pub(super) fn read_journal(address: usize, len: usize) -> Option<&'static [u8]> {
    let offset = address.checked_sub(BASE)?;
    FLASH.with(|f| {
        let f = f.borrow();
        let bytes = f.bytes.get(offset..offset.checked_add(len)?)?;
        // Snapshot reads avoid aliasing mutable simulated flash. Test-only leak.
        Some(&*std::boxed::Box::leak(bytes.to_vec().into_boxed_slice()))
    })
}
pub(super) fn program_page(address: usize, bytes: &[u8]) -> FlashResult<()> {
    FLASH.with(|f| {
        let mut f = f.borrow_mut();
        f.calls += 1;
        match f.fault {
            Some(Fault::Program) => {
                f.fault = None;
                return Err(FlashError::VerifyFailed);
            }
            Some(Fault::Readback) => {
                f.fault = None;
                return Ok(()); // Exercise the journal's additional readback check.
            }
            _ => {}
        }
        let offset = address - BASE;
        for (old, new) in f.bytes[offset..offset + bytes.len()].iter_mut().zip(bytes) {
            assert_eq!(*old & *new, *new);
            *old = *new;
        }
        Ok(())
    })
}
pub(super) fn erase_sector(address: usize) -> FlashResult<()> {
    FLASH.with(|f| {
        let mut f = f.borrow_mut();
        f.calls += 1;
        if matches!(f.fault, Some(Fault::Erase(a)) if a == address) {
            f.fault = None;
            return Err(FlashError::VerifyFailed); // Completed error, no physical effect.
        }
        f.bytes[address - BASE..address - BASE + SECTOR].fill(255);
        Ok(())
    })
}
