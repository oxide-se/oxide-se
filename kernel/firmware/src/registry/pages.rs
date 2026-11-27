//! One nibble per page: ownership (0 free, 1 base, 2..7 scopes) and validation.
use super::format::{PersistentRange, Protection};
use super::objects::{RegistryError, RegistryResult};
use crate::kernel_cell::KernelCell;
const MAX_PAGES: usize = 1024;
pub(crate) const MASK_BYTES: usize = MAX_PAGES / 8;
const VALID: u8 = 8;
struct Table {
    bytes: [u8; MAX_PAGES / 2],
    page_size: usize,
    depth: u8,
    owned_scopes: u8,
    collection_needed: bool,
}
pub(crate) struct Pages {
    table: KernelCell<Table>,
}
impl Table {
    fn get(&self, i: usize) -> u8 {
        (self.bytes[i / 2] >> ((i % 2) * 4)) & 15
    }
    fn set(&mut self, i: usize, v: u8) {
        let shift = (i % 2) * 4;
        self.bytes[i / 2] = (self.bytes[i / 2] & !(15 << shift)) | (v << shift);
    }
    fn range(&self, r: PersistentRange) -> RegistryResult<core::ops::Range<usize>> {
        if self.page_size == 0 {
            return Err(RegistryError::Persistence);
        }
        let end = r
            .offset
            .checked_add(r.total_len)
            .ok_or(RegistryError::Persistence)?
            .div_ceil(self.page_size);
        if end > MAX_PAGES {
            return Err(RegistryError::Capacity);
        }
        Ok(r.offset / self.page_size..end)
    }
}
impl Pages {
    pub(crate) const fn new() -> Self {
        // SAFETY: privileged owner core, no IRQ access; each operation takes a
        // short checked loan. Flash callbacks can invalidate between operations.
        Self {
            table: unsafe {
                KernelCell::new(Table {
                    bytes: [0; MAX_PAGES / 2],
                    page_size: 0,
                    depth: 0,
                    owned_scopes: 0,
                    collection_needed: false,
                })
            },
        }
    }
    pub(crate) fn reset(&self, page_size: usize, area_len: usize) -> RegistryResult {
        if page_size == 0 || area_len / page_size > MAX_PAGES || !area_len.is_multiple_of(page_size)
        {
            return Err(RegistryError::Capacity);
        }
        let mut t = self.table.borrow_mut();
        t.bytes.fill(0);
        t.page_size = page_size;
        t.owned_scopes = 0;
        t.collection_needed = false;
        Ok(())
    }
    pub(crate) fn invalidate(&self) {
        self.table.borrow_mut().page_size = 0;
    }
    pub(crate) fn initialized(&self) -> bool {
        self.table.borrow().page_size != 0
    }
    pub(crate) fn collection_needed(&self) -> bool {
        self.table.borrow().collection_needed
    }
    pub(crate) fn changed(&self) {
        self.table.borrow_mut().collection_needed = true;
    }
    pub(crate) fn set_depth(&self, depth: usize) {
        assert!(depth <= 6);
        self.table.borrow_mut().depth = depth as u8;
    }
    pub(crate) fn reserve(&self, range: PersistentRange) -> RegistryResult {
        let mut t = self.table.borrow_mut();
        let owner = t.depth + 1;
        for i in t.range(range)? {
            if t.get(i) & 7 != 0 {
                return Err(RegistryError::InvalidState);
            }
        }
        for i in t.range(range)? {
            t.set(i, owner);
        }
        t.owned_scopes |= 1 << t.depth;
        t.collection_needed = true;
        Ok(())
    }
    /// Recovery/explicit long-lived reservation, preserving validation.
    pub(crate) fn retain(&self, range: PersistentRange) -> RegistryResult {
        self.rehome(range, 0)
    }
    pub(crate) fn rehome(&self, range: PersistentRange, depth: usize) -> RegistryResult {
        if depth > 6 {
            return Err(RegistryError::Capacity);
        }
        let mut t = self.table.borrow_mut();
        for i in t.range(range)? {
            let auth = t.get(i) & VALID;
            t.set(i, auth | (depth as u8 + 1));
        }
        t.owned_scopes |= 1 << depth;
        Ok(())
    }
    pub(crate) fn release(&self, range: PersistentRange) -> RegistryResult {
        let mut t = self.table.borrow_mut();
        for i in t.range(range)? {
            t.set(i, 0);
        }
        Ok(())
    }
    pub(crate) fn finish_scope(&self, depth: usize, accept: bool) {
        assert!((1..=6).contains(&depth));
        let mut t = self.table.borrow_mut();
        // Conservative summary: false positives cost a scan; no owned page may
        // be missed. Rehoming/releasing may leave a stale bit until scope exit.
        let bit = 1 << depth;
        if t.owned_scopes & bit == 0 {
            t.depth = depth as u8 - 1;
            return;
        }
        t.owned_scopes &= !bit;
        if accept {
            t.owned_scopes |= 1 << (depth - 1);
        }
        for i in 0..MAX_PAGES {
            let value = t.get(i);
            if value & 7 == depth as u8 + 1 {
                t.set(
                    i,
                    if accept {
                        (value & VALID) | depth as u8
                    } else {
                        0
                    },
                );
            }
        }
        t.depth = depth as u8 - 1;
    }
    /// Apply only after the whole live mask has been constructed successfully.
    pub(crate) fn collect(&self, live: &[u8]) {
        assert!(live.len() >= MASK_BYTES);
        let mut t = self.table.borrow_mut();
        for i in 0..MAX_PAGES {
            let auth = t.get(i) & VALID;
            t.set(
                i,
                if live[i / 8] & (1 << (i % 8)) != 0 {
                    auth | 1
                } else {
                    0
                },
            );
        }
        t.collection_needed = false;
        t.owned_scopes = 0;
    }
    pub(crate) fn authenticated(&self, index: usize) -> bool {
        index < MAX_PAGES && self.table.borrow().get(index) & VALID != 0
    }
    pub(crate) fn authenticate(&self, index: usize) {
        if index >= MAX_PAGES {
            return;
        }
        let mut t = self.table.borrow_mut();
        let value = t.get(index);
        // Free candidates may be checked but are not cached.
        if value & 7 != 0 {
            t.set(index, value | VALID);
        }
    }
    pub(crate) fn invalidate_auth(
        &self,
        page: usize,
        start: usize,
        end: usize,
        mut length: impl FnMut(usize) -> Option<usize>,
    ) {
        if page == 0 || start >= end {
            return;
        }
        let mut t = self.table.borrow_mut();
        for i in 0..end.div_ceil(page).min(MAX_PAGES) {
            let v = t.get(i);
            if v & VALID == 0 {
                continue;
            }
            let offset = i * page;
            if offset >= start || length(offset).is_none_or(|len| len > start - offset) {
                t.set(i, v & 7);
            }
        }
    }
}
impl Protection for Pages {
    fn overlaps(&self, range: PersistentRange) -> bool {
        let t = self.table.borrow();
        t.range(range)
            .map_or(true, |mut indices| indices.any(|i| t.get(i) & 7 != 0))
    }
}

/// The collection mask lives in the existing payload scratch, not another
/// resident table. Apply it only after every live extent has been marked.
pub(crate) fn update_mask(
    bits: &mut [u8],
    page: usize,
    range: PersistentRange,
    retain: bool,
) -> RegistryResult {
    if page == 0 || bits.len() < MASK_BYTES {
        return Err(RegistryError::Persistence);
    }
    let end = range
        .offset
        .checked_add(range.total_len)
        .ok_or(RegistryError::Persistence)?
        .div_ceil(page);
    if end > MAX_PAGES {
        return Err(RegistryError::Persistence);
    }
    for i in range.offset / page..end {
        if retain {
            bits[i / 8] |= 1 << (i % 8);
        } else {
            bits[i / 8] &= !(1 << (i % 8));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn range(page: usize) -> PersistentRange {
        PersistentRange::new(page * 256, 256)
    }
    #[test]
    fn six_levels_transfer_and_rollback_without_touching_ancestors() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.retain(range(0)).unwrap();
        for depth in 1..=6 {
            pages.set_depth(depth);
            pages.reserve(range(depth)).unwrap();
            pages.authenticate(depth);
        }
        pages.finish_scope(6, true);
        assert_eq!(pages.table.borrow().get(6), 8 | 6);
        pages.finish_scope(5, false);
        for i in 0..5 {
            assert!(pages.overlaps(range(i)));
        }
        for i in 5..7 {
            assert!(!pages.overlaps(range(i)));
            assert!(!pages.authenticated(i));
        }
        for depth in (1..=4).rev() {
            pages.finish_scope(depth, true);
        }
        for i in 1..5 {
            assert_eq!(pages.table.borrow().get(i), 9);
        }
    }
    #[test]
    fn unfinished_reservations_are_never_authenticated() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.set_depth(2);
        pages.reserve(range(3)).unwrap();
        assert!(pages.overlaps(range(3)));
        assert!(!pages.authenticated(3));
        pages.authenticate(4);
        assert!(!pages.authenticated(4)); // free candidate
        pages.authenticate(3);
        assert!(pages.authenticated(3));
        pages.invalidate_auth(256, 768, 1024, |_| Some(256));
        assert!(pages.overlaps(range(3)));
        assert!(!pages.authenticated(3));
    }
    #[test]
    fn body_invalidation_preserves_ownership_and_other_blocks() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.reserve(PersistentRange::new(0, 1280)).unwrap();
        for i in [0, 3, 4] {
            pages.authenticate(i);
        }
        pages.invalidate_auth(256, 500, 520, |offset| {
            Some(if offset == 0 { 768 } else { 256 })
        });
        assert!(!pages.authenticated(0));
        assert!(pages.authenticated(3));
        assert!(pages.authenticated(4));
        for i in 0..5 {
            assert!(pages.overlaps(range(i)));
        }
    }
    #[test]
    fn final_collection_keeps_current_shared_and_pending_pages_only() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.set_depth(1);
        pages.reserve(PersistentRange::new(0, 2048)).unwrap();
        pages.authenticate(2);
        pages.finish_scope(1, true);
        let mut live = [0; MASK_BYTES];
        for i in [0, 2, 6] {
            update_mask(&mut live, 256, range(i), true).unwrap();
        }
        pages.collect(&live);
        for i in 0..8 {
            assert_eq!(pages.overlaps(range(i)), [0, 2, 6].contains(&i));
        }
        assert!(pages.authenticated(2));
    }
    #[test]
    fn shared_prestate_snapshot_and_load_survive_child_rollback() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.set_depth(3);
        pages.reserve(range(1)).unwrap();
        pages.rehome(range(1), 1).unwrap();
        pages.reserve(range(2)).unwrap();
        pages.retain(range(2)).unwrap(); // LOAD
        pages.reserve(range(3)).unwrap();
        pages.finish_scope(3, false);
        assert!(pages.overlaps(range(1)));
        assert!(pages.overlaps(range(2)));
        assert!(!pages.overlaps(range(3)));
        pages.finish_scope(2, false);
        assert!(pages.overlaps(range(1)));
    }
    #[test]
    fn clean_scopes_skip_collection_but_preserve_pending_work() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.retain(range(0)).unwrap();
        pages.set_depth(1);
        pages.set_depth(2);
        pages.authenticate(0); // Cache changes do not change the live graph.
        pages.finish_scope(2, true);
        pages.finish_scope(1, false);
        assert!(!pages.collection_needed());
        assert!(pages.authenticated(0));
        pages.changed(); // Deletion/replacement can obsolete a base-owned block.
        pages.set_depth(1);
        pages.finish_scope(1, true);
        assert!(pages.collection_needed()); // Deferred collection is not forgotten.
        let mut live = [0; MASK_BYTES];
        update_mask(&mut live, 256, range(0), true).unwrap();
        pages.collect(&live);
        assert!(!pages.collection_needed());
    }
    #[test]
    fn child_allocations_transfer_summary_and_failed_reservation_stays_clean() {
        let pages = Pages::new();
        pages.reset(256, 8192).unwrap();
        pages.retain(range(0)).unwrap();
        pages.set_depth(2);
        assert!(pages.reserve(range(0)).is_err());
        assert!(!pages.collection_needed());
        pages.reserve(range(1)).unwrap();
        pages.finish_scope(2, true);
        pages.finish_scope(1, false);
        assert!(!pages.overlaps(range(1)));
        assert!(pages.overlaps(range(0)));
        assert!(pages.collection_needed());
    }
    #[test]
    fn geometry_and_overlapping_reservations_fail_closed() {
        let pages = Pages::new();
        assert!(pages.overlaps(range(0)));
        assert!(pages.reset(0, 256).is_err());
        assert!(pages.reset(256, 1025 * 256).is_err());
        pages.reset(256, 8192).unwrap();
        pages.reserve(range(1)).unwrap();
        assert!(pages.reserve(PersistentRange::new(0, 512)).is_err());
        assert!(!pages.overlaps(range(0))); // rejection has no partial effect
        assert!(pages.overlaps(PersistentRange::new(usize::MAX, 256)));
    }
}
