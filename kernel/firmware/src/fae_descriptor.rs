//! Validate untrusted ABI words without constructing Rust function pointers.
#![forbid(unsafe_code)]

use core::num::NonZeroUsize;
use oxi_core::core::isolation::AppMemoryWindow;

/// A kernel-owned snapshot, valid only while its owning loaded image lives.
/// No reference into writable Rustlet descriptor storage survives validation.
pub(super) struct Descriptor {
    pub state: NonZeroUsize,
    pub install: usize,
    pub process: usize,
    pub sddispatch: usize,
    pub heap: AppMemoryWindow,
}

pub(super) fn contains(window: AppMemoryWindow, address: usize, len: usize) -> bool {
    match (
        window.start.checked_add(window.len),
        address.checked_add(len),
    ) {
        (Some(limit), Some(end)) => address >= window.start && end <= limit,
        _ => false,
    }
}

fn overlaps(a: AppMemoryWindow, start: usize, len: usize) -> bool {
    // Both spans have already passed contains(), including overflow checks.
    a.start < start + len && start < a.start + a.len
}

/// The reader is called only for aligned words wholly within `data`.
pub(super) fn read(
    data: AppMemoryWindow,
    code: AppMemoryWindow,
    security_domain: bool,
    address: usize,
    mut word: impl FnMut(usize) -> Option<usize>,
) -> Option<Descriptor> {
    let size = core::mem::size_of::<usize>();
    let valid_span = |address: usize, words: usize| {
        address != 0 && address.is_multiple_of(size) && contains(data, address, words * size)
    };
    if !valid_span(address, 5) {
        return None;
    }
    let state = NonZeroUsize::new(word(address)?)?;
    let vtable = word(address + size)?;
    let sd_vtable = word(address + 2 * size)?;
    let heap = AppMemoryWindow {
        start: word(address + 3 * size)?,
        len: word(address + 4 * size)?,
    };
    if !valid_span(state.get(), 1)
        || !valid_span(vtable, 2)
        || (sd_vtable != 0) != security_domain
        || (sd_vtable != 0 && !valid_span(sd_vtable, 1))
        || heap.len == 0
        || !heap
            .start
            .is_multiple_of(oxi_core::core::ALLOCATION_GRANULE)
        || !heap.len.is_multiple_of(oxi_core::core::ALLOCATION_GRANULE)
        || !contains(data, heap.start, heap.len)
        || overlaps(heap, address, 5 * size)
        || overlaps(heap, state.get(), size)
        || overlaps(heap, vtable, 2 * size)
        || (sd_vtable != 0 && overlaps(heap, sd_vtable, size))
    {
        return None;
    }
    let install = word(vtable)?;
    let process = word(vtable + size)?;
    let sddispatch = if sd_vtable == 0 { 0 } else { word(sd_vtable)? };
    let valid_handler = |pc: usize| pc & 1 == 1 && contains(code, pc & !1, 2);
    if !valid_handler(install)
        || !valid_handler(process)
        || (security_domain && !valid_handler(sddispatch))
    {
        return None;
    }
    Some(Descriptor {
        state,
        install,
        process,
        sddispatch,
        heap,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> ([usize; 16], AppMemoryWindow, AppMemoryWindow) {
        let mut words = [0; 16];
        let size = core::mem::size_of::<usize>();
        words[..5].copy_from_slice(&[0x1000 + 8 * size, 0x1000 + 5 * size, 0, 0x1100, 256]);
        words[5] = 0x2001;
        words[6] = 0x2021;
        (
            words,
            AppMemoryWindow {
                start: 0x1000,
                len: 512,
            },
            AppMemoryWindow {
                start: 0x2000,
                len: 64,
            },
        )
    }

    #[test]
    fn snapshot_retains_checked_words_after_descriptor_changes() {
        let (mut words, data, code) = fixture();
        let snapshot = read(data, code, false, 0x1000, |address| {
            words
                .get((address - 0x1000) / core::mem::size_of::<usize>())
                .copied()
        })
        .unwrap();
        words[5] = 0;
        assert_ne!(snapshot.install, words[5]);
        assert_eq!(snapshot.install, 0x2001);
        assert_eq!(snapshot.sddispatch, 0);
    }

    #[test]
    fn malformed_descriptors_are_rejected_before_invalid_reads() {
        let (words, data, code) = fixture();
        for address in [0, 0x1001, 0x11f8, usize::MAX] {
            assert!(read(data, code, false, address, |_| panic!("invalid span read")).is_none());
        }
        for (slot, value) in [
            (0, 0),
            (0, 0x1001),
            (1, 0x1001),
            (1, 0x1200),
            (2, 0x1040),
            (3, 0x1000),
            (4, usize::MAX),
            (5, 0),
            (5, 0x2000),
            (5, 0x2041),
            (6, 0x1fff),
        ] {
            let mut malformed = words;
            malformed[slot] = value;
            assert!(
                read(data, code, false, 0x1000, |address| malformed
                    .get((address - 0x1000) / core::mem::size_of::<usize>())
                    .copied())
                .is_none(),
                "slot {slot}, value {value:x}"
            );
        }
    }

    #[test]
    fn security_domain_requires_its_own_valid_handler() {
        let (mut words, data, code) = fixture();
        let size = core::mem::size_of::<usize>();
        words[2] = 0x1000 + 7 * size;
        words[7] = 0x2031;
        assert!(read(data, code, true, 0x1000, |address| words
            .get((address - 0x1000) / size)
            .copied())
        .is_some());
        words[7] = 0;
        assert!(read(data, code, true, 0x1000, |address| words
            .get((address - 0x1000) / size)
            .copied())
        .is_none());
    }
}
