//! Borrowed access to the suspended Rustlet's syscall memory.
//!
//! Range checks precede every raw access. Simultaneous outputs are disjoint
//! from each other and from inputs; all returned borrows are tied to one
//! exclusive memory scope. Cipher staging uses memmove before creating a
//! reference, so in-place and partially overlapping buffers remain supported.
#![deny(unsafe_op_in_unsafe_fn)]

use super::ActiveAppCall;
use core::{mem, ptr, slice};
use oxi_core::core::isolation::AppMemoryWindow;
use rustlet_runtime::{
    CryptoCipherDoFinalParams, CryptoEcGenerateKeypairParams, CryptoEcdhDoFinalParams,
    CryptoHkdfSha256Params, CryptoMacDoFinalParams, CryptoRandomGenerateParams,
    CryptoX963Sha256Params, Scp03LoadKeyParams,
};

/// ABI records that can be copied from untrusted, initialized memory.
///
/// # Safety
/// Every initialized field bit pattern must be valid. Fields must contain no
/// references, owned resources, enums with invalid discriminants, or booleans.
/// Padding may be uninitialized; it must not be inspected as bytes.
pub(super) unsafe trait Params: Copy {
    /// Semantic constraints common to the record, before any service side effect.
    fn valid_reserved_fields(&self) -> bool {
        true
    }
}

// SAFETY: these repr(C) records contain only integers and raw pointers. Their
// discriminants are integer fields decoded by the syscall, never Rust enums.
unsafe impl Params for CryptoCipherDoFinalParams {}
unsafe impl Params for CryptoRandomGenerateParams {}
unsafe impl Params for CryptoMacDoFinalParams {}
unsafe impl Params for Scp03LoadKeyParams {
    fn valid_reserved_fields(&self) -> bool {
        self.reserved == 0
    }
}
unsafe impl Params for CryptoEcGenerateKeypairParams {
    fn valid_reserved_fields(&self) -> bool {
        self.reserved0 == 0 && self.reserved1 == 0 && self.reserved2 == 0
    }
}
unsafe impl Params for CryptoEcdhDoFinalParams {
    fn valid_reserved_fields(&self) -> bool {
        self.reserved0 == 0 && self.reserved1 == 0 && self.reserved2 == 0
    }
}
unsafe impl Params for CryptoHkdfSha256Params {}
unsafe impl Params for CryptoX963Sha256Params {}

type Buffers<'a, const R: usize, const W: usize> = ([&'a [u8]; R], [&'a mut [u8]; W]);

pub(super) struct Memory<'a> {
    call: &'a mut ActiveAppCall,
}

impl<'a> Memory<'a> {
    /// Borrows memory for one synchronous syscall on the kernel owner core.
    ///
    /// # Safety
    /// The call's windows must describe live, initialized Rustlet memory, with
    /// writable RAM in shared/data/stack and readable storage in text. Each
    /// window must fit within a backing allocation. The Rustlet must remain
    /// suspended, with no concurrent hardware writer or competing kernel
    /// reference to those bytes for this scope. Construct only one scope at a
    /// time, and do not reenter the Rustlet while it is borrowed.
    unsafe fn new(call: &'a mut ActiveAppCall) -> Self {
        Self { call }
    }

    /// Open a request only after its complete ABI record has been validated.
    /// Payloads remain borrowed in place; only the small record is snapshotted.
    ///
    /// # Safety
    /// The caller must satisfy the same suspended-memory contract as `new`.
    #[inline(always)]
    pub(super) unsafe fn request<T: Params>(
        call: &'a mut ActiveAppCall,
        address: usize,
    ) -> Option<(Self, T)> {
        // SAFETY: the request caller supplies the scoped memory ownership.
        let memory = unsafe { Self::new(call) };
        let params = memory.params(address)?;
        Some((memory, params))
    }

    #[inline(always)]
    fn params<T: Params>(&self, addr: usize) -> Option<T> {
        if addr == 0
            || !addr.is_multiple_of(mem::align_of::<T>())
            || !self.readable(addr, mem::size_of::<T>())
        {
            return None;
        }
        // SAFETY: checked aligned, initialized, readable storage. Params
        // restricts values to ABI records accepting arbitrary field bits.
        let params = unsafe { ptr::read(addr as *const T) };
        params.valid_reserved_fields().then_some(params)
    }

    pub(super) fn read(&self, address: *const u8, len: usize) -> Option<&[u8]> {
        if !self.readable(address as usize, len) {
            return None;
        }
        // SAFETY: the range belongs to the suspended Rustlet. The shared
        // scope borrow prevents any writable view from coexisting with it.
        Some(unsafe { read_slice(address, len) })
    }

    pub(super) fn write(&mut self, address: *mut u8, len: usize) -> Option<&mut [u8]> {
        if !self.writable(address as usize, len) {
            return None;
        }
        // SAFETY: validated writable storage and exclusive scope borrow.
        Some(unsafe { write_slice(address, len) })
    }

    /// Borrows two disjoint outputs without an intermediate descriptor array.
    #[inline(always)]
    pub(super) fn write_pair(
        &mut self,
        first: (*mut u8, usize),
        second: (*mut u8, usize),
    ) -> Option<(&mut [u8], &mut [u8])> {
        if !self.writable(first.0 as usize, first.1)
            || !self.writable(second.0 as usize, second.1)
            || overlaps(first.0 as usize, first.1, second.0 as usize, second.1)
        {
            return None;
        }
        // SAFETY: both writable ranges are valid and disjoint, and the scope
        // stays exclusively borrowed until both output views are released.
        Some(unsafe {
            (
                write_slice(first.0, first.1),
                write_slice(second.0, second.1),
            )
        })
    }

    /// Borrows the two inputs and output used by ECDH and X9.63 directly.
    #[inline(always)]
    pub(super) fn read_pair_write(
        &mut self,
        first: (*const u8, usize),
        second: (*const u8, usize),
        output: (*mut u8, usize),
    ) -> Option<(&[u8], &[u8], &mut [u8])> {
        if !self.readable(first.0 as usize, first.1)
            || !self.readable(second.0 as usize, second.1)
            || !self.writable(output.0 as usize, output.1)
            || overlaps(first.0 as usize, first.1, output.0 as usize, output.1)
            || overlaps(second.0 as usize, second.1, output.0 as usize, output.1)
        {
            return None;
        }
        // SAFETY: validated readable inputs and writable output; neither input
        // overlaps output. The views retain the exclusive scope borrow.
        Some(unsafe {
            (
                read_slice(first.0, first.1),
                read_slice(second.0, second.1),
                write_slice(output.0, output.1),
            )
        })
    }

    /// Validates all simultaneous buffers before creating any references.
    pub(super) fn buffers<const R: usize, const W: usize>(
        &mut self,
        reads: [(*const u8, usize); R],
        writes: [(*mut u8, usize); W],
    ) -> Option<Buffers<'_, R, W>> {
        for &(address, len) in &reads {
            if !self.readable(address as usize, len) {
                return None;
            }
        }
        for (index, &(address, len)) in writes.iter().enumerate() {
            if !self.writable(address as usize, len)
                || reads
                    .iter()
                    .any(|&(other, count)| overlaps(address as usize, len, other as usize, count))
                || writes[..index]
                    .iter()
                    .any(|&(other, count)| overlaps(address as usize, len, other as usize, count))
            {
                return None;
            }
        }
        // SAFETY: all ranges are valid and no nonempty output overlaps any
        // other view. Returned lifetimes retain the exclusive scope borrow.
        Some(unsafe {
            (
                reads.map(|(address, len)| read_slice(address, len)),
                writes.map(|(address, len)| write_slice(address, len)),
            )
        })
    }

    /// Stages input in output, then lends output alone. No scratch allocation.
    pub(super) fn copy_to_output(
        &mut self,
        input: *const u8,
        input_len: usize,
        output: *mut u8,
        output_capacity: usize,
    ) -> Option<&mut [u8]> {
        if input_len > output_capacity
            || !self.readable(input as usize, input_len)
            || !self.writable(output as usize, output_capacity)
        {
            return None;
        }
        if input_len != 0 && !ptr::eq(input, output) {
            // SAFETY: both ranges validated, no live slices, overlap allowed.
            unsafe { ptr::copy(input, output, input_len) };
        }
        // SAFETY: the raw copy has finished; only output is now borrowed.
        Some(unsafe { write_slice(output, output_capacity) })
    }

    #[inline(always)]
    fn readable(&self, addr: usize, len: usize) -> bool {
        contains(self.call.text_window, addr, len) || self.writable(addr, len)
    }

    #[inline(always)]
    fn writable(&self, addr: usize, len: usize) -> bool {
        contains(self.call.shared_window, addr, len)
            || contains(self.call.data_window, addr, len)
            || contains(self.call.stack_window, addr, len)
    }
}

#[inline(always)]
fn contains(window: AppMemoryWindow, addr: usize, len: usize) -> bool {
    // Empty ABI buffers need no backing memory: slice constructors below
    // canonicalize them rather than constructing a slice from an untrusted ptr.
    if len == 0 {
        return true;
    }
    if addr == 0 || len > isize::MAX as usize {
        return false;
    }
    match (addr.checked_add(len), window.start.checked_add(window.len)) {
        (Some(end), Some(window_end)) => addr >= window.start && end <= window_end,
        _ => false,
    }
}

#[inline(always)]
fn overlaps(a: usize, a_len: usize, b: usize, b_len: usize) -> bool {
    // Subtraction avoids wrap even when the second range is not validated yet.
    a_len != 0 && b_len != 0 && if a <= b { b - a < a_len } else { a - b < b_len }
}

unsafe fn read_slice<'a>(address: *const u8, len: usize) -> &'a [u8] {
    if len == 0 {
        &[]
    } else {
        // SAFETY: callers validate memory and bind the returned borrow to scope.
        unsafe { slice::from_raw_parts(address, len) }
    }
}

unsafe fn write_slice<'a>(address: *mut u8, len: usize) -> &'a mut [u8] {
    if len == 0 {
        &mut []
    } else {
        // SAFETY: callers also establish exclusivity before using this helper.
        unsafe { slice::from_raw_parts_mut(address, len) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(window: AppMemoryWindow) -> ActiveAppCall {
        let empty = AppMemoryWindow { start: 0, len: 0 };
        ActiveAppCall {
            transport: ptr::null_mut(),
            shared_buffer: ptr::null_mut(),
            text_window: empty,
            shared_window: empty,
            data_window: window,
            stack_window: empty,
        }
    }

    fn record_bounds<T: Params>() {
        // SAFETY: Params permits all initialized field bit patterns, including zero.
        let record: T = unsafe { mem::zeroed() };
        let address = &record as *const T as usize;
        let size = mem::size_of::<T>();
        let mut call = call(AppMemoryWindow {
            start: address,
            len: size,
        });
        // SAFETY: the only window is the live record, exclusively scoped here.
        let memory = unsafe { Memory::new(&mut call) };
        assert!(memory.params::<T>(address).is_some());
        for bad in [
            0,
            address + 1,
            address + mem::align_of::<T>(),
            usize::MAX & !(mem::align_of::<T>() - 1),
        ] {
            assert!(memory.params::<T>(bad).is_none());
        }
        for len in 0..size {
            call.data_window.len = len;
            // SAFETY: the shortened window remains inside the same live record.
            assert!(unsafe { Memory::request::<T>(&mut call, address) }.is_none());
        }
    }

    #[test]
    fn every_abi_record_requires_complete_aligned_storage() {
        record_bounds::<CryptoCipherDoFinalParams>();
        record_bounds::<CryptoRandomGenerateParams>();
        record_bounds::<CryptoMacDoFinalParams>();
        record_bounds::<Scp03LoadKeyParams>();
        record_bounds::<CryptoEcGenerateKeypairParams>();
        record_bounds::<CryptoEcdhDoFinalParams>();
        record_bounds::<CryptoHkdfSha256Params>();
        record_bounds::<CryptoX963Sha256Params>();
    }

    #[test]
    fn output_may_replace_its_snapshotted_parameter_record() {
        let mut storage = [0usize; 8];
        let base = storage.as_mut_ptr().cast::<u8>();
        let size = mem::size_of::<CryptoRandomGenerateParams>();
        let record = CryptoRandomGenerateParams {
            algorithm: 1,
            output_ptr: base,
            output_len: size,
        };
        // SAFETY: usize storage supplies sufficient size/alignment; the record
        // contains no resources and no references to this storage are retained.
        unsafe { base.cast::<CryptoRandomGenerateParams>().write(record) };
        let mut call = call(AppMemoryWindow {
            start: base as usize,
            len: size,
        });
        // SAFETY: the initialized record is exclusively lent until this scope ends.
        let (mut memory, params) =
            unsafe { Memory::request::<CryptoRandomGenerateParams>(&mut call, base as usize) }
                .unwrap();
        memory
            .write(params.output_ptr, params.output_len)
            .unwrap()
            .fill(0x5a);
        assert_eq!(params.algorithm, 1);
        assert_eq!(params.output_ptr, base);
        assert_eq!(params.output_len, size);
        assert!(storage[..size / mem::size_of::<usize>()]
            .iter()
            .all(|word| *word == usize::from_ne_bytes([0x5a; mem::size_of::<usize>()])));
        assert!(storage[size / mem::size_of::<usize>()..]
            .iter()
            .all(|word| *word == 0));
    }

    #[test]
    fn reserved_bytes_are_rejected_for_every_nonzero_value() {
        for value in 1..=u8::MAX {
            // SAFETY: these ABI records contain only integers and raw pointers.
            let mut key: Scp03LoadKeyParams = unsafe { mem::zeroed() };
            key.reserved = value;
            assert!(!key.valid_reserved_fields());
            for slot in 0..3 {
                // SAFETY: these ABI records accept zero field bit patterns.
                let mut ec: CryptoEcGenerateKeypairParams = unsafe { mem::zeroed() };
                let mut dh: CryptoEcdhDoFinalParams = unsafe { mem::zeroed() };
                match slot {
                    0 => {
                        ec.reserved0 = value;
                        dh.reserved0 = value;
                    }
                    1 => {
                        ec.reserved1 = value;
                        dh.reserved1 = value;
                    }
                    _ => {
                        ec.reserved2 = value;
                        dh.reserved2 = value;
                    }
                }
                assert!(!ec.valid_reserved_fields());
                assert!(!dh.valid_reserved_fields());
            }
        }
    }

    #[test]
    fn bounds_reject_overflow_null_nonempty_and_excessive_slice_lengths() {
        let window = AppMemoryWindow { start: 16, len: 32 };
        assert!(contains(window, 16, 32));
        assert!(!contains(window, 15, 1));
        assert!(!contains(window, 47, 2));
        assert!(!contains(window, usize::MAX, 2));
        assert!(!contains(window, 0, 1));
        assert!(!contains(window, 16, isize::MAX as usize + 1));
        assert!(!contains(
            AppMemoryWindow {
                start: usize::MAX - 8,
                len: 16
            },
            usize::MAX - 4,
            1
        ));
    }

    #[test]
    fn empty_buffers_are_canonicalized_without_dereferencing_their_address() {
        let mut call = call(AppMemoryWindow { start: 0, len: 0 });
        // SAFETY: the scope has no nonempty windows and no memory is accessed.
        let mut memory = unsafe { Memory::new(&mut call) };
        assert_eq!(memory.read(ptr::null(), 0), Some(&[][..]));
        assert_eq!(memory.write(usize::MAX as *mut u8, 0), Some(&mut [][..]));
        assert!(memory
            .buffers([(ptr::null(), 0)], [(ptr::null_mut(), 0); 2])
            .is_some());
        assert!(memory
            .copy_to_output(ptr::null(), 0, ptr::null_mut(), 0)
            .is_some());
        assert!(memory.params::<CryptoRandomGenerateParams>(0).is_none());
    }

    #[test]
    fn parameters_require_alignment_and_a_complete_record() {
        let params = CryptoRandomGenerateParams {
            algorithm: 255,
            output_ptr: ptr::null_mut(),
            output_len: usize::MAX,
        };
        let address = &params as *const _ as usize;
        let mut call = call(AppMemoryWindow {
            start: address,
            len: mem::size_of_val(&params),
        });
        // Treat the record as read-only, just as parameters can reside in XIP.
        call.text_window = call.data_window;
        call.data_window.len = 0;
        // SAFETY: the text window is the live, initialized params value.
        let memory = unsafe { Memory::new(&mut call) };
        let read = memory
            .params::<CryptoRandomGenerateParams>(address)
            .unwrap();
        assert_eq!(read.algorithm, 255); // discriminants stay integers until decoded
        assert!(memory
            .params::<CryptoRandomGenerateParams>(address + 1)
            .is_none());
        assert!(memory
            .params::<CryptoRandomGenerateParams>(address + mem::align_of_val(&params))
            .is_none());
    }

    #[test]
    fn overlapping_outputs_and_read_write_aliases_are_rejected_before_mutation() {
        let mut data = [0xA5; 64];
        let base = data.as_mut_ptr();
        let mut call = call(AppMemoryWindow {
            start: base as usize,
            len: data.len(),
        });
        // SAFETY: data is exclusively lent for the scope; no other access occurs.
        let mut memory = unsafe { Memory::new(&mut call) };
        let middle = base.wrapping_add(16);
        assert!(memory.buffers([], [(base, 32), (middle, 32)]).is_none());
        assert!(memory
            .buffers([(base.cast_const(), 32)], [(middle, 16)])
            .is_none());
        assert!(memory
            .buffers([(middle.cast_const(), 16)], [(base, 32)])
            .is_none());
        assert!(memory
            .buffers([(base.cast_const(), 64)], [(base, 64)])
            .is_none());
        assert!(memory.write_pair((base, 32), (middle, 32)).is_none());
        assert!(memory
            .read_pair_write((base, 32), (middle, 16), (middle, 16))
            .is_none());
        assert!(memory
            .read_pair_write((middle, 16), (base, 32), (base, 16))
            .is_none());
        assert!(memory
            .read_pair_write((ptr::null(), 1), (base, 8), (middle, 8))
            .is_none());
        assert!(memory
            .read_pair_write((base, 8), (base, 8), (ptr::null_mut(), 1))
            .is_none());
        let (first, second) = memory.write_pair((base, 16), (middle, 16)).unwrap();
        second.copy_from_slice(first);
        let (first, second, output) = memory
            .read_pair_write((base, 8), (base, 8), (middle, 8))
            .unwrap();
        assert_eq!(first, second);
        output.copy_from_slice(first);
        let ([input], [output]) = memory
            .buffers([(base.cast_const(), 16)], [(middle, 16)])
            .unwrap();
        output.copy_from_slice(input);
        assert_eq!(data, [0xA5; 64]);
    }

    #[test]
    fn text_is_read_only_and_inputs_may_share_bytes() {
        let mut data = [9; 32];
        let base = data.as_mut_ptr();
        let mut call = call(AppMemoryWindow {
            start: base as usize,
            len: data.len(),
        });
        call.text_window = call.data_window;
        call.data_window.len = 0;
        // SAFETY: the text window is backed by the initialized data array.
        let mut memory = unsafe { Memory::new(&mut call) };
        assert!(memory.write(base, 1).is_none());
        let ([a, b], []) = memory.buffers([(base.cast_const(), 16); 2], []).unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn cipher_staging_supports_both_overlap_directions_and_identity() {
        for (src, dst) in [(0, 4), (4, 0), (0, 0)] {
            let mut data = core::array::from_fn::<_, 32, _>(|index| index as u8);
            let expected = data[src..src + 16].to_vec();
            let base = data.as_mut_ptr();
            let mut call = call(AppMemoryWindow {
                start: base as usize,
                len: data.len(),
            });
            // SAFETY: data belongs solely to this scope until output is released.
            let mut memory = unsafe { Memory::new(&mut call) };
            let output = memory
                .copy_to_output(base.wrapping_add(src), 16, base.wrapping_add(dst), 20)
                .unwrap();
            assert_eq!(&output[..16], expected);
        }
    }

    #[test]
    fn invalid_cipher_ranges_leave_output_untouched() {
        let mut data = [7; 32];
        let base = data.as_mut_ptr();
        let mut call = call(AppMemoryWindow {
            start: base as usize,
            len: data.len(),
        });
        // SAFETY: data belongs solely to this scope.
        let mut memory = unsafe { Memory::new(&mut call) };
        assert!(memory.copy_to_output(base, 17, base, 16).is_none());
        assert!(memory.copy_to_output(ptr::null(), 16, base, 16).is_none());
        assert!(memory
            .copy_to_output(base, 16, base.wrapping_add(24), 16)
            .is_none());
        assert_eq!(data, [7; 32]);
    }
}
