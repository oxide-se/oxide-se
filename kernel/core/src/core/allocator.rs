use ::core::alloc::{GlobalAlloc, Layout};
use ::core::cell::UnsafeCell;
use ::core::ptr::null_mut;
use ::core::sync::atomic::{AtomicBool, Ordering};

/// # Buddy Allocator with External Bit-Tree (V2: Arbitrary Size Support)
///
/// ### (1) Operating Principle
/// This allocator manages memory using a binary tree represented as a flat bit-table stored **outside**
/// the heap. To support arbitrary heap sizes and alignments:
/// - The physical heap is mapped onto a "virtual" power-of-two space.
/// - The tree is "pruned" at initialization: nodes representing addresses outside the physical
///   storage boundaries are marked as `Unavailable`.
/// - Each node in the tree is represented by 2 bits, encoding 4 states:
///   `00` (Free), `01` (Unavailable), `10` (Partial/Split), `11` (Full/Allocated).
///
/// ### (2) Motivations
/// - **Performance**: Fast power-of-two allocations and coalescing in $O(\log n)$.
/// - **MPU Alignment**: Guaranteed alignment on power-of-two boundaries, essential for MPU region protection.
/// - **Integrity**: Metadata is isolated from the managed heap. User-space memory corruption
///   cannot overwrite the allocator's internal state.
/// - **Flexibility**: Supports non-power-of-two heap sizes through the `Unavailable` state marking.
///
/// ### (3) Constraints & Overhead
/// - **Memory Footprint**: Metadata size is $(4 \times g) / 8$ bytes, where $g$ is the number
///   of granules in the virtual power-of-two space.
/// - **Complexity**: All operations are $O(\log n)$.
pub const ALLOCATION_GRANULE: usize = 8;

#[derive(PartialEq, Copy, Clone)]
#[repr(u8)]
enum NodeState {
    Free = 0b00,
    Unavailable = 0b01,
    Partial = 0b10,
    Full = 0b11,
}

/// Header for the allocator state.
/// All control state lives in kernel-owned memory, protecting it from user-space heap corruption.
#[repr(C)]
pub struct HeapAllocatorState {
    storage_start: *mut u8,
    storage_len: usize,
    virtual_start: *mut u8,
    virtual_len: usize,
    metadata_start: *mut u8,
    metadata_len: usize,
    initialized: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KernelHeapPartition {
    pub metadata_start: usize,
    pub metadata_len: usize,
    pub heap_start: usize,
    pub heap_len: usize,
}

impl HeapAllocatorState {
    pub const fn new() -> Self {
        Self {
            storage_start: null_mut(),
            storage_len: 0,
            virtual_start: null_mut(),
            virtual_len: 0,
            metadata_start: null_mut(),
            metadata_len: 0,
            initialized: false,
        }
    }

    /// Retrieves the 2-bit state of a specific node in the bit-table.
    #[inline]
    fn get_state(&self, node_idx: usize) -> NodeState {
        // Invariant: node_idx * 2 / 8 must be less than metadata_len.
        let bit_pos = node_idx * 2;
        if bit_pos / 8 >= self.metadata_len {
            panic!("allocator metadata read out of bounds");
        }
        // Invariant: reset_heap() installs a valid metadata buffer covering
        // metadata_len bytes before any allocator operation can reach here.
        // SAFETY: initialization owns this metadata; the state borrow bounds access.
        let metadata =
            unsafe { ::core::slice::from_raw_parts(self.metadata_start, self.metadata_len) };
        let byte = metadata[bit_pos / 8];
        match (byte >> (bit_pos % 8)) & 0b11 {
            0b00 => NodeState::Free,
            0b01 => NodeState::Unavailable,
            0b10 => NodeState::Partial,
            _ => NodeState::Full,
        }
    }

    /// Sets the 2-bit state of a specific node in the bit-table.
    #[inline]
    fn set_state(&mut self, node_idx: usize, state: NodeState) {
        let bit_pos = node_idx * 2;
        if bit_pos / 8 >= self.metadata_len {
            panic!("allocator metadata write out of bounds");
        }
        // Invariant: reset_heap() installs a valid metadata buffer covering
        // metadata_len bytes before any allocator operation can reach here.
        // SAFETY: the exclusive state borrow grants exclusive metadata access.
        let metadata =
            unsafe { ::core::slice::from_raw_parts_mut(self.metadata_start, self.metadata_len) };
        let byte = &mut metadata[bit_pos / 8];
        let offset = bit_pos % 8;
        let mask = 0b11 << offset;
        *byte = (*byte & !mask) | ((state as u8) << offset);
    }
}

impl Default for HeapAllocatorState {
    fn default() -> Self {
        Self::new()
    }
}

// --- Internal Helper Functions ---

const fn virtual_len_capacity_for_heap_size(heap_size: usize) -> usize {
    // We over-provision the virtual tree so any granule-aligned physical base
    // can be represented without losing allocator metadata coverage.
    let base = if heap_size <= ALLOCATION_GRANULE {
        ALLOCATION_GRANULE
    } else {
        heap_size.next_power_of_two()
    };
    base * 4
}

pub const fn metadata_size_for_heap_size(heap_size: usize) -> usize {
    let v_size = virtual_len_capacity_for_heap_size(heap_size);
    let granules = v_size / ALLOCATION_GRANULE;
    let total_bits = (2 * granules - 1) * 2;
    total_bits.div_ceil(8)
}

fn exact_metadata_size_for_heap(storage_addr: usize, size: usize) -> Option<usize> {
    if size < ALLOCATION_GRANULE || !size.is_multiple_of(ALLOCATION_GRANULE) {
        return None;
    }

    let mut v_len = if size <= ALLOCATION_GRANULE {
        ALLOCATION_GRANULE
    } else {
        size.checked_next_power_of_two()?
    };
    let mut v_start = align_down(storage_addr, v_len);
    while storage_addr.checked_add(size)? > v_start.checked_add(v_len)? {
        v_len = v_len.checked_mul(2)?;
        v_start = align_down(storage_addr, v_len);
    }

    let granules = v_len / ALLOCATION_GRANULE;
    let total_bits = (2 * granules - 1) * 2;
    Some(total_bits.div_ceil(8))
}

pub fn partition_kernel_heap(free_start: usize, ram_end: usize) -> Option<KernelHeapPartition> {
    let metadata_start = align_up(free_start, ALLOCATION_GRANULE);
    let ram_end = align_down(ram_end, ALLOCATION_GRANULE);
    if metadata_start >= ram_end {
        return None;
    }

    let mut metadata_len = 0usize;
    for _ in 0..32 {
        let heap_start = align_up(
            metadata_start.checked_add(metadata_len)?,
            ALLOCATION_GRANULE,
        );
        if heap_start >= ram_end {
            return None;
        }
        let heap_len = ram_end - heap_start;
        let required_metadata_len = align_up(
            exact_metadata_size_for_heap(heap_start, heap_len)?,
            ALLOCATION_GRANULE,
        );

        if required_metadata_len <= metadata_len {
            return Some(KernelHeapPartition {
                metadata_start,
                metadata_len,
                heap_start,
                heap_len,
            });
        }
        metadata_len = required_metadata_len;
    }

    None
}

const fn align_down(value: usize, align: usize) -> usize {
    value & !(align - 1)
}

const fn align_up(value: usize, align: usize) -> usize {
    (value + align - 1) & !(align - 1)
}

// --- Allocator Implementation ---

struct KernelAllocator;

struct KernelHeapStateCell {
    state: UnsafeCell<HeapAllocatorState>,
    borrowed: AtomicBool,
}

// SAFETY: with_state is the only access to the cell. It admits one borrower,
// refuses reentry, and retains exclusion until the short metadata access ends.
// ARMv6-M runs the kernel on core 0; its IRQ mask replaces unavailable CAS.
unsafe impl Sync for KernelHeapStateCell {}

impl KernelHeapStateCell {
    const fn new() -> Self {
        Self {
            state: UnsafeCell::new(HeapAllocatorState::new()),
            borrowed: AtomicBool::new(false),
        }
    }

    fn with_state<R>(&self, access: impl FnOnce(&mut HeapAllocatorState) -> R) -> Option<R> {
        #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
        let mask = crate::core::target::armv6m_profile::interrupts_save_and_disable();
        #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
        let acquired = {
            let vacant = !self.borrowed.load(Ordering::Relaxed);
            if vacant {
                self.borrowed.store(true, Ordering::Relaxed);
            }
            vacant
        };
        #[cfg(not(all(target_arch = "arm", oxide_se_target_armv6m)))]
        let acquired = self
            .borrowed
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok();
        if !acquired {
            #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
            crate::core::target::armv6m_profile::interrupts_restore(mask);
            return None;
        }
        struct Borrow<'a> {
            flag: &'a AtomicBool,
            #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
            mask: u32,
        }
        impl Drop for Borrow<'_> {
            fn drop(&mut self) {
                self.flag.store(false, Ordering::Release);
                #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
                crate::core::target::armv6m_profile::interrupts_restore(self.mask);
            }
        }
        let _borrow = Borrow {
            flag: &self.borrowed,
            #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
            mask,
        };
        // SAFETY: exclusion was acquired above. The closure cannot return a
        // reference into the state, nor access the private release guard.
        Some(access(unsafe { &mut *self.state.get() }))
    }
}

static KERNEL_HEAP_STATE: KernelHeapStateCell = KernelHeapStateCell::new();

#[cfg(all(not(test), not(feature = "host-test")))]
#[global_allocator]
static ALLOCATOR: KernelAllocator = KernelAllocator;

#[cfg(any(test, feature = "host-test"))]
#[global_allocator]
static ALLOCATOR: std::alloc::System = std::alloc::System;

impl KernelAllocator {
    /// Marks nodes as Unavailable if they are outside physical memory bounds.
    ///
    /// Invariant: node_offset is always relative to virtual_start.
    fn prune_tree(
        &self,
        state: &mut HeapAllocatorState,
        node_idx: usize,
        node_offset: usize,
        node_size: usize,
    ) -> NodeState {
        let node_end = node_offset + node_size;
        let storage_offset = state.storage_start as usize - state.virtual_start as usize;
        let storage_end = storage_offset + state.storage_len;

        // Node is entirely outside the physical storage
        if node_end <= storage_offset || node_offset >= storage_end {
            state.set_state(node_idx, NodeState::Unavailable);
            return NodeState::Unavailable;
        }

        // Node straddles the boundary: recurse if not a leaf
        if node_offset < storage_offset || node_end > storage_end {
            if node_size > ALLOCATION_GRANULE {
                let left = self.prune_tree(state, node_idx * 2 + 1, node_offset, node_size / 2);
                let right = self.prune_tree(
                    state,
                    node_idx * 2 + 2,
                    node_offset + node_size / 2,
                    node_size / 2,
                );

                let s = if left == NodeState::Unavailable && right == NodeState::Unavailable {
                    NodeState::Unavailable
                } else {
                    NodeState::Partial
                };
                state.set_state(node_idx, s);
                return s;
            } else {
                state.set_state(node_idx, NodeState::Unavailable);
                return NodeState::Unavailable;
            }
        }

        // Node is entirely inside
        state.set_state(node_idx, NodeState::Free);
        NodeState::Free
    }

    /// Searches the tree in left-first order using parent indices as the path.
    /// No recursion or auxiliary traversal buffer is needed on MSP.
    fn alloc_node(
        &self,
        state: &mut HeapAllocatorState,
        mut node_idx: usize,
        mut node_offset: usize,
        mut node_size: usize,
        target_size: usize,
    ) -> Option<usize> {
        loop {
            let current = state.get_state(node_idx);
            if current == NodeState::Free && node_size == target_size {
                let candidate = state.virtual_start as usize + node_offset;
                if candidate >= state.storage_start as usize
                    && candidate + target_size <= state.storage_start as usize + state.storage_len
                {
                    state.set_state(node_idx, NodeState::Full);
                    let mut parent = node_idx;
                    while parent != 0 {
                        parent = (parent - 1) / 2;
                        state.set_state(parent, NodeState::Partial);
                    }
                    return Some(node_offset);
                }
            }
            if node_size > target_size && matches!(current, NodeState::Free | NodeState::Partial) {
                let child_size = node_size / 2;
                if current == NodeState::Free {
                    // Splitting must reset stale descendants after coalescing
                    // while retaining any unavailable physical-address holes.
                    self.prune_tree(state, node_idx * 2 + 1, node_offset, child_size);
                    self.prune_tree(
                        state,
                        node_idx * 2 + 2,
                        node_offset + child_size,
                        child_size,
                    );
                }
                node_idx = node_idx * 2 + 1;
                node_size = child_size;
                continue;
            }
            // Ascend exhausted right branches; the first left branch has an
            // unvisited right sibling. Index parity encodes the traversal path.
            while node_idx != 0 && node_idx.is_multiple_of(2) {
                node_idx = (node_idx - 1) / 2;
                node_offset -= node_size;
                node_size *= 2;
            }
            if node_idx == 0 {
                return None;
            }
            node_idx += 1;
            node_offset += node_size;
        }
    }

    /// Validates a live block before changing metadata, then coalesces upwards.
    /// The existing tree proves the rounded block size, not the original Layout.
    /// Iteration keeps adversarial frees bounded without recursive stack growth.
    fn dealloc_node(
        &self,
        state: &mut HeapAllocatorState,
        mut node_idx: usize,
        mut node_size: usize,
        mut target_offset: usize,
        target_size: usize,
    ) -> bool {
        while node_size > target_size {
            if state.get_state(node_idx) != NodeState::Partial {
                return false;
            }
            node_size /= 2;
            node_idx = node_idx * 2 + 1;
            if target_offset >= node_size {
                target_offset -= node_size;
                node_idx += 1;
            }
        }
        if node_size != target_size
            || target_offset != 0
            || state.get_state(node_idx) != NodeState::Full
        {
            return false;
        }
        state.set_state(node_idx, NodeState::Free);
        while node_idx != 0 {
            node_idx = (node_idx - 1) / 2;
            let left = state.get_state(node_idx * 2 + 1);
            let right = state.get_state(node_idx * 2 + 2);
            state.set_state(
                node_idx,
                if left == NodeState::Free && right == NodeState::Free {
                    NodeState::Free
                } else {
                    NodeState::Partial
                },
            );
        }
        true
    }
}

// --- Public Interface ---

/// Initializes the heap state.
///
/// Invariant: `storage` must be aligned to `ALLOCATION_GRANULE`.
/// Invariant: `metadata` must be cleared before calling `prune_tree`.
///
/// # Safety
/// `state`, `storage`, and `metadata` must point to writable, non-overlapping
/// memory ranges owned by the kernel for the complete lifetime of the heap.
// Keep one-time tree initialization out of the loader's persistent frame.
#[inline(never)]
pub unsafe fn reset_heap(
    state: *mut HeapAllocatorState,
    storage: *mut u8,
    size: usize,
    metadata: *mut u8,
    meta_size: usize,
) -> bool {
    if state.is_null() || storage.is_null() || metadata.is_null() {
        return false;
    }
    if size < ALLOCATION_GRANULE || !size.is_multiple_of(ALLOCATION_GRANULE) {
        return false;
    }
    if !(storage as usize).is_multiple_of(ALLOCATION_GRANULE) {
        return false;
    }

    let storage_addr = storage as usize;
    let mut v_len = if size <= ALLOCATION_GRANULE {
        ALLOCATION_GRANULE
    } else {
        size.next_power_of_two()
    };
    let mut v_start = align_down(storage_addr, v_len);
    while storage_addr + size > v_start + v_len {
        v_len *= 2;
        v_start = align_down(storage_addr, v_len);
    }

    // Verify metadata buffer is large enough for the calculated virtual tree
    let granules = v_len / ALLOCATION_GRANULE;
    let total_bits = (2 * granules - 1) * 2;
    let required_metadata_len = total_bits.div_ceil(8);
    if meta_size < required_metadata_len {
        return false;
    }

    // Invariant: null was rejected above and the caller owns this state object.
    let s = unsafe { &mut *state };
    s.storage_start = storage;
    s.storage_len = size;
    s.virtual_start = v_start as *mut u8;
    s.virtual_len = v_len;
    s.metadata_start = metadata;
    s.metadata_len = meta_size;

    // Clear metadata
    // Invariant: null was rejected above and the caller promised meta_size
    // writable bytes of kernel-owned metadata storage.
    unsafe {
        ::core::ptr::write_bytes(metadata, 0, meta_size);
    }

    // Build the pruned tree
    KernelAllocator.prune_tree(s, 0, 0, v_len);

    s.initialized = true;
    true
}

/// Allocates one block from an explicitly supplied heap state.
///
/// # Safety
///
/// `state` must point to a live, exclusively accessible allocator state whose
/// backing storage and metadata remain valid for the complete call.
pub unsafe fn alloc_from_heap(state: *mut HeapAllocatorState, layout: Layout) -> *mut u8 {
    // Invariant: callers pass an allocator state pointer owned by the kernel.
    let Some(s) = (unsafe { state.as_mut() }) else {
        return null_mut();
    };
    alloc_from_heap_state(s, layout)
}

pub(crate) fn alloc_from_heap_state(s: &mut HeapAllocatorState, layout: Layout) -> *mut u8 {
    if !s.initialized {
        return null_mut();
    }

    let Some(size) = allocation_size(layout) else {
        return null_mut();
    };
    if size > s.virtual_len {
        return null_mut();
    }

    match KernelAllocator.alloc_node(s, 0, 0, s.virtual_len, size) {
        Some(offset) => (s.virtual_start as usize + offset) as *mut u8,
        None => null_mut(),
    }
}

/// Returns one allocation to an explicitly supplied heap state.
///
/// # Safety
///
/// `state` must be live and exclusively accessible, with valid backing storage
/// and metadata. No Rust reference into a released block may be used afterwards.
/// Invalid addresses and mismatched rounded block sizes are rejected before any
/// metadata change; this does not prove the original Layout or pointer ownership.
/// Callers at an untrusted boundary must restrict this state to that caller's heap.
pub unsafe fn dealloc_from_heap(
    state: *mut HeapAllocatorState,
    ptr: *mut u8,
    layout: Layout,
) -> bool {
    // Invariant: callers pass an allocator state pointer owned by the kernel.
    let Some(s) = (unsafe { state.as_mut() }) else {
        return false;
    };
    dealloc_from_heap_state(s, ptr, layout)
}

// Keep validation/coalescing temporaries out of long-lived loader frames.
#[inline(never)]
pub(crate) fn dealloc_from_heap_state(
    s: &mut HeapAllocatorState,
    ptr: *mut u8,
    layout: Layout,
) -> bool {
    if !s.initialized || ptr.is_null() {
        return false;
    }

    let Some(size) = allocation_size(layout) else {
        return false;
    };
    let ptr_addr = ptr as usize;

    let storage_start = s.storage_start as usize;
    let Some(storage_end) = storage_start.checked_add(s.storage_len) else {
        return false;
    };
    let Some(block_end) = ptr_addr.checked_add(size) else {
        return false;
    };
    if size > s.virtual_len || ptr_addr < storage_start || block_end > storage_end {
        return false;
    }
    let offset = ptr_addr - s.virtual_start as usize;
    if !offset.is_multiple_of(size) {
        return false;
    }
    KernelAllocator.dealloc_node(s, 0, s.virtual_len, offset, size)
}

fn allocation_size(layout: Layout) -> Option<usize> {
    layout
        .size()
        .max(layout.align())
        .max(ALLOCATION_GRANULE)
        .checked_next_power_of_two()
}

/// Allocates from the kernel heap using the standard Rust allocation layout.
pub fn alloc(layout: Layout) -> *mut u8 {
    KERNEL_HEAP_STATE
        .with_state(|state| alloc_from_heap_state(state, layout))
        .unwrap_or(null_mut())
}

/// Deallocates from the kernel heap using the original Rust allocation layout.
///
/// # Safety
/// `ptr` and `layout` must describe a live allocation returned by [`alloc`].
pub unsafe fn dealloc(ptr: *mut u8, layout: Layout) {
    // Reentry refuses metadata access; it cannot create an aliased state borrow.
    let _ = KERNEL_HEAP_STATE.with_state(|state| dealloc_from_heap_state(state, ptr, layout));
}

/// Snapshots heap bounds, or zeroes if metadata is currently borrowed.
pub fn kernel_heap_debug_window() -> (usize, usize, usize, usize) {
    KERNEL_HEAP_STATE
        .with_state(|state| {
            (
                state.storage_start as usize,
                state.storage_len,
                state.virtual_start as usize,
                state.virtual_len,
            )
        })
        .unwrap_or_default()
}

/// Snapshots metadata bounds without aliasing an allocator mutation.
pub fn kernel_heap_metadata_debug_window() -> (usize, usize) {
    KERNEL_HEAP_STATE
        .with_state(|state| (state.metadata_start as usize, state.metadata_len))
        .unwrap_or_default()
}

// --- GlobalAlloc Glue ---

unsafe impl GlobalAlloc for KernelAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        crate::core::allocator::alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: GlobalAlloc forwards the caller's live allocation contract.
        unsafe { crate::core::allocator::dealloc(ptr, layout) };
    }
}

/// Public API to initialize the kernel allocator.
///
/// This function sets up the physical storage, cleans up the alignment,
/// and triggers the tree pruning to lock out-of-bounds memory nodes.
#[cfg_attr(test, allow(dead_code))]
pub fn initialize() {
    unsafe {
        unsafe extern "C" {
            static __ram_end: u8;
        }

        let free_start = ::core::ptr::addr_of!(__ram_end) as usize;
        let Some(ram_end) = crate::core::target::kernel_heap_end() else {
            panic!("missing kernel heap end for target");
        };
        let Some(partition) = partition_kernel_heap(free_start, ram_end) else {
            panic!("failed to partition kernel heap");
        };

        let success = KERNEL_HEAP_STATE
            .with_state(|state| {
                reset_heap(
                    state,
                    partition.heap_start as *mut u8,
                    partition.heap_len,
                    partition.metadata_start as *mut u8,
                    partition.metadata_len,
                )
            })
            .unwrap_or(false);

        if !success {
            crate::consoleln!(
                "allocator init failed free=0x{:08x} meta=0x{:08x}+{} heap=0x{:08x}+{} granule={}",
                free_start,
                partition.metadata_start,
                partition.metadata_len,
                partition.heap_start,
                partition.heap_len,
                ALLOCATION_GRANULE
            );
            // Optional: Panic or Log. In a micro-system, an init failure
            // of the global allocator is usually fatal.
            panic!("Failed to initialize Kernel Buddy Allocator");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iterative_search_preserves_pruned_non_power_of_two_windows() {
        #[repr(align(512))]
        struct Storage([u8; 512]);
        let mut storage = Storage([0; 512]);
        for (offset, len) in [(8, 40), (24, 72), (56, 152)] {
            let mut metadata = [0; 256];
            let mut state = HeapAllocatorState::new();
            let base = storage.0.as_mut_ptr().wrapping_add(offset);
            // SAFETY: each subrange fits the aligned backing array; metadata
            // remains disjoint and live throughout this allocator's lifetime.
            assert!(unsafe {
                reset_heap(&mut state, base, len, metadata.as_mut_ptr(), metadata.len())
            });
            let layout = Layout::from_size_align(8, 8).unwrap();
            let mut blocks = [null_mut(); 32];
            for (index, block) in blocks[..len / 8].iter_mut().enumerate() {
                *block = alloc_from_heap_state(&mut state, layout);
                assert_eq!(*block, base.wrapping_add(index * 8));
            }
            assert!(alloc_from_heap_state(&mut state, layout).is_null());
            for block in blocks[..len / 8].iter().rev() {
                assert!(dealloc_from_heap_state(&mut state, *block, layout));
            }
            assert_eq!(alloc_from_heap_state(&mut state, layout), base);
        }
    }

    #[test]
    fn iterative_search_exhausts_fragmented_heap_and_coalesces_all_blocks() {
        #[repr(align(256))]
        struct Storage([u8; 256]);
        let mut storage = Storage([0; 256]);
        let mut metadata = [0; metadata_size_for_heap_size(256)];
        let mut state = HeapAllocatorState::new();
        // SAFETY: disjoint aligned buffers remain alive for this test.
        assert!(unsafe {
            reset_heap(
                &mut state,
                storage.0.as_mut_ptr(),
                256,
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        });
        let small = Layout::from_size_align(8, 8).unwrap();
        let mut blocks = [null_mut(); 32];
        for (index, block) in blocks.iter_mut().enumerate() {
            *block = alloc_from_heap_state(&mut state, small);
            assert_eq!(*block, storage.0.as_mut_ptr().wrapping_add(index * 8));
        }
        assert!(alloc_from_heap_state(&mut state, small).is_null());
        for block in blocks.iter().step_by(2) {
            assert!(dealloc_from_heap_state(&mut state, *block, small));
        }
        assert!(
            alloc_from_heap_state(&mut state, Layout::from_size_align(16, 8).unwrap()).is_null()
        );
        for block in blocks.iter().skip(1).step_by(2) {
            assert!(dealloc_from_heap_state(&mut state, *block, small));
        }
        assert_eq!(
            alloc_from_heap_state(&mut state, Layout::from_size_align(256, 256).unwrap()),
            storage.0.as_mut_ptr()
        );
    }

    #[test]
    fn kernel_metadata_borrow_refuses_reentry_and_recovers_after_unwind() {
        let cell = KernelHeapStateCell::new();
        assert_eq!(cell.with_state(|_| cell.with_state(|_| ())), Some(None));
        let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            cell.with_state(|_| panic!("test unwind"));
        }));
        assert!(failure.is_err());
        assert_eq!(cell.with_state(|_| 7), Some(7));
    }

    #[test]
    fn foreign_gate_and_its_halves_cannot_be_freed_by_a_rustlet_heap() {
        #[repr(align(512))]
        struct Region([u8; 512]);
        let mut storage = Region([0; 512]);
        let mut gate = Region([0xa5; 512]);
        let mut metadata = [0; metadata_size_for_heap_size(512)];
        let mut state = HeapAllocatorState::new();
        // SAFETY: aligned, disjoint storage and metadata outlive this private heap.
        assert!(unsafe {
            reset_heap(
                &mut state,
                storage.0.as_mut_ptr(),
                512,
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        });
        let layout = Layout::from_size_align(32, 8).unwrap();
        let live = alloc_from_heap_state(&mut state, layout);
        assert!(!live.is_null());
        let before = metadata;
        for (offset, size) in [(0, 512), (0, 256), (256, 256)] {
            let address = gate.0.as_mut_ptr().wrapping_add(offset);
            let foreign_layout = Layout::from_size_align(size, size).unwrap();
            assert!(!dealloc_from_heap_state(
                &mut state,
                address,
                foreign_layout
            ));
            assert_eq!(metadata, before);
            assert_eq!(gate.0, [0xa5; 512]);
        }
        assert!(dealloc_from_heap_state(&mut state, live, layout));
        assert_eq!(alloc_from_heap_state(&mut state, layout), live);
    }

    #[test]
    fn untrusted_free_rejects_wrong_blocks_without_changing_metadata() {
        #[repr(align(256))]
        struct Storage([u8; 256]);
        let mut storage = Storage([0; 256]);
        let mut metadata = [0; metadata_size_for_heap_size(256)];
        let mut state = HeapAllocatorState::new();
        // SAFETY: disjoint, aligned buffers stay live until the test ends.
        assert!(unsafe {
            reset_heap(
                &mut state,
                storage.0.as_mut_ptr(),
                256,
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        });
        let small = Layout::from_size_align(8, 8).unwrap();
        let first = alloc_from_heap_state(&mut state, small);
        let neighbor = alloc_from_heap_state(&mut state, small);
        assert_eq!(neighbor as usize, first as usize + 8);
        let before = metadata;
        for (address, size) in [
            (first as usize, 16),
            (first as usize, 512),
            (first as usize + 1, 8),
            (first as usize + 128, 8),
            (usize::MAX - 7, 16),
        ] {
            assert!(!dealloc_from_heap_state(
                &mut state,
                address as *mut u8,
                Layout::from_size_align(size, 8).unwrap()
            ));
            assert_eq!(metadata, before);
        }
        assert!(dealloc_from_heap_state(&mut state, first, small));
        let before = metadata;
        assert!(!dealloc_from_heap_state(&mut state, first, small));
        assert_eq!(metadata, before);
        assert!(dealloc_from_heap_state(&mut state, neighbor, small));
        let large = Layout::from_size_align(32, 8).unwrap();
        let block = alloc_from_heap_state(&mut state, large);
        let before = metadata;
        for address in [block, block.wrapping_add(8)] {
            assert!(!dealloc_from_heap_state(&mut state, address, small));
            assert_eq!(metadata, before);
        }
        assert!(dealloc_from_heap_state(&mut state, block, large));
        assert_eq!(alloc_from_heap_state(&mut state, large), block);
    }

    #[test]
    fn heap_state_allocates_power_of_two_blocks_inside_storage() {
        let mut state = HeapAllocatorState::new();
        let mut storage = [0u8; 256];
        let mut metadata = [0u8; metadata_size_for_heap_size(256)];

        let initialized = unsafe {
            reset_heap(
                &mut state,
                storage.as_mut_ptr(),
                storage.len(),
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        };
        assert!(initialized);

        let layout = Layout::from_size_align(24, 16).unwrap();
        let ptr = alloc_from_heap_state(&mut state, layout);
        assert!(!ptr.is_null());

        let start = storage.as_ptr() as usize;
        let end = start + storage.len();
        let ptr_addr = ptr as usize;
        assert!((start..end).contains(&ptr_addr));
        assert_eq!(ptr_addr % 32, 0);
    }

    #[test]
    fn heap_state_reuses_deallocated_block() {
        let mut state = HeapAllocatorState::new();
        let mut storage = [0u8; 256];
        let mut metadata = [0u8; metadata_size_for_heap_size(256)];

        let initialized = unsafe {
            reset_heap(
                &mut state,
                storage.as_mut_ptr(),
                storage.len(),
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        };
        assert!(initialized);

        let layout = Layout::from_size_align(32, 8).unwrap();
        let first = alloc_from_heap_state(&mut state, layout);
        assert!(!first.is_null());
        assert!(dealloc_from_heap_state(&mut state, first, layout));

        let second = alloc_from_heap_state(&mut state, layout);
        assert_eq!(second, first);
    }

    #[test]
    fn heap_state_rejects_foreign_deallocation() {
        let mut state = HeapAllocatorState::new();
        let mut storage = [0u8; 256];
        let mut metadata = [0u8; metadata_size_for_heap_size(256)];
        let mut foreign = [0u8; 32];

        let initialized = unsafe {
            reset_heap(
                &mut state,
                storage.as_mut_ptr(),
                storage.len(),
                metadata.as_mut_ptr(),
                metadata.len(),
            )
        };
        assert!(initialized);

        let layout = Layout::from_size_align(16, 8).unwrap();
        assert!(!dealloc_from_heap_state(
            &mut state,
            foreign.as_mut_ptr(),
            layout
        ));
    }
}
