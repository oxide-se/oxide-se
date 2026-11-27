#![forbid(unsafe_code)]
/// Static RAM and flash layout for one supported target.
///
/// These values describe the board-level memory budget used by the kernel
/// runtime, bootable startup linker scripts, and host-side layout diagnostics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetMemoryLayout {
    pub name: &'static str,
    pub ram_base: usize,
    pub ram_size: usize,
    pub flash_base: usize,
    pub flash_size: usize,
    pub kernel_heap_min_size: usize,
    pub kernel_stack_size: usize,
}

impl TargetMemoryLayout {
    /// Checks that a source remains readable from RAM while XIP is suspended.
    /// This validates a range, not ownership; the caller supplies a live slice.
    #[cfg(any(test, target_arch = "arm"))]
    pub(crate) fn contains_ram_buffer(self, start: usize, len: usize) -> bool {
        let Some(end) = start.checked_add(len) else {
            return false;
        };
        let Some(ram_end) = self.ram_base.checked_add(self.ram_size) else {
            return false;
        };
        start >= self.ram_base && end <= ram_end
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn flash_source_must_fit_entirely_in_ram_without_wrapping() {
        let layout = TargetMemoryLayout {
            name: "test",
            ram_base: 0x2000_0000,
            ram_size: 65536,
            flash_base: 0x1000_0000,
            flash_size: 4096,
            kernel_heap_min_size: 0,
            kernel_stack_size: 8192,
        };
        assert!(layout.contains_ram_buffer(0x2000_ff00, 256));
        assert!(!layout.contains_ram_buffer(0x2000_ff01, 256));
        assert!(!layout.contains_ram_buffer(0x1000_0000, 256));
        assert!(!layout.contains_ram_buffer(usize::MAX - 1, 256));
    }
}
