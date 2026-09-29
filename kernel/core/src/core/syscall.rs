pub type SyscallNumber = rustlet_runtime::syscall_abi::SyscallNumber;
pub type SyscallWord = rustlet_runtime::syscall_abi::SyscallWord;
use core::alloc::Layout;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicPtr, Ordering};

pub type SyscallHandler =
    unsafe extern "C" fn(SyscallWord, SyscallWord, SyscallWord, SyscallWord) -> SyscallWord;

static CURRENT_APP_ALLOCATOR: AtomicPtr<crate::core::HeapAllocatorState> =
    AtomicPtr::new(null_mut());

#[derive(Clone, Copy)]
pub struct SyscallBinding {
    pub number: SyscallNumber,
    pub handler: SyscallHandler,
}

pub fn initialize() {
    crate::core::target::syscall_initialize();
    install_bindings(&BUILTIN_BINDINGS);
}

pub fn install_handler(number: SyscallNumber, handler: SyscallHandler) {
    crate::core::target::install_syscall_handler(number, handler);
}

pub fn install_bindings(bindings: &[SyscallBinding]) {
    for binding in bindings {
        install_handler(binding.number, binding.handler);
    }
}

pub fn request_thread_redirect(pc: usize, r0: SyscallWord, r1: SyscallWord) {
    crate::core::target::request_syscall_thread_redirect(pc, r0, r1);
}

/// Runs a synchronous Rustlet invocation with exclusive access to its allocator.
///
/// The state stays borrowed until the invocation returns, including fault returns.
/// Nested publication is rejected. The private guard cannot escape or be forgotten
/// by the callback, and clears the pointer on normal return or host unwinding.
/// No heap contents are borrowed, copied, or moved by this scope.
pub fn with_app_allocator<R>(
    state: &mut crate::core::HeapAllocatorState,
    invoke: impl FnOnce() -> R,
) -> R {
    #[cfg(all(target_arch = "arm", oxide_se_target_armv6m))]
    let published = {
        // RP2040 kernel execution is confined to core 0. Mask interrupts only
        // during publication; ARMv6-M has no compare-exchange instruction.
        let mask = crate::core::target::armv6m_profile::interrupts_save_and_disable();
        let vacant = CURRENT_APP_ALLOCATOR.load(Ordering::Relaxed).is_null();
        if vacant {
            CURRENT_APP_ALLOCATOR.store(state, Ordering::Release);
        }
        crate::core::target::armv6m_profile::interrupts_restore(mask);
        vacant
    };
    #[cfg(not(all(target_arch = "arm", oxide_se_target_armv6m)))]
    let published = CURRENT_APP_ALLOCATOR
        .compare_exchange(null_mut(), state, Ordering::AcqRel, Ordering::Acquire)
        .is_ok();
    assert!(published, "an app allocator is already active");
    struct Scope;
    impl Drop for Scope {
        fn drop(&mut self) {
            CURRENT_APP_ALLOCATOR.store(null_mut(), Ordering::Release);
        }
    }
    let _scope = Scope;
    invoke()
}

pub fn syscall_table_debug_addr() -> usize {
    crate::core::target::syscall_table_debug_addr()
}

pub fn syscall_handler_debug_addr(number: SyscallNumber) -> usize {
    crate::core::target::syscall_handler_debug_addr(number)
}

extern "C" fn enter_app_handler(
    _arg0: SyscallWord,
    _arg1: SyscallWord,
    _arg2: SyscallWord,
    _arg3: SyscallWord,
) -> SyscallWord {
    0
}

extern "C" fn alloc_handler(
    arg0: SyscallWord,
    arg1: SyscallWord,
    _arg2: SyscallWord,
    _arg3: SyscallWord,
) -> SyscallWord {
    let Some((allocator, layout)) = active_allocator_and_layout(arg0, arg1) else {
        return 0;
    };
    // SAFETY: with_app_allocator retains the exclusive state borrow for the
    // complete invocation; SVC handlers run serially on the kernel-owning core.
    unsafe { crate::core::allocator::alloc_from_heap(allocator, layout) as SyscallWord }
}

extern "C" fn dealloc_handler(
    arg0: SyscallWord,
    arg1: SyscallWord,
    arg2: SyscallWord,
    _arg3: SyscallWord,
) -> SyscallWord {
    if let Some((allocator, layout)) = active_allocator_and_layout(arg1, arg2) {
        // SAFETY: the scoped publisher keeps the state and metadata exclusive
        // and live. The allocator validates the untrusted address and rounded
        // block size before mutation. This heap belongs only to the Rustlet;
        // the kernel retains no Rust references into its allocated blocks.
        unsafe {
            let _ = crate::core::allocator::dealloc_from_heap(allocator, arg0 as *mut u8, layout);
        }
    }
    0
}

#[inline(always)]
fn active_allocator_and_layout(
    size: SyscallWord,
    align: SyscallWord,
) -> Option<(*mut crate::core::HeapAllocatorState, Layout)> {
    let allocator = CURRENT_APP_ALLOCATOR.load(Ordering::Acquire);
    if allocator.is_null() {
        return None;
    }
    let layout = Layout::from_size_align(size, align).ok()?;
    Some((allocator, layout))
}

const BUILTIN_BINDINGS: [SyscallBinding; 3] = [
    SyscallBinding {
        number: rustlet_runtime::syscall_abi::ENTER_APP,
        handler: enter_app_handler,
    },
    SyscallBinding {
        number: rustlet_runtime::syscall_abi::ALLOC,
        handler: alloc_handler,
    },
    SyscallBinding {
        number: rustlet_runtime::syscall_abi::DEALLOC,
        handler: dealloc_handler,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scoped_allocator_retires_after_return_and_unwind_and_rejects_nesting() {
        let mut state = crate::core::HeapAllocatorState::new();
        assert!(CURRENT_APP_ALLOCATOR.load(Ordering::Acquire).is_null());
        assert_eq!(
            with_app_allocator(&mut state, || {
                assert!(!CURRENT_APP_ALLOCATOR.load(Ordering::Acquire).is_null());
                let nested = std::panic::catch_unwind(|| {
                    let mut other = crate::core::HeapAllocatorState::new();
                    with_app_allocator(&mut other, || ());
                });
                assert!(nested.is_err());
                assert!(!CURRENT_APP_ALLOCATOR.load(Ordering::Acquire).is_null());
                42
            }),
            42
        );
        assert!(CURRENT_APP_ALLOCATOR.load(Ordering::Acquire).is_null());
        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_app_allocator(&mut state, || panic!("test unwind"));
        }));
        assert!(unwind.is_err());
        assert!(CURRENT_APP_ALLOCATOR.load(Ordering::Acquire).is_null());
        assert_eq!(alloc_handler(8, 8, 0, 0), 0);
        assert_eq!(dealloc_handler(1, 8, 8, 0), 0);
    }
}
