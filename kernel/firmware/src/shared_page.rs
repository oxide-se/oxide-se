//! Exclusive kernel access to the resident APDU page and protocol scratch.
//!
//! Tokens own access, never the bytes. The kernel owner core is the only caller;
//! interrupt handlers do not acquire these buffers. Rustlet entry transfers the
//! whole page to the ABI; synchronous SVC handlers may temporarily borrow it.
//! Separate control/payload tokens permit disjoint transport and crypto views.
#![deny(unsafe_op_in_unsafe_fn)]

use core::marker::PhantomData;
use core::sync::atomic::{AtomicU8, Ordering};

pub(crate) const CONTROL: u8 = 1;
pub(crate) const PAYLOAD: u8 = 2;
pub(crate) const PAGE: u8 = CONTROL | PAYLOAD;
const EXECUTING: u8 = 4;
pub(crate) const PROXY: u8 = 8;
pub(crate) const AUX: u8 = 16;
pub(crate) const MAC: u8 = 32;
pub(crate) const CERTIFICATE_CHAIN: u8 = 64;
pub(crate) const MANAGEMENT: u8 = 128;

static BORROWED: AtomicU8 = AtomicU8::new(0);

/// ARM firmware runs this protocol on its owner core only, with no IRQ user.
/// Host builds also exclude simultaneous callers, so the test harness cannot
/// turn a rejected acquisition into aliased resident references.
#[inline(always)]
fn transition(remove: u8, add: u8, required: u8, forbidden: u8) {
    #[allow(unused_mut)]
    let mut occupied = BORROWED.load(Ordering::Relaxed);
    loop {
        assert!(
            occupied & required == required && occupied & forbidden == 0,
            "APDU buffer phase conflict"
        );
        let next = (occupied & !remove) | add;
        #[cfg(target_arch = "arm")]
        {
            BORROWED.store(next, Ordering::Relaxed);
            return;
        }
        #[cfg(not(target_arch = "arm"))]
        match BORROWED.compare_exchange_weak(occupied, next, Ordering::Acquire, Ordering::Relaxed) {
            Ok(_) => return,
            Err(actual) => occupied = actual,
        }
    }
}

#[cfg(test)]
pub(crate) static TEST_PAGE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Non-copyable access token. References must borrow this token, not its address.
/// Acquisition is checked because ABI entry cannot carry a Rust lifetime.
/// The marker also prevents moving a token to another core/thread.
pub(crate) struct Lease {
    mask: u8,
    _owner: PhantomData<*mut ()>,
}

impl Lease {
    #[inline(always)]
    pub(crate) fn acquire(mask: u8) -> Self {
        assert!(
            mask != 0 && mask & EXECUTING == 0,
            "invalid APDU access region"
        );
        transition(
            0,
            mask,
            0,
            mask | if mask & PAGE != 0 { EXECUTING } else { 0 },
        );
        Self {
            mask,
            _owner: PhantomData,
        }
    }

    /// Temporarily borrows the page delegated to the suspended Rustlet.
    ///
    /// # Safety
    /// Only a synchronous SVC or terminal-exit callback may call this. The
    /// Rustlet must be suspended and the ABI must grant the requested access.
    #[inline(always)]
    pub(crate) unsafe fn syscall() -> Self {
        transition(0, PAGE, EXECUTING, PAGE);
        Self {
            mask: PAGE,
            _owner: PhantomData,
        }
    }

    #[inline(always)]
    pub(crate) fn delegate(mut self) -> Self {
        assert_eq!(self.mask, PAGE);
        transition(PAGE, EXECUTING, PAGE, EXECUTING);
        self.mask = EXECUTING;
        self
    }

    #[inline(always)]
    pub(crate) fn resume(mut self) -> Self {
        assert_eq!(self.mask, EXECUTING);
        transition(EXECUTING, PAGE, EXECUTING, PAGE);
        self.mask = PAGE;
        self
    }
}

impl Drop for Lease {
    #[inline(always)]
    fn drop(&mut self) {
        #[cfg(target_arch = "arm")]
        BORROWED.store(
            BORROWED.load(Ordering::Relaxed) & !self.mask,
            Ordering::Relaxed,
        );
        #[cfg(not(target_arch = "arm"))]
        BORROWED.fetch_and(!self.mask, Ordering::Release);
    }
}

/// Resident storage accessed only through an exclusive, bounded guard.
/// Each use reserves its assigned bit in the owner-core access map.
pub(crate) struct Resident<T, const MASK: u8> {
    value: core::cell::UnsafeCell<T>,
}

// SAFETY: only the kernel owner core accesses resident protocol storage. The
// checked lease excludes reentry; guards cannot be sent to another thread.
unsafe impl<T: Send, const MASK: u8> Sync for Resident<T, MASK> {}

impl<T, const MASK: u8> Resident<T, MASK> {
    pub(crate) const fn new(value: T) -> Self {
        Self {
            value: core::cell::UnsafeCell::new(value),
        }
    }

    pub(crate) fn borrow(&self) -> ResidentGuard<'_, T> {
        ResidentGuard {
            ptr: self.value.get(),
            lease: Lease::acquire(MASK),
            _lifetime: PhantomData,
        }
    }
}

pub(crate) struct ResidentGuard<'a, T> {
    ptr: *mut T,
    lease: Lease,
    _lifetime: PhantomData<&'a mut T>,
}

impl<T> core::ops::Deref for ResidentGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: the lease excludes other accesses and the storage outlives it.
        unsafe { &*self.ptr }
    }
}
impl<T> core::ops::DerefMut for ResidentGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: the exclusive guard borrow bounds the reference.
        unsafe { &mut *self.ptr }
    }
}

impl<T> ResidentGuard<'static, T> {
    /// Transfers the lease together with the resident pointer to a typed view.
    pub(crate) fn into_raw_parts(self) -> (*mut T, Lease) {
        (self.ptr, self.lease)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn disjoint_halves_exclude_whole_page_and_release_after_unwind() {
        let _lock = TEST_PAGE_LOCK.lock().unwrap();
        let control = Lease::acquire(CONTROL);
        let payload = Lease::acquire(PAYLOAD);
        assert!(catch_unwind(|| Lease::acquire(PAGE)).is_err());
        assert!(catch_unwind(|| Lease::acquire(CONTROL)).is_err());
        drop((control, payload));
        assert!(catch_unwind(|| {
            let _page = Lease::acquire(PAGE);
            panic!("early return test");
        })
        .is_err());
        drop(Lease::acquire(PAGE));
    }

    #[test]
    fn execution_lends_page_only_to_one_synchronous_syscall() {
        let _lock = TEST_PAGE_LOCK.lock().unwrap();
        assert!(catch_unwind(|| unsafe { Lease::syscall() }).is_err());
        let execution = Lease::acquire(PAGE).delegate();
        assert!(catch_unwind(|| Lease::acquire(PAYLOAD)).is_err());
        assert!(catch_unwind(|| Lease::acquire(CONTROL)).is_err());
        // SAFETY: this test models a suspended ABI invocation.
        let call = unsafe { Lease::syscall() };
        assert!(catch_unwind(|| unsafe { Lease::syscall() }).is_err());
        drop(call);
        let returned = execution.resume();
        assert!(catch_unwind(|| Lease::acquire(PAGE)).is_err());
        drop(returned);
        drop(Lease::acquire(PAGE));
    }

    #[test]
    fn resident_borrows_reject_reentry_and_keep_the_same_storage() {
        let _lock = TEST_PAGE_LOCK.lock().unwrap();
        let storage: Resident<[u8; 16], AUX> = Resident::new([0; 16]);
        let address;
        {
            let mut first = storage.borrow();
            address = first.as_ptr();
            first[0] = 0xA5;
            assert!(catch_unwind(AssertUnwindSafe(|| storage.borrow())).is_err());
        }
        let second = storage.borrow();
        assert_eq!(second.as_ptr(), address);
        assert_eq!(second[0], 0xA5);
    }
}
