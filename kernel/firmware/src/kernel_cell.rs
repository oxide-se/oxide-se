//! Scoped access to resident kernel state on the privileged owner core.
//!
//! Read loans may nest; a writer excludes every other loan. Guards own only a
//! pointer and a reservation, never a copy of the resident object. Construction
//! is unsafe because firmware scheduling, IRQ exclusion and non-Send values
//! cannot be proved by Rust's global type system.
#![deny(unsafe_op_in_unsafe_fn)]

use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicU8, Ordering};

const WRITER: u8 = u8::MAX;

pub(crate) struct KernelCell<T> {
    value: UnsafeCell<T>,
    borrowed: AtomicU8,
}

// SAFETY: construction establishes the owner-core contract for T. The checked
// loans exclude reentrant writers; host acquisition additionally uses CAS.
unsafe impl<T> Sync for KernelCell<T> {}

impl<T> KernelCell<T> {
    /// # Safety
    /// Firmware callers must run on the privileged owner core, with no IRQ
    /// accesses. Values which are not Send/Sync must stay on their owning thread
    /// in host builds too. Every access must use this cell's guards.
    pub(crate) const unsafe fn new(value: T) -> Self {
        Self {
            value: UnsafeCell::new(value),
            borrowed: AtomicU8::new(0),
        }
    }

    #[inline(always)]
    fn acquire<const WRITE: bool>(&self) -> Option<Loan<'_, WRITE>> {
        #[allow(unused_mut)]
        let mut current = self.borrowed.load(Ordering::Relaxed);
        loop {
            if !(if WRITE {
                current == 0
            } else {
                current < WRITER - 1
            }) {
                return None;
            }
            let next = if WRITE { WRITER } else { current + 1 };
            #[cfg(target_arch = "arm")]
            {
                self.borrowed.store(next, Ordering::Relaxed);
                break;
            }
            #[cfg(not(target_arch = "arm"))]
            match self.borrowed.compare_exchange_weak(
                current,
                next,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(actual) => current = actual,
            }
        }
        Some(Loan {
            state: &self.borrowed,
            _owner: PhantomData,
        })
    }

    #[inline(always)]
    pub(crate) fn borrow(&self) -> KernelRef<'_, T> {
        KernelRef {
            ptr: self.value.get(),
            loan: self
                .acquire::<false>()
                .expect("conflicting kernel state borrow"),
            _lifetime: PhantomData,
        }
    }

    #[inline(always)]
    pub(crate) fn borrow_mut(&self) -> KernelRefMut<'_, T> {
        KernelRefMut {
            ptr: self.value.get(),
            loan: self
                .acquire::<true>()
                .expect("conflicting kernel state borrow"),
            _lifetime: PhantomData,
        }
    }

    pub(crate) fn try_borrow_mut(&self) -> Option<KernelRefMut<'_, T>> {
        Some(KernelRefMut {
            ptr: self.value.get(),
            loan: self.acquire::<true>()?,
            _lifetime: PhantomData,
        })
    }

    #[inline(always)]
    pub(crate) fn get(&self) -> T
    where
        T: Copy,
    {
        *self.borrow()
    }
    pub(crate) fn set(&self, value: T) {
        *self.borrow_mut() = value;
    }
    pub(crate) fn replace(&self, value: T) -> T {
        core::mem::replace(&mut *self.borrow_mut(), value)
    }
}

struct Loan<'a, const WRITE: bool> {
    state: &'a AtomicU8,
    _owner: PhantomData<*mut ()>,
}

impl<const WRITE: bool> Drop for Loan<'_, WRITE> {
    #[inline]
    fn drop(&mut self) {
        if WRITE {
            self.state.store(0, Ordering::Release);
        } else {
            #[cfg(target_arch = "arm")]
            self.state
                .store(self.state.load(Ordering::Relaxed) - 1, Ordering::Relaxed);
            #[cfg(not(target_arch = "arm"))]
            self.state.fetch_sub(1, Ordering::Release);
        }
    }
}

pub(crate) struct KernelRef<'a, T: ?Sized> {
    ptr: *const T,
    loan: Loan<'a, false>,
    _lifetime: PhantomData<&'a T>,
}

impl<'a, T: ?Sized> KernelRef<'a, T> {
    pub(crate) fn filter_map<U: ?Sized>(
        self,
        f: impl FnOnce(&T) -> Option<&U>,
    ) -> Option<KernelRef<'a, U>> {
        let ptr = f(&self)? as *const U;
        Some(KernelRef {
            ptr,
            loan: self.loan,
            _lifetime: PhantomData,
        })
    }
}
impl<T: ?Sized> Deref for KernelRef<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: the live read loan excludes writers; references borrow the guard.
        unsafe { &*self.ptr }
    }
}

pub(crate) struct KernelRefMut<'a, T: ?Sized> {
    ptr: *mut T,
    loan: Loan<'a, true>,
    _lifetime: PhantomData<&'a mut T>,
}
impl<'a, T: ?Sized> KernelRefMut<'a, T> {
    pub(crate) fn filter_map<U: ?Sized>(
        mut self,
        f: impl FnOnce(&mut T) -> Option<&mut U>,
    ) -> Option<KernelRefMut<'a, U>> {
        let ptr = f(&mut self)? as *mut U;
        Some(KernelRefMut {
            ptr,
            loan: self.loan,
            _lifetime: PhantomData,
        })
    }
}
impl<T: ?Sized> Deref for KernelRefMut<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // SAFETY: the live exclusive loan owns this storage.
        unsafe { &*self.ptr }
    }
}
impl<T: ?Sized> DerefMut for KernelRefMut<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: both the loan and the guard borrow are exclusive.
        unsafe { &mut *self.ptr }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn nested_reads_exclude_writers_and_mapped_views_keep_the_loan() {
        // SAFETY: this local test owns all accesses.
        let cell = unsafe { KernelCell::new([1, 2, 3]) };
        let first = cell.borrow();
        let second = cell.borrow().filter_map(|v| Some(&v[1..])).unwrap();
        assert_eq!(&*second, &[2, 3]);
        assert!(catch_unwind(AssertUnwindSafe(|| cell.borrow_mut())).is_err());
        drop(first);
        assert!(catch_unwind(AssertUnwindSafe(|| cell.borrow_mut())).is_err());
        drop(second);
        cell.borrow_mut()[1] = 4;
        assert_eq!(cell.get(), [1, 4, 3]);
    }

    #[test]
    fn exclusive_loan_rejects_reentry_and_unwinds_without_poisoning() {
        // SAFETY: this local test owns all accesses.
        let cell = unsafe { KernelCell::new(Some(1)) };
        assert!(catch_unwind(AssertUnwindSafe(|| {
            let mut value = cell.borrow_mut().filter_map(Option::as_mut).unwrap();
            *value = 2;
            let _conflict = cell.borrow();
        }))
        .is_err());
        assert_eq!(cell.replace(None), Some(2));
        assert!(cell.borrow_mut().filter_map(Option::as_mut).is_none());
        cell.set(Some(3));
    }
}
