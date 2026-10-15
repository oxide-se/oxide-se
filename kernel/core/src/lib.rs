#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

extern crate alloc;
#[cfg(any(test, feature = "host-test"))]
extern crate std;

pub mod core;
