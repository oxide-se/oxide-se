#![no_std]
#![no_main]

use alloc::boxed::Box;
use rustlet_runtime::{declare_app, Apdu, ApduStatus, Rustlet, RustletCtx};

declare_app!(MinimalValidRustlet, 256);

#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct MinimalValidRustlet {
    counter: u8,
}

impl Rustlet for MinimalValidRustlet {
    fn process_apdu(&mut self, ctx: &mut RustletCtx) -> ApduStatus {
        // Diagnostic: even a selected SD has no key authority in process_apdu.
        if Apdu::new(ctx).ins() == 0x0A {
            let mut output = [0xA5; 16];
            let result = ctx.load_scp03_key_material(1, 3, 0x01, &mut output);
            let denied = result == Err(rustlet_runtime::CryptoError::PermissionDenied)
                && output == [0xA5; 16];
            // Do not return key material even if the isolation check regresses.
            output.fill(0);
            return if denied {
                ApduStatus::success()
            } else {
                ApduStatus::internal_error()
            };
        }
        let apdu = Apdu::new(ctx);

        match apdu.ins() {
            0x0D => {
                self.counter = self.counter.wrapping_add(1);
                apdu.as_sending().send(&[self.counter, 0xD3, 0x91, 0xA7, 0x5E])
            }
            0x0E => apdu.as_sending().send(&[self.counter]),
            0x0F => {
                self.counter = self.counter.wrapping_add(1);
                panic!("application transaction diagnostic");
            }
            0x10 => {
                self.counter = self.counter.wrapping_add(1);
                apdu.as_sending().send(&[self.counter])
            }
            0x00 => apdu.accept(),
            0x02 => apdu.as_receiving().accept(),
            0x04 => apdu.as_sending().send(&[0x10, 0x11, 0x12]),
            0x06 => apdu.as_receiving().accept_and_send(&[0xAA, 0xBB, 0xCC]),
            0x08 => apdu.as_sending().send(&[large_stack_probe()]),
            0x01 => {
                let value = Box::new(0x5Au8);
                drop(value);
                panic!("minimal alloc/dealloc/panic");
            }
            _ => apdu.reject(ApduStatus::instruction_not_supported()),
        }
    }
}

// This instruction is invoked only by the dynamic campaign with a 4096-byte
// footer stack. Keep its frame separate from ordinary minimal APDU handlers.
#[inline(never)]
fn large_stack_probe() -> u8 {
    let mut scratch = [0u8; 2304];
    for (index, byte) in scratch.iter_mut().enumerate() {
        // Volatile accesses force the complete stack frame to remain materialized.
        unsafe { core::ptr::write_volatile(byte, index as u8); }
    }
    let mut sum = 0u8;
    for byte in &scratch {
        sum = sum.wrapping_add(unsafe { core::ptr::read_volatile(byte) });
    }
    sum
}
