#![no_std]
#![no_main]
use rpc_shared_interface::{counter, CALLER};
use rustlet_runtime::{declare_rpc_rustlet, Aid};

// The shared dispatcher supplies the wire contract; this image only implements the service.
declare_rpc_rustlet!(Counter, counter::dispatch, 384usize);
#[derive(Default, rustlet_runtime::serde::Serialize, rustlet_runtime::serde::Deserialize)]
#[serde(crate = "rustlet_runtime::serde")]
struct Counter {
    value: u32,
}
impl counter::Service for Counter {
    fn add(&mut self, caller: &Aid, value: u32) -> u32 {
        assert!(caller == &CALLER);
        self.value = self.value.wrapping_add(value);
        self.value
    }
    fn value(&mut self, _: &Aid) -> u32 {
        self.value
    }
    fn identity(&mut self, caller: &Aid) -> [u8; 17] {
        let mut result = [0; 17];
        result[0] = caller.len;
        result[1..].copy_from_slice(&caller.bytes);
        result
    }
    fn crash(&mut self, _: &Aid) {
        self.value = 999;
        panic!("RPC rollback probe");
    }
    fn fault(&mut self, _: &Aid) {
        self.value = 999;
        // SAFETY: deliberate isolated CPU fault for the containment test.
        unsafe {
            core::arch::asm!("udf #0", options(noreturn));
        }
    }
    fn nested(&mut self, _: &Aid) -> bool {
        counter::Client::new(CALLER).value().is_err()
    }
}
