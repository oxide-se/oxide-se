#![no_std]
//! Shared interface consumed by both examples; only Rustlet code understands it.
use rustlet_runtime::Aid;
/// Installed caller identifier.
pub const CALLER: Aid = Aid::from_array([0xa0, 0, 0, 0x47, 0x50, 0x4f, 0x53, 0x31]);
/// Installed callee identifier.
pub const CALLEE: Aid = Aid::from_array([0xa0, 0, 0, 0x47, 0x50, 0x4f, 0x53, 0x32]);
rustlet_runtime::rpc_interface! {
    pub mod counter, id = 0x525043, version = 1 {
        fn add(value: u32) -> u32;
        fn value() -> u32;
        fn identity() -> [u8; 17];
        fn crash() -> ();
        fn fault() -> ();
        fn nested() -> bool;
    }
}
