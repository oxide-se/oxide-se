#![deny(unsafe_op_in_unsafe_fn)]
#![cfg_attr(not(test), no_std)]
#![allow(dead_code)]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod apdu_debug_mod;
mod apdu_layer;
mod apdu_manager;
mod embedded_apps;
mod fae_runtime;
mod firmware_uid;
mod gp_status;
mod in_place_request;
mod kernel_cell;
mod kernel_main_app;
mod predeployment;
mod registry;
mod secure_channel;
pub mod security_domain;
pub mod selected_app;
mod shared_page;
mod time_manager;
mod transport_layer;

pub use firmware_uid::get_firmware_uid;
pub use oxi_core::core;
