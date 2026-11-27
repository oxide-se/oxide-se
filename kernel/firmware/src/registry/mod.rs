//! Compact registry with deferred flash snapshots.
//!
//! Format, storage, publication, reconstruction, transactions and savepoints
//! and physical payload preparation live here. APDU/runtime policy and LOAD
//! protocol orchestration remain in `selected_app`.
//! See `docs/registry.contracts.md` and `proofs/registry/README.md` for the
//! characterized behavior and updated proof assumptions.

// Some format helpers are used only by host tests and diagnostic configurations.
pub(crate) mod boss_crypto;
pub(crate) mod content;
pub(crate) mod data_crypto;
#[allow(dead_code)]
pub mod format;
pub(crate) mod header_auth;
pub(crate) mod state;
pub(crate) mod storage;
#[cfg(oxide_se_kernel_app_module = "registry-test")]
pub(crate) mod write_fault;

pub(crate) mod publication;
pub(crate) mod recovery;

pub(crate) mod savepoint;
pub(crate) mod transaction;

pub(crate) mod payload;

pub(crate) mod boot;
pub(crate) mod journal;
pub(crate) mod objects;
pub(crate) mod operations;
pub(crate) mod physical;

// Stable component entry points. Typed mutations stage changes; the operation
// adapter owns or joins a transaction separately from this borrowed interface.
pub(crate) use boot::init_on_reset;
pub(crate) use operations::{edit, read, Mutation};
pub(crate) use transaction::{begin_transaction, commit_transaction, request_abort};

#[cfg(oxide_se_kernel_app_module = "registry-test")]
pub(crate) mod perf;

// Single resident image and bounded snapshot roots.
pub(crate) mod image;
mod limits;
pub(crate) mod snapshots;

pub(crate) mod pages;
pub(crate) mod references;
pub(crate) mod retention;
#[cfg(not(test))]
mod volatile;
#[cfg(not(test))]
pub(crate) use volatile::enabled as uses_volatile_storage;
#[cfg(test)]
pub(crate) mod testing;
