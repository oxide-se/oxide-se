//! Volatile publication cache; reconstructed after reset, never recovery evidence.

use super::format as registry_persistence;
use crate::kernel_cell::KernelCell;
use crate::registry::objects::{
    ManagedObjectKind, Registry, DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY,
};
use rustlet_runtime::Aid;

// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static PERSISTENCE_RUNTIME_STATE: KernelCell<PersistenceRuntimeState> =
    unsafe { KernelCell::new(PersistenceRuntimeState::EMPTY) };

#[derive(Clone, Copy)]
pub(crate) struct PersistenceRuntimeState {
    pub(crate) initialized: bool,
    pub(crate) latest_registry: Option<registry_persistence::PersistentRange>,
    pub(crate) mutation_counter: u32,
    pub(crate) append_offset: usize,
}

impl PersistenceRuntimeState {
    pub(crate) const EMPTY: Self = Self {
        initialized: false,
        latest_registry: None,
        mutation_counter: 0,
        append_offset: 0,
    };
}

// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(super) static OBJECT_REGISTRY: KernelCell<Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>> =
    unsafe { KernelCell::new(Registry::new()) };
// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static PERSISTENCE_PAYLOAD_BUFFER: KernelCell<[u8; PERSISTENCE_PAYLOAD_BUFFER_SIZE]> =
    unsafe { KernelCell::new([0; PERSISTENCE_PAYLOAD_BUFFER_SIZE]) };
// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static USED_PAGES: super::pages::Pages = super::pages::Pages::new();
// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static PERSISTENCE_BOOTSTRAP_IN_PROGRESS: KernelCell<bool> =
    unsafe { KernelCell::new(false) };
// SAFETY: privileged owner-core state; IRQ handlers never access it.
pub(crate) static DYNAMIC_LOAD_CONTEXT: KernelCell<Option<DynamicLoadContext>> =
    unsafe { KernelCell::new(None) };

pub(crate) const PERSISTENCE_PAYLOAD_BUFFER_SIZE: usize = 512;

/// In-progress GP `INSTALL [for load]` / `LOAD` transaction.
///
/// The payload is streamed directly into the registry persistence area. The
/// context therefore tracks only the announced metadata, the reserved flash
/// span and the page currently staged in [`super::storage::PERSISTENCE_PAGE_BUFFER`].
#[derive(Clone, Copy)]
pub(crate) struct DynamicLoadContext {
    pub(crate) authority_aid: Aid,
    pub(crate) target_sd_aid: Aid,
    pub(crate) package_aid: Aid,
    pub(crate) protected: bool,
    pub(crate) expected_hash: [u8; 32],
    pub(crate) next_block_number: u8,
    pub(crate) payload: super::payload::PayloadPreparation,
}

pub(crate) fn initialize_persistence_runtime_state(
    latest_registry: Option<registry_persistence::PersistentRange>,
    mutation_counter: u32,
    append_offset: usize,
) {
    let mut state_guard = PERSISTENCE_RUNTIME_STATE.borrow_mut();
    let state = &mut *state_guard;
    *state = PersistenceRuntimeState {
        initialized: true,
        latest_registry,
        mutation_counter,
        append_offset,
    };
}

pub(super) const fn runtime_object_kind(
    kind: registry_persistence::PersistentObjectKind,
) -> ManagedObjectKind {
    match kind {
        registry_persistence::PersistentObjectKind::SecurityDomain => {
            ManagedObjectKind::SecurityDomain
        }
        registry_persistence::PersistentObjectKind::Package => ManagedObjectKind::Package,
        registry_persistence::PersistentObjectKind::Instance => ManagedObjectKind::Instance,
        registry_persistence::PersistentObjectKind::Key => ManagedObjectKind::Key,
        registry_persistence::PersistentObjectKind::Data => ManagedObjectKind::Data,
    }
}

/// Returns true while a GP `INSTALL [for load]` / `LOAD` transaction is active.
///
/// The context is intentionally volatile: it is never published in the object
/// registry and therefore disappears naturally on reset before the final LOAD
/// block commits the package object.
pub fn dynamic_package_load_in_progress() -> bool {
    {
        (*DYNAMIC_LOAD_CONTEXT.borrow()).is_some()
    }
}
