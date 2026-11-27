use core::alloc::Layout;

use rustlet_runtime::{
    Aid, CryptoCipherDoFinalParams, CryptoEcCurve, CryptoEcGenerateKeypairParams,
    CryptoEcdhDoFinalParams, CryptoErrorCode, CryptoHkdfSha256Params, CryptoMacDoFinalParams,
    CryptoMacOperation, CryptoRandomGenerateParams, CryptoX963Sha256Params, RustletCtx, SEApdu,
    SEApduHeader, Scp03LoadKeyParams, SddispatchOpcode, INS_INSTALL, SDDISPATCH_BOOL_TRUE,
    SDDISPATCH_CLA,
};
use sha2::{Digest, Sha256};

#[path = "rpc.rs"]
mod rpc;
#[path = "syscall_memory.rs"]
mod syscall_memory;
pub(crate) use rpc::complete_rpc;

use crate::apdu_manager;
use crate::fae_runtime;
use crate::kernel_cell::{KernelCell, KernelRefMut};
use crate::registry::format as registry_persistence;
use crate::registry::objects::{
    InstanceObjectState, KeyObjectState, KeyObjectType, ObjectView, PackageObjectState,
    RegistryError, RegistryResult, SecurityDomainObjectState,
    DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY,
};
pub use crate::registry::objects::{ManagedObjectKind, SecurityDomainObjectBackend};
use crate::registry::payload as registry_payload;
#[cfg(test)]
use crate::registry::recovery::validate_security_domain_registry_topology;
pub use crate::registry::state::dynamic_package_load_in_progress;
use crate::registry::state::{DynamicLoadContext, DYNAMIC_LOAD_CONTEXT};
use crate::registry::storage::{
    persistent_registry_area_bytes, PERSISTENCE_PAGE_BUFFER, PERSISTENCE_PAGE_BUFFER_SIZE,
};

#[cfg(oxide_se_kernel_app_module = "registry-test")]
pub(crate) use crate::registry::write_fault as registry_write_fault;

struct LoadedApp {
    registry: AppRegistryReference,
    loaded_fae: fae_runtime::LoadedFae,
    allocator: oxi_core::core::HeapAllocatorState,
    allocator_metadata: AllocatorMetadata,
}

struct AllocatorMetadata {
    ptr: *mut u8,
    len: usize,
    layout: Layout,
}

impl AllocatorMetadata {
    fn allocate(len: usize) -> Option<Self> {
        let layout = Layout::from_size_align(len, oxi_core::core::ALLOCATION_GRANULE).ok()?;
        let ptr = oxi_core::core::alloc(layout);
        if ptr.is_null() {
            None
        } else {
            Some(Self { ptr, len, layout })
        }
    }

    fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr
    }

    const fn len(&self) -> usize {
        self.len
    }
}

// SAFETY: privileged owner-core state; IRQ handlers never access it.
static SELECTED_APP: KernelCell<Option<LoadedApp>> = unsafe { KernelCell::new(None) };
// Invariant: the active Rustlet Security Domain remains resident here while an
// ordinary Rustlet occupies SELECTED_APP. Its volatile SCP state must never be
// reconstructed from the registry between unwrap, dispatch, and wrap.
// SAFETY: privileged owner-core state; IRQ handlers never access it.
static SELECTED_SECURITY_DOMAIN: KernelCell<Option<LoadedApp>> = unsafe { KernelCell::new(None) };
// SAFETY: privileged owner-core state; IRQ handlers never access it.
static ACTIVE_SECURITY_DOMAIN_SLOT: KernelCell<Option<usize>> = unsafe { KernelCell::new(None) };
// SAFETY: privileged owner-core state; IRQ handlers never access it.
static ACTIVE_APP_CALL: KernelCell<Option<ActiveAppCall>> = unsafe { KernelCell::new(None) };
// Capture the called registry slot before entry: SVC must not reborrow the
// selected runtime while SDDISPATCH holds its exclusive loan.
// SAFETY: privileged owner-core state; IRQ handlers never access it.
static SD_DISPATCH_INSTANCE: KernelCell<Option<usize>> = unsafe { KernelCell::new(None) };
impl AppRegistryReference {
    fn pending_install(package: usize) -> Self {
        Self::PendingInstall { package }
    }

    fn from_instance(instance: usize) -> Option<Self> {
        let registry_guard = crate::registry::read();
        let registry = &*registry_guard;
        let instance_object = registry.resolve(instance)?;
        let package_aid = instance_object.package_aid()?;
        let package = registry
            .find_index(
                &instance_object.parent_sd_aid,
                ManagedObjectKind::Package,
                &package_aid,
            )
            .or_else(|| {
                registry.find_index(
                    &top_level_parent_sd_aid(),
                    ManagedObjectKind::Package,
                    &package_aid,
                )
            })?;
        Some(Self::Installed { package, instance })
    }

    fn package_index(self) -> usize {
        match self {
            Self::PendingInstall { package, .. } | Self::Installed { package, .. } => package,
        }
    }

    fn instance_index(self) -> Option<usize> {
        match self {
            Self::PendingInstall { .. } => None,
            Self::Installed { instance, .. } => Some(instance),
        }
    }

    fn package_object(self) -> Option<crate::registry::operations::ObjectRead> {
        crate::registry::operations::read_object(|registry| registry.resolve(self.package_index()))
    }

    fn instance_object(self) -> Option<crate::registry::operations::ObjectRead> {
        crate::registry::operations::read_object(|registry| {
            registry.resolve(self.instance_index()?)
        })
    }

    fn security_domain_aid(self) -> Option<Aid> {
        match self {
            Self::PendingInstall { .. } => None,
            Self::Installed { .. } => Some(self.instance_object()?.parent_sd_aid),
        }
    }

    fn package_aid(self) -> Option<Aid> {
        Some(self.package_object()?.object_aid)
    }

    fn applet_aid(self) -> Option<Aid> {
        self.package_object()?.package_applet_aid()
    }

    fn instance_aid(self) -> Option<Aid> {
        match self {
            Self::PendingInstall { .. } => None,
            Self::Installed { .. } => Some(self.instance_object()?.object_aid),
        }
    }

    fn fae(self) -> Option<&'static [u8]> {
        self.package_object()?.package_binary_code()
    }

    fn identity(self) -> Option<(Aid, Aid, Aid, Aid)> {
        Some((
            self.security_domain_aid()?,
            self.package_aid()?,
            self.applet_aid()?,
            self.instance_aid()?,
        ))
    }

    /// Extracts persisted state directly into the shared page, ending the registry
    /// loan before the Rustlet can issue a mutating syscall.
    fn stage_state(self, context: &mut RustletCtx) -> bool {
        RESTORE_REFERENCE.set(Some(self));
        let instance = self.instance_object();
        match instance.as_ref() {
            Some(object) => object.stage_state_into(context),
            None => context.stage_state(&[]),
        }
    }

    fn is_valid(self) -> bool {
        self.package_object().is_some()
            && match self {
                Self::PendingInstall { .. } => true,
                Self::Installed { .. } => self.instance_object().is_some(),
            }
    }

    fn references_slot(self, slot: usize) -> bool {
        self.package_index() == slot || self.instance_index() == Some(slot)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AppRegistryReference {
    /// Temporary identity used only while `INSTALL [for install]` creates the
    /// instance that will become the stable registry reference.
    PendingInstall { package: usize },
    /// Normal selected-object identity. Both slot numbers remain stable until
    /// the corresponding objects are deleted.
    Installed { package: usize, instance: usize },
}

#[derive(Clone, Copy)]
struct ActiveAppCall {
    caller: Aid,
    transport: *mut apdu_manager::TransportApdu,
    shared_buffer: *mut RustletCtx,
    shared_window: oxi_core::core::isolation::AppMemoryWindow,
    text_window: oxi_core::core::isolation::AppMemoryWindow,
    data_window: oxi_core::core::isolation::AppMemoryWindow,
    stack_window: oxi_core::core::isolation::AppMemoryWindow,
}

// SAFETY: invocation-local state on the single privileged dispatcher.
static RESTORE_REFERENCE: KernelCell<Option<AppRegistryReference>> =
    unsafe { KernelCell::new(None) };
static RESTORE_PHASE: KernelCell<u8> = unsafe { KernelCell::new(0) };
pub(crate) fn rollback_restore_completed() -> bool {
    RESTORE_PHASE.get() == 3
}

unsafe extern "C" fn reset_rollback_heap_syscall(_: usize, _: usize, _: usize, _: usize) -> usize {
    let Some(call) = active_app_call() else {
        return 0x6985;
    };
    if RESTORE_PHASE.get() != 1 || RESTORE_REFERENCE.get().is_none() {
        return 0x6985;
    }
    // The session snapshot is in the gate, outside the private heap being scrubbed.
    let _lease = unsafe { crate::shared_page::Lease::syscall() };
    let ctx = unsafe { &*call.shared_buffer };
    if ctx.try_state_bytes().is_none() {
        return 0x6700;
    }
    if !unsafe { oxi_core::core::syscall::scrub_and_reset_app_allocator() } {
        return 0x6f00;
    }
    RESTORE_PHASE.set(2);
    0x9000
}

unsafe extern "C" fn load_rollback_state_syscall(_: usize, _: usize, _: usize, _: usize) -> usize {
    let Some(call) = active_app_call() else {
        return 0x6985;
    };
    if RESTORE_PHASE.get() != 2 {
        return 0x6985;
    }
    let Some(reference) = RESTORE_REFERENCE.get() else {
        return 0x6985;
    };
    // End the session-byte loan before publishing the restored transaction snapshot.
    let _lease = unsafe { crate::shared_page::Lease::syscall() };
    let ctx = unsafe { &mut *call.shared_buffer };
    ctx.clear_state();
    if !reference.stage_state(ctx) {
        return 0x6700;
    }
    RESTORE_PHASE.set(3);
    0x9000
}

struct RunningSEApdu<'a> {
    transport: &'a mut apdu_manager::TransportApdu,
    shared_buffer: &'a mut RustletCtx,
    _page: crate::shared_page::Lease,
}

#[derive(Clone, Copy)]
enum CipherMode {
    Encrypt,
    Decrypt,
}

#[derive(Clone, Copy)]
enum CipherAlgorithm {
    Aes128CbcNoPadding,
    Aes256CbcNoPadding,
    Aes128CbcIso9797M2,
    Aes256CbcIso9797M2,
    Aes128EcbNoPadding,
    Aes256EcbNoPadding,
}

#[derive(Clone, Copy)]
enum RandomAlgorithm {
    SecureRandom,
}

#[derive(Clone, Copy)]
enum MacAlgorithm {
    AesCmac,
}

struct ActiveAppCallGuard;

impl ActiveAppCallGuard {
    /// Bounds the raw SVC context by the live transport and image borrows.
    #[inline(always)]
    fn with_transport<R>(
        apdu: &mut apdu_manager::Apdu<'_>,
        loaded: &fae_runtime::LoadedFae,
        run: impl FnOnce(&mut apdu_manager::Apdu<'_>) -> R,
    ) -> R {
        let _guard = Self::install(apdu, loaded);
        run(apdu)
    }

    #[inline(always)]
    fn with_shared<R>(
        loaded: &fae_runtime::LoadedFae,
        sd_dispatch: Option<usize>,
        run: impl FnOnce() -> R,
    ) -> R {
        let _guard = Self::install_shared_only(loaded);
        SD_DISPATCH_INSTANCE.set(sd_dispatch);
        run()
    }

    fn assert_vacant() {
        // SAFETY: only the owner core installs/retires this ABI context. The
        // short tag inspection retains no reference across Rustlet execution.
        assert!(
            { (ACTIVE_APP_CALL.borrow()).is_none() },
            "nested Rustlet invocation context"
        );
    }

    fn install(apdu: &mut apdu_manager::Apdu<'_>, loaded: &fae_runtime::LoadedFae) -> Self {
        Self::assert_vacant();
        let transport = apdu.transport_ptr();
        let shared_buffer = &loaded.shared_buffer();
        let shared_start = shared_buffer.as_mut_ptr() as usize;
        set_active_app_call(Some(ActiveAppCall {
            caller: loaded.instance_aid,
            transport,
            shared_buffer: shared_buffer.as_mut_ptr(),
            shared_window: oxi_core::core::isolation::AppMemoryWindow {
                start: shared_start,
                len: rustlet_runtime::APDU_SHARED_REGION_SIZE,
            },
            text_window: loaded.text_window(),
            data_window: loaded.data_window(),
            stack_window: loaded.stack_window(),
        }));
        RESTORE_PHASE.set(if loaded.needs_persistent_restore() {
            1
        } else {
            0
        });

        Self
    }

    fn install_shared_only(loaded: &fae_runtime::LoadedFae) -> Self {
        Self::assert_vacant();
        let shared_buffer = &loaded.shared_buffer();
        let shared_start = shared_buffer.as_mut_ptr() as usize;
        set_active_app_call(Some(ActiveAppCall {
            caller: loaded.instance_aid,
            transport: core::ptr::null_mut(),
            shared_buffer: shared_buffer.as_mut_ptr(),
            shared_window: oxi_core::core::isolation::AppMemoryWindow {
                start: shared_start,
                len: rustlet_runtime::APDU_SHARED_REGION_SIZE,
            },
            text_window: loaded.text_window(),
            data_window: loaded.data_window(),
            stack_window: loaded.stack_window(),
        }));
        RESTORE_PHASE.set(if loaded.needs_persistent_restore() {
            1
        } else {
            0
        });

        Self
    }
}

impl Drop for ActiveAppCallGuard {
    fn drop(&mut self) {
        set_active_app_call(None);
    }
}

pub fn initialize() {
    crate::registry::init_on_reset::<RegistryBootPolicy>();
}

struct RegistryBootPolicy;
impl crate::registry::boot::BootPolicy for RegistryBootPolicy {
    fn install_runtime_hooks() {
        oxi_core::core::isolation::initialize_runtime_hooks();
        oxi_core::core::isolation::install_exit_observer(app_exit_observer);
        oxi_core::core::syscall::install_bindings(&RUSTLET_SERVICE_SYSCALLS);
    }
    fn activate_root(aid: Aid) {
        set_active_security_domain_instance_aid(aid);
    }
    fn bootstrap_root() {
        bootstrap_root_security_domain();
    }
    fn bootstrap_plan() {
        bootstrap_predeployed_plan();
    }
}

const RUSTLET_SERVICE_SYSCALLS: [oxi_core::core::syscall::SyscallBinding; 14] = [
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::RuntimeSyscall::RpcCall as u8,
        handler: rpc::call_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::RuntimeSyscall::ResetRollbackHeap as u8,
        handler: reset_rollback_heap_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::RuntimeSyscall::LoadRollbackState as u8,
        handler: load_rollback_state_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::APDU_SET_INCOMING_AND_RECEIVE,
        handler: apdu_set_incoming_and_receive_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::APDU_SET_OUTGOING,
        handler: apdu_set_outgoing_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::APDU_SET_OUTGOING_LENGTH,
        handler: apdu_set_outgoing_length_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_CIPHER_DO_FINAL,
        handler: crypto_cipher_do_final_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_RANDOM_GENERATE,
        handler: crypto_random_generate_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_MAC_DO_FINAL,
        handler: crypto_mac_do_final_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::SECURITY_DOMAIN_LOAD_SCP03_KEY,
        handler: security_domain_load_scp03_key_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_EC_GENERATE_KEYPAIR,
        handler: crypto_ec_generate_keypair_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_ECDH_DO_FINAL,
        handler: crypto_ecdh_do_final_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_HKDF_SHA256,
        handler: crypto_hkdf_sha256_syscall,
    },
    oxi_core::core::syscall::SyscallBinding {
        number: rustlet_runtime::syscall_abi::CRYPTO_X963_SHA256,
        handler: crypto_x963_sha256_syscall,
    },
];

// Set only by an abnormal SD hook return, never by an ordinary error SW.
// SAFETY: privileged owner-core state; IRQ handlers never access it.
static SD_HOOK_FAILED: KernelCell<bool> = unsafe { KernelCell::new(false) };
static SD_HOOK_FAULT_STATUS: KernelCell<Option<apdu_manager::ApduStatus>> =
    unsafe { KernelCell::new(None) };

/// An SD crash invalidates every staged APDU participant.
/// Finalization preserves the original fault SW while abandoning publication.
pub(crate) fn abort_registry_apdu() {
    // Invariant: only the privileged APDU dispatcher owns this transaction.
    {
        crate::registry::request_abort();
    }
}

pub(crate) fn sd_hook_fault_status() -> Option<apdu_manager::ApduStatus> {
    SD_HOOK_FAULT_STATUS.get()
}

pub(crate) fn sd_hook_failed() -> bool {
    // Invariant: access is serialized by the privileged APDU dispatcher.
    {
        *SD_HOOK_FAILED.borrow()
    }
}

/// Opens the transaction owned by the complete external APDU exchange.
pub(crate) fn begin_registry_apdu() -> RegistryResult {
    SD_HOOK_FAULT_STATUS.set(None);
    // Invariant: each external APDU starts a new failure scope.
    {
        *SD_HOOK_FAILED.borrow_mut() = false;
    }
    crate::registry::begin_transaction()
}

fn registry_mut() -> crate::registry::Mutation {
    // Invariant: registry access is serialized by the single-core APDU dispatcher.
    crate::registry::edit()
}

/// Publishes once after every participant has staged its mutations.
/// Runtime/session policy follows registry finalization; errors restore RAM but
/// do not claim byte-for-byte flash rollback. The caller must distinguish an
/// abandoned transaction from retained changes (which may require no write).
pub(crate) fn finish_registry_apdu() -> RegistryResult<crate::registry::transaction::CommitOutcome>
{
    finish_registry_apdu_outcome(crate::registry::commit_transaction())
}

#[cfg(test)]
fn finish_registry_apdu_with(
    publish: impl FnOnce() -> RegistryResult,
) -> RegistryResult<crate::registry::transaction::CommitOutcome> {
    finish_registry_apdu_outcome(crate::registry::transaction::commit_transaction_with(
        publish,
    ))
}

fn finish_registry_apdu_outcome(
    outcome: RegistryResult<crate::registry::transaction::CommitOutcome>,
) -> RegistryResult<crate::registry::transaction::CommitOutcome> {
    if !matches!(
        outcome,
        Ok(crate::registry::transaction::CommitOutcome::Retained)
    ) {
        // A failed command cannot leave a partially accepted LOAD resumable.
        clear_dynamic_load_context();
        // Resident heaps may describe the abandoned view; force reconstruction.
        set_selected_app(None);
        set_selected_security_domain(None);
        {
            *ACTIVE_SECURITY_DOMAIN_SLOT.borrow_mut() = None;
        }
        crate::security_domain::retire_failed_session();
    }
    outcome
}

/// Runtime policy attached to registry mechanisms, with no userland calls.
pub(crate) struct RegistryRuntimePolicy;

impl crate::registry::savepoint::RollbackObserver for RegistryRuntimePolicy {
    fn before_rollback(view: &crate::registry::savepoint::RollbackView) {
        // A same-identity rollback restores the registry but leaves the cached
        // object's persistent state stale. Rebuild it before the next handler.
        // Do not enter userland here, or discard legitimate secure-channel progress.
        for selected in [&SELECTED_APP, &SELECTED_SECURITY_DOMAIN] {
            if let Some(app) = selected.borrow().as_ref() {
                if app
                    .registry
                    .instance_index()
                    .is_some_and(|slot| view.touches(slot))
                {
                    app.loaded_fae.request_persistent_restore();
                }
            }
        }
    }

    fn after_rollback(invalidated: crate::registry::savepoint::InvalidatedSlots) {
        if !invalidated.iter().any(|changed| *changed) {
            return;
        }
        // A restored slot must never retarget a handle created in the abandoned scope.
        // Do not call SD hooks during rollback: those could mutate the journal again.
        let invalidate_app = SELECTED_APP.borrow().as_ref().is_some_and(|app| {
            invalidated
                .iter()
                .enumerate()
                .any(|(slot, changed)| *changed && app.registry.references_slot(slot))
        });
        if invalidate_app {
            set_selected_app(None);
        }
        // Invariant: all registry/selection transitions run on the single APDU dispatcher.
        {
            if (SELECTED_SECURITY_DOMAIN.borrow())
                .as_ref()
                .is_some_and(|sd| {
                    invalidated
                        .iter()
                        .enumerate()
                        .any(|(slot, changed)| *changed && sd.registry.references_slot(slot))
                })
            {
                set_selected_security_domain(None);
            }
            if (*ACTIVE_SECURITY_DOMAIN_SLOT.borrow()).is_some_and(|slot| invalidated[slot]) {
                *ACTIVE_SECURITY_DOMAIN_SLOT.borrow_mut() = None;
                crate::security_domain::retire_failed_session();
            }
        }
    }
}

impl crate::registry::transaction::OperationOwner for RegistryRuntimePolicy {
    fn begin_owned_transaction() -> RegistryResult {
        begin_registry_apdu()
    }

    fn finish_owned_transaction() -> RegistryResult<crate::registry::transaction::CommitOutcome> {
        finish_registry_apdu()
    }
}

/// Compatibility name for the registry-owned scope with runtime notifications.
pub(crate) type RegistryOperationScope =
    crate::registry::savepoint::OperationScope<RegistryRuntimePolicy>;

/// Join or temporarily own a registry transaction using the APDU runtime policy.
pub(crate) fn registry_operation<T>(
    operation: impl FnOnce() -> RegistryResult<T>,
) -> RegistryResult<T> {
    crate::registry::transaction::run_operation::<RegistryRuntimePolicy, T>(operation)
}

/// Starts one GP package LOAD transaction after `INSTALL [for load]`.
///
/// The package code is reserved in the mutable persistence area immediately,
/// but it becomes reachable only after the last `LOAD` block validates the
/// announced size and SHA-256 hash, then publishes a new registry snapshot.
pub fn prepare_dynamic_package_load(
    authority_aid: Aid,
    target_sd_aid: Aid,
    package_aid: Aid,
    protected: bool,
    expected_size: usize,
    expected_hash: [u8; 32],
) -> apdu_manager::ApduStatus {
    if expected_size == 0 || expected_size > 64 * 1024 {
        return apdu_manager::ApduStatus::wrong_data();
    }
    // Invariant: a new INSTALL [for load] aborts any unfinished LOAD. Since no
    // BOSS snapshot references unfinished C0DE pages, discarding the volatile
    // context is equivalent to recovering from a reset before final LOAD.
    clear_dynamic_load_context();
    if let Err(error) = require_managed_object_authority(&authority_aid, &target_sd_aid) {
        return error.status();
    }
    if find_object_by_kind_and_aid_raw(ManagedObjectKind::SecurityDomain, &target_sd_aid).is_none()
    {
        return apdu_manager::ApduStatus::referenced_data_not_found();
    }

    // Publication rollback removes a newly created entry, never an existing package.
    if find_object_by_kind_and_aid_raw(ManagedObjectKind::Package, &package_aid).is_some() {
        return RegistryError::InvalidState.status();
    }

    let payload = match registry_payload::prepare_payload(expected_size) {
        Ok(payload) => payload,
        Err(error) => return error.status(),
    };
    {
        *DYNAMIC_LOAD_CONTEXT.borrow_mut() = Some(DynamicLoadContext {
            authority_aid,
            target_sd_aid,
            package_aid,
            protected,
            expected_hash,
            next_block_number: 0,
            payload,
        });
    }
    apdu_manager::ApduStatus::success()
}

/// Appends one GP `LOAD` block to the active package-load transaction.
///
/// Invariants enforced here:
/// - block numbers are consecutive and start at zero;
/// - total received bytes never exceed the size announced by install-for-load;
/// - only the final block may publish the package;
/// - finalization requires exact size and exact SHA-256 hash match.
pub fn append_dynamic_package_load_block(
    authority_aid: Aid,
    protected: bool,
    block_number: u8,
    is_last_block: bool,
    data: &[u8],
) -> apdu_manager::ApduStatus {
    if data.is_empty() {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }

    let mut context = match DYNAMIC_LOAD_CONTEXT.get() {
        Some(context) => context,
        None => return apdu_manager::ApduStatus::conditions_not_satisfied(),
    };
    // Invariant: LOAD is a continuation of the accepted INSTALL [for load].
    // The stream must remain under the same Security Domain authority and the
    // same clear/protected channel posture until the final block publishes the
    // package. A clear block may not complete a protected SCP03 load and a
    // protected block may not be spliced into a clear development load.
    if context.authority_aid != authority_aid || context.protected != protected {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::security_status_not_satisfied();
    }
    if block_number != context.next_block_number {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }
    let data = if block_number == 0 {
        let Some((declared_len, payload)) = parse_gp_load_file_data_block_header(data) else {
            clear_dynamic_load_context();
            return apdu_manager::ApduStatus::wrong_data();
        };
        if declared_len != context.payload.expected_size {
            clear_dynamic_load_context();
            return apdu_manager::ApduStatus::wrong_data();
        }
        payload
    } else {
        data
    };
    if context
        .payload
        .bytes_received
        .checked_add(data.len())
        .map(|received| received > context.payload.expected_size)
        .unwrap_or(true)
    {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }

    let page_size = crate::registry::physical::logical_page_size();
    if page_size == 0 || page_size > PERSISTENCE_PAGE_BUFFER_SIZE {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    }
    let mut page_guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    let page = &mut *page_guard;
    if !registry_payload::append_payload(&mut context.payload, page_size, page, data) {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::memory_failure();
    }
    if !is_last_block && context.next_block_number == u8::MAX {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }
    context.next_block_number = context.next_block_number.wrapping_add(1);
    {
        *DYNAMIC_LOAD_CONTEXT.borrow_mut() = Some(context);
    }

    drop(page_guard);
    if !is_last_block {
        return apdu_manager::ApduStatus::success();
    }
    finalize_dynamic_package_load(context)
}

fn parse_gp_load_file_data_block_header(data: &[u8]) -> Option<(usize, &[u8])> {
    if data.first().copied()? != 0xC4 {
        return None;
    }
    let first_len = *data.get(1)?;
    match first_len {
        0x00..=0x7F => Some((first_len as usize, data.get(2..)?)),
        0x81 => Some((*data.get(2)? as usize, data.get(3..)?)),
        0x82 => Some((
            u16::from_be_bytes([*data.get(2)?, *data.get(3)?]) as usize,
            data.get(4..)?,
        )),
        _ => None,
    }
}

fn finalize_dynamic_package_load(context: DynamicLoadContext) -> apdu_manager::ApduStatus {
    if context.payload.bytes_received != context.payload.expected_size {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }
    let Some(area_bytes) = persistent_registry_area_bytes() else {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::memory_failure();
    };
    let page_size = crate::registry::physical::logical_page_size();
    let mut page_guard = PERSISTENCE_PAGE_BUFFER.borrow_mut();
    let page = &mut *page_guard;
    let mut hasher = Sha256::new();
    registry_payload::update_sha256_from_payload_region(
        &context.payload,
        area_bytes,
        page,
        registry_persistence::OBJECT_BLOCK_HEADER_LEN,
        context.payload.expected_size,
        &mut hasher,
    );
    let digest = hasher.finalize();
    if digest[..] != context.expected_hash {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }

    let payload_in_block = registry_persistence::OBJECT_BLOCK_HEADER_LEN;
    let valid_fae =
        crate::fae_runtime::validate_fae_reader(context.payload.expected_size, |offset| {
            let absolute = payload_in_block.checked_add(offset)?;
            let page_index = absolute / page_size;
            let offset_in_page = absolute % page_size;
            if page_index == context.payload.current_page_index {
                page.get(offset_in_page).copied()
            } else {
                area_bytes
                    .get(context.payload.reserved_offset.checked_add(absolute)?)
                    .copied()
            }
        });
    if !valid_fae {
        clear_dynamic_load_context();
        return apdu_manager::ApduStatus::wrong_data();
    }

    let prepared =
        match registry_payload::finalize_payload(context.payload, area_bytes, page_size, page) {
            Ok(prepared) => prepared,
            Err(error) => {
                clear_dynamic_load_context();
                return error.status();
            }
        };

    drop(page_guard);
    // The registry stores the executable package as the C0DE payload slice. The
    // persistent header stays kernel metadata and is never part of the FAE image
    // handed to the Rustlet runtime. The maintained bitmap retains the reserved
    // pages during attachment; no pending partial page needs preserving now.
    registry_payload::complete_payload();
    let result = registry_operation(|| {
        registry_mut().insert_package_object(
            context.target_sd_aid,
            context.package_aid,
            context.package_aid,
            prepared.into_bytes(),
        )
    });
    if result.is_err() {
        registry_payload::discard_prepared_payload(context.payload);
    }
    registry_result_status(result)
}

fn clear_dynamic_load_context() {
    registry_payload::abandon_payload();
}

/// Cancels any in-progress dynamic package load.
///
/// Invariant: because unfinished C0DE pages are not referenced by a committed
/// BOSS snapshot, cancellation only drops volatile state. The flash span is
/// later recyclable as an invalid or unreferenced object block.
pub fn cancel_dynamic_package_load() {
    clear_dynamic_load_context();
}

fn bootstrap_root_security_domain() {
    let root_package_aid = crate::predeployment::root_package_aid();
    let root_instance_aid = crate::predeployment::root_instance_aid();
    match crate::predeployment::root_backend() {
        crate::predeployment::RootSecurityDomainBackend::RustletSecurityDomainProxy => {
            let status = install_instance_in_parent(
                &top_level_parent_sd_aid(),
                &root_package_aid,
                &root_package_aid,
                &root_instance_aid,
                crate::predeployment::root_privileges(),
                crate::predeployment::root_install_payload(),
                InstallHandlerPayload::Encode {
                    privileges: crate::predeployment::root_privileges(),
                    install_parameters: crate::predeployment::root_install_payload(),
                },
            );
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                panic!(
                    "root Rustlet Security Domain bootstrap failed: {:02x}{:02x}",
                    status.sw1, status.sw2
                );
            }
            if find_runtime_state_object_by_aid(&top_level_parent_sd_aid(), &root_instance_aid)
                .is_none()
            {
                let save_status = save_selected_instance_state(
                    &top_level_parent_sd_aid(),
                    &root_package_aid,
                    &root_package_aid,
                    &root_instance_aid,
                    Some(crate::predeployment::root_privileges()),
                );
                if save_status.sw1 != 0x90 || save_status.sw2 != 0x00 {
                    panic!(
                        "root Rustlet Security Domain state save failed: {:02x}{:02x}",
                        save_status.sw1, save_status.sw2
                    );
                }
            }
            set_active_security_domain_instance_aid(root_instance_aid);
            activate_root_rustlet_security_domain(root_instance_aid);
        }
        crate::predeployment::RootSecurityDomainBackend::NullSecurityDomain => {
            bootstrap_kernel_side_security_domain_root(
                SecurityDomainObjectBackend::NullSecurityDomain,
                crate::predeployment::root_install_payload(),
            );
        }
        crate::predeployment::RootSecurityDomainBackend::KernelSecurityDomain => {
            bootstrap_kernel_side_security_domain_root(
                SecurityDomainObjectBackend::KernelSecurityDomain,
                crate::predeployment::root_install_payload(),
            );
        }
    }
}

fn activate_root_rustlet_security_domain(root_instance_aid: Aid) {
    let reference = {
        let registry_guard = crate::registry::read();
        let registry = &*registry_guard;
        let Some(instance) = registry.find_index(
            &top_level_parent_sd_aid(),
            ManagedObjectKind::SecurityDomain,
            &root_instance_aid,
        ) else {
            panic!("root Rustlet Security Domain instance is not registered");
        };
        let Some(reference) = AppRegistryReference::from_instance(instance) else {
            panic!("root Rustlet Security Domain package is not registered");
        };
        reference
    };
    let status = activate_registry_reference(reference);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        panic!(
            "root Rustlet Security Domain activation failed: {:02x}{:02x}",
            status.sw1, status.sw2
        );
    }
    let Some(selected_app) = selected_app_mut() else {
        panic!("root Rustlet Security Domain activation did not select an app");
    };
    let Some(instance) = reference.instance_object() else {
        panic!("root Rustlet Security Domain state is not registered");
    };
    if !selected_app
        .loaded_fae
        .shared_buffer()
        .stage_state_from_object(&instance)
    {
        panic!("root Rustlet Security Domain state does not fit in the shared buffer");
    }
    drop(selected_app);
    promote_selected_app_to_security_domain();
}

fn bootstrap_kernel_side_security_domain_root(
    backend: SecurityDomainObjectBackend,
    install_payload: &[u8],
) {
    let root_package_aid = crate::predeployment::root_package_aid();
    let root_instance_aid = crate::predeployment::root_instance_aid();
    let status = install_kernel_side_security_domain_instance(
        backend,
        top_level_parent_sd_aid(),
        root_package_aid,
        root_instance_aid,
        install_payload,
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        panic!(
            "kernel Security Domain bootstrap install failed: {:02x}{:02x}",
            status.sw1, status.sw2
        );
    }
    set_active_security_domain_instance_aid(root_instance_aid);
}

fn bootstrap_predeployed_plan() {
    provision_predeployed_keys(&crate::predeployment::root_instance_aid());
    // The build script orders parents before children. Provision each parent's
    // effective keys before a child can inherit them; explicit keys override
    // inherited keys with the same identity without allocating another buffer.
    for security_domain in crate::predeployment::predeployed_security_domains() {
        let status = match security_domain.backend {
            crate::predeployment::RootSecurityDomainBackend::NullSecurityDomain => {
                install_kernel_side_security_domain_instance(
                    SecurityDomainObjectBackend::NullSecurityDomain,
                    security_domain.parent_instance_aid,
                    security_domain.package_aid,
                    security_domain.instance_aid,
                    security_domain.install_payload,
                )
            }
            crate::predeployment::RootSecurityDomainBackend::KernelSecurityDomain => {
                install_kernel_side_security_domain_instance(
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    security_domain.parent_instance_aid,
                    security_domain.package_aid,
                    security_domain.instance_aid,
                    security_domain.install_payload,
                )
            }
            crate::predeployment::RootSecurityDomainBackend::RustletSecurityDomainProxy => {
                install_instance_in_parent(
                    &security_domain.parent_instance_aid,
                    &security_domain.package_aid,
                    &security_domain.package_aid,
                    &security_domain.instance_aid,
                    &security_domain.privileges,
                    security_domain.install_payload,
                    InstallHandlerPayload::Encode {
                        privileges: &security_domain.privileges,
                        install_parameters: security_domain.install_payload,
                    },
                )
            }
        };
        if status.sw1 != 0x90 || status.sw2 != 0x00 {
            panic!(
                "predeployment security domain install failed: {:02x}{:02x}",
                status.sw1, status.sw2
            );
        }
        provision_predeployed_keys(&security_domain.instance_aid);
    }

    for instance in crate::predeployment::predeployed_rustlet_instances() {
        let status = install_instance_in_parent(
            &instance.parent_instance_aid,
            &instance.package_aid,
            &instance.applet_aid,
            &instance.instance_aid,
            &[0x00, 0x00, 0x00],
            instance.install_parameters,
            InstallHandlerPayload::Encode {
                privileges: &[0x00, 0x00, 0x00],
                install_parameters: instance.install_parameters,
            },
        );
        if status.sw1 != 0x90 || status.sw2 != 0x00 {
            panic!(
                "predeployment rustlet install failed: {:02x}{:02x}",
                status.sw1, status.sw2
            );
        }
    }
}

fn provision_predeployed_keys(owner: &Aid) {
    for key in crate::predeployment::predeployed_keys() {
        if key.parent_instance_aid != *owner {
            continue;
        }
        let usage = match key.usage {
            crate::predeployment::PredeployedKeyUsage::Enc => {
                crate::security_domain::Scp03KeyUsage::Enc
            }
            crate::predeployment::PredeployedKeyUsage::Mac => {
                crate::security_domain::Scp03KeyUsage::Mac
            }
        };
        let inserted = match key.key_type {
            crate::predeployment::PredeployedKeyType::Scp03Static => upsert_scp03_key_object(
                key.parent_instance_aid,
                key.key_version,
                key.key_id,
                usage,
                key.material,
            ),
        };
        if inserted.is_err() {
            panic!("predeployment key insertion failed");
        }
    }
}

pub fn select_aid(aid: &[u8]) -> apdu_manager::ApduStatus {
    let instance_aid = Aid::new(aid);
    let Some(instance) = find_visible_object_by_aid(&instance_aid) else {
        return apdu_manager::ApduStatus::file_not_found();
    };
    if !instance.may_select() {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    }
    if is_security_domain_kind(instance.object_kind) {
        set_active_security_domain_instance_aid(instance.object_aid);
    }
    let Some(instance_index) = registry_index_for_object(&instance) else {
        return apdu_manager::ApduStatus::file_not_found();
    };
    let Some(reference) = AppRegistryReference::from_instance(instance_index) else {
        return if is_security_domain_kind(instance.object_kind) {
            apdu_manager::ApduStatus::success()
        } else {
            apdu_manager::ApduStatus::file_not_found()
        };
    };

    if let Some(selected_app) = selected_app_mut() {
        if selected_app.registry == reference {
            if !selected_app
                .loaded_fae
                .shared_buffer()
                .stage_state_from_object(&instance)
            {
                return apdu_manager::ApduStatus::wrong_length();
            }
            return apdu_manager::ApduStatus::success();
        }
    }

    let status = activate_registry_reference(reference);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return status;
    }

    let Some(selected_app) = selected_app_mut() else {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    };
    if !selected_app
        .loaded_fae
        .shared_buffer()
        .stage_state_from_object(&instance)
    {
        drop(selected_app);
        set_selected_app(None);
        return apdu_manager::ApduStatus::wrong_length();
    }

    apdu_manager::ApduStatus::success()
}

#[allow(dead_code)]
pub fn install_instance_in_security_domain(
    parent_sd_aid: &Aid,
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    install_parameters: &[u8],
) -> apdu_manager::ApduStatus {
    install_instance_in_parent(
        parent_sd_aid,
        package_aid,
        applet_aid,
        instance_aid,
        privileges,
        install_parameters,
        InstallHandlerPayload::Encode {
            privileges,
            install_parameters,
        },
    )
}

pub fn install_instance_in_security_domain_from_current_apdu(
    parent_sd_aid: &Aid,
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    install_parameters: &[u8],
    header: rustlet_runtime::RustletApduHeader,
    incoming_len: usize,
) -> apdu_manager::ApduStatus {
    install_instance_in_parent(
        parent_sd_aid,
        package_aid,
        applet_aid,
        instance_aid,
        privileges,
        install_parameters,
        InstallHandlerPayload::CurrentApdu {
            header,
            incoming_len,
        },
    )
}

enum InstallHandlerPayload<'a> {
    Encode {
        privileges: &'a [u8],
        install_parameters: &'a [u8],
    },
    CurrentApdu {
        header: rustlet_runtime::RustletApduHeader,
        incoming_len: usize,
    },
}

fn install_instance_in_parent(
    parent_sd_aid: &Aid,
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    _install_parameters: &[u8],
    install_payload: InstallHandlerPayload<'_>,
) -> apdu_manager::ApduStatus {
    let package_index =
        match pending_registry_reference_for_install(parent_sd_aid, package_aid, applet_aid) {
            Ok(index) => index,
            Err(error) => return error.status(),
        };
    let reference = AppRegistryReference::pending_install(package_index);

    if selected_app_matches_install_target(parent_sd_aid, package_aid, applet_aid) {
        set_selected_app(None);
    }

    {
        let activation_status = activate_registry_reference(reference);
        if activation_status.sw1 != 0x90 || activation_status.sw2 != 0x00 {
            activation_status
        } else {
            let result = match install_payload {
                InstallHandlerPayload::Encode {
                    privileges,
                    install_parameters,
                } => {
                    // Invariant: synthetic INSTALL payloads are encoded directly
                    // in the shared Rustlet context. Do not stage them through
                    // TransportApdu.
                    dispatch_install_handler_encoded(|out| {
                        encode_install_for_install_data(
                            out,
                            package_aid,
                            applet_aid,
                            instance_aid,
                            privileges,
                            install_parameters,
                        )
                    })
                }
                InstallHandlerPayload::CurrentApdu {
                    header,
                    incoming_len,
                } => {
                    // Invariant: APDU-originated INSTALL already occupies the
                    // shared APDU buffer. Publish it as-is so install parameters
                    // are not recopied or destroyed by start/control
                    // initialization.
                    dispatch_install_handler_current_apdu(header, incoming_len)
                }
            };
            let status = from_abi_status(result.status);
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                set_selected_app(None);
                status
            } else {
                // Invariant: a successful INSTALL always leaves a registry
                // object behind. Some runtimes complete through their
                // termination gate rather than a normal function return, so the
                // APDU status is the authoritative result.
                let save_status = save_selected_instance_state(
                    parent_sd_aid,
                    package_aid,
                    applet_aid,
                    instance_aid,
                    Some(privileges),
                );
                if save_status.sw1 == 0x90 && save_status.sw2 == 0x00 {
                    set_selected_app(None);
                    status
                } else {
                    set_selected_app(None);
                    save_status
                }
            }
        }
    }
}

fn encode_install_for_install_data(
    out: &mut [u8],
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    install_parameters: &[u8],
) -> Option<usize> {
    let mut offset = 0usize;
    push_install_lv(out, &mut offset, package_aid.as_slice())?;
    push_install_lv(out, &mut offset, applet_aid.as_slice())?;
    push_install_lv(out, &mut offset, instance_aid.as_slice())?;
    push_install_lv(out, &mut offset, privileges)?;
    push_install_lv(out, &mut offset, install_parameters)?;
    // GlobalPlatform INSTALL [for install] always carries the INSTALL Token
    // LV, even when the active Security Domain policy requires no token.
    push_install_lv(out, &mut offset, &[])?;
    Some(offset)
}

fn push_install_lv(out: &mut [u8], offset: &mut usize, bytes: &[u8]) -> Option<()> {
    let len = u8::try_from(bytes.len()).ok()? as usize;
    let next = offset.checked_add(1 + len)?;
    if next > out.len() {
        return None;
    }
    out[*offset] = len as u8;
    let start = *offset + 1;
    out[start..start + len].copy_from_slice(bytes);
    *offset = next;
    Some(())
}

pub fn dispatch(apdu: &mut apdu_manager::Apdu<'_>) -> apdu_manager::ApduStatus {
    let operation = match RegistryOperationScope::begin(true) {
        Ok(scope) => scope,
        Err(error) => return error.status(),
    };
    let (result, registry_reference, ordinary_rustlet) = {
        let Some(mut selected_app) = selected_app_mut() else {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        };
        let registry_reference = selected_app.registry;
        selected_app.loaded_fae.instance_aid =
            registry_reference.instance_aid().unwrap_or(Aid::empty());
        if !registry_reference.is_valid() {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        }

        let handler = fae_runtime::Handler::Process;

        let selected_app = &mut *selected_app;
        let result = ActiveAppCallGuard::with_transport(apdu, &selected_app.loaded_fae, |apdu| {
            oxi_core::core::syscall::with_app_allocator(&mut selected_app.allocator, || {
                fae_runtime::call_handler(&selected_app.loaded_fae, handler, apdu, |ctx| {
                    registry_reference.stage_state(ctx)
                })
            })
        });

        // Invariant: registry slots remain stable while the Rustlet runs.
        // Keep only the compact slot reference live across the user call and
        // resolve its AIDs after return, rather than retaining four AID copies
        // on the kernel stack throughout every Rustlet syscall.
        (
            result,
            registry_reference,
            !selected_app.loaded_fae.is_security_domain(),
        )
    };

    let status = from_abi_status(result.status);
    let mut retain = result.returned_normally;
    let status = if result.returned_normally {
        let save_status = save_selected_instance_state_by_reference(registry_reference);
        if save_status.sw1 == 0x90 && save_status.sw2 == 0x00 {
            status
        } else {
            // Saving may fail before journaling this slot: its heap is still stale.
            if let Some(app) = current_selected_app_mut() {
                if app.registry.instance_index() == registry_reference.instance_index() {
                    app.loaded_fae.request_persistent_restore();
                }
            }
            retain = false;
            save_status
        }
    } else {
        retire_failed_dispatch(ordinary_rustlet);
        status
    };
    operation.finish(retain);
    status
}

// Keep fault-only teardown temporaries off the stack retained during Rustlet
// execution and nested crypto SVC. The invocation guards have already retired.
#[inline(never)]
fn retire_failed_dispatch(ordinary_rustlet: bool) {
    set_selected_app(None);
    if !ordinary_rustlet {
        abort_registry_apdu();
        set_selected_security_domain(None);
        ACTIVE_SECURITY_DOMAIN_SLOT.set(None);
        crate::security_domain::retire_failed_session();
    }
}

#[inline(never)]
fn save_selected_instance_state_by_reference(
    registry_reference: AppRegistryReference,
) -> apdu_manager::ApduStatus {
    let Some((security_domain_aid, package_aid, applet_aid, instance_aid)) =
        registry_reference.identity()
    else {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    };
    save_selected_instance_state(
        &security_domain_aid,
        &package_aid,
        &applet_aid,
        &instance_aid,
        None,
    )
}

pub fn dispatch_select(apdu: &mut apdu_manager::Apdu<'_>) -> apdu_manager::ApduStatus {
    let status = dispatch(apdu);
    if (status.sw1 == 0x6d && status.sw2 == 0x00) || (status.sw1 == 0x69 && status.sw2 == 0x85) {
        apdu_manager::ApduStatus::success()
    } else {
        status
    }
}

pub fn security_domain_authorize_install(
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    install_parameters: &[u8],
) -> apdu_manager::ApduStatus {
    let status =
        call_selected_security_domain_encoded(SddispatchOpcode::INSTALL_FOR_INSTALL, |out| {
            encode_sddispatch_install_for_install(
                package_aid,
                applet_aid,
                instance_aid,
                privileges,
                install_parameters,
                out,
            )
        });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return status;
    }

    match selected_security_domain_bool_response() {
        Some(true) => apdu_manager::ApduStatus::success(),
        Some(false) => apdu_manager::ApduStatus::security_status_not_satisfied(),
        None => from_abi_status(rustlet_runtime::ApduStatus::internal_error()),
    }
}

pub fn security_domain_authorize_load(package_aid: &Aid) -> apdu_manager::ApduStatus {
    call_selected_security_domain_encoded(SddispatchOpcode::INSTALL_FOR_LOAD, |out| {
        encode_sddispatch_install_for_load(package_aid, out)
    })
}

pub fn security_domain_delete_aid(aid: &Aid) -> apdu_manager::ApduStatus {
    call_selected_security_domain_encoded(SddispatchOpcode::DELETE_AID, |out| {
        encode_sddispatch_one_aid(aid, out)
    })
}

pub fn security_domain_authorize_put_key(
    key_version: u8,
    key_id: u8,
    key_data: &[u8],
) -> apdu_manager::ApduStatus {
    call_selected_security_domain_encoded(SddispatchOpcode::PUT_KEY, |out| {
        encode_sddispatch_put_key(key_version, key_id, key_data, out)
    })
}

pub fn security_domain_authorize_store_data(tag: u16, data: &[u8]) -> apdu_manager::ApduStatus {
    call_selected_security_domain_encoded(SddispatchOpcode::STORE_DATA, |out| {
        encode_sddispatch_store_data(tag, data, out)
    })
}

pub fn security_domain_authorize_set_status(
    target_kind: u8,
    target_state: u8,
    target_aid: &Aid,
) -> apdu_manager::ApduStatus {
    call_selected_security_domain_encoded(SddispatchOpcode::SET_STATUS, |out| {
        if out.len() < 2 {
            return None;
        }
        out[0] = target_kind;
        out[1] = target_state;
        encode_sddispatch_one_aid(target_aid, &mut out[2..]).map(|len| 2 + len)
    })
}

pub fn security_domain_supports_secure_channel_protocol(
    protocol: crate::security_domain::SecureChannelProtocol,
) -> bool {
    let build_mode = crate::core::target::secure_channel_mode();
    match protocol {
        crate::security_domain::SecureChannelProtocol::Scp03 => {
            if !build_mode.supports_scp03() {
                return false;
            }
            let status = call_selected_security_domain(SddispatchOpcode::SUPPORTS_SCP03, &[]);
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                return false;
            }
            selected_security_domain_bool_response().unwrap_or(false)
        }
        crate::security_domain::SecureChannelProtocol::Scp11(
            crate::core::scp11::Scp11Profile::A,
        ) => {
            if !build_mode.supports_scp11()
                || !crate::core::target::scp11_profiles()
                    .supports(crate::core::scp11::Scp11Profile::A)
            {
                return false;
            }
            let status = call_selected_security_domain(SddispatchOpcode::SUPPORTS_SCP11A, &[]);
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                return false;
            }
            selected_security_domain_bool_response().unwrap_or(false)
        }
        crate::security_domain::SecureChannelProtocol::Scp11(
            crate::core::scp11::Scp11Profile::B,
        ) => {
            if !build_mode.supports_scp11()
                || !crate::core::target::scp11_profiles()
                    .supports(crate::core::scp11::Scp11Profile::B)
            {
                return false;
            }
            let status = call_selected_security_domain(SddispatchOpcode::SUPPORTS_SCP11B, &[]);
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                return false;
            }
            selected_security_domain_bool_response().unwrap_or(false)
        }
        crate::security_domain::SecureChannelProtocol::Scp11(
            crate::core::scp11::Scp11Profile::C,
        ) => {
            if !build_mode.supports_scp11()
                || !crate::core::target::scp11_profiles()
                    .supports(crate::core::scp11::Scp11Profile::C)
            {
                return false;
            }
            let status = call_selected_security_domain(SddispatchOpcode::SUPPORTS_SCP11C, &[]);
            if status.sw1 != 0x90 || status.sw2 != 0x00 {
                return false;
            }
            selected_security_domain_bool_response().unwrap_or(false)
        }
    }
}

/// Asks the selected Rustlet Security Domain to claim one otherwise unknown
/// secure-channel establishment header.
pub fn security_domain_claims_delegated_secure_channel_command(
    header: crate::security_domain::DelegatedSecureChannelHeader,
) -> bool {
    let status = call_selected_security_domain(
        SddispatchOpcode::CLAIM_DELEGATED_SECURE_CHANNEL,
        &[header.cla, header.ins, header.p1, header.p2, header.p3],
    );
    status.sw1 == 0x90
        && status.sw2 == 0x00
        && selected_security_domain_bool_response().unwrap_or(false)
}

/// Dispatches one claimed establishment command without kernel protocol
/// decoding and returns the response length already staged in the shared page.
pub fn security_domain_handle_delegated_secure_channel_command(
    command: &crate::security_domain::SecureChannelEstablishmentCommand<'_>,
) -> Result<usize, apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(
        SddispatchOpcode::HANDLE_DELEGATED_SECURE_CHANNEL,
        |out| encode_sddispatch_delegated_secure_channel(command, out),
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_scp11_stage_oce_certificate(
    ca_key_version: u8,
    ca_key_id: u8,
    public_key: &[u8],
    subject_id: &[u8],
    discretionary_data: &[u8],
) -> Result<(), apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(
        SddispatchOpcode::SCP11_STAGE_OCE_CERTIFICATE,
        |out| {
            encode_sddispatch_scp11_oce_certificate(
                ca_key_version,
                ca_key_id,
                public_key,
                subject_id,
                discretionary_data,
                out,
            )
        },
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    Ok(())
}

pub fn security_domain_scp11a_mutual_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
) -> Result<usize, apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(
        SddispatchOpcode::SCP11A_MUTUAL_AUTHENTICATE,
        |out| {
            encode_sddispatch_scp11a_mutual_authenticate(
                ecka_key_version,
                ecka_key_id,
                request,
                out,
            )
        },
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_scp11b_internal_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
) -> Result<usize, apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(
        SddispatchOpcode::SCP11B_INTERNAL_AUTHENTICATE,
        |out| {
            encode_sddispatch_scp11b_internal_authenticate(
                ecka_key_version,
                ecka_key_id,
                request,
                out,
            )
        },
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_scp11c_mutual_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
) -> Result<usize, apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(
        SddispatchOpcode::SCP11C_MUTUAL_AUTHENTICATE,
        |out| {
            encode_sddispatch_scp11c_mutual_authenticate(
                ecka_key_version,
                ecka_key_id,
                request,
                out,
            )
        },
    );
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_current_security_level() -> Option<u8> {
    let status = call_selected_security_domain(SddispatchOpcode::CURRENT_SECURITY_LEVEL, &[]);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return None;
    }
    selected_security_domain_u8_response()
}

pub fn security_domain_secure_channel_open() -> bool {
    let status = call_selected_security_domain(SddispatchOpcode::SECURE_CHANNEL_OPEN, &[]);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return false;
    }
    selected_security_domain_bool_response().unwrap_or(false)
}

pub fn security_domain_current_mac_len() -> Option<usize> {
    let status = call_selected_security_domain(SddispatchOpcode::CURRENT_MAC_LEN, &[]);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return None;
    }
    selected_security_domain_u16_response().map(|value| value as usize)
}

pub fn security_domain_initialize_update(
    key_version: u8,
    key_id: u8,
    host_challenge: &[u8],
) -> Result<usize, apdu_manager::ApduStatus> {
    let status =
        call_selected_security_domain_encoded(SddispatchOpcode::INITIALIZE_UPDATE, |out| {
            encode_sddispatch_initialize_update(key_version, key_id, host_challenge, out)
        });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_external_authenticate(
    cla: u8,
    security_level: u8,
    p2: u8,
    authentication_data: &[u8],
) -> Result<u8, apdu_manager::ApduStatus> {
    let status =
        call_selected_security_domain_encoded(SddispatchOpcode::EXTERNAL_AUTHENTICATE, |out| {
            encode_sddispatch_external_authenticate(
                cla,
                security_level,
                p2,
                authentication_data,
                out,
            )
        });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_u8_response().ok_or(from_abi_status(
        rustlet_runtime::ApduStatus::internal_error(),
    ))
}

pub fn security_domain_unwrap_command(
    authenticated_header: &[u8],
    authenticated_data: &[u8],
    data: &[u8],
    mac: &[u8],
    out: &mut [u8],
) -> Result<usize, apdu_manager::ApduStatus> {
    // Retain the original ABI for small requests and older SD runtimes. Large
    // LOAD blocks need the extension to avoid duplicating their ciphertext.
    let compact =
        6 + authenticated_header.len() + authenticated_data.len() + data.len() + mac.len()
            > rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX
            && authenticated_data.ends_with(data);
    let opcode = if compact {
        SddispatchOpcode::UNWRAP_COMMAND_COMPACT
    } else {
        SddispatchOpcode::UNWRAP_COMMAND
    };
    let status = call_selected_security_domain_encoded(opcode, |out| {
        encode_sddispatch_unwrap_command(
            authenticated_header,
            authenticated_data,
            data,
            mac,
            compact,
            out,
        )
    });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_bytes_response(out)
}

pub fn security_domain_wrap_response(
    data: &[u8],
    status: (u8, u8),
    wrapped_data_out: &mut [u8],
    wrapped_mac_out: &mut [u8],
) -> Result<(usize, usize), apdu_manager::ApduStatus> {
    let status_word = status;
    let status = call_selected_security_domain_encoded(SddispatchOpcode::WRAP_RESPONSE, |out| {
        encode_sddispatch_wrap_response(data, status_word, out)
    });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }

    let Some(selected_security_domain) = selected_security_domain_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let response = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if response.len() < 4 {
        return Err(apdu_manager::ApduStatus::wrong_data());
    }
    let data_len = ((response[0] as usize) << 8) | response[1] as usize;
    let mac_len = ((response[2] as usize) << 8) | response[3] as usize;
    let Some(data_end) = 4usize.checked_add(data_len) else {
        return Err(apdu_manager::ApduStatus::wrong_data());
    };
    let Some(mac_end) = data_end.checked_add(mac_len) else {
        return Err(apdu_manager::ApduStatus::wrong_data());
    };
    if mac_end != response.len()
        || data_len > wrapped_data_out.len()
        || mac_len > wrapped_mac_out.len()
    {
        return Err(apdu_manager::ApduStatus::wrong_length());
    }
    wrapped_data_out[..data_len].copy_from_slice(&response[4..data_end]);
    wrapped_mac_out[..mac_len].copy_from_slice(&response[data_end..mac_end]);
    Ok((data_len, mac_len))
}

pub fn security_domain_reset_secure_channel() {
    let _ = call_selected_security_domain(SddispatchOpcode::RESET_SECURE_CHANNEL, &[]);
}

pub fn security_domain_may_manage_applet(
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
) -> bool {
    let status =
        call_selected_security_domain_encoded(SddispatchOpcode::MAY_MANAGE_APPLET, |out| {
            encode_sddispatch_three_aids(package_aid, applet_aid, instance_aid, out)
        });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return false;
    }
    selected_security_domain_bool_response().unwrap_or(false)
}

pub fn security_domain_may_make_selectable(instance_aid: &Aid) -> bool {
    let status =
        call_selected_security_domain_encoded(SddispatchOpcode::MAY_MAKE_SELECTABLE, |out| {
            encode_sddispatch_one_aid(instance_aid, out)
        });
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return false;
    }
    selected_security_domain_bool_response().unwrap_or(false)
}

/// Returns a response resident in the transport payload, after its loan ends.
pub fn security_domain_get_data_in_place(tag: u16) -> Result<usize, apdu_manager::ApduStatus> {
    let payload = [(tag >> 8) as u8, tag as u8];
    let status = call_selected_security_domain(SddispatchOpcode::GET_DATA, &payload);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

pub fn security_domain_get_data(
    tag: u16,
    out: &mut [u8],
) -> Result<usize, apdu_manager::ApduStatus> {
    let payload = [(tag >> 8) as u8, tag as u8];
    let status = call_selected_security_domain(SddispatchOpcode::GET_DATA, &payload);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }

    let Some(selected_security_domain) = selected_security_domain_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let data = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if data.len() > out.len() {
        return Err(apdu_manager::ApduStatus::wrong_length());
    }
    copy_sddispatch_bytes_at(out, 0, &data).ok_or_else(apdu_manager::ApduStatus::wrong_length)?;
    Ok(data.len())
}

fn dispatch_install_handler_encoded(
    encode_payload: impl FnOnce(&mut [u8]) -> Option<usize>,
) -> fae_runtime::HandlerCallResult {
    let Some(mut selected_app) = selected_app_mut() else {
        return fae_runtime::HandlerCallResult {
            status: rustlet_runtime::ApduStatus::conditions_not_satisfied(),
            returned_normally: false,
        };
    };

    let handler = fae_runtime::Handler::Install;

    let selected_app = &mut *selected_app;
    ActiveAppCallGuard::with_shared(&selected_app.loaded_fae, None, || {
        oxi_core::core::syscall::with_app_allocator(&mut selected_app.allocator, || {
            fae_runtime::call_handler_with_encoded_command(
                &selected_app.loaded_fae,
                handler,
                rustlet_runtime::RustletApduHeader {
                    cla: 0x80,
                    ins: INS_INSTALL,
                    p1: 0x0c,
                    p2: 0x00,
                    lc: 0x00,
                    le: 0x00,
                },
                encode_payload,
                |ctx| ctx.stage_state(&[]),
            )
        })
    })
}

fn dispatch_install_handler_current_apdu(
    header: rustlet_runtime::RustletApduHeader,
    incoming_len: usize,
) -> fae_runtime::HandlerCallResult {
    let Some(mut selected_app) = selected_app_mut() else {
        return fae_runtime::HandlerCallResult {
            status: rustlet_runtime::ApduStatus::conditions_not_satisfied(),
            returned_normally: false,
        };
    };

    let handler = fae_runtime::Handler::Install;

    let selected_app = &mut *selected_app;
    ActiveAppCallGuard::with_shared(&selected_app.loaded_fae, None, || {
        oxi_core::core::syscall::with_app_allocator(&mut selected_app.allocator, || {
            fae_runtime::call_handler_with_existing_command(
                &selected_app.loaded_fae,
                handler,
                header,
                incoming_len,
                |ctx| ctx.stage_state(&[]),
            )
        })
    })
}

fn call_selected_security_domain(opcode: u8, payload: &[u8]) -> apdu_manager::ApduStatus {
    if payload.len() > u8::MAX as usize {
        return apdu_manager::ApduStatus::wrong_length();
    }
    call_selected_security_domain_encoded(opcode, |out| {
        if payload.len() > out.len() {
            return None;
        }
        out[..payload.len()].copy_from_slice(payload);
        Some(payload.len())
    })
}

/// Encodes an already resident command after its transport view is released.
pub(crate) fn security_domain_in_place_request(
    opcode: u8,
    request: crate::in_place_request::InPlaceRequest,
) -> Result<usize, apdu_manager::ApduStatus> {
    let status = call_selected_security_domain_encoded(opcode, |out| request.encode(out));
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    selected_security_domain_response_len()
}

fn call_selected_security_domain_encoded(
    opcode: u8,
    encode_payload: impl FnOnce(&mut [u8]) -> Option<usize>,
) -> apdu_manager::ApduStatus {
    let operation = match RegistryOperationScope::begin(true) {
        Ok(scope) => scope,
        Err(error) => return error.status(),
    };
    let (result, registry_reference) = {
        let Some(mut selected_security_domain) = selected_security_domain_mut() else {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        };
        let registry_reference = selected_security_domain.registry;
        if !selected_security_domain.loaded_fae.is_security_domain() {
            return apdu_manager::ApduStatus::instruction_not_supported();
        };
        // Invariant: only this kernel-owned SDDISPATCH entry grants SD services.
        // Capture the registry slot before entry. The call guard revokes this
        // authority before state saving, including on a Rustlet fault.
        let selected_security_domain = &mut *selected_security_domain;
        let result = ActiveAppCallGuard::with_shared(
            &selected_security_domain.loaded_fae,
            registry_reference.instance_index(),
            || {
                oxi_core::core::syscall::with_app_allocator(
                    &mut selected_security_domain.allocator,
                    || {
                        fae_runtime::call_handler_with_encoded_command(
                            &selected_security_domain.loaded_fae,
                            fae_runtime::Handler::SecurityDomain,
                            rustlet_runtime::RustletApduHeader {
                                cla: SDDISPATCH_CLA,
                                ins: opcode,
                                p1: 0x00,
                                p2: 0x00,
                                lc: 0x00,
                                le: 0x00,
                            },
                            encode_payload,
                            |ctx| registry_reference.stage_state(ctx),
                        )
                    },
                )
            },
        );

        (result, registry_reference)
    };

    finish_selected_security_domain_call(operation, result, registry_reference)
}

// Keep persistence and fault-cleanup locals out of the frame used by the Rustlet.
#[inline(never)]
fn finish_selected_security_domain_call(
    operation: RegistryOperationScope,
    result: fae_runtime::HandlerCallResult,
    registry_reference: AppRegistryReference,
) -> apdu_manager::ApduStatus {
    let status = from_abi_status(result.status);
    let mut retain = result.returned_normally;
    let status = if result.returned_normally {
        let save_status = save_selected_security_domain_state(registry_reference);
        if save_status.sw1 == 0x90 && save_status.sw2 == 0x00 {
            status
        } else {
            // Saving may fail before journaling this slot: its heap is still stale.
            if let Some(sd) = selected_security_domain_mut() {
                if sd.registry.instance_index() == registry_reference.instance_index() {
                    sd.loaded_fae.request_persistent_restore();
                }
            }
            retain = false;
            save_status
        }
    } else {
        status
    };
    operation.finish(retain);
    if !result.returned_normally {
        SD_HOOK_FAULT_STATUS.set(Some(status));
        abort_registry_apdu();
        {
            *SD_HOOK_FAILED.borrow_mut() = true;
        }
        // Never re-enter a faulted SD, even to reset its secure channel. Its
        // heap may contain unsaved changes and invalid protocol state.
        if current_selected_app_mut().is_some_and(|app| app.loaded_fae.is_security_domain()) {
            set_selected_app(None);
        }
        set_selected_security_domain(None);
        {
            *ACTIVE_SECURITY_DOMAIN_SLOT.borrow_mut() = None;
        }
        crate::security_domain::retire_failed_session();
    }
    status
}

fn encode_sddispatch_install_for_load(package_aid: &Aid, out: &mut [u8]) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_aid(out, &mut offset, package_aid)?;
    push_sddispatch_lv(out, &mut offset, &[])?;
    Some(offset)
}

fn encode_sddispatch_install_for_install(
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    privileges: &[u8],
    install_parameters: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_aid(out, &mut offset, package_aid)?;
    push_sddispatch_aid(out, &mut offset, applet_aid)?;
    push_sddispatch_aid(out, &mut offset, instance_aid)?;
    push_sddispatch_lv(out, &mut offset, privileges)?;
    push_sddispatch_lv(out, &mut offset, install_parameters)?;
    Some(offset)
}

fn encode_sddispatch_put_key(
    key_version: u8,
    key_id: u8,
    key_data: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    let end = 2usize.checked_add(key_data.len())?;
    if end > out.len() {
        return None;
    }
    // Management input is borrowed from separate resident scratch while the
    // shared page is owned by the encoded command.
    copy_sddispatch_bytes_at(out, 2, key_data)?;
    out[0] = key_version;
    out[1] = key_id;
    Some(end)
}

fn encode_sddispatch_store_data(tag: u16, data: &[u8], out: &mut [u8]) -> Option<usize> {
    let end = 2usize.checked_add(data.len())?;
    if end > out.len() {
        return None;
    }
    // The source loan belongs to management scratch, independently of the
    // shared command page borrowed as output.
    copy_sddispatch_bytes_at(out, 2, data)?;
    out[0] = (tag >> 8) as u8;
    out[1] = tag as u8;
    Some(end)
}

fn encode_sddispatch_three_aids(
    package_aid: &Aid,
    applet_aid: &Aid,
    instance_aid: &Aid,
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_aid(out, &mut offset, package_aid)?;
    push_sddispatch_aid(out, &mut offset, applet_aid)?;
    push_sddispatch_aid(out, &mut offset, instance_aid)?;
    Some(offset)
}

fn encode_sddispatch_one_aid(aid: &Aid, out: &mut [u8]) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_aid(out, &mut offset, aid)?;
    Some(offset)
}

fn encode_sddispatch_initialize_update(
    key_version: u8,
    key_id: u8,
    host_challenge: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    let end = 2usize.checked_add(host_challenge.len())?;
    if end > out.len() {
        return None;
    }
    // External input is disjoint from the exclusively borrowed dispatch page.
    copy_sddispatch_bytes_at(out, 2, host_challenge)?;
    out[0] = key_version;
    out[1] = key_id;
    Some(end)
}

fn encode_sddispatch_delegated_secure_channel(
    command: &crate::security_domain::SecureChannelEstablishmentCommand<'_>,
    out: &mut [u8],
) -> Option<usize> {
    let end = 5usize.checked_add(command.data.len())?;
    if end > out.len() {
        return None;
    }
    copy_sddispatch_bytes_at(out, 5, command.data)?;
    out[..5].copy_from_slice(&[command.cla, command.ins, command.p1, command.p2, command.p3]);
    Some(end)
}

fn encode_sddispatch_external_authenticate(
    cla: u8,
    security_level: u8,
    p2: u8,
    authentication_data: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    let end = 3usize.checked_add(authentication_data.len())?;
    if end > out.len() {
        return None;
    }
    // Shared-payload callers use an offset-only InPlaceRequest instead.
    copy_sddispatch_bytes_at(out, 3, authentication_data)?;
    out[0] = cla;
    out[1] = security_level;
    out[2] = p2;
    Some(end)
}

fn encode_sddispatch_scp11_oce_certificate(
    ca_key_version: u8,
    ca_key_id: u8,
    public_key: &[u8],
    subject_id: &[u8],
    discretionary_data: &[u8],
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_byte(out, &mut offset, ca_key_version)?;
    push_sddispatch_byte(out, &mut offset, ca_key_id)?;
    push_sddispatch_lv(out, &mut offset, public_key)?;
    push_sddispatch_lv(out, &mut offset, subject_id)?;
    push_sddispatch_lv(out, &mut offset, discretionary_data)?;
    Some(offset)
}

fn encode_sddispatch_scp11a_mutual_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_byte(out, &mut offset, ecka_key_version)?;
    push_sddispatch_byte(out, &mut offset, ecka_key_id)?;
    push_sddispatch_byte(
        out,
        &mut offset,
        u8::from(request.parameters.include_identifiers),
    )?;
    push_sddispatch_byte(out, &mut offset, request.key_usage_qualifier)?;
    push_sddispatch_byte(out, &mut offset, request.key_type)?;
    push_sddispatch_byte(out, &mut offset, request.key_length)?;
    push_sddispatch_lv(out, &mut offset, request.host_id)?;
    push_sddispatch_lv(out, &mut offset, request.host_ephemeral_public)?;
    Some(offset)
}

fn encode_sddispatch_scp11b_internal_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_byte(out, &mut offset, ecka_key_version)?;
    push_sddispatch_byte(out, &mut offset, ecka_key_id)?;
    push_sddispatch_byte(
        out,
        &mut offset,
        u8::from(request.parameters.include_identifiers),
    )?;
    push_sddispatch_byte(out, &mut offset, request.key_usage_qualifier)?;
    push_sddispatch_byte(out, &mut offset, request.key_type)?;
    push_sddispatch_byte(out, &mut offset, request.key_length)?;
    push_sddispatch_lv(out, &mut offset, request.host_id)?;
    push_sddispatch_lv(out, &mut offset, request.host_ephemeral_public)?;
    Some(offset)
}

fn encode_sddispatch_scp11c_mutual_authenticate(
    ecka_key_version: u8,
    ecka_key_id: u8,
    request: &crate::core::scp11::MutualAuthenticateRequest<'_>,
    out: &mut [u8],
) -> Option<usize> {
    let mut offset = 0;
    push_sddispatch_byte(out, &mut offset, ecka_key_version)?;
    push_sddispatch_byte(out, &mut offset, ecka_key_id)?;
    push_sddispatch_byte(
        out,
        &mut offset,
        u8::from(request.parameters.include_identifiers),
    )?;
    push_sddispatch_byte(out, &mut offset, request.key_usage_qualifier)?;
    push_sddispatch_byte(out, &mut offset, request.key_type)?;
    push_sddispatch_byte(out, &mut offset, request.key_length)?;
    push_sddispatch_lv(out, &mut offset, request.host_id)?;
    push_sddispatch_lv(out, &mut offset, request.host_ephemeral_public)?;
    Some(offset)
}

fn encode_sddispatch_unwrap_command(
    authenticated_header: &[u8],
    authenticated_data: &[u8],
    data: &[u8],
    mac: &[u8],
    compact: bool,
    out: &mut [u8],
) -> Option<usize> {
    let authenticated_len = authenticated_header
        .len()
        .checked_add(authenticated_data.len())?;
    let auth_offset = 6usize;
    let authenticated_data_offset = auth_offset.checked_add(authenticated_header.len())?;
    let authenticated_end = auth_offset.checked_add(authenticated_len)?;
    let data_offset = if compact {
        if !authenticated_data.ends_with(data) {
            return None;
        }
        authenticated_end.checked_sub(data.len())?
    } else {
        authenticated_end
    };
    let mac_offset = data_offset.checked_add(data.len())?;
    let end = mac_offset.checked_add(mac.len())?;
    if end > out.len()
        || authenticated_len > u16::MAX as usize
        || data.len() > u16::MAX as usize
        || mac.len() > u16::MAX as usize
    {
        return None;
    }
    // Inputs here live outside the shared page; in-place requests use offsets.
    copy_sddispatch_bytes_at(out, mac_offset, mac)?;
    if !compact {
        copy_sddispatch_bytes_at(out, data_offset, data)?;
    }
    copy_sddispatch_bytes_at(out, authenticated_data_offset, authenticated_data)?;
    copy_sddispatch_bytes_at(out, auth_offset, authenticated_header)?;
    out[0] = (authenticated_len >> 8) as u8;
    out[1] = authenticated_len as u8;
    out[2] = (data.len() >> 8) as u8;
    out[3] = data.len() as u8;
    out[4] = (mac.len() >> 8) as u8;
    out[5] = mac.len() as u8;
    Some(end)
}

fn encode_sddispatch_wrap_response(data: &[u8], status: (u8, u8), out: &mut [u8]) -> Option<usize> {
    let end = 4usize.checked_add(data.len())?;
    if end > out.len() || data.len() > u16::MAX as usize {
        return None;
    }
    // The proxy retains response data in its existing auxiliary storage.
    copy_sddispatch_bytes_at(out, 4, data)?;
    out[0] = (data.len() >> 8) as u8;
    out[1] = data.len() as u8;
    out[2] = status.0;
    out[3] = status.1;
    Some(end)
}

fn push_sddispatch_byte(out: &mut [u8], offset: &mut usize, value: u8) -> Option<()> {
    let end = offset.checked_add(1)?;
    if end > out.len() {
        return None;
    }
    out[*offset] = value;
    *offset = end;
    Some(())
}

fn push_sddispatch_aid(out: &mut [u8], offset: &mut usize, aid: &Aid) -> Option<()> {
    push_sddispatch_lv(out, offset, aid.as_slice())
}

fn push_sddispatch_lv(out: &mut [u8], offset: &mut usize, value: &[u8]) -> Option<()> {
    if value.len() > u8::MAX as usize {
        return None;
    }
    let end = offset.checked_add(1)?.checked_add(value.len())?;
    if end > out.len() {
        return None;
    }
    // The source is outside the dispatch page and remains borrowed only here.
    copy_sddispatch_bytes_at(out, *offset + 1, value)?;
    out[*offset] = value.len() as u8;
    *offset = end;
    Some(())
}

fn copy_sddispatch_bytes_at(out: &mut [u8], dst: usize, value: &[u8]) -> Option<()> {
    let end = dst.checked_add(value.len())?;
    if end > out.len() {
        return None;
    }
    out[dst..end].copy_from_slice(value);
    Some(())
}

fn selected_security_domain_bool_response() -> Option<bool> {
    let selected_security_domain = selected_security_domain_mut()?;
    let data = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if data.len() != 1 {
        return None;
    }
    Some(data[0] == SDDISPATCH_BOOL_TRUE)
}

fn selected_security_domain_u8_response() -> Option<u8> {
    let selected_security_domain = selected_security_domain_mut()?;
    let data = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if data.len() != 1 {
        return None;
    }
    Some(data[0])
}

fn selected_security_domain_u16_response() -> Option<u16> {
    let selected_security_domain = selected_security_domain_mut()?;
    let data = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if data.len() != 2 {
        return None;
    }
    Some(((data[0] as u16) << 8) | data[1] as u16)
}

pub(crate) fn selected_security_domain_bytes_response(
    out: &mut [u8],
) -> Result<usize, apdu_manager::ApduStatus> {
    let Some(selected_security_domain) = selected_security_domain_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let data = selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data();
    if data.len() > out.len() {
        return Err(apdu_manager::ApduStatus::wrong_length());
    }
    out[..data.len()].copy_from_slice(&data);
    Ok(data.len())
}

/// Returns the length of a response already published in the shared APDU payload.
///
/// Establishment callers deliberately do not copy these bytes: the transport
/// APDU and SDDISPATCH use the same kernel-owned gate page.
fn selected_security_domain_response_len() -> Result<usize, apdu_manager::ApduStatus> {
    let Some(selected_security_domain) = selected_security_domain_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    Ok(selected_security_domain
        .loaded_fae
        .shared_buffer()
        .outgoing_data()
        .len())
}

fn install_selected_app(
    registry: AppRegistryReference,
    mut loaded: fae_runtime::LoadedFae,
) -> Result<(), apdu_manager::ApduStatus> {
    loaded.instance_aid = registry.instance_aid().unwrap_or(Aid::empty());
    let Some(heap) = loaded.heap_window() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let required_metadata_len = oxi_core::core::metadata_size_for_heap_size(heap.len);
    let allocator_metadata = match AllocatorMetadata::allocate(required_metadata_len) {
        Some(metadata) => metadata,
        None => {
            fae_runtime::unload(loaded);
            return Err(apdu_manager::ApduStatus::insufficient_memory());
        }
    };

    set_selected_app(Some(LoadedApp {
        registry,
        loaded_fae: loaded,
        allocator: oxi_core::core::HeapAllocatorState::new(),
        allocator_metadata,
    }));

    let Some(mut selected_app) = selected_app_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };

    // SAFETY: the loader validated this private heap inside its owned RAM.
    // Its metadata is a separate owned allocation. The stable resident allocator
    // has not been published to SVC yet; all three live until LoadedApp is dropped.
    let heap_ready = unsafe {
        oxi_core::core::reset_heap(
            core::ptr::addr_of_mut!(selected_app.allocator),
            heap.start as *mut u8,
            heap.len,
            selected_app.allocator_metadata.as_mut_ptr(),
            selected_app.allocator_metadata.len(),
        )
    };
    if !heap_ready {
        drop(selected_app);
        set_selected_app(None);
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    }

    Ok(())
}

pub fn top_level_parent_sd_aid() -> Aid {
    Aid::new(&[])
}

pub fn root_security_domain_instance_aid() -> Aid {
    crate::security_domain::root_security_domain_aid()
}

pub fn active_security_domain_instance_aid() -> Aid {
    let active_slot = ACTIVE_SECURITY_DOMAIN_SLOT.get();
    active_slot
        .and_then(|slot| {
            (crate::registry::read())
                .identity(slot)
                .map(|entry| entry.object())
        })
        .unwrap_or_else(root_security_domain_instance_aid)
}

pub fn ensure_active_security_domain_loaded_for_secure_channel(
) -> Result<Option<usize>, apdu_manager::ApduStatus> {
    let active = active_security_domain_instance_aid();
    let Some(active_object) = find_any_object_by_aid_raw(&active) else {
        return Ok(None);
    };
    let Some(active_slot) = registry_index_for_object(&active_object) else {
        return Ok(None);
    };
    if active_object.object_kind != ManagedObjectKind::SecurityDomain
        || active_object.security_domain_backend()
            != Some(SecurityDomainObjectBackend::RustletSecurityDomain)
    {
        return Ok(None);
    }
    drop(active_object);
    let already_loaded = {
        let slot = SELECTED_SECURITY_DOMAIN.borrow();
        slot.as_ref()
            .is_some_and(|app| app.registry.instance_index() == Some(active_slot))
    };
    if already_loaded {
        return Ok(None);
    }

    // The active Rustlet Security Domain normally remains resident while an
    // ordinary Rustlet occupies SELECTED_APP. This recovery path reloads a
    // missing SD without ever treating its volatile SCP state as persistent.
    let mut displaced_app = None;
    if let Some(selected_app) = current_selected_app_mut() {
        let registry = selected_app.registry;
        drop(selected_app);
        displaced_app = registry.instance_index();
        let Some((security_domain_aid, package_aid, applet_aid, instance_aid)) =
            registry.identity()
        else {
            return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
        };
        let save_status = save_selected_instance_state(
            &security_domain_aid,
            &package_aid,
            &applet_aid,
            &instance_aid,
            None,
        );
        if save_status.sw1 != 0x90 || save_status.sw2 != 0x00 {
            return Err(save_status);
        }
        set_selected_app(None);
    }

    let Some(reference) = AppRegistryReference::from_instance(active_slot) else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let Some(instance) = reference.instance_object() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    let status = activate_registry_reference(reference);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return Err(status);
    }
    let Some(selected_security_domain) = current_selected_app_mut() else {
        return Err(apdu_manager::ApduStatus::conditions_not_satisfied());
    };
    if !selected_security_domain
        .loaded_fae
        .shared_buffer()
        .stage_state_from_object(&instance)
    {
        drop(selected_security_domain);
        set_selected_app(None);
        return Err(apdu_manager::ApduStatus::wrong_length());
    }
    drop(selected_security_domain);
    promote_selected_app_to_security_domain();
    Ok(displaced_app)
}

pub fn restore_selected_app_after_secure_channel(
    displaced_app: Option<usize>,
) -> apdu_manager::ApduStatus {
    let Some(instance_index) = displaced_app else {
        return apdu_manager::ApduStatus::success();
    };
    let Some(reference) = AppRegistryReference::from_instance(instance_index) else {
        return apdu_manager::ApduStatus::file_not_found();
    };
    let Some(instance) = reference.instance_object() else {
        return apdu_manager::ApduStatus::file_not_found();
    };
    if is_security_domain_kind(instance.object_kind) {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    }
    let status = activate_registry_reference(reference);
    if status.sw1 != 0x90 || status.sw2 != 0x00 {
        return status;
    }
    let Some(selected_app) = selected_app_mut() else {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    };
    if !selected_app
        .loaded_fae
        .shared_buffer()
        .stage_state_from_object(&instance)
    {
        drop(selected_app);
        set_selected_app(None);
        return apdu_manager::ApduStatus::wrong_length();
    }
    apdu_manager::ApduStatus::success()
}

pub fn set_active_security_domain_instance_aid(aid: Aid) {
    let previous = active_security_domain_instance_aid();
    let slot = {
        let registry = crate::registry::read();
        registry.find_any_index(&aid).filter(|index| {
            registry
                .identity(*index)
                .and_then(|entry| crate::registry::recovery::security_domain_backend(*entry))
                .is_some()
        })
    };
    ACTIVE_SECURITY_DOMAIN_SLOT.set(slot);
    let next = active_security_domain_instance_aid();
    if previous != next {
        crate::security_domain::on_active_security_domain_instance_switched(previous, next);
    }
}

fn pending_registry_reference_for_install(
    security_domain_aid: &Aid,
    package_aid: &Aid,
    applet_aid: &Aid,
) -> RegistryResult<usize> {
    let registry_guard = crate::registry::read();
    let registry = &*registry_guard;
    let package_index = registry
        .find_index(security_domain_aid, ManagedObjectKind::Package, package_aid)
        .or_else(|| {
            registry.find_index(
                &top_level_parent_sd_aid(),
                ManagedObjectKind::Package,
                package_aid,
            )
        })
        .ok_or_else(|| {
            if find_object_by_kind_and_aid_raw(ManagedObjectKind::Package, package_aid).is_some() {
                RegistryError::AuthorityDenied
            } else {
                RegistryError::NotFound
            }
        })?;
    let package = registry
        .resolve(package_index)
        .ok_or(RegistryError::NotFound)?;
    if !package.may_instantiate_package() {
        return Err(RegistryError::InvalidState);
    }
    if package.package_applet_aid() != Some(*applet_aid) {
        return Err(RegistryError::NotFound);
    }
    Ok(package_index)
}

fn registry_index_for_object(object: &ObjectView) -> Option<usize> {
    {
        (crate::registry::read()).find_index(
            &object.parent_sd_aid,
            object.object_kind,
            &object.object_aid,
        )
    }
}

fn find_security_domain_object_by_aid(
    parent_sd_aid: &Aid,
    aid: &Aid,
) -> Option<crate::registry::operations::ObjectRead> {
    crate::registry::operations::read_object(|registry| {
        registry.find_security_domain_object(parent_sd_aid, aid)
    })
}

fn find_instance_object_by_aid(
    parent_sd_aid: &Aid,
    aid: &Aid,
) -> Option<crate::registry::operations::ObjectRead> {
    crate::registry::operations::read_object(|registry| {
        registry.find_instance_object(parent_sd_aid, aid)
    })
}

fn find_key_object_by_aid(
    parent_sd_aid: &Aid,
    aid: &Aid,
) -> Option<crate::registry::operations::ObjectRead> {
    crate::registry::operations::read_object(|registry| {
        registry.find_key_object(parent_sd_aid, aid)
    })
}

fn find_any_object_by_aid_raw(aid: &Aid) -> Option<crate::registry::operations::ObjectRead> {
    crate::registry::operations::read_object(|registry| registry.find_any_object(aid))
}

fn find_object_by_kind_and_aid_raw(
    kind: ManagedObjectKind,
    aid: &Aid,
) -> Option<crate::registry::operations::ObjectRead> {
    crate::registry::operations::read_object(|registry| {
        registry.resolve(registry.find_kind_index(kind, aid)?)
    })
}

fn find_visible_object_by_aid(aid: &Aid) -> Option<crate::registry::operations::ObjectRead> {
    let object = find_any_object_by_aid_raw(aid)?;
    if active_security_domain_may_reach_instance(aid) {
        Some(object)
    } else {
        None
    }
}

fn find_runtime_state_object_by_aid(
    parent_sd_aid: &Aid,
    aid: &Aid,
) -> Option<crate::registry::operations::ObjectRead> {
    find_security_domain_object_by_aid(parent_sd_aid, aid)
        .or_else(|| find_instance_object_by_aid(parent_sd_aid, aid))
}

pub fn security_domain_backend_by_aid(aid: &Aid) -> Option<SecurityDomainObjectBackend> {
    let registry = crate::registry::read();
    let entry = registry.find_identity(aid)?;
    let backend = crate::registry::recovery::security_domain_backend(*entry)?;
    active_security_domain_may_reach_instance(aid).then_some(backend)
}

pub fn security_domain_may_open_secure_channel(aid: &Aid) -> bool {
    let Some(object) = find_visible_object_by_aid(aid) else {
        return false;
    };
    object.object_kind == ManagedObjectKind::SecurityDomain && object.may_open_secure_channel()
}

pub fn security_domain_privilege_bytes_by_aid(aid: &Aid) -> Option<[u8; 3]> {
    let object = find_visible_object_by_aid(aid)?;
    if object.object_kind != ManagedObjectKind::SecurityDomain {
        return None;
    }
    object.security_domain_privilege_bytes()
}

pub(crate) fn read_security_domain_state_by_aid(aid: &Aid, out: &mut [u8]) -> Option<usize> {
    let object = find_visible_object_by_aid(aid)?;
    if object.object_kind != ManagedObjectKind::SecurityDomain
        || object.content_len().ok()? > out.len()
    {
        return None;
    }
    object.read_range(0, out).ok()
}

/// Checks an explicit authority against an existing object, preserving both errors.
pub(crate) fn require_managed_object_authority(authority: &Aid, aid: &Aid) -> RegistryResult {
    let registry = crate::registry::read();
    let entry = registry.find_identity(aid).ok_or(RegistryError::NotFound)?;
    if security_domain_may_reach_identity(authority, &entry.object(), entry.parent()) {
        Ok(())
    } else {
        Err(RegistryError::AuthorityDenied)
    }
}

pub fn find_managed_object_kind_by_aid(aid: &Aid) -> Option<ManagedObjectKind> {
    let registry = crate::registry::read();
    let slot = registry.find_any_index(aid)?;
    active_security_domain_may_reach_instance(aid)
        .then(|| registry.identity_kind(slot))
        .flatten()
}

/// Mutates the staged registry through the common operation savepoint.
fn mutate_registry(
    mutate: impl FnOnce(&mut crate::registry::Mutation) -> RegistryResult,
) -> RegistryResult {
    registry_operation(|| mutate(&mut registry_mut()))
}

pub fn upsert_security_domain_state_object(
    parent_sd_aid: Aid,
    package_aid: Aid,
    instance_aid: Aid,
    backend: SecurityDomainObjectBackend,
    privilege_bytes: [u8; 3],
    state: &[u8],
) -> RegistryResult {
    mutate_registry(|registry| {
        registry.upsert_security_domain_object(
            parent_sd_aid,
            instance_aid,
            package_aid,
            backend,
            privilege_bytes,
            state,
        )
    })
}

pub fn install_kernel_side_security_domain_instance(
    backend: SecurityDomainObjectBackend,
    parent_sd_aid: Aid,
    package_aid: Aid,
    instance_aid: Aid,
    install_payload: &[u8],
) -> apdu_manager::ApduStatus {
    let Some(privileges) = install_payload.get(..3) else {
        return apdu_manager::ApduStatus::wrong_length();
    };
    let Some(encoded_state) = crate::security_domain::encode_administrative_state(privileges)
    else {
        return apdu_manager::ApduStatus::wrong_data();
    };
    let privilege_bytes = [
        privileges[0],
        *privileges.get(1).unwrap_or(&0),
        *privileges.get(2).unwrap_or(&0),
    ];
    if parent_sd_aid == top_level_parent_sd_aid() {
        if instance_aid != root_security_domain_instance_aid() {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        }
    } else {
        let Some(parent) =
            find_object_by_kind_and_aid_raw(ManagedObjectKind::SecurityDomain, &parent_sd_aid)
        else {
            return RegistryError::NotFound.status();
        };
        let Some(parent_privileges) = parent.security_domain_privilege_bytes().and_then(|bytes| {
            crate::security_domain::SecurityDomainPrivileges::from_install_bytes(&bytes)
        }) else {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        };
        let Some(child_privileges) =
            crate::security_domain::SecurityDomainPrivileges::from_install_bytes(&privilege_bytes)
        else {
            return apdu_manager::ApduStatus::wrong_data();
        };
        if !parent_privileges.contains(child_privileges) {
            return RegistryError::AuthorityDenied.status();
        }
    }
    registry_result_status(registry_operation(|| {
        registry_mut().upsert_security_domain_object(
            parent_sd_aid,
            instance_aid,
            package_aid,
            backend,
            privilege_bytes,
            &encoded_state,
        )?;
        if matches!(backend, SecurityDomainObjectBackend::KernelSecurityDomain)
            && parent_sd_aid != top_level_parent_sd_aid()
        {
            registry_mut().clone_scp03_keys(parent_sd_aid, instance_aid)?;
        }
        Ok(())
    }))
}

/// Derives the synthetic registry AID used to store one SCP03 key object.
///
/// The tuple `(key_version, key_id, usage)` must map to a stable object AID so
/// that `PUT KEY`, `INITIALIZE UPDATE`, and later persistence all resolve the
/// same material through one lookup path.
fn scp03_key_object_instance_aid(key_version: u8, key_id: u8, usage: u8) -> Aid {
    Aid::from_array([0x4B, 0x45, 0x59, key_version, key_id, usage])
}

fn upsert_typed_key_object(
    parent_sd_aid: Aid,
    key_version: u8,
    key_id: u8,
    usage: u8,
    key_type: KeyObjectType,
    key_material: &[u8],
) -> RegistryResult {
    let instance_aid = scp03_key_object_instance_aid(key_version, key_id, usage);
    mutate_registry(|registry| {
        registry.upsert_key_object(
            parent_sd_aid,
            instance_aid,
            key_type,
            KeyObjectState::Active,
            key_version,
            key_id,
            usage,
            key_material,
        )
    })
}

/// Validates and stages all entries of one PUT KEY in the shared APDU transaction.
/// An operation error restores earlier replacements/insertions through its savepoint.
pub fn put_key_objects(
    owner: Aid,
    reference: crate::security_domain::PutKeyReferenceControl,
    version: u8,
    encoded: &[u8],
) -> RegistryResult {
    put_key_objects_with_publish(owner, reference, version, encoded, || Ok(()))
}

fn put_key_objects_with_publish(
    owner: Aid,
    reference: crate::security_domain::PutKeyReferenceControl,
    version: u8,
    encoded: &[u8],
    publish: impl FnOnce() -> RegistryResult,
) -> RegistryResult {
    struct Change<'a> {
        aid: Aid,
        id: u8,
        usage: u8,
        kind: KeyObjectType,
        material: &'a [u8],
    }
    if version == 0 || !reference.last_command || encoded.is_empty() || encoded.len() > 254 {
        return Err(RegistryError::InvalidData);
    }
    let mut changes = alloc::vec::Vec::new();
    // Bound the parser storage by the APDU payload length.
    changes
        .try_reserve_exact(encoded.len().min(38) / 19 + encoded.len().saturating_sub(38) / 35)
        .map_err(|_| RegistryError::Capacity)?;
    let mut offset = 0;
    while offset < encoded.len() {
        let index = changes.len();
        let id = reference
            .key_id_for_entry(index)
            .ok_or(RegistryError::InvalidData)?;
        let key_type = encoded[offset];
        let len = *encoded.get(offset + 1).ok_or(RegistryError::InvalidData)? as usize;
        let end = offset + 2 + len;
        let material = encoded
            .get(offset + 2..end)
            .ok_or(RegistryError::InvalidData)?;
        let kcv_len = *encoded.get(end).ok_or(RegistryError::InvalidData)? as usize;
        offset = end + 1 + kcv_len;
        if offset > encoded.len() {
            return Err(RegistryError::InvalidData);
        }
        let (kind, usage) = match key_type {
            0x88 if index < 2 && len == 16 => (KeyObjectType::Scp03Static, index as u8 + 1),
            0xB1 => (validate_scp11_key(0x11, material)?, 0x11),
            0xB0 => (validate_scp11_key(0x12, material)?, 0x12),
            _ => return Err(RegistryError::InvalidData),
        };
        let aid = scp03_key_object_instance_aid(version, id, usage);
        changes.push(Change {
            aid,
            id,
            usage,
            kind,
            material,
        });
    }
    registry_operation(|| {
        for change in &changes {
            crate::registry::edit().upsert_key_object(
                owner,
                change.aid,
                change.kind,
                KeyObjectState::Active,
                version,
                change.id,
                change.usage,
                change.material,
            )?;
        }
        publish()
    })
}

/// Stores or replaces one SCP03 static key object under the given Security Domain.
///
/// The kernel stores SCP03 material as typed registry objects owned by a
/// specific Security Domain instance. This keeps key visibility aligned with
/// the administrative subtree and lets the secure-channel path reuse the same
/// lookup logic as persistence and `PUT KEY`.
pub fn upsert_scp03_key_object(
    parent_sd_aid: Aid,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
    key_material: &[u8],
) -> RegistryResult {
    if key_material.len() != crate::security_domain::SCP03_STATIC_KEY_LEN {
        return Err(RegistryError::InvalidData);
    }
    upsert_typed_key_object(
        parent_sd_aid,
        key_version,
        key_id,
        usage.as_byte(),
        KeyObjectType::Scp03Static,
        key_material,
    )
}

/// Stores or replaces one SCP11 key owned by a Security Domain.
#[cfg(test)]
pub fn upsert_scp11_key_object(
    parent_sd_aid: Aid,
    key_version: u8,
    key_id: u8,
    usage: u8,
    key_material: &[u8],
) -> RegistryResult {
    let key_type = validate_scp11_key(usage, key_material)?;
    upsert_typed_key_object(
        parent_sd_aid,
        key_version,
        key_id,
        usage,
        key_type,
        key_material,
    )
}

fn validate_scp11_key(usage: u8, key_material: &[u8]) -> RegistryResult<KeyObjectType> {
    let (key_type, expected_len) = match usage {
        crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA => {
            (KeyObjectType::Scp11SdEckaPrivate, 32)
        }
        crate::security_domain::SCP11_PUT_KEY_USAGE_CA_KLOC => {
            (KeyObjectType::Scp11CaKlocPublic, 65)
        }
        _ => return Err(RegistryError::InvalidData),
    };
    if key_material.len() != expected_len {
        return Err(RegistryError::InvalidData);
    }
    let valid = match usage {
        crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA => {
            let mut public = [0u8; 65];
            oxi_core::core::crypto::p256_public_from_private(key_material, &mut public).is_ok()
        }
        crate::security_domain::SCP11_PUT_KEY_USAGE_CA_KLOC => {
            let mut scalar_one = [0u8; 32];
            scalar_one[31] = 1;
            let mut shared = [0u8; 32];
            oxi_core::core::crypto::p256_ecdh(&scalar_one, key_material, &mut shared).is_ok()
        }
        _ => false,
    };
    if !valid {
        return Err(RegistryError::InvalidData);
    }
    Ok(key_type)
}

/// Loads one active SCP11 key with the exact owner, selector and type.
pub fn load_scp11_key_material(
    parent_sd_aid: &Aid,
    key_version: u8,
    key_id: u8,
    usage: u8,
    out: &mut [u8],
) -> Option<usize> {
    let expected_type = match usage {
        crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA => KeyObjectType::Scp11SdEckaPrivate,
        crate::security_domain::SCP11_PUT_KEY_USAGE_CA_KLOC => KeyObjectType::Scp11CaKlocPublic,
        _ => return None,
    };
    let instance_aid = scp03_key_object_instance_aid(key_version, key_id, usage);
    let object = find_key_object_by_aid(parent_sd_aid, &instance_aid)?;
    if object.key_state()? != KeyObjectState::Active {
        return None;
    }
    let (key_type, stored_version, stored_id, stored_usage, material) = object.key_metadata()?;
    if key_type != expected_type
        || stored_version != key_version
        || stored_id != key_id
        || stored_usage != usage
        || out.len() < material
    {
        return None;
    }
    object.read_range(0, &mut out[..material]).ok()
}

fn gp_data_object_aid(tag: u16) -> Aid {
    Aid::from_array([0x44, 0x41, 0x54, 0x41, (tag >> 8) as u8, tag as u8])
}

/// Stores or replaces one GP data object under the given Security Domain.
///
/// The object AID is kernel-derived from the two-byte GET/STORE DATA tag. This
/// keeps the public APDU vocabulary tag-based while letting the polymorphic
/// registry remain uniformly AID-addressed.
pub fn upsert_registry_data_object(parent_sd_aid: Aid, tag: u16, data: &[u8]) -> RegistryResult {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::WriteData);
    #[cfg(test)]
    if crate::registry::physical::persistence_area().page_count == 0 {
        let object_aid = gp_data_object_aid(tag);
        return mutate_registry(|registry| {
            registry.upsert_data_object(parent_sd_aid, object_aid, data)
        });
    }
    write_registry_data_objects(parent_sd_aid, &[(tag, data.len())], |_, i| data[i])
}

/// Streams up to two immutable data payloads and stages their references atomically.
/// The producer must be deterministic and must not mutate the registry or flash.
pub(crate) fn write_registry_data_objects(
    parent: Aid,
    objects: &[(u16, usize)],
    mut byte: impl FnMut(usize, usize) -> u8,
) -> RegistryResult {
    if objects.is_empty() || objects.len() > 2 || dynamic_package_load_in_progress() {
        return Err(RegistryError::InvalidState);
    }
    // Compare before any snapshot, allocation or mutation. Keep the producer's
    // original indices when only one member of the atomic pair has changed.
    let mut changed = [0usize; 2];
    let mut count = 0;
    {
        let registry = crate::registry::read();
        for (i, &(tag, len)) in objects.iter().enumerate() {
            let duplicate = objects[..i].iter().any(|&(previous, _)| previous == tag);
            let equal = if duplicate {
                false // preserve sequential replacement semantics for repeated tags
            } else if let Some(object) =
                registry.find_data_object(&parent, &gp_data_object_aid(tag))
            {
                object.data_matches_generated(len, |offset| byte(i, offset))?
            } else {
                false
            };
            if !equal {
                changed[count] = i;
                count += 1;
            }
        }
    }
    if count == 0 {
        return Ok(());
    }
    registry_operation(|| {
        // Invariant: snapshot preparation completes before changing the image.
        // Only one unattached reservation is live; its cleanup precedes rollback.
        // Accepting this scope never publishes one member independently of the pair.
        for &i in &changed[..count] {
            #[cfg(not(test))]
            if crate::registry::uses_volatile_storage() {
                let (tag, len) = objects[i];
                let content =
                    crate::registry::content::Content::volatile_generated(len, |offset| {
                        byte(i, offset)
                    })?;
                registry_mut().attach_volatile_data_object(
                    parent,
                    gp_data_object_aid(tag),
                    content,
                )?;
                continue;
            }
            let prepared =
                registry_payload::prepare_data_payload(objects[i].1, |offset| byte(i, offset))?;
            registry_mut().attach_prepared_data_object(
                parent,
                gp_data_object_aid(objects[i].0),
                prepared,
            )?;
        }
        Ok(())
    })
}

#[cfg(all(
    oxide_se_kernel_app_module = "sram-fingerprint",
    target_arch = "arm",
    oxide_se_board_raspi_pico2
))]
pub(crate) fn probe_data_len(tag: u16) -> Option<usize> {
    crate::registry::read()
        .find_data_object(
            &root_security_domain_instance_aid(),
            &gp_data_object_aid(tag),
        )?
        .content_len()
        .ok()
}

/// Loads one GP data object visible under the given Security Domain.
pub fn load_registry_data_object(
    parent_sd_aid: &Aid,
    tag: u16,
    out: &mut [u8],
) -> RegistryResult<usize> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::ReadData);
    let object_aid = gp_data_object_aid(tag);
    let registry = crate::registry::read();
    let object = registry
        .find_data_object(parent_sd_aid, &object_aid)
        .ok_or(RegistryError::NotFound)?;
    if out.len() < object.content_len()? {
        return Err(RegistryError::OutputTooSmall);
    }
    object.read_range(0, out)
}

/// Copies a bounded range of a visible Data object. An offset at EOF returns
/// zero bytes; an offset beyond EOF is rejected. The caller owns the output.
#[allow(dead_code)]
pub(crate) fn load_registry_data_object_range(
    parent_sd_aid: &Aid,
    tag: u16,
    start: usize,
    out: &mut [u8],
) -> RegistryResult<usize> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::ReadData);
    let registry = crate::registry::read();
    let object = registry
        .find_data_object(parent_sd_aid, &gp_data_object_aid(tag))
        .ok_or(RegistryError::NotFound)?;
    object.read_range(start, out)
}

/// Deletes the complete requested closure, preserving authority and persistence errors.
pub fn delete_visible_managed_object_under_authority(
    authority_aid: Aid,
    aid: &Aid,
    delete_related: bool,
) -> RegistryResult {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Delete);
    let Some(object) = find_any_object_by_aid_raw(aid) else {
        return Err(RegistryError::NotFound);
    };
    if !security_domain_may_reach_object(&authority_aid, &object) {
        return Err(RegistryError::AuthorityDenied);
    }
    if object.object_kind == ManagedObjectKind::SecurityDomain
        && object.object_aid == root_security_domain_instance_aid()
    {
        return Err(RegistryError::InvalidState);
    }
    let Some(slot) = registry_index_for_object(&object) else {
        return Err(RegistryError::NotFound);
    };
    drop(object);
    let mut deletion_set = [false; DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY];
    deletion_set[slot] = true;
    loop {
        let mut changed = false;
        let registry_guard = crate::registry::read();
        let registry = &*registry_guard;
        let mut candidate_slot = 0usize;
        while candidate_slot < DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY {
            let Some(candidate) = registry.resolve(candidate_slot) else {
                candidate_slot += 1;
                continue;
            };
            let mut owner_slot = 0usize;
            while owner_slot < DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY {
                let Some(owner) = registry.resolve(owner_slot) else {
                    owner_slot += 1;
                    continue;
                };
                let related = deletion_set[owner_slot]
                    && ((owner.object_kind == ManagedObjectKind::SecurityDomain
                        && candidate.parent_sd_aid == owner.object_aid)
                        || (owner.object_kind == ManagedObjectKind::Package
                            && candidate.package_aid() == Some(owner.object_aid)));
                if related && !deletion_set[candidate_slot] {
                    deletion_set[candidate_slot] = true;
                    changed = true;
                }
                owner_slot += 1;
            }
            candidate_slot += 1;
        }
        if !changed {
            break;
        }
    }

    if !delete_related && deletion_set.iter().filter(|selected| **selected).count() != 1 {
        return Err(RegistryError::InvalidState);
    }

    // Validate the complete closure before mutating the first slot. Package
    // dependencies must never turn cumulative deletion into a cross-tree
    // operation, even if a corrupt registry contains such a relationship.
    let registry_guard = crate::registry::read();
    let registry = &*registry_guard;
    let mut candidate_slot = 0usize;
    while candidate_slot < DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY {
        if deletion_set[candidate_slot] {
            let Some(candidate) = registry.resolve(candidate_slot) else {
                return Err(RegistryError::NotFound);
            };
            if !security_domain_may_reach_object(&authority_aid, &candidate) {
                return Err(RegistryError::AuthorityDenied);
            }
            if candidate.object_kind == ManagedObjectKind::SecurityDomain
                && candidate.object_aid == root_security_domain_instance_aid()
            {
                return Err(RegistryError::InvalidState);
            }
        }
        candidate_slot += 1;
    }

    drop(registry_guard);
    registry_operation(|| {
        // Delete dependants before their owner. Registry slots remain stable, so
        // reverse slot order is sufficient after the complete closure is known.
        let mut candidate_slot = DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY;
        while candidate_slot != 0 {
            candidate_slot -= 1;
            if candidate_slot != slot && deletion_set[candidate_slot] {
                delete_resolved_managed_object(candidate_slot)?;
            }
        }
        delete_resolved_managed_object(slot)
    })
}

fn delete_resolved_managed_object(slot: usize) -> RegistryResult {
    let (parent_sd_aid, object_kind, object_aid) = {
        let registry = crate::registry::read();
        let object = registry.resolve(slot).ok_or(RegistryError::NotFound)?;
        if object.object_kind == ManagedObjectKind::SecurityDomain
            && object.object_aid == root_security_domain_instance_aid()
        {
            return Err(RegistryError::NotFound);
        }
        (object.parent_sd_aid, object.object_kind, object.object_aid)
    };
    invalidate_runtime_references_to_registry_slot(slot);

    {
        (crate::registry::edit()).delete_object(&parent_sd_aid, object_kind, &object_aid)
    }
}

fn invalidate_runtime_references_to_registry_slot(slot: usize) {
    let selected_app_uses_slot = {
        (SELECTED_APP.borrow())
            .as_ref()
            .is_some_and(|app| app.registry.references_slot(slot))
    };
    if selected_app_uses_slot {
        set_selected_app(None);
    }

    let selected_security_domain_uses_slot = {
        (SELECTED_SECURITY_DOMAIN.borrow())
            .as_ref()
            .is_some_and(|app| app.registry.references_slot(slot))
    };
    if selected_security_domain_uses_slot {
        set_selected_security_domain(None);
    }

    let active_slot = ACTIVE_SECURITY_DOMAIN_SLOT.get();
    if active_slot == Some(slot) {
        let previous = active_security_domain_instance_aid();
        ACTIVE_SECURITY_DOMAIN_SLOT.set(None);
        crate::security_domain::on_active_security_domain_instance_switched(
            previous,
            root_security_domain_instance_aid(),
        );
    }
}

pub fn set_visible_managed_object_status(
    authority_aid: Aid,
    p1: u8,
    p2: u8,
    aid: &Aid,
) -> RegistryResult {
    let Some(kind) = set_status_target_kind(p1) else {
        return Err(RegistryError::InvalidState);
    };
    let Some(object) = find_object_by_kind_and_aid_raw(kind, aid) else {
        return Err(RegistryError::NotFound);
    };
    if !security_domain_may_reach_object(&authority_aid, &object) {
        return Err(RegistryError::AuthorityDenied);
    }
    if object.object_kind == ManagedObjectKind::SecurityDomain
        && object.object_aid == root_security_domain_instance_aid()
    {
        // The technical root is a bootstrap anchor, not an ordinary
        // GlobalPlatform lifecycle object.
        return Err(RegistryError::InvalidState);
    }

    // Retire the borrowed registry view before opening its mutable operation.
    let parent = object.parent_sd_aid;
    let object_aid = object.object_aid;
    drop(object);
    mutate_registry(|registry| match kind {
        ManagedObjectKind::Package => {
            let Some(state) = package_state_from_set_status_p2(p2) else {
                return Err(RegistryError::InvalidState);
            };
            registry.set_package_state(&parent, &object_aid, state)
        }
        ManagedObjectKind::Instance => {
            let Some(state) = instance_state_from_set_status_p2(p2) else {
                return Err(RegistryError::InvalidState);
            };
            registry.set_instance_state(&parent, &object_aid, state)
        }
        ManagedObjectKind::SecurityDomain => {
            let Some(state) = security_domain_state_from_set_status_p2(p2) else {
                return Err(RegistryError::InvalidState);
            };
            registry.set_security_domain_state(&parent, &object_aid, state)
        }
        ManagedObjectKind::Key | ManagedObjectKind::Data => Err(RegistryError::InvalidData),
    })
}

fn set_status_target_kind(p1: u8) -> Option<ManagedObjectKind> {
    match p1 {
        crate::security_domain::SET_STATUS_KIND_PACKAGE => Some(ManagedObjectKind::Package),
        crate::security_domain::SET_STATUS_KIND_APPLICATION => Some(ManagedObjectKind::Instance),
        crate::security_domain::SET_STATUS_KIND_SECURITY_DOMAIN => {
            Some(ManagedObjectKind::SecurityDomain)
        }
        _ => None,
    }
}

fn package_state_from_set_status_p2(p2: u8) -> Option<PackageObjectState> {
    match p2 {
        crate::security_domain::SET_STATUS_STATE_UNLOCK => Some(PackageObjectState::Loaded),
        crate::security_domain::SET_STATUS_STATE_LOCK => Some(PackageObjectState::Locked),
        _ => None,
    }
}

fn instance_state_from_set_status_p2(p2: u8) -> Option<InstanceObjectState> {
    match p2 {
        crate::security_domain::SET_STATUS_STATE_UNLOCK => Some(InstanceObjectState::Selectable),
        crate::security_domain::SET_STATUS_STATE_LOCK => Some(InstanceObjectState::Locked),
        _ => None,
    }
}

fn security_domain_state_from_set_status_p2(p2: u8) -> Option<SecurityDomainObjectState> {
    match p2 {
        crate::security_domain::SET_STATUS_STATE_UNLOCK => {
            Some(SecurityDomainObjectState::Selectable)
        }
        crate::security_domain::SET_STATUS_STATE_LOCK => Some(SecurityDomainObjectState::Locked),
        _ => None,
    }
}

/// Loads the ENC and MAC static keys required to derive one SCP03 session.
///
/// Returns `None` unless both companion key objects are present under the same
/// owner Security Domain and carry valid AES-128 raw material.
pub fn load_scp03_static_keys(
    parent_sd_aid: &Aid,
    key_version: u8,
    key_id: u8,
) -> Option<crate::core::scp03::StaticKeys> {
    load_scp03_static_keys_with_ids(parent_sd_aid, key_version, key_id, key_id).or_else(|| {
        let mac_key_id = key_id.checked_add(1)?;
        load_scp03_static_keys_with_ids(parent_sd_aid, key_version, key_id, mac_key_id)
    })
}

/// Resolves the active SCP03 ENC/MAC pair selected by an INITIALIZE UPDATE key
/// version. GP does not carry a key identifier in P2 for this command, so the
/// identifier is an internal property of the matching keyset rather than a
/// host-supplied selector.
pub fn load_scp03_static_keys_for_version(
    parent_sd_aid: &Aid,
    key_version: u8,
) -> Option<(crate::core::scp03::StaticKeys, u8)> {
    let key_id = scp03_key_id_for_version(parent_sd_aid, key_version)?;
    Some((
        load_scp03_static_keys(parent_sd_aid, key_version, key_id)?,
        key_id,
    ))
}

/// Resolve selectors using metadata only; never decrypt keys to discover their ID.
fn scp03_key_id_for_version(parent_sd_aid: &Aid, key_version: u8) -> Option<u8> {
    let registry = crate::registry::read();
    let usable_mac = |id| {
        let aid = scp03_key_object_instance_aid(
            key_version,
            id,
            crate::security_domain::SCP03_PUT_KEY_USAGE_MAC,
        );
        registry
            .find_key_object(parent_sd_aid, &aid)
            .is_some_and(|object| {
                object.key_state() == Some(KeyObjectState::Active)
                    && object.key_metadata()
                        == Some((
                            KeyObjectType::Scp03Static,
                            key_version,
                            id,
                            crate::security_domain::SCP03_PUT_KEY_USAGE_MAC,
                            crate::security_domain::SCP03_STATIC_KEY_LEN,
                        ))
            })
    };
    let found = registry.entries().find_map(|object| {
        if object.parent_sd_aid != *parent_sd_aid
            || object.key_state() != Some(KeyObjectState::Active)
        {
            return None;
        }
        let (kind, version, id, usage, len) = object.key_metadata()?;
        (kind == KeyObjectType::Scp03Static
            && version == key_version
            && usage == crate::security_domain::SCP03_PUT_KEY_USAGE_ENC
            && len == crate::security_domain::SCP03_STATIC_KEY_LEN
            && (usable_mac(id) || id.checked_add(1).is_some_and(usable_mac)))
        .then_some(id)
    });
    found
}

fn load_scp03_static_keys_with_ids(
    parent_sd_aid: &Aid,
    key_version: u8,
    enc_key_id: u8,
    mac_key_id: u8,
) -> Option<crate::core::scp03::StaticKeys> {
    let enc_aid = scp03_key_object_instance_aid(
        key_version,
        enc_key_id,
        crate::security_domain::SCP03_PUT_KEY_USAGE_ENC,
    );
    let mac_aid = scp03_key_object_instance_aid(
        key_version,
        mac_key_id,
        crate::security_domain::SCP03_PUT_KEY_USAGE_MAC,
    );
    let enc_state = find_key_object_by_aid(parent_sd_aid, &enc_aid)?;
    let mac_state = find_key_object_by_aid(parent_sd_aid, &mac_aid)?;
    let enc = scp03_key_material_from_object(
        &enc_state,
        key_version,
        enc_key_id,
        crate::security_domain::Scp03KeyUsage::Enc,
    )?;
    let mac = scp03_key_material_from_object(
        &mac_state,
        key_version,
        mac_key_id,
        crate::security_domain::Scp03KeyUsage::Mac,
    )?;
    Some(crate::core::scp03::StaticKeys::aes128(enc, mac))
}

/// Loads one SCP03 key payload for a specific `(owner, version, id, usage)`.
///
/// This helper is used by the Rustlet Security Domain syscall path. Callers
/// must provide the owner instance AID explicitly so kernel policy decides
/// visibility before user-land touches key bytes.
pub fn load_scp03_key_material(
    parent_sd_aid: &Aid,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
    out: &mut [u8],
) -> Option<usize> {
    if key_id == 0 {
        let resolved_id = scp03_key_id_for_version(parent_sd_aid, key_version)?;
        return load_scp03_key_material(parent_sd_aid, key_version, resolved_id, usage, out);
    }
    load_scp03_key_material_with_id(parent_sd_aid, key_version, key_id, usage, out).or_else(|| {
        if usage != crate::security_domain::Scp03KeyUsage::Mac {
            return None;
        }
        let mac_key_id = key_id.checked_add(1)?;
        load_scp03_key_material_with_id(parent_sd_aid, key_version, mac_key_id, usage, out)
    })
}

fn load_scp03_key_material_with_id(
    parent_sd_aid: &Aid,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
    out: &mut [u8],
) -> Option<usize> {
    let instance_aid = scp03_key_object_instance_aid(key_version, key_id, usage.as_byte());
    let state = find_key_object_by_aid(parent_sd_aid, &instance_aid)?;
    read_scp03_key_material_from_object(&state, key_version, key_id, usage, out)
}

fn scp03_key_material_from_object(
    object: &ObjectView,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
) -> Option<[u8; crate::security_domain::SCP03_STATIC_KEY_LEN]> {
    let mut material = [0u8; crate::security_domain::SCP03_STATIC_KEY_LEN];
    read_scp03_key_material_from_object(object, key_version, key_id, usage, &mut material)?;
    Some(material)
}

fn read_scp03_key_material_from_object(
    object: &ObjectView,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
    out: &mut [u8],
) -> Option<usize> {
    if object.key_state()? != KeyObjectState::Active {
        return None;
    }
    let (key_type, stored_version, stored_id, stored_usage, raw_key) = object.key_metadata()?;
    if key_type != KeyObjectType::Scp03Static
        || stored_version != key_version
        || stored_id != key_id
        || stored_usage != usage.as_byte()
        || raw_key != crate::security_domain::SCP03_STATIC_KEY_LEN
    {
        return None;
    }
    if out.len() < raw_key {
        return None;
    }
    object.read_range(0, &mut out[..raw_key]).ok()
}

/// Deletes one SCP03 key object from the given Security Domain keyset.
#[allow(dead_code)]
pub fn delete_scp03_key_object(
    parent_sd_aid: Aid,
    key_version: u8,
    key_id: u8,
    usage: crate::security_domain::Scp03KeyUsage,
) -> RegistryResult {
    let object_aid = scp03_key_object_instance_aid(key_version, key_id, usage.as_byte());
    registry_operation(|| {
        registry_mut().delete_object(&parent_sd_aid, ManagedObjectKind::Key, &object_aid)
    })
}

fn is_security_domain_kind(kind: ManagedObjectKind) -> bool {
    matches!(kind, ManagedObjectKind::SecurityDomain)
}

pub fn active_security_domain_may_reach_instance(instance_aid: &Aid) -> bool {
    let active = active_security_domain_instance_aid();
    let registry = crate::registry::read();
    let Some(entry) = registry.find_identity(instance_aid) else {
        return false;
    };
    security_domain_may_reach_identity(&active, &entry.object(), entry.parent())
}

fn security_domain_may_reach_object(authority_aid: &Aid, object: &ObjectView) -> bool {
    security_domain_may_reach_identity(authority_aid, &object.object_aid, object.parent_sd_aid)
}

/// Authorization uses the BOSS identity graph, not decrypted payload metadata.
/// Read loans keep this graph stable throughout the decision, including nested
/// callers that already hold a decoded object. No second table is maintained.
fn security_domain_may_reach_identity(
    authority_aid: &Aid,
    object_aid: &Aid,
    mut parent_aid: Aid,
) -> bool {
    if object_aid == authority_aid {
        return true;
    }
    let registry = crate::registry::read();
    let mut remaining_hops = DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY;
    while remaining_hops != 0 {
        if parent_aid == *authority_aid {
            return true;
        }
        if parent_aid == top_level_parent_sd_aid() {
            return *authority_aid == root_security_domain_instance_aid();
        }
        let Some(slot) = registry.find_any_index(&parent_aid) else {
            return false;
        };
        if registry.identity_kind(slot) != Some(ManagedObjectKind::SecurityDomain) {
            return false;
        }
        parent_aid = registry.identity(slot).unwrap().parent();
        remaining_hops -= 1;
    }
    false // Corrupt/cyclic topology must fail closed.
}

/// Result of encoding one short-APDU page of `GET STATUS` records.
pub struct GetStatusPage {
    pub len: usize,
    pub next_slot: Option<usize>,
    pub found: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GetStatusEncodeError {
    InvalidRecord,
    OutputTooSmall,
}

/// Encodes one visible page of GP registry records in stable slot order.
///
/// `start_slot` is the continuation cursor returned by a previous page. The
/// registry itself remains the single source of truth; no object or response
/// record is copied into a pagination cache.
pub fn encode_get_status_page(
    authority_aid: &Aid,
    query: crate::gp_status::GetStatusQuery,
    start_slot: usize,
    out: &mut [u8],
) -> Result<GetStatusPage, GetStatusEncodeError> {
    let registry_guard = crate::registry::read();
    let registry = &*registry_guard;
    let root_sd_aid = crate::predeployment::root_instance_aid();
    let issuer_sd_aid = crate::predeployment::issuer_instance_aid();
    let mut slot = start_slot;
    let mut offset = 0usize;
    let mut found = false;

    while slot < DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY {
        let Some(object) = registry.resolve(slot) else {
            slot += 1;
            continue;
        };
        if !crate::gp_status::matches_category(query, &object, &root_sd_aid, issuer_sd_aid.as_ref())
            || !crate::gp_status::matches_aid(query, &object.object_aid)
            || !security_domain_may_reach_object(authority_aid, &object)
        {
            slot += 1;
            continue;
        }

        let record_len = crate::gp_status::encoded_record_len(query, &object, &root_sd_aid)
            .ok_or(GetStatusEncodeError::InvalidRecord)?;
        if record_len > out.len().saturating_sub(offset) {
            return if offset == 0 {
                Err(GetStatusEncodeError::OutputTooSmall)
            } else {
                Ok(GetStatusPage {
                    len: offset,
                    next_slot: Some(slot),
                    found,
                })
            };
        }
        let encoded =
            crate::gp_status::encode_record(query, &object, &root_sd_aid, &mut out[offset..])
                .map_err(|_| GetStatusEncodeError::InvalidRecord)?;
        if encoded != record_len {
            return Err(GetStatusEncodeError::InvalidRecord);
        }
        offset += encoded;
        found = true;
        slot += 1;
    }

    Ok(GetStatusPage {
        len: offset,
        next_slot: None,
        found,
    })
}

fn save_selected_instance_state(
    security_domain_aid: &Aid,
    package_aid: &Aid,
    _applet_aid: &Aid,
    instance_aid: &Aid,
    install_privileges: Option<&[u8]>,
) -> apdu_manager::ApduStatus {
    let result = registry_operation(|| {
        let mut selected_app = selected_app_mut().ok_or(RegistryError::InvalidState)?;
        let state = selected_app
            .loaded_fae
            .shared_buffer()
            .state_bytes()
            .ok_or(RegistryError::InvalidState)?;
        let inserted = {
            let mut registry = crate::registry::edit();
            if !selected_app.loaded_fae.is_security_domain() {
                registry.upsert_instance_object(
                    *security_domain_aid,
                    *instance_aid,
                    *package_aid,
                    &state,
                )
            } else {
                let privileges = registry
                    .find_security_domain_object(security_domain_aid, instance_aid)
                    .and_then(|object| object.security_domain_privilege_bytes())
                    .or_else(|| {
                        install_privileges.map(|bytes| {
                            [
                                bytes.first().copied().unwrap_or(0),
                                bytes.get(1).copied().unwrap_or(0),
                                bytes.get(2).copied().unwrap_or(0),
                            ]
                        })
                    })
                    .unwrap_or([0; 3]);
                registry.upsert_security_domain_object(
                    *security_domain_aid,
                    *instance_aid,
                    *package_aid,
                    SecurityDomainObjectBackend::RustletSecurityDomain,
                    privileges,
                    &state,
                )
            }
        };
        drop(state);
        selected_app.loaded_fae.shared_buffer().clear_state();
        inserted?;
        let kind = if !selected_app.loaded_fae.is_security_domain() {
            ManagedObjectKind::Instance
        } else {
            ManagedObjectKind::SecurityDomain
        };
        let instance = crate::registry::read()
            .find_index(security_domain_aid, kind, instance_aid)
            .ok_or(RegistryError::InvalidState)?;
        selected_app.registry = AppRegistryReference::Installed {
            package: selected_app.registry.package_index(),
            instance,
        };
        Ok(())
    });
    registry_result_status(result)
}

// Resolve identity after Rustlet exit so AID copies do not occupy the kernel
// stack during nested SVC and crypto calls.
#[inline(never)]
fn save_selected_security_domain_state(
    reference: AppRegistryReference,
) -> apdu_manager::ApduStatus {
    let Some((security_domain_aid, package_aid, _, instance_aid)) = reference.identity() else {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    };
    let result = registry_operation(|| {
        let selected = selected_security_domain_mut().ok_or(RegistryError::InvalidState)?;
        let state = selected
            .loaded_fae
            .shared_buffer()
            .state_bytes()
            .ok_or(RegistryError::InvalidState)?;
        let inserted = {
            let mut registry = crate::registry::edit();
            let privileges = registry
                .find_security_domain_object(&security_domain_aid, &instance_aid)
                .and_then(|object| object.security_domain_privilege_bytes())
                .unwrap_or([0; 3]);
            registry.upsert_security_domain_object(
                security_domain_aid,
                instance_aid,
                package_aid,
                SecurityDomainObjectBackend::RustletSecurityDomain,
                privileges,
                &state,
            )
        };
        drop(state);
        selected.loaded_fae.shared_buffer().clear_state();
        inserted
    });
    registry_result_status(result)
}

fn selected_app_mut() -> Option<KernelRefMut<'static, LoadedApp>> {
    current_selected_app_mut().or_else(|| {
        SELECTED_SECURITY_DOMAIN
            .borrow_mut()
            .filter_map(Option::as_mut)
    })
}

fn current_selected_app_mut() -> Option<KernelRefMut<'static, LoadedApp>> {
    SELECTED_APP.borrow_mut().filter_map(Option::as_mut)
}

fn selected_security_domain_mut() -> Option<KernelRefMut<'static, LoadedApp>> {
    let app = SELECTED_APP.borrow_mut().filter_map(|slot| {
        slot.as_mut()
            .filter(|app| app.loaded_fae.is_security_domain())
    });
    app.or_else(|| {
        SELECTED_SECURITY_DOMAIN
            .borrow_mut()
            .filter_map(Option::as_mut)
    })
}

fn selected_app_matches_install_target(
    security_domain_aid: &Aid,
    package_aid: &Aid,
    applet_aid: &Aid,
) -> bool {
    let Some(selected_app) = current_selected_app_mut() else {
        return false;
    };

    selected_app.registry.security_domain_aid() == Some(*security_domain_aid)
        && selected_app.registry.package_aid() == Some(*package_aid)
        && selected_app.registry.applet_aid() == Some(*applet_aid)
}

/// Resolves the complete owned flash extent without enlarging the FAE slice.
fn package_text_window(fae: &'static [u8]) -> Option<oxi_core::core::isolation::AppMemoryWindow> {
    use oxi_core::core::isolation::AppMemoryWindow;
    let start = fae.as_ptr() as usize;
    if let Some(area) = persistent_registry_area_bytes() {
        let area_start = area.as_ptr() as usize;
        if start >= area_start && start < area_start.checked_add(area.len())? {
            let offset = start
                .checked_sub(area_start)?
                .checked_sub(registry_persistence::OBJECT_BLOCK_HEADER_LEN)?;
            let block = registry_persistence::decode_object_block_at(
                area,
                offset,
                crate::registry::physical::logical_page_size(),
            )
            .ok()?;
            if block.magic != registry_persistence::PACKAGE_BLOCK_MAGIC
                || block.payload.as_ptr() != fae.as_ptr()
                || block.payload.len() != fae.len()
            {
                return None;
            }
            return Some(AppMemoryWindow {
                start: area_start + offset,
                len: block.total_len,
            });
        }
    }
    // Embedded packages use dedicated aligned statics, including their tail.
    let (start, len) = fae_runtime::aligned_text_window(start, fae.len())?;
    Some(AppMemoryWindow { start, len })
}

/// F-07: fixed synthetic key only; never accepts an arbitrary key/AID or returns
/// key material. Inspect actual persistent bytes, not the plaintext serializer.
#[cfg(oxide_se_kernel_app_module = "integrity-test")]
pub(crate) fn integrity_key_storage(mode: u8) -> Option<[u8; 4]> {
    if mode > 3 {
        return None;
    }
    let owner = root_security_domain_instance_aid();
    let usage = crate::security_domain::Scp03KeyUsage::Enc;
    let aid = scp03_key_object_instance_aid(0xfd, 0xfd, usage.as_byte());
    let marker = [if mode < 2 { 0xc7 } else { 0x39 }; 16];
    if mode % 2 == 0 {
        upsert_scp03_key_object(owner, 0xfd, 0xfd, usage, &marker).ok()?;
    }
    let registry = crate::registry::read();
    let slot = registry.find_index(&owner, ManagedObjectKind::Key, &aid)?;
    let address = registry.image.slot(slot)?.address();
    let object = registry.find_key_object(&owner, &aid)?;
    let area = persistent_registry_area_bytes()?;
    let block = crate::registry::recovery::persistent_payload_at_address(
        area,
        crate::registry::physical::logical_page_size(),
        address,
    )?;
    let mut readback = [0; 16];
    let logical = object.content_len().ok()? == marker.len()
        && object.read_range(0, &mut readback).ok()? == marker.len()
        && readback == marker;
    // Scan the entire persistence area, including obsolete copies and BOSSes.
    // This is a plaintext-exposure regression, not a cryptographic proof.
    Some([
        u8::from(block.magic == registry_persistence::ENCRYPTED_KEY_MAGIC),
        u8::from(logical),
        u8::from(!area.windows(16).any(|w| w == [0xc7; 16])),
        u8::from(!area.windows(16).any(|w| w == [0x39; 16])),
    ])
}

/// Diagnostic-only ownership witnesses for the dynamic mapping regression.
/// Returns C0DE/FAE bounds and two root-owned marker addresses and values.
#[cfg(oxide_se_kernel_app_module = "integrity-test")]
pub(crate) fn integrity_package_mapping(aid: &Aid, out: &mut [u8]) -> Option<usize> {
    let owner = root_security_domain_instance_aid();
    let fae = crate::registry::read()
        .find_package_object(&owner, aid)?
        .package_binary_code()?;
    let window = package_text_window(fae)?;
    let area = persistent_registry_area_bytes()?;
    let page_size = crate::registry::physical::logical_page_size();
    let mut words = [
        window.start,
        window.len,
        fae.as_ptr() as usize,
        fae.len(),
        0,
        0,
        0,
        0,
    ];
    for (i, tag) in [0xdf31, 0xdf32].into_iter().enumerate() {
        let slot = crate::registry::read().find_index(
            &owner,
            ManagedObjectKind::Data,
            &gp_data_object_aid(tag),
        )?;
        let address = crate::registry::read().image.slot(slot)?.address();
        let block =
            crate::registry::recovery::persistent_payload_at_address(area, page_size, address)?;
        if block.magic != registry_persistence::ENCRYPTED_DATA_MAGIC {
            return None;
        }
        let object = crate::registry::read().find_data_object(&owner, &gp_data_object_aid(tag))?;
        let mut value = [0u8; 4];
        if object.content_len().ok()? != value.len()
            || object.read_range(0, &mut value).ok()? != value.len()
        {
            return None;
        }
        // Report the physical ciphertext location and the logical value separately.
        words[4 + i] = block.payload.as_ptr() as usize;
        words[6 + i] = u32::from_le_bytes(value) as usize;
    }
    let output = out.get_mut(..32)?;
    for (word, bytes) in words.into_iter().zip(output.chunks_exact_mut(4)) {
        bytes.copy_from_slice(&u32::try_from(word).ok()?.to_le_bytes());
    }
    Some(output.len())
}

fn activate_registry_reference(reference: AppRegistryReference) -> apdu_manager::ApduStatus {
    if !reference.is_valid() {
        return apdu_manager::ApduStatus::file_not_found();
    }
    let previous = SELECTED_APP
        .borrow()
        .as_ref()
        .map(|app| (app.registry, app.loaded_fae.is_security_domain()));
    if let Some((previous, is_sd)) = previous {
        if previous != reference {
            if is_sd {
                promote_selected_app_to_security_domain();
            } else {
                set_selected_app(None);
            }
        }
    }

    let Some(fae) = reference.fae() else {
        return apdu_manager::ApduStatus::file_not_found();
    };
    let Some(text_window) = package_text_window(fae) else {
        return apdu_manager::ApduStatus::conditions_not_satisfied();
    };
    let mut loaded = match fae_runtime::load(fae, text_window) {
        Ok(loaded) => loaded,
        Err(fae_runtime::LoadError::InsufficientMemory) => {
            return apdu_manager::ApduStatus::insufficient_memory();
        }
        Err(fae_runtime::LoadError::Unsupported) => {
            return apdu_manager::ApduStatus::conditions_not_satisfied();
        }
    };
    match fae_runtime::call_start(&mut loaded) {
        Ok(()) => (),
        Err(status) => {
            fae_runtime::unload(loaded);
            return from_abi_status(status);
        }
    };

    match install_selected_app(reference, loaded) {
        Ok(()) => apdu_manager::ApduStatus::success(),
        Err(status) => status,
    }
}

impl Drop for AllocatorMetadata {
    fn drop(&mut self) {
        // SAFETY: metadata has one owner and the original Layout. The allocator
        // binding is retired before its owning LoadedApp can be dropped.
        unsafe {
            oxi_core::core::secure_zero_raw(self.ptr, self.len);
            oxi_core::core::dealloc(self.ptr, self.layout);
        }
    }
}

fn drop_loaded_app(app: LoadedApp) {
    drop(app);
}

fn set_selected_app(app: Option<LoadedApp>) {
    // A selected SD can occupy this slot before promotion to the resident slot.
    SD_DISPATCH_INSTANCE.set(None);
    {
        let previous = SELECTED_APP.replace(app);
        if let Some(previous) = previous {
            drop_loaded_app(previous);
        }
    }
}

fn set_selected_security_domain(app: Option<LoadedApp>) {
    // Changing the identity cannot transfer a live SDDISPATCH authorization.
    SD_DISPATCH_INSTANCE.set(None);
    {
        let previous = SELECTED_SECURITY_DOMAIN.replace(app);
        if let Some(previous) = previous {
            drop_loaded_app(previous);
        }
    }
}

/// Drops volatile SD heaps on authority changes without invoking another hook.
/// A later selection reconstructs administrative state from the registry.
pub(crate) fn retire_security_domain_runtime() {
    let selected_is_sd = SELECTED_APP
        .borrow()
        .as_ref()
        .is_some_and(|app| app.loaded_fae.is_security_domain());
    if selected_is_sd {
        set_selected_app(None);
    }
    set_selected_security_domain(None);
}

pub fn promote_selected_app_to_security_domain() {
    {
        let selected = SELECTED_APP.replace(None);
        // Invariant: reselecting an already active rustlet Security Domain may
        // dispatch through the persisted SD slot without repopulating
        // `SELECTED_APP`. In that case the promotion is already satisfied and
        // must remain a no-op.
        if selected.is_none() {
            return;
        }
        set_selected_security_domain(selected);
    }
}

// Inline this scalar snapshot so syscall validation can load only the windows
// it needs instead of retaining an aggregate return slot on the kernel stack.
#[inline(always)]
fn active_app_call() -> Option<ActiveAppCall> {
    ACTIVE_APP_CALL.get()
}

fn sd_dispatch_active() -> bool {
    SD_DISPATCH_INSTANCE.get().is_some()
}

fn set_active_app_call(call: Option<ActiveAppCall>) {
    RESTORE_REFERENCE.set(None);
    RESTORE_PHASE.set(0);
    // Never let a new ordinary invocation inherit a previous SD's authority.
    SD_DISPATCH_INSTANCE.set(None);
    ACTIVE_APP_CALL.set(call);
}

fn crypto_error_word(error: CryptoErrorCode) -> usize {
    rustlet_runtime::syscall_abi::CRYPTO_RESULT_ERROR_FLAG | error.word()
}

fn from_abi_status(status: rustlet_runtime::ApduStatus) -> apdu_manager::ApduStatus {
    apdu_manager::ApduStatus {
        sw1: status.sw1,
        sw2: status.sw2,
    }
}

fn app_exit_observer(event: oxi_core::core::isolation::AppExitEvent) {
    let active_call = active_app_call();
    // Retire authority before handling a requested exit, fault or watchdog
    // termination. Cleanup uses the captured context, not a live authorization.
    set_active_app_call(None);
    if let Some(active_call) = active_call {
        complete_abrupt_app_call(active_call);
        clear_abrupt_app_shared_page(active_call);
    }
    let _ = event;
}

fn complete_abrupt_app_call(mut active_call: ActiveAppCall) {
    // SAFETY: the exit callback runs inside the live invocation scope after
    // suspending the Rustlet; no APDU SVC loan survives terminal exit.
    let Some(transport) = (unsafe { active_call_transport(&mut active_call) }) else {
        return;
    };

    transport.abort_remaining_io();
}

fn clear_abrupt_app_shared_page(active_call: ActiveAppCall) {
    // SAFETY: terminal exit suspends the Rustlet permanently. The invocation
    // retains the page, and no SVC borrow survives this callback.
    let _page = unsafe { crate::shared_page::Lease::syscall() };
    unsafe {
        oxi_core::core::secure_zero_raw(
            active_call.shared_buffer.cast(),
            core::mem::size_of::<RustletCtx>(),
        );
    }
}

/// # Safety
/// The captured invocation must still own the live transport exclusively;
/// no other SVC or kernel reference may access it during this loan.
unsafe fn active_call_transport(
    active_call: &mut ActiveAppCall,
) -> Option<&mut apdu_manager::TransportApdu> {
    if active_call.transport.is_null() {
        return None;
    }
    // SAFETY: the caller establishes validity and exclusion; the context
    // borrow bounds the returned reference.
    Some(unsafe { &mut *active_call.transport })
}

/// # Safety
/// SVC entry must suspend the Rustlet and lend its APDU page for this call.
unsafe fn running_se_apdu(active_call: &mut ActiveAppCall) -> Option<RunningSEApdu<'_>> {
    if active_call.transport.is_null() {
        return None;
    }
    // SAFETY: the caller establishes the synchronous ABI loan. The lease
    // rejects reentry and both references are bounded by this captured context.
    let page = unsafe { crate::shared_page::Lease::syscall() };
    Some(RunningSEApdu {
        transport: unsafe { &mut *active_call.transport },
        shared_buffer: unsafe { &mut *active_call.shared_buffer },
        _page: page,
    })
}

impl SEApdu for RunningSEApdu<'_> {
    fn header(&self) -> SEApduHeader {
        SEApduHeader {
            cla: self.transport.cla(),
            ins: self.transport.ins(),
            p1: self.transport.p1(),
            p2: self.transport.p2(),
            p3: self.transport.ln(),
        }
    }

    fn buffer_mut(&mut self) -> &mut [u8] {
        &mut self.shared_buffer.data
    }

    fn incoming_data(&self) -> &[u8] {
        self.shared_buffer.incoming_data()
    }

    fn set_incoming_and_receive(&mut self) -> usize {
        let Some(incoming_len) = self
            .transport
            .receive_incoming_into_for_runtime(&mut self.shared_buffer.data)
        else {
            return 0;
        };
        if !self.shared_buffer.stage_incoming_len(incoming_len) {
            return 0;
        }
        incoming_len
    }

    fn set_outgoing(&mut self) -> usize {
        let requested = self.transport.begin_outgoing_for_runtime();
        self.shared_buffer.set_outgoing();
        requested
    }

    fn set_outgoing_length(&mut self, len: usize) {
        if !self.transport.outgoing_started() {
            let _ = self.transport.begin_outgoing_for_runtime();
        }
        self.transport.set_outgoing_length_for_runtime(len);
        self.shared_buffer.set_outgoing_length(len);
    }
}

unsafe extern "C" fn apdu_set_incoming_and_receive_syscall(
    _arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return 0;
    };

    let Some(mut apdu) = (unsafe { running_se_apdu(&mut active_call) }) else {
        return 0;
    };
    apdu.set_incoming_and_receive()
}

unsafe extern "C" fn apdu_set_outgoing_syscall(
    _arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return 0;
    };

    let Some(mut apdu) = (unsafe { running_se_apdu(&mut active_call) }) else {
        return 0;
    };
    let _ = apdu.set_outgoing();
    0
}

unsafe extern "C" fn apdu_set_outgoing_length_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    // An untrusted length must not reach the transport's programming-error
    // panic or change the APDU phase. This void ABI ignores invalid requests.
    if arg0 > rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX {
        return 0;
    }
    let Some(mut active_call) = active_app_call() else {
        return 0;
    };

    let Some(mut apdu) = (unsafe { running_se_apdu(&mut active_call) }) else {
        return 0;
    };
    apdu.set_outgoing_length(arg0);
    0
}

// SVC-PERF: svc=9; replay=9; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_cipher_do_final_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // Inputs may also use the active image text; outputs require writable RAM.
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoCipherDoFinalParams>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let Some(mode) = decode_cipher_mode(params.mode) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    let Some(algorithm) = decode_cipher_algorithm(params.algorithm) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    if params.iv_len != oxi_core::core::crypto::AES_BLOCK_SIZE {
        return crypto_error_word(CryptoErrorCode::InvalidBufferLength);
    }
    if !key_len_matches_algorithm(params.key_len, algorithm) {
        return crypto_error_word(CryptoErrorCode::InvalidKeyLength);
    }
    let Some(key_slice) = memory.read(params.key_ptr, params.key_len) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let Some(iv_slice) = memory.read(params.iv_ptr, params.iv_len) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let mut iv = [0u8; oxi_core::core::crypto::AES_BLOCK_SIZE];
    iv.copy_from_slice(iv_slice);
    let key = match oxi_core::core::crypto::AesKey::from_bytes(key_slice) {
        Ok(key) => key,
        Err(error) => {
            return crypto_error_word(map_core_crypto_error(error));
        }
    };

    let padded_encrypt = matches!(mode, CipherMode::Encrypt)
        && matches!(
            algorithm,
            CipherAlgorithm::Aes128CbcIso9797M2 | CipherAlgorithm::Aes256CbcIso9797M2
        );
    if !padded_encrypt
        && !params
            .input_len
            .is_multiple_of(oxi_core::core::crypto::AES_BLOCK_SIZE)
    {
        return crypto_error_word(CryptoErrorCode::InvalidBufferLength);
    }
    let required = if padded_encrypt {
        params
            .input_len
            .checked_add(oxi_core::core::crypto::AES_BLOCK_SIZE)
            .map(|len| len & !(oxi_core::core::crypto::AES_BLOCK_SIZE - 1))
    } else {
        Some(params.input_len)
    };
    if required.is_none_or(|len| params.output_capacity < len) {
        return crypto_error_word(CryptoErrorCode::InvalidOutputLength);
    }
    let Some(output) = memory.copy_to_output(
        params.input_ptr,
        params.input_len,
        params.output_ptr,
        params.output_capacity,
    ) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let result = match (mode, algorithm) {
        (CipherMode::Encrypt, CipherAlgorithm::Aes128CbcNoPadding)
        | (CipherMode::Encrypt, CipherAlgorithm::Aes256CbcNoPadding) => {
            oxi_core::core::crypto::aes_cbc_encrypt_in_place(
                &key,
                &iv,
                &mut output[..params.input_len],
            )
            .map(|_| params.input_len)
        }
        (CipherMode::Decrypt, CipherAlgorithm::Aes128CbcNoPadding)
        | (CipherMode::Decrypt, CipherAlgorithm::Aes256CbcNoPadding) => {
            oxi_core::core::crypto::aes_cbc_decrypt_in_place(
                &key,
                &iv,
                &mut output[..params.input_len],
            )
            .map(|_| params.input_len)
        }
        (CipherMode::Encrypt, CipherAlgorithm::Aes128CbcIso9797M2)
        | (CipherMode::Encrypt, CipherAlgorithm::Aes256CbcIso9797M2) => {
            oxi_core::core::crypto::aes_cbc_encrypt_iso9797_m2_in_place(
                &key,
                &iv,
                output,
                params.input_len,
            )
        }
        (CipherMode::Decrypt, CipherAlgorithm::Aes128CbcIso9797M2)
        | (CipherMode::Decrypt, CipherAlgorithm::Aes256CbcIso9797M2) => {
            oxi_core::core::crypto::aes_cbc_decrypt_iso9797_m2_in_place(
                &key,
                &iv,
                &mut output[..params.input_len],
            )
        }
        (CipherMode::Encrypt, CipherAlgorithm::Aes128EcbNoPadding)
        | (CipherMode::Encrypt, CipherAlgorithm::Aes256EcbNoPadding) => {
            oxi_core::core::crypto::aes_ecb_encrypt_in_place(&key, &mut output[..params.input_len])
                .map(|_| params.input_len)
        }
        (CipherMode::Decrypt, CipherAlgorithm::Aes128EcbNoPadding)
        | (CipherMode::Decrypt, CipherAlgorithm::Aes256EcbNoPadding) => {
            oxi_core::core::crypto::aes_ecb_decrypt_in_place(&key, &mut output[..params.input_len])
                .map(|_| params.input_len)
        }
    };
    match result {
        Ok(len) => len,
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

// SVC-PERF: svc=10; replay=10; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_random_generate_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoRandomGenerateParams>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    if decode_random_algorithm(params.algorithm).is_none() {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    }
    let Some(output) = memory.write(params.output_ptr, params.output_len) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    match oxi_core::core::crypto::fill_random(output) {
        Ok(()) => 0,
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

// SVC-PERF: svc=11; replay=11; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_mac_do_final_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoMacDoFinalParams>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    // Application MAC is independent from the future SCP03 secure-channel MAC.
    let Some(algorithm) = decode_mac_algorithm(params.algorithm) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    let Ok(operation) = decode_mac_operation(params.operation) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    if !mac_key_len_matches_algorithm(params.key_len, algorithm) {
        return crypto_error_word(CryptoErrorCode::InvalidKeyLength);
    }
    let Some(key_slice) = memory.read(params.key_ptr, params.key_len) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let Some(input) = memory.read(params.input_ptr, params.input_len) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let key = match oxi_core::core::crypto::AesKey::from_bytes(key_slice) {
        Ok(key) => key,
        Err(error) => return crypto_error_word(map_core_crypto_error(error)),
    };

    let mut tag = [0u8; oxi_core::core::crypto::AES_CMAC_SIZE];
    if let Err(error) = match algorithm {
        MacAlgorithm::AesCmac => oxi_core::core::crypto::aes_cmac(&key, input, &mut tag),
    } {
        return crypto_error_word(map_core_crypto_error(error));
    }

    match operation {
        CryptoMacOperation::Compute => {
            if params.output_capacity < tag.len() {
                return crypto_error_word(CryptoErrorCode::PermissionDenied);
            }
            let Some(output) = memory.write(params.output_ptr, params.output_capacity) else {
                return crypto_error_word(CryptoErrorCode::PermissionDenied);
            };
            output[..tag.len()].copy_from_slice(&tag);
            tag.len()
        }
        CryptoMacOperation::Verify => {
            if params.expected_tag_len != tag.len() {
                return crypto_error_word(CryptoErrorCode::InvalidBufferLength);
            }
            let Some(expected) = memory.read(params.expected_tag_ptr, params.expected_tag_len)
            else {
                return crypto_error_word(CryptoErrorCode::InvalidBufferLength);
            };
            if constant_time_eq(&tag, expected) {
                1
            } else {
                0
            }
        }
    }
}

unsafe extern "C" fn security_domain_load_scp03_key_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    // SAFETY: SVC entry suspends the active Rustlet for the complete call.
    unsafe { load_sd_key_for_call(active_app_call(), arg0) }
}

/// Loads a key under the captured invocation authority.
///
/// # Safety
/// An active call must describe live, initialized memory exclusively available
/// to this synchronous syscall while its Rustlet is suspended on the owner core.
unsafe fn load_sd_key_for_call(active_call: Option<ActiveAppCall>, params_addr: usize) -> usize {
    if !sd_dispatch_active() {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    }
    let Some(mut active_call) = active_call else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let Some(instance_aid) = SD_DISPATCH_INSTANCE.get().and_then(|slot| {
        crate::registry::read()
            .resolve(slot)
            .map(|object| object.object_aid)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<Scp03LoadKeyParams>(&mut active_call, params_addr)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let Some(output) = memory.write(params.output_ptr, params.output_capacity) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    let Some(usage) = crate::security_domain::Scp03KeyUsage::from_byte(params.usage) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    match load_scp03_key_material(
        &instance_aid,
        params.key_version,
        params.key_id,
        usage,
        output,
    ) {
        Some(len) => len,
        None => crypto_error_word(CryptoErrorCode::NotFound),
    }
}

// SVC-PERF: svc=13; replay=13; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_ec_generate_keypair_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoEcGenerateKeypairParams>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let Some(curve) = decode_ec_curve(params.curve) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    if params.private_key_capacity != oxi_core::core::crypto::P256_PRIVATE_KEY_SIZE
        || params.public_key_capacity != oxi_core::core::crypto::P256_PUBLIC_KEY_UNCOMPRESSED_SIZE
    {
        return crypto_error_word(CryptoErrorCode::InvalidOutputLength);
    }
    let Some((private_key, public_key)) = memory.write_pair(
        (params.private_key_ptr, params.private_key_capacity),
        (params.public_key_ptr, params.public_key_capacity),
    ) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let result = match curve {
        oxi_core::core::crypto::EcCurve::P256 => {
            oxi_core::core::crypto::p256_generate_keypair(private_key, public_key)
        }
    };
    match result {
        Ok(()) => 0,
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

// SVC-PERF: svc=14; replay=14; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_ecdh_do_final_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoEcdhDoFinalParams>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let Some(curve) = decode_ec_curve(params.curve) else {
        return crypto_error_word(CryptoErrorCode::Unsupported);
    };
    if params.private_key_len != oxi_core::core::crypto::P256_PRIVATE_KEY_SIZE {
        return crypto_error_word(CryptoErrorCode::InvalidKeyLength);
    }
    if params.output_capacity != oxi_core::core::crypto::P256_SHARED_SECRET_SIZE {
        return crypto_error_word(CryptoErrorCode::InvalidOutputLength);
    }
    let Some((private_key, peer_public_key, output)) = memory.read_pair_write(
        (params.private_key_ptr, params.private_key_len),
        (params.peer_public_key_ptr, params.peer_public_key_len),
        (params.output_ptr, params.output_capacity),
    ) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    let result = match curve {
        oxi_core::core::crypto::EcCurve::P256 => {
            oxi_core::core::crypto::p256_ecdh(private_key, peer_public_key, output)
                .map(|_| oxi_core::core::crypto::P256_SHARED_SECRET_SIZE)
        }
    };
    match result {
        Ok(len) => len,
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

// SVC-PERF: svc=15; replay=15; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_hkdf_sha256_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoHkdfSha256Params>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    if params.output_capacity == 0 {
        return crypto_error_word(CryptoErrorCode::InvalidOutputLength);
    }
    let Some(([ikm, salt, info], [output])) = memory.buffers(
        [
            (params.ikm_ptr, params.ikm_len),
            (params.salt_ptr, params.salt_len),
            (params.info_ptr, params.info_len),
        ],
        [(params.output_ptr, params.output_capacity)],
    ) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    match oxi_core::core::crypto::hkdf_sha256(ikm, salt, info, output) {
        Ok(()) => output.len(),
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

// SVC-PERF: svc=16; replay=16; see docs/kernel.developer.guide.md#svc-performance-maintenance.
unsafe extern "C" fn crypto_x963_sha256_syscall(
    arg0: usize,
    _arg1: usize,
    _arg2: usize,
    _arg3: usize,
) -> usize {
    let Some(mut active_call) = active_app_call() else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };
    // SAFETY: this synchronous SVC owns the suspended Rustlet memory until return.
    let Some((mut memory, params)) = (unsafe {
        syscall_memory::Memory::request::<CryptoX963Sha256Params>(&mut active_call, arg0)
    }) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    if params.output_capacity == 0 {
        return crypto_error_word(CryptoErrorCode::InvalidOutputLength);
    }
    let Some((shared_secret, shared_info, output)) = memory.read_pair_write(
        (params.shared_secret_ptr, params.shared_secret_len),
        (params.shared_info_ptr, params.shared_info_len),
        (params.output_ptr, params.output_capacity),
    ) else {
        return crypto_error_word(CryptoErrorCode::PermissionDenied);
    };

    match oxi_core::core::crypto::x963_sha256_kdf(shared_secret, shared_info, output) {
        Ok(()) => output.len(),
        Err(error) => crypto_error_word(map_core_crypto_error(error)),
    }
}

fn decode_cipher_mode(mode: u8) -> Option<CipherMode> {
    match mode {
        1 => Some(CipherMode::Encrypt),
        2 => Some(CipherMode::Decrypt),
        _ => None,
    }
}

fn decode_cipher_algorithm(algorithm: u8) -> Option<CipherAlgorithm> {
    match algorithm {
        1 => Some(CipherAlgorithm::Aes128CbcNoPadding),
        2 => Some(CipherAlgorithm::Aes256CbcNoPadding),
        3 => Some(CipherAlgorithm::Aes128CbcIso9797M2),
        4 => Some(CipherAlgorithm::Aes256CbcIso9797M2),
        5 => Some(CipherAlgorithm::Aes128EcbNoPadding),
        6 => Some(CipherAlgorithm::Aes256EcbNoPadding),
        _ => None,
    }
}

fn key_len_matches_algorithm(len: usize, algorithm: CipherAlgorithm) -> bool {
    match algorithm {
        CipherAlgorithm::Aes128CbcNoPadding | CipherAlgorithm::Aes128CbcIso9797M2 => {
            len == oxi_core::core::crypto::AES128_KEY_SIZE
        }
        CipherAlgorithm::Aes256CbcNoPadding | CipherAlgorithm::Aes256CbcIso9797M2 => {
            len == oxi_core::core::crypto::AES256_KEY_SIZE
        }
        CipherAlgorithm::Aes128EcbNoPadding => len == oxi_core::core::crypto::AES128_KEY_SIZE,
        CipherAlgorithm::Aes256EcbNoPadding => len == oxi_core::core::crypto::AES256_KEY_SIZE,
    }
}

fn decode_random_algorithm(algorithm: u8) -> Option<RandomAlgorithm> {
    match algorithm {
        1 => Some(RandomAlgorithm::SecureRandom),
        _ => None,
    }
}

fn decode_mac_algorithm(algorithm: u8) -> Option<MacAlgorithm> {
    match algorithm {
        1 => Some(MacAlgorithm::AesCmac),
        _ => None,
    }
}

fn decode_mac_operation(operation: u8) -> Result<CryptoMacOperation, ()> {
    match operation {
        value if value == CryptoMacOperation::Compute as u8 => Ok(CryptoMacOperation::Compute),
        value if value == CryptoMacOperation::Verify as u8 => Ok(CryptoMacOperation::Verify),
        _ => Err(()),
    }
}

fn decode_ec_curve(curve: u8) -> Option<oxi_core::core::crypto::EcCurve> {
    match curve {
        value if value == CryptoEcCurve::P256 as u8 => Some(oxi_core::core::crypto::EcCurve::P256),
        _ => None,
    }
}

fn mac_key_len_matches_algorithm(len: usize, algorithm: MacAlgorithm) -> bool {
    match algorithm {
        MacAlgorithm::AesCmac => {
            len == oxi_core::core::crypto::AES128_KEY_SIZE
                || len == oxi_core::core::crypto::AES256_KEY_SIZE
        }
    }
}

fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }

    let mut diff = 0u8;
    for index in 0..left.len() {
        diff |= left[index] ^ right[index];
    }
    diff == 0
}

fn map_core_crypto_error(error: oxi_core::core::crypto::CryptoError) -> CryptoErrorCode {
    match error {
        oxi_core::core::crypto::CryptoError::InvalidKeyLength => CryptoErrorCode::InvalidKeyLength,
        oxi_core::core::crypto::CryptoError::InvalidBufferLength => {
            CryptoErrorCode::InvalidBufferLength
        }
        oxi_core::core::crypto::CryptoError::InvalidOutputLength => {
            CryptoErrorCode::InvalidOutputLength
        }
        oxi_core::core::crypto::CryptoError::Busy
        | oxi_core::core::crypto::CryptoError::Unsupported => CryptoErrorCode::Unsupported,
        oxi_core::core::crypto::CryptoError::EntropyUnavailable => CryptoErrorCode::Unsupported,
    }
}

/// Encodes a typed registry outcome before command-specific GP normalization.
pub(crate) fn registry_result_status(result: RegistryResult) -> apdu_manager::ApduStatus {
    match result {
        Ok(()) => apdu_manager::ApduStatus::success(),
        Err(error) => error.status(),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    #[test]
    fn data_range_read_checks_eof_and_preserves_output_on_rejection() {
        let _lock = reset_registry_test_state();
        let parent = Aid::from_array([0xf0, 0x01]);
        registry_mut()
            .upsert_data_object(parent, gp_data_object_aid(0xd001), b"abcdef")
            .unwrap();
        let mut out = [0xa5; 3];
        assert_eq!(
            load_registry_data_object_range(&parent, 0xd001, 2, &mut out),
            Ok(3)
        );
        assert_eq!(&out, b"cde");
        assert_eq!(
            load_registry_data_object_range(&parent, 0xd001, 5, &mut out),
            Ok(1)
        );
        assert_eq!(out[0], b'f');
        let prior = out;
        assert_eq!(
            load_registry_data_object_range(&parent, 0xd001, 6, &mut out),
            Ok(0)
        );
        assert_eq!(
            load_registry_data_object_range(&parent, 0xd001, usize::MAX, &mut out),
            Err(RegistryError::InvalidData)
        );
        assert_eq!(out, prior);
    }

    use super::*;
    use crate::security_domain::{Scp03KeyUsage, SCP03_STATIC_KEY_LEN};
    use std::sync::{Mutex, MutexGuard};

    const OWNER_A: Aid = Aid::from_array([0xA0, 0x00, 0x00, 0x47, 0x50, 0x4F, 0x53, 0x41]);
    const OWNER_B: Aid = Aid::from_array([0xA0, 0x00, 0x00, 0x47, 0x50, 0x4F, 0x53, 0x42]);
    static REGISTRY_TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn rollback_services_require_kernel_authorization_and_order() {
        let _lock = reset_registry_test_state();
        set_active_app_call(None);
        assert_eq!(unsafe { reset_rollback_heap_syscall(0, 0, 0, 0) }, 0x6985);
        assert_eq!(unsafe { load_rollback_state_syscall(0, 0, 0, 0) }, 0x6985);
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        let mut ctx = RustletCtx::new();
        // A forged user-visible flag cannot grant kernel restoration authority.
        ctx.request_persistent_restore(true);
        set_active_app_call(Some(ActiveAppCall {
            caller: Aid::empty(),
            transport: core::ptr::null_mut(),
            shared_buffer: &mut ctx,
            shared_window: empty,
            text_window: empty,
            data_window: empty,
            stack_window: empty,
        }));
        assert_eq!(unsafe { reset_rollback_heap_syscall(0, 0, 0, 0) }, 0x6985);
        assert_eq!(unsafe { load_rollback_state_syscall(0, 0, 0, 0) }, 0x6985);
        RESTORE_PHASE.set(1);
        assert_eq!(unsafe { load_rollback_state_syscall(0, 0, 0, 0) }, 0x6985);
        RESTORE_PHASE.set(3);
        assert_eq!(unsafe { reset_rollback_heap_syscall(0, 0, 0, 0) }, 0x6985);
        assert_eq!(unsafe { load_rollback_state_syscall(0, 0, 0, 0) }, 0x6985);
        set_active_app_call(None);
    }

    #[test]
    fn apdu_order_incoming_svc_after_output_preserves_shared_response() {
        let _page_lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let _execution = crate::shared_page::Lease::acquire(crate::shared_page::PAGE).delegate();
        let _lock = reset_registry_test_state();
        let mut shared = RustletCtx::new();
        shared.data.fill(0xa5);
        let mut transport = apdu_manager::TransportApdu::runtime_test_command();
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        set_active_app_call(Some(ActiveAppCall {
            caller: Aid::empty(),
            transport: &mut transport,
            shared_buffer: &mut shared,
            shared_window: empty,
            text_window: empty,
            data_window: empty,
            stack_window: empty,
        }));
        let _call = ActiveAppCallGuard;
        for len in [0, 2, 255] {
            // SAFETY: the serialized test owns the active transport and shared page.
            unsafe {
                apdu_set_outgoing_length_syscall(len, 0, 0, 0);
            }
            for _ in 0..2 {
                // SAFETY: the active call borrows the same live test-owned objects.
                assert_eq!(
                    unsafe { apdu_set_incoming_and_receive_syscall(0, 0, 0, 0) },
                    0
                );
                assert!(transport.outgoing_started());
                assert_eq!(transport.outgoing_length(), len);
                assert_eq!(shared.outgoing_len(), len);
                assert!(shared.outgoing_started());
                assert!(shared.data.iter().all(|byte| *byte == 0xa5));
            }
        }
    }

    #[test]
    fn outgoing_length_svc_rejects_oversize_without_mutating_response() {
        let _page_lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let _execution = crate::shared_page::Lease::acquire(crate::shared_page::PAGE).delegate();
        let _lock = reset_registry_test_state();
        let mut shared = RustletCtx::new();
        shared.data.fill(0xa5);
        let mut transport = apdu_manager::TransportApdu::runtime_test_command();
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        set_active_app_call(Some(ActiveAppCall {
            caller: Aid::empty(),
            transport: &mut transport,
            shared_buffer: &mut shared,
            shared_window: empty,
            text_window: empty,
            data_window: empty,
            stack_window: empty,
        }));
        let _call = ActiveAppCallGuard;
        // SAFETY: the test retains the transport/page and serializes every SVC
        // loan; no Rustlet or other test accesses the invocation concurrently.
        let set_len = |len| unsafe { apdu_set_outgoing_length_syscall(len, 0, 0, 0) };
        for accepted in [None, Some(0), Some(2), Some(255)] {
            if let Some(len) = accepted {
                assert_eq!(set_len(len), 0);
            }
            for bad in (256..=511).chain([u16::MAX as usize, u32::MAX as usize, usize::MAX]) {
                assert_eq!(set_len(bad), 0);
                assert_eq!(transport.outgoing_started(), accepted.is_some());
                assert_eq!(transport.outgoing_length(), accepted.unwrap_or(0));
                assert_eq!(shared.outgoing_len(), accepted.unwrap_or(0));
                assert!(shared.data.iter().all(|byte| *byte == 0xa5));
            }
        }
        // SET_LENGTH implicitly begins output, while SET_OUTGOING explicitly
        // resets the staged length. Both are supported by the existing ABI.
        unsafe {
            apdu_set_outgoing_syscall(0, 0, 0, 0);
        }
        assert_eq!(transport.outgoing_length(), 0);
        assert_eq!(shared.outgoing_len(), 0);
        assert_eq!(set_len(2), 0);
        assert_eq!(transport.outgoing_length(), 2);
        assert_eq!(shared.outgoing_len(), 2);
    }

    #[test]
    fn all_parameter_svcs_reject_malformed_records_before_writing() {
        let _page_lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let _execution = crate::shared_page::Lease::acquire(crate::shared_page::PAGE).delegate();
        let _lock = reset_registry_test_state();
        let mut words = [0xa5a5_a5a5usize; 32];
        let start = words.as_mut_ptr() as usize;
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        let cases: &[(oxi_core::core::syscall::SyscallHandler, usize)] = &[
            (
                crypto_cipher_do_final_syscall,
                core::mem::size_of::<CryptoCipherDoFinalParams>(),
            ),
            (
                crypto_random_generate_syscall,
                core::mem::size_of::<CryptoRandomGenerateParams>(),
            ),
            (
                crypto_mac_do_final_syscall,
                core::mem::size_of::<CryptoMacDoFinalParams>(),
            ),
            (
                crypto_ec_generate_keypair_syscall,
                core::mem::size_of::<CryptoEcGenerateKeypairParams>(),
            ),
            (
                crypto_ecdh_do_final_syscall,
                core::mem::size_of::<CryptoEcdhDoFinalParams>(),
            ),
            (
                crypto_hkdf_sha256_syscall,
                core::mem::size_of::<CryptoHkdfSha256Params>(),
            ),
            (
                crypto_x963_sha256_syscall,
                core::mem::size_of::<CryptoX963Sha256Params>(),
            ),
        ];
        let _call = ActiveAppCallGuard;
        for &(handler, size) in cases {
            for (address, len) in [
                (0, size),
                (start + 1, size),
                (start, size - 1),
                (usize::MAX & !(core::mem::align_of::<usize>() - 1), size),
            ] {
                set_active_app_call(Some(ActiveAppCall {
                    caller: Aid::empty(),
                    transport: core::ptr::null_mut(),
                    shared_buffer: core::ptr::null_mut(),
                    text_window: empty,
                    shared_window: empty,
                    stack_window: empty,
                    data_window: oxi_core::core::isolation::AppMemoryWindow { start, len },
                }));
                // SAFETY: the serialized test owns the only exposed memory window.
                assert_eq!(
                    unsafe { handler(address, 0, 0, 0) },
                    crypto_error_word(CryptoErrorCode::PermissionDenied)
                );
                assert!(words.iter().all(|word| *word == 0xa5a5_a5a5));
            }
        }
    }

    #[test]
    fn sd_key_svc_uses_invocation_authority_and_retires_it_on_every_exit() {
        let _page_lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let _execution = crate::shared_page::Lease::acquire(crate::shared_page::PAGE).delegate();
        let _lock = reset_registry_test_state();
        for (owner, fill) in [(OWNER_A, 0xA1), (OWNER_B, 0xB2)] {
            crate::registry::edit()
                .upsert_security_domain_object(
                    top_level_parent_sd_aid(),
                    owner,
                    owner,
                    SecurityDomainObjectBackend::RustletSecurityDomain,
                    [0; 3],
                    &[],
                )
                .unwrap();
            upsert_scp03_key_object(owner, 1, 3, Scp03KeyUsage::Enc, &sample_key(fill)).unwrap();
        }
        // The ambient cursor deliberately names a different SD from the call.
        set_active_security_domain_instance_aid(OWNER_A);
        let mut shared = RustletCtx::new();
        let mut output = [0xCC; 16];
        let params = Scp03LoadKeyParams {
            key_version: 1,
            key_id: 3,
            usage: Scp03KeyUsage::Enc.as_byte(),
            reserved: 0,
            output_ptr: output.as_mut_ptr(),
            output_capacity: output.len(),
        };
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        let call = ActiveAppCall {
            caller: Aid::empty(),
            transport: core::ptr::null_mut(),
            shared_buffer: &mut shared,
            shared_window: empty,
            text_window: empty,
            data_window: oxi_core::core::isolation::AppMemoryWindow {
                start: output.as_mut_ptr() as usize,
                len: output.len(),
            },
            stack_window: oxi_core::core::isolation::AppMemoryWindow {
                start: &params as *const _ as usize,
                len: core::mem::size_of_val(&params),
            },
        };
        let instance = crate::registry::read()
            .find_index(
                &top_level_parent_sd_aid(),
                ManagedObjectKind::SecurityDomain,
                &OWNER_B,
            )
            .unwrap();
        // Only the instance is consulted by key lookup; no package is executed.
        let invoke = || {
            // SAFETY: the test owns all windows and invokes one syscall at a time.
            unsafe { load_sd_key_for_call(active_app_call(), &params as *const _ as usize) }
        };
        let denied = crypto_error_word(CryptoErrorCode::PermissionDenied);
        set_active_app_call(None);
        assert_eq!(invoke(), denied);
        set_active_app_call(Some(call));
        SD_DISPATCH_INSTANCE.set(Some(instance));
        assert_eq!(invoke(), 16);
        assert_eq!(output, sample_key(0xB2));

        // Exercise the same record checks with SD authority actually established.
        output.fill(0xCC);
        for (address, len) in [
            (0, call.stack_window.len),
            (call.stack_window.start + 1, call.stack_window.len),
            (call.stack_window.start, call.stack_window.len - 1),
            (
                usize::MAX & !(core::mem::align_of::<Scp03LoadKeyParams>() - 1),
                call.stack_window.len,
            ),
        ] {
            set_active_app_call(Some(ActiveAppCall {
                caller: Aid::empty(),
                stack_window: oxi_core::core::isolation::AppMemoryWindow {
                    start: call.stack_window.start,
                    len,
                },
                ..call
            }));
            SD_DISPATCH_INSTANCE.set(Some(instance));
            // SAFETY: the test exclusively owns the live record and output windows.
            assert_eq!(
                unsafe { load_sd_key_for_call(active_app_call(), address) },
                denied
            );
            assert_eq!(output, [0xCC; 16]);
        }
        for reserved in [1, 255] {
            let malformed = Scp03LoadKeyParams { reserved, ..params };
            let address = &malformed as *const _ as usize;
            set_active_app_call(Some(ActiveAppCall {
                caller: Aid::empty(),
                stack_window: oxi_core::core::isolation::AppMemoryWindow {
                    start: address,
                    len: core::mem::size_of_val(&malformed),
                },
                ..call
            }));
            SD_DISPATCH_INSTANCE.set(Some(instance));
            // SAFETY: malformed and output remain live and exclusive during the call.
            assert_eq!(
                unsafe { load_sd_key_for_call(active_app_call(), address) },
                denied
            );
            assert_eq!(output, [0xCC; 16]);
        }
        set_active_app_call(Some(call));
        SD_DISPATCH_INSTANCE.set(Some(instance));

        set_selected_security_domain(None);
        assert!(!sd_dispatch_active());
        assert_eq!(invoke(), denied);
        SD_DISPATCH_INSTANCE.set(Some(instance));
        set_selected_app(None);
        assert!(!sd_dispatch_active());
        assert_eq!(invoke(), denied);

        // A later ordinary call replaces, rather than inherits, SD authority.
        output.fill(0xCC);
        set_active_app_call(Some(call));
        assert_eq!(invoke(), denied);
        assert_eq!(output, [0xCC; 16]);

        // Scope exit removes the complete context even after an early return.
        set_active_app_call(Some(call));
        SD_DISPATCH_INSTANCE.set(Some(instance));
        drop(ActiveAppCallGuard);
        assert_eq!(invoke(), denied);
        for event in [
            oxi_core::core::isolation::AppExitEvent::Requested { sw1: 0x6F, sw2: 0 },
            oxi_core::core::isolation::AppExitEvent::Fault(
                oxi_core::core::isolation::AppFault::WatchdogTimeout,
            ),
            oxi_core::core::isolation::AppExitEvent::Fault(
                oxi_core::core::isolation::AppFault::UnknownSyscall(255),
            ),
        ] {
            set_active_app_call(Some(call));
            SD_DISPATCH_INSTANCE.set(Some(instance));
            app_exit_observer(event);
            assert_eq!(invoke(), denied);
        }

        // Authority does not bypass the caller's output bounds.
        set_active_app_call(Some(ActiveAppCall {
            caller: Aid::empty(),
            data_window: empty,
            ..call
        }));
        SD_DISPATCH_INSTANCE.set(Some(instance));
        assert_eq!(invoke(), denied);
        set_active_app_call(None);
    }

    #[test]
    fn sd_key_svc_isolates_parent_and_siblings_including_lookup_fallbacks() {
        let _page_lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let _execution = crate::shared_page::Lease::acquire(crate::shared_page::PAGE).delegate();
        let _lock = reset_registry_test_state();
        let root = root_security_domain_instance_aid();
        let owners = [root, OWNER_A, OWNER_B];
        let mut slots = [0; 3];
        for (i, owner) in owners.iter().copied().enumerate() {
            let parent = if i == 0 {
                top_level_parent_sd_aid()
            } else {
                root
            };
            crate::registry::edit()
                .upsert_security_domain_object(
                    parent,
                    owner,
                    owner,
                    SecurityDomainObjectBackend::RustletSecurityDomain,
                    [0; 3],
                    &[],
                )
                .unwrap();
            slots[i] = crate::registry::read()
                .find_index(&parent, ManagedObjectKind::SecurityDomain, &owner)
                .unwrap();
            // Identical identifiers with distinct bytes expose owner confusion.
            // Consecutive MAC IDs and id=0 also exercise the lookup fallbacks.
            for (usage, id, extra) in [(Scp03KeyUsage::Enc, 3, 0), (Scp03KeyUsage::Mac, 4, 8)] {
                upsert_scp03_key_object(owner, 1, id, usage, &sample_key(0x30 + i as u8 + extra))
                    .unwrap();
                // Each owner alone has this version: no foreign fallback is allowed.
                upsert_scp03_key_object(
                    owner,
                    10 + i as u8,
                    id,
                    usage,
                    &sample_key(0x60 + i as u8 + extra),
                )
                .unwrap();
            }
        }
        let empty = oxi_core::core::isolation::AppMemoryWindow { start: 0, len: 0 };
        let mut shared = RustletCtx::new();
        let mut output = [0xCC; 16];
        for (i, slot) in slots.into_iter().enumerate() {
            for ambient in owners {
                set_active_security_domain_instance_aid(ambient);
                for (usage, extra) in [(Scp03KeyUsage::Enc, 0), (Scp03KeyUsage::Mac, 8)] {
                    for id in [0, 3] {
                        for version in [1, 10, 11, 12] {
                            output.fill(0xCC);
                            let params = Scp03LoadKeyParams {
                                key_version: version,
                                key_id: id,
                                usage: usage.as_byte(),
                                reserved: 0,
                                output_ptr: output.as_mut_ptr(),
                                output_capacity: output.len(),
                            };
                            let call = ActiveAppCall {
                                caller: Aid::empty(),
                                transport: core::ptr::null_mut(),
                                shared_buffer: &mut shared,
                                shared_window: empty,
                                text_window: empty,
                                data_window: oxi_core::core::isolation::AppMemoryWindow {
                                    start: output.as_mut_ptr() as usize,
                                    len: output.len(),
                                },
                                stack_window: oxi_core::core::isolation::AppMemoryWindow {
                                    start: &params as *const _ as usize,
                                    len: core::mem::size_of_val(&params),
                                },
                            };
                            set_active_app_call(Some(call));
                            let _guard = ActiveAppCallGuard;
                            // Ordinary calls cannot use even their resident domain's keys.
                            // SAFETY: the test exclusively owns the live record and buffer.
                            let invoke = || unsafe {
                                security_domain_load_scp03_key_syscall(
                                    &params as *const _ as usize,
                                    0,
                                    0,
                                    0,
                                )
                            };
                            assert_eq!(
                                invoke(),
                                crypto_error_word(CryptoErrorCode::PermissionDenied)
                            );
                            assert_eq!(output, [0xCC; 16]);
                            SD_DISPATCH_INSTANCE.set(Some(slot));
                            if version == 1 || version == 10 + i as u8 {
                                assert_eq!(invoke(), 16);
                                let base = if version == 1 { 0x30 } else { 0x60 };
                                assert_eq!(output, sample_key(base + i as u8 + extra));
                            } else {
                                assert_eq!(invoke(), crypto_error_word(CryptoErrorCode::NotFound));
                                assert_eq!(output, [0xCC; 16]);
                            }
                            output.fill(0xCC);
                            app_exit_observer(oxi_core::core::isolation::AppExitEvent::Fault(
                                oxi_core::core::isolation::AppFault::UnknownSyscall(255),
                            ));
                            // Reentry as an ordinary application after an SD fault stays denied.
                            set_active_app_call(Some(call));
                            assert_eq!(
                                invoke(),
                                crypto_error_word(CryptoErrorCode::PermissionDenied)
                            );
                            assert_eq!(output, [0xCC; 16]);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn install_for_load_cannot_replace_a_live_package() {
        let _guard = reset_registry_test_state();
        let owner = root_security_domain_instance_aid();
        let package = Aid::from_array([0xf0, 0x66]);
        {
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    top_level_parent_sd_aid(),
                    owner,
                    owner,
                    SecurityDomainObjectBackend::NullSecurityDomain,
                    [0; 3],
                    &[],
                )
                .unwrap();
            registry
                .insert_package_object(owner, package, package, &[0xca, 0xfe])
                .unwrap();
        }
        assert_eq!(
            prepare_dynamic_package_load(owner, owner, package, false, 256, [0; 32]),
            RegistryError::InvalidState.status()
        );
        let registry_guard = crate::registry::read();
        let registry = &*registry_guard;
        assert_eq!(
            registry
                .find_package_object(&owner, &package)
                .unwrap()
                .package_binary_code(),
            Some([0xca, 0xfe].as_slice())
        );
        assert!(!dynamic_package_load_in_progress());
    }

    #[test]
    fn compact_sd_unwrap_fits_full_encrypted_load_block() {
        let header = [0x84, 0xe8, 0, 0, 240];
        let ciphertext = [0x53; 224];
        let mac = [0x71; 16];
        let mut out = [0; rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX];
        assert!(encode_sddispatch_unwrap_command(
            &header,
            &ciphertext,
            &ciphertext,
            &mac,
            false,
            &mut out
        )
        .is_none());
        let len = encode_sddispatch_unwrap_command(
            &header,
            &ciphertext,
            &ciphertext,
            &mac,
            true,
            &mut out,
        )
        .unwrap();
        assert_eq!(len, 251);
        assert_eq!(&out[..6], &[0, 229, 0, 224, 0, 16]);
        assert_eq!(&out[6..11], &header);
        assert_eq!(&out[11..235], &ciphertext);
        assert_eq!(&out[235..len], &mac);
        assert!(encode_sddispatch_unwrap_command(
            &header,
            &ciphertext,
            &[0x99; 224],
            &mac,
            true,
            &mut out
        )
        .is_none());
    }

    pub(crate) fn reset_registry_test_state() -> MutexGuard<'static, ()> {
        let guard = REGISTRY_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        // Invariant: host tests must start from an empty object registry so key
        // ownership and lookup are validated without predeployment noise.
        {
            (crate::registry::edit()).clear();
            crate::registry::transaction::reset_abort_for_test();
            *SD_HOOK_FAILED.borrow_mut() = false;
        }
        ACTIVE_SECURITY_DOMAIN_SLOT.set(None);
        set_active_app_call(None);
        clear_dynamic_load_context();
        guard
    }

    fn sample_key(fill: u8) -> [u8; SCP03_STATIC_KEY_LEN] {
        [fill; SCP03_STATIC_KEY_LEN]
    }

    #[test]
    fn contract_data_reads_observe_staged_writes_until_global_rollback() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"old").unwrap();
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"new").unwrap();
        let mut out = [0; 8];
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"new");
        assert!(registry_mut().transaction_active());
        abort_registry_apdu();
        // Abort requests deferred rollback; finalization performs it.
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"new");
        finish_registry_apdu_with(|| panic!("aborted transaction must not publish")).unwrap();
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"old");
        assert!(!registry_mut().transaction_active());
    }

    #[test]
    fn unchanged_streamed_data_does_not_publish_or_clear_other_changes() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"first").unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"second").unwrap();
        begin_registry_apdu().unwrap();
        write_registry_data_objects(OWNER_A, &[(0xd001, 5), (0xd002, 6)], |which, i| {
            [b"first".as_slice(), b"second".as_slice()][which][i]
        })
        .unwrap();
        assert!(!registry_mut().transaction_dirty());
        finish_registry_apdu_with(|| panic!("identical data must not publish")).unwrap();

        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd003, b"new").unwrap();
        write_registry_data_objects(OWNER_A, &[(0xd001, 5)], |_, i| b"first"[i]).unwrap();
        assert!(registry_mut().transaction_dirty());
        let mut published = false;
        finish_registry_apdu_with(|| {
            published = true;
            Ok(())
        })
        .unwrap();
        assert!(published);
    }

    #[test]
    fn contract_data_reads_and_read_errors_do_not_dirty_transaction() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"value").unwrap();
        begin_registry_apdu().unwrap();
        let mut out = [0xa5; 8];
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd001, &mut out[..2]),
            Err(RegistryError::OutputTooSmall)
        );
        assert_eq!(out, [0xa5; 8]);
        assert_eq!(
            load_registry_data_object(&OWNER_B, 0xd001, &mut out),
            Err(RegistryError::NotFound)
        );
        assert_eq!(out, [0xa5; 8]);
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(5));
        assert_eq!(&out[..5], b"value");
        assert_eq!(&out[5..], &[0xa5; 3]);
        assert!(!registry_mut().transaction_dirty());
        finish_registry_apdu_with(|| panic!("reads must not publish")).unwrap();
    }

    #[test]
    fn contract_accepted_inner_scope_remains_subject_to_outer_rollback() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"initial").unwrap();
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"before scope").unwrap();
        {
            let _outer = RegistryOperationScope::begin(true).unwrap();
            upsert_registry_data_object(OWNER_A, 0xd001, b"outer").unwrap();
            let inner = RegistryOperationScope::begin(true).unwrap();
            upsert_registry_data_object(OWNER_A, 0xd001, b"inner").unwrap();
            upsert_registry_data_object(OWNER_A, 0xd002, b"inserted").unwrap();
            inner.finish(true);
            // Dropping the outer scope must also undo accepted inner changes.
        }
        let mut out = [0; 16];
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd001, &mut out),
            Ok(12)
        );
        assert_eq!(&out[..12], b"before scope");
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd002, &mut out),
            Err(RegistryError::NotFound)
        );
        let mut publications = 0;
        finish_registry_apdu_with(|| {
            publications += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(publications, 1);
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd001, &mut out),
            Ok(12)
        );
        assert_eq!(&out[..12], b"before scope");
    }

    #[test]
    fn standalone_and_nested_operations_roll_back_on_unwind() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"before").unwrap();
        let failure = catch_unwind(AssertUnwindSafe(|| {
            let _: RegistryResult = registry_operation(|| {
                upsert_registry_data_object(OWNER_A, 0xd001, b"after")?;
                registry_operation(|| {
                    upsert_registry_data_object(OWNER_A, 0xd002, b"nested")?;
                    panic!("simulated host unwind");
                })
            });
        }));
        assert!(failure.is_err());
        assert!(!crate::registry::read().transaction_active());
        let mut bytes = [0; 16];
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd001, &mut bytes),
            Ok(6)
        );
        assert_eq!(&bytes[..6], b"before");
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd002, &mut bytes),
            Err(RegistryError::NotFound)
        );
        upsert_registry_data_object(OWNER_A, 0xd002, b"recovered").unwrap();
    }

    #[test]
    fn registry_view_prevents_mutation_until_its_operation_ends() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"resident").unwrap();
        let object = find_any_object_by_aid_raw(&gp_data_object_aid(0xd001)).unwrap();
        let address = object.data_bytes().unwrap().as_ptr();
        assert!(
            catch_unwind(AssertUnwindSafe(|| upsert_registry_data_object(
                OWNER_A,
                0xd001,
                b"replacement"
            )))
            .is_err()
        );
        assert_eq!(object.data_bytes().unwrap(), b"resident");
        assert_eq!(object.data_bytes().unwrap().as_ptr(), address);
        drop(object);
        upsert_registry_data_object(OWNER_A, 0xd001, b"replacement").unwrap();
    }

    #[test]
    fn apdu_stages_all_services_and_publishes_dirty_registry_once() {
        let _guard = reset_registry_test_state();
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"first").unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"second").unwrap();
        assert!(registry_mut().transaction_active());
        assert!(registry_mut().transaction_dirty());
        let mut publications = 0;
        finish_registry_apdu_with(|| {
            publications += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(publications, 1);
        assert_eq!(registry_mut().len(), 2);
        begin_registry_apdu().unwrap();
        finish_registry_apdu_with(|| panic!("read-only APDU must not publish")).unwrap();
    }

    #[test]
    fn temporary_operation_abort_is_not_a_success() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"old").unwrap();
        let result = registry_operation(|| {
            upsert_registry_data_object(OWNER_A, 0xd001, b"abandoned")?;
            abort_registry_apdu();
            Ok(42)
        });
        assert_eq!(result, Err(RegistryError::InvalidState));
        assert!(!crate::registry::transaction::transaction_active());
        let mut bytes = [0; 16];
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd001, &mut bytes),
            Ok(3)
        );
        assert_eq!(&bytes[..3], b"old");
        // A fresh clean temporary transaction succeeds and clears sticky abort.
        assert_eq!(registry_operation(|| Ok(7)), Ok(7));
    }

    #[test]
    fn joined_operation_keeps_outer_abort_visible_at_finalization() {
        let _guard = reset_registry_test_state();
        begin_registry_apdu().unwrap();
        assert_eq!(
            registry_operation(|| {
                abort_registry_apdu();
                Ok(7)
            }),
            Ok(7)
        );
        assert!(crate::registry::transaction::transaction_active());
        assert_eq!(
            finish_registry_apdu_with(|| panic!("abort must not publish")),
            Ok(crate::registry::transaction::CommitOutcome::Aborted)
        );
    }

    #[test]
    fn apdu_abort_is_sticky_across_later_successful_savepoints() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"old").unwrap();
        begin_registry_apdu().unwrap();
        let outer = RegistryOperationScope::begin(true).unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"before failure").unwrap();
        let failed = RegistryOperationScope::begin(true).unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"failed stage").unwrap();
        abort_registry_apdu();
        failed.finish(false);
        let later = RegistryOperationScope::begin(true).unwrap();
        upsert_registry_data_object(OWNER_A, 0xd003, b"later success").unwrap();
        later.finish(true);
        outer.finish(true);
        abort_registry_apdu(); // Repeated failures are idempotent.
        finish_registry_apdu_with(|| panic!("later success cannot authorize publication")).unwrap();
        let mut out = [0; 32];
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"old");
        for tag in [0xd002, 0xd003] {
            assert_eq!(
                load_registry_data_object(&OWNER_A, tag, &mut out),
                Err(RegistryError::NotFound)
            );
        }
    }

    #[test]
    fn late_response_crash_abandons_all_staged_state_without_publication() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"old").unwrap();
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"application update").unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"SD update").unwrap();
        abort_registry_apdu();
        finish_registry_apdu_with(|| panic!("aborted response must not publish BOSS")).unwrap();
        let mut out = [0; 32];
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"old");
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd002, &mut out),
            Err(RegistryError::NotFound)
        );
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"recovered").unwrap();
        let mut published = false;
        finish_registry_apdu_with(|| {
            published = true;
            Ok(())
        })
        .unwrap();
        assert!(published);
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(9));
        assert_eq!(&out[..9], b"recovered");
    }

    #[test]
    fn failed_apdu_publication_restores_replacements_insertions_and_deletions() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"old").unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"survives").unwrap();
        let old_slot = registry_mut().find_index(
            &OWNER_A,
            ManagedObjectKind::Data,
            &gp_data_object_aid(0xd002),
        );
        seed_dynamic_load_context(OWNER_A, false);
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"new").unwrap();
        registry_operation(|| {
            registry_mut().delete_object(
                &OWNER_A,
                ManagedObjectKind::Data,
                &gp_data_object_aid(0xd002),
            )
        })
        .unwrap();
        upsert_registry_data_object(OWNER_A, 0xd003, b"reuses deleted slot").unwrap();
        assert_eq!(
            finish_registry_apdu_with(|| Err(RegistryError::Persistence)),
            Err(RegistryError::Persistence)
        );
        assert!(!dynamic_package_load_in_progress());
        let mut out = [0; 32];
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(3));
        assert_eq!(&out[..3], b"old");
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd002, &mut out), Ok(8));
        assert_eq!(&out[..8], b"survives");
        assert_eq!(
            registry_mut().find_index(
                &OWNER_A,
                ManagedObjectKind::Data,
                &gp_data_object_aid(0xd002)
            ),
            old_slot
        );
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd003, &mut out),
            Err(RegistryError::NotFound)
        );
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd004, b"later").unwrap();
        finish_registry_apdu().unwrap();
        assert_eq!(registry_mut().len(), 3);
    }

    #[test]
    fn management_abandon_preserves_protocol_changes_before_and_after_dispatch() {
        let _guard = reset_registry_test_state();
        upsert_registry_data_object(OWNER_A, 0xd001, b"original").unwrap();
        begin_registry_apdu().unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"unwrap").unwrap();
        let operation = RegistryOperationScope::begin(true).unwrap();
        upsert_registry_data_object(OWNER_A, 0xd001, b"management").unwrap();
        upsert_registry_data_object(OWNER_A, 0xd002, b"abandoned").unwrap();
        operation.finish(false);
        let mut out = [0; 32];
        assert_eq!(load_registry_data_object(&OWNER_A, 0xd001, &mut out), Ok(6));
        assert_eq!(&out[..6], b"unwrap");
        upsert_registry_data_object(OWNER_A, 0xd003, b"wrap").unwrap();
        finish_registry_apdu().unwrap();
        assert_eq!(registry_mut().len(), 2);
        assert_eq!(
            load_registry_data_object(&OWNER_A, 0xd002, &mut out),
            Err(RegistryError::NotFound)
        );
    }

    #[test]
    fn rollback_retires_authority_before_a_restored_slot_can_be_reused() {
        let _guard = reset_registry_test_state();
        begin_registry_apdu().unwrap();
        let operation = RegistryOperationScope::begin(true).unwrap();
        upsert_security_domain_state_object(
            OWNER_A,
            OWNER_A,
            OWNER_B,
            SecurityDomainObjectBackend::KernelSecurityDomain,
            [0x80, 0, 0],
            &[],
        )
        .unwrap();
        let slot = registry_mut()
            .find_index(&OWNER_A, ManagedObjectKind::SecurityDomain, &OWNER_B)
            .unwrap();
        // Invariant: this test owns the registry/selection mutex.
        {
            *ACTIVE_SECURITY_DOMAIN_SLOT.borrow_mut() = Some(slot);
        }
        operation.finish(false);
        assert!(active_security_domain_instance_aid() == root_security_domain_instance_aid());
        upsert_registry_data_object(OWNER_A, 0xd001, b"reused").unwrap();
        assert_eq!(
            registry_mut().find_index(
                &OWNER_A,
                ManagedObjectKind::Data,
                &gp_data_object_aid(0xd001)
            ),
            Some(slot)
        );
        assert!(active_security_domain_instance_aid() == root_security_domain_instance_aid());
        finish_registry_apdu().unwrap();
    }

    fn seed_inheritance_parent() {
        registry_mut()
            .upsert_security_domain_object(
                top_level_parent_sd_aid(),
                OWNER_A,
                OWNER_A,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0x80, 0, 0],
                &[],
            )
            .unwrap();
        for usage in [Scp03KeyUsage::Enc, Scp03KeyUsage::Mac] {
            upsert_scp03_key_object(OWNER_A, 1, 3, usage, &[usage.as_byte(); 16]).unwrap();
        }
    }

    #[test]
    fn sd_inherited_key_capacity_failure_restores_the_whole_operation() {
        let _guard = reset_registry_test_state();
        seed_inheritance_parent();
        for tag in 0..(DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY - 5) {
            upsert_registry_data_object(OWNER_A, tag as u16, b"filler").unwrap();
        }
        let before = registry_mut().len();
        begin_registry_apdu().unwrap();
        let status = install_kernel_side_security_domain_instance(
            SecurityDomainObjectBackend::KernelSecurityDomain,
            OWNER_A,
            OWNER_A,
            OWNER_B,
            &[0x80, 0, 0],
        );
        assert_eq!(status, RegistryError::Capacity.status());
        assert_eq!(registry_mut().len(), before);
        assert!(!registry_mut()
            .entries()
            .any(|object| object.parent_sd_aid == OWNER_B || object.object_aid == OWNER_B));
        finish_registry_apdu_with(|| panic!("failed operation must not dirty the BOSS")).unwrap();
    }

    #[test]
    fn sd_and_inherited_keys_share_the_apdu_publication_failure() {
        let _guard = reset_registry_test_state();
        seed_inheritance_parent();
        begin_registry_apdu().unwrap();
        assert_eq!(
            install_kernel_side_security_domain_instance(
                SecurityDomainObjectBackend::KernelSecurityDomain,
                OWNER_A,
                OWNER_A,
                OWNER_B,
                &[0x80, 0, 0],
            ),
            apdu_manager::ApduStatus::success()
        );
        assert_eq!(registry_mut().len(), 6);
        assert_eq!(
            finish_registry_apdu_with(|| Err(RegistryError::Persistence)),
            Err(RegistryError::Persistence)
        );
        assert_eq!(registry_mut().len(), 3);
        assert!(!registry_mut()
            .entries()
            .any(|object| object.parent_sd_aid == OWNER_B || object.object_aid == OWNER_B));
        begin_registry_apdu().unwrap();
        assert_eq!(
            install_kernel_side_security_domain_instance(
                SecurityDomainObjectBackend::KernelSecurityDomain,
                OWNER_A,
                OWNER_A,
                OWNER_B,
                &[0x80, 0, 0],
            ),
            apdu_manager::ApduStatus::success()
        );
        finish_registry_apdu().unwrap();
        let mut out = [0; 16];
        assert_eq!(
            load_scp03_key_material(&OWNER_B, 1, 3, Scp03KeyUsage::Mac, &mut out),
            Some(16)
        );
        assert_eq!(out, [Scp03KeyUsage::Mac.as_byte(); 16]);
    }

    #[test]
    fn scp11_keys_round_trip_by_owner_version_id_and_role() {
        let _registry_guard = reset_registry_test_state();
        let mut private = [0u8; 32];
        private[31] = 1;
        let mut public = [0u8; 65];
        oxi_core::core::crypto::p256_public_from_private(&private, &mut public).unwrap();

        assert!(upsert_scp11_key_object(
            OWNER_A,
            2,
            4,
            crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA,
            &private,
        )
        .is_ok());
        assert!(upsert_scp11_key_object(
            OWNER_A,
            2,
            5,
            crate::security_domain::SCP11_PUT_KEY_USAGE_CA_KLOC,
            &public,
        )
        .is_ok());

        let mut loaded_private = [0u8; 32];
        assert_eq!(
            load_scp11_key_material(
                &OWNER_A,
                2,
                4,
                crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA,
                &mut loaded_private,
            ),
            Some(32)
        );
        assert_eq!(loaded_private, private);
        assert!(load_scp11_key_material(
            &OWNER_B,
            2,
            4,
            crate::security_domain::SCP11_PUT_KEY_USAGE_SD_ECKA,
            &mut loaded_private,
        )
        .is_none());
    }

    #[test]
    fn runtime_registry_references_remain_word_sized() {
        assert!(core::mem::size_of::<AppRegistryReference>() <= 3 * core::mem::size_of::<usize>());
    }

    #[test]
    fn get_status_pages_visible_gp_objects_without_exposing_keys() {
        let _registry_guard = reset_registry_test_state();
        let root_aid = crate::predeployment::root_instance_aid();
        let root_parent = top_level_parent_sd_aid();
        let package_a = Aid::from_array([0xf0, 0x0d, 0x10]);
        let package_b = Aid::from_array([0xf0, 0x0d, 0x11]);
        {
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            assert!(registry
                .upsert_security_domain_object(
                    root_parent,
                    root_aid,
                    root_aid,
                    SecurityDomainObjectBackend::NullSecurityDomain,
                    [0xff; 3],
                    &[],
                )
                .is_ok());
            assert!(registry
                .insert_package_object(root_aid, package_a, package_a, &[0xca],)
                .is_ok());
            assert!(registry
                .insert_package_object(root_aid, package_b, package_b, &[0xfe],)
                .is_ok());
            assert!(registry
                .upsert_key_object(
                    root_aid,
                    Aid::from_array([0x4b, 0x45, 0x59]),
                    KeyObjectType::Scp03Static,
                    KeyObjectState::Active,
                    1,
                    3,
                    1,
                    &[0xaa; SCP03_STATIC_KEY_LEN],
                )
                .is_ok());
        }

        let query = crate::gp_status::GetStatusQuery {
            category: crate::gp_status::GetStatusCategory::ExecutableLoadFiles,
            next_occurrence: false,
            aid_filter: Aid::from_array([0xf0, 0x0d]),
        };
        let first_record_len = {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            let object = registry
                .find_package_object(&root_aid, &package_a)
                .expect("package A");
            crate::gp_status::encoded_record_len(query, &object, &root_aid).expect("record length")
        };
        let mut first = [0u8; 64];
        let first_page =
            encode_get_status_page(&root_aid, query, 0, &mut first[..first_record_len])
                .expect("first page");
        assert!(first_page.found);
        assert_eq!(first_page.len, first_record_len);
        let next_slot = first_page.next_slot.expect("second page cursor");

        let mut second = [0u8; 64];
        let second_page =
            encode_get_status_page(&root_aid, query, next_slot, &mut second).expect("second page");
        assert!(second_page.found);
        assert!(second_page.next_slot.is_none());

        let first_stream = &first[..first_page.len];
        let second_stream = &second[..second_page.len];
        assert!(first_stream
            .windows(package_a.len as usize)
            .any(|value| value == package_a.as_slice()));
        assert!(second_stream
            .windows(package_b.len as usize)
            .any(|value| value == package_b.as_slice()));
        assert!(!first_stream
            .windows(3)
            .any(|value| value == [0x4b, 0x45, 0x59]));
        assert!(!second_stream
            .windows(3)
            .any(|value| value == [0x4b, 0x45, 0x59]));
    }

    #[test]
    fn failed_dynamic_publication_cannot_leak_into_a_later_snapshot() {
        let _guard = reset_registry_test_state();
        let rejected = Aid::from_array([0xF0, 0x01]);
        let accepted = Aid::from_array([0xF0, 0x02]);
        begin_registry_apdu().unwrap();
        {
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            assert!(registry
                .insert_package_object(OWNER_A, rejected, rejected, &[1])
                .is_ok());
        }
        finish_registry_apdu_with(|| Err(RegistryError::Persistence)).unwrap_err();
        {
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            assert!(registry.find_package_object(&OWNER_A, &rejected).is_none());
            assert!(registry
                .insert_package_object(OWNER_A, accepted, accepted, &[2])
                .is_ok());
        }
        finish_registry_apdu().unwrap();
        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            // Snapshot publication enumerates precisely these live entries.
            assert_eq!(registry.entries().count(), 1);
            assert!(registry.find_package_object(&OWNER_A, &accepted).is_some());
            assert!(registry.find_package_object(&OWNER_A, &rejected).is_none());
        }
    }

    fn seed_dynamic_load_context(authority_aid: Aid, protected: bool) {
        {
            *DYNAMIC_LOAD_CONTEXT.borrow_mut() = Some(DynamicLoadContext {
                authority_aid,
                target_sd_aid: authority_aid,
                package_aid: Aid::from_array([0xF0, 0x0D]),
                protected,
                expected_hash: [0; 32],
                next_block_number: 0,
                payload: registry_payload::PayloadPreparation {
                    expected_size: 16,
                    reserved_offset: 4096,
                    block_total_len: 4096,
                    bytes_received: 0,
                    current_page_index: 0,
                    current_page_dirty: false,
                },
            });
        }
    }

    #[test]
    fn dynamic_load_cancel_drops_only_volatile_context() {
        let _registry_guard = reset_registry_test_state();
        seed_dynamic_load_context(OWNER_A, true);
        assert!(dynamic_package_load_in_progress());
        cancel_dynamic_package_load();
        assert!(!dynamic_package_load_in_progress());
    }

    #[test]
    fn dynamic_load_rejects_mismatched_authority_before_flash_access() {
        let _registry_guard = reset_registry_test_state();
        seed_dynamic_load_context(OWNER_A, true);

        let status = append_dynamic_package_load_block(OWNER_B, true, 0, false, &[0xAA]);

        assert_eq!(
            status,
            apdu_manager::ApduStatus::security_status_not_satisfied()
        );
        assert!(!dynamic_package_load_in_progress());
    }

    #[test]
    fn scp03_key_material_round_trips_for_matching_owner() {
        let _registry_guard = reset_registry_test_state();
        let enc = sample_key(0x11);
        assert!(upsert_scp03_key_object(OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &enc,).is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        let len = load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out)
            .expect("ENC key should be present under matching owner");
        assert_eq!(len, SCP03_STATIC_KEY_LEN);
        assert_eq!(out, enc);
    }

    #[test]
    fn multi_key_validation_and_publication_failure_preserve_old_keys() {
        let _guard = reset_registry_test_state();
        let reference = crate::security_domain::PutKeyReferenceControl::decode(0, 0x83);
        let mut encoded = std::vec::Vec::new();
        for byte in [0x11, 0x22] {
            encoded.extend_from_slice(&[0x88, 16]);
            encoded.extend_from_slice(&[byte; 16]);
            encoded.push(0);
        }
        let mut publications = 0;
        put_key_objects_with_publish(OWNER_A, reference, 2, &encoded, || {
            publications += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(publications, 1);
        encoded[2..18].fill(0x33);
        encoded[19] = 0xff;
        assert_eq!(
            put_key_objects_with_publish(OWNER_A, reference, 2, &encoded, || panic!(
                "malformed command must not publish"
            )),
            Err(RegistryError::InvalidData)
        );
        encoded[19] = 0x88;
        assert_eq!(
            put_key_objects_with_publish(OWNER_A, reference, 2, &encoded, || Err(
                RegistryError::Persistence
            )),
            Err(RegistryError::Persistence)
        );
        let mut out = [0; 16];
        assert_eq!(
            load_scp03_key_material(&OWNER_A, 2, 3, Scp03KeyUsage::Enc, &mut out),
            Some(16)
        );
        assert_eq!(out, [0x11; 16]);
        assert_eq!(
            load_scp03_key_material(&OWNER_A, 2, 4, Scp03KeyUsage::Mac, &mut out),
            Some(16)
        );
        assert_eq!(out, [0x22; 16]);
        assert_eq!(
            put_key_objects_with_publish(OWNER_A, reference, 3, &encoded, || Err(
                RegistryError::Persistence
            )),
            Err(RegistryError::Persistence)
        );
        assert!(load_scp03_static_keys(&OWNER_A, 3, 3).is_none());
    }

    #[test]
    fn multi_key_capacity_failure_removes_earlier_insertion() {
        let _guard = reset_registry_test_state();
        let mut registry_guard = crate::registry::edit();
        let registry = &mut *registry_guard;
        for i in 0..DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY - 1 {
            registry
                .upsert_data_object(OWNER_A, Aid::from_array([1, 2, 3, 4, i as u8]), &[i as u8])
                .unwrap();
        }
        let mut encoded = std::vec::Vec::new();
        for byte in [0x11, 0x22] {
            encoded.extend_from_slice(&[0x88, 16]);
            encoded.extend_from_slice(&[byte; 16]);
            encoded.push(0);
        }
        let reference = crate::security_domain::PutKeyReferenceControl::decode(0, 0x83);
        drop(registry_guard);
        assert_eq!(
            put_key_objects_with_publish(OWNER_A, reference, 2, &encoded, || panic!(
                "capacity failure must not publish"
            )),
            Err(RegistryError::Capacity)
        );
        let registry_guard = crate::registry::read();
        let registry = &*registry_guard;
        assert_eq!(registry.len(), DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY - 1);
        assert!(load_scp03_static_keys(&OWNER_A, 2, 3).is_none());
        let mut out = [0; 16];
        assert!(load_scp03_key_material(&OWNER_A, 2, 3, Scp03KeyUsage::Enc, &mut out).is_none());
    }

    #[test]
    fn scp03_key_material_is_isolated_per_owner() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x22),
        )
        .is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        assert!(
            load_scp03_key_material(&OWNER_B, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out).is_none()
        );
    }

    #[test]
    fn scp03_static_keys_require_both_enc_and_mac_under_same_owner() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x33),
        )
        .is_ok());
        assert!(load_scp03_static_keys(&OWNER_A, 0x01, 0x03).is_none());

        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Mac,
            &sample_key(0x44),
        )
        .is_ok());
        assert!(load_scp03_static_keys(&OWNER_A, 0x01, 0x03).is_some());
    }

    #[test]
    fn scp03_static_keys_accept_gp_multi_entry_consecutive_ids() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x35),
        )
        .is_ok());
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x04,
            Scp03KeyUsage::Mac,
            &sample_key(0x46),
        )
        .is_ok());

        // Invariant: GP multi-entry PUT KEY advances the key identifier for
        // each entry. INITIALIZE UPDATE carries only the version, so the card
        // resolves the first valid ENC/MAC pair for that version internally.
        assert!(load_scp03_static_keys(&OWNER_A, 0x01, 0x03).is_some());
        assert_eq!(
            load_scp03_static_keys_for_version(&OWNER_A, 0x01).map(|(_, id)| id),
            Some(0x03)
        );
    }

    #[test]
    fn scp03_static_keys_do_not_cross_security_domain_boundaries() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x55),
        )
        .is_ok());
        assert!(upsert_scp03_key_object(
            OWNER_B,
            0x01,
            0x03,
            Scp03KeyUsage::Mac,
            &sample_key(0x66),
        )
        .is_ok());

        // Invariant: SCP03 session derivation is valid only when both halves of
        // the keyset belong to the same owner Security Domain instance.
        assert!(load_scp03_static_keys(&OWNER_A, 0x01, 0x03).is_none());
        assert!(load_scp03_static_keys(&OWNER_B, 0x01, 0x03).is_none());
    }

    #[test]
    fn scp03_key_upsert_replaces_existing_material() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x77),
        )
        .is_ok());
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0x88),
        )
        .is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        let len = load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out)
            .expect("replaced ENC key should still be readable");
        assert_eq!(len, SCP03_STATIC_KEY_LEN);
        assert_eq!(out, sample_key(0x88));
    }

    #[test]
    fn scp03_key_usage_lookup_is_specific() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Mac,
            &sample_key(0x99),
        )
        .is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        assert!(
            load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out).is_none()
        );
        let len = load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Mac, &mut out)
            .expect("MAC key should be readable only through MAC usage");
        assert_eq!(len, SCP03_STATIC_KEY_LEN);
        assert_eq!(out, sample_key(0x99));
    }

    #[test]
    fn scp03_key_material_rejects_too_small_output_buffer() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0xAA),
        )
        .is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN - 1];
        assert!(
            load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out).is_none()
        );
    }

    #[test]
    fn scp03_key_material_ignores_locked_keys() {
        let _registry_guard = reset_registry_test_state();
        let object_aid = scp03_key_object_instance_aid(0x01, 0x03, Scp03KeyUsage::Enc.as_byte());
        assert!({
            (crate::registry::edit()).upsert_key_object(
                OWNER_A,
                object_aid,
                KeyObjectType::Scp03Static,
                KeyObjectState::Locked,
                0x01,
                0x03,
                Scp03KeyUsage::Enc.as_byte(),
                &sample_key(0xBB),
            )
        }
        .is_ok());

        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        assert!(
            load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out).is_none()
        );
    }

    #[test]
    fn install_lookup_rejects_locked_package_objects() {
        let _registry_guard = reset_registry_test_state();
        let parent = OWNER_A;
        let package = Aid::from_array([0xF0, 0x0D, 0x01]);
        let applet = Aid::from_array([0xF0, 0x0D, 0x02]);
        assert!({
            (crate::registry::edit()).insert_package_object(parent, package, applet, &[0xCA, 0xFE])
        }
        .is_ok());
        assert!({
            (crate::registry::edit()).set_package_state(
                &parent,
                &package,
                crate::registry::objects::PackageObjectState::Locked,
            )
        }
        .is_ok());

        assert!(pending_registry_reference_for_install(&parent, &package, &applet).is_err());
    }

    #[test]
    fn locked_security_domain_cannot_open_secure_channel() {
        let _registry_guard = reset_registry_test_state();
        let root = top_level_parent_sd_aid();
        assert!({
            (crate::registry::edit()).upsert_security_domain_object(
                root,
                OWNER_A,
                Aid::from_array([0xF0, 0x0D, 0x03]),
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF, 0xFF, 0xFF],
                &[0x01],
            )
        }
        .is_ok());
        assert!(security_domain_may_open_secure_channel(&OWNER_A));
        assert!({
            (crate::registry::edit()).set_security_domain_state(
                &root,
                &OWNER_A,
                crate::registry::objects::SecurityDomainObjectState::Locked,
            )
        }
        .is_ok());

        assert!(!security_domain_may_open_secure_channel(&OWNER_A));
    }

    #[test]
    fn delete_requires_authority_over_target_object() {
        let _registry_guard = reset_registry_test_state();
        let package = Aid::from_array([0xF0, 0x0D, 0x30]);
        assert!({
            (crate::registry::edit()).insert_package_object(
                OWNER_A,
                package,
                package,
                &[0xCA, 0xFE],
            )
        }
        .is_ok());

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_B, &package, false),
            Err(RegistryError::AuthorityDenied)
        );
        {
            assert!((crate::registry::read())
                .find_package_object(&OWNER_A, &package)
                .is_some());
        }

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_A, &package, false),
            Ok(())
        );
        {
            assert!((crate::registry::read())
                .find_package_object(&OWNER_A, &package)
                .is_none());
        }
    }

    #[test]
    fn global_registry_privilege_does_not_escape_the_authority_subtree() {
        let _registry_guard = reset_registry_test_state();
        let root_parent = top_level_parent_sd_aid();
        let package = Aid::from_array([0xF0, 0x0D, 0x3A]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    root_parent,
                    OWNER_A,
                    OWNER_A,
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    [0x80, 0x04, 0x00],
                    &[],
                )
                .is_ok()
                && registry
                    .upsert_security_domain_object(
                        root_parent,
                        OWNER_B,
                        OWNER_B,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0x80, 0x00, 0x00],
                        &[],
                    )
                    .is_ok()
                && registry
                    .insert_package_object(OWNER_B, package, package, &[0xCA, 0xFE])
                    .is_ok()
        });

        let object = find_any_object_by_aid_raw(&package).expect("sibling package");
        assert!(!security_domain_may_reach_object(&OWNER_A, &object));
    }

    #[test]
    fn compact_identity_and_topology_do_not_open_bodies_and_backend_follows_rollback() {
        let _guard = reset_registry_test_state();
        let root = root_security_domain_instance_aid();
        let child = Aid::new(&[0xa1]);
        let grandchild = Aid::new(&[0xa2]);
        for (parent, id) in [
            (top_level_parent_sd_aid(), root),
            (root, child),
            (child, grandchild),
        ] {
            crate::registry::edit()
                .upsert_security_domain_object(
                    parent,
                    id,
                    id,
                    SecurityDomainObjectBackend::NullSecurityDomain,
                    [0x80, 0, 0],
                    &[],
                )
                .unwrap();
        }
        ACTIVE_SECURITY_DOMAIN_SLOT.set(crate::registry::read().find_any_index(&root));
        crate::registry::testing::take_object_opens();
        assert!(active_security_domain_instance_aid() == root);
        assert!(active_security_domain_may_reach_instance(&grandchild));
        assert_eq!(
            find_managed_object_kind_by_aid(&grandchild),
            Some(ManagedObjectKind::SecurityDomain)
        );
        assert_eq!(require_managed_object_authority(&root, &grandchild), Ok(()));
        assert_eq!(
            require_managed_object_authority(&child, &root),
            Err(RegistryError::AuthorityDenied)
        );
        assert_eq!(crate::registry::testing::take_object_opens(), 0);
        assert_eq!(
            security_domain_backend_by_aid(&root),
            Some(SecurityDomainObjectBackend::NullSecurityDomain)
        );
        assert_eq!(crate::registry::testing::take_object_opens(), 1);
        begin_registry_apdu().unwrap();
        crate::registry::edit()
            .upsert_security_domain_object(
                top_level_parent_sd_aid(),
                root,
                root,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0x80, 0, 0],
                &[],
            )
            .unwrap();
        crate::registry::testing::take_object_opens();
        assert_eq!(
            security_domain_backend_by_aid(&root),
            Some(SecurityDomainObjectBackend::KernelSecurityDomain)
        );
        assert_eq!(crate::registry::testing::take_object_opens(), 1);
        abort_registry_apdu();
        finish_registry_apdu_with(|| panic!("aborted APDU cannot publish")).unwrap();
        crate::registry::testing::take_object_opens();
        assert_eq!(
            security_domain_backend_by_aid(&root),
            Some(SecurityDomainObjectBackend::NullSecurityDomain)
        );
        assert_eq!(crate::registry::testing::take_object_opens(), 1);
        // A cycle not containing the authority must terminate without opening bodies.
        let a = Aid::new(&[0xb1]);
        let b = Aid::new(&[0xb2]);
        for (parent, id) in [(b, a), (a, b)] {
            crate::registry::edit()
                .upsert_security_domain_object(
                    parent,
                    id,
                    id,
                    SecurityDomainObjectBackend::NullSecurityDomain,
                    [0x80, 0, 0],
                    &[],
                )
                .unwrap();
        }
        crate::registry::testing::take_object_opens();
        assert!(!active_security_domain_may_reach_instance(&a));
        assert_eq!(crate::registry::testing::take_object_opens(), 0);
        ACTIVE_SECURITY_DOMAIN_SLOT.set(crate::registry::read().find_any_index(&child));
        assert_eq!(security_domain_backend_by_aid(&root), None);
        assert_eq!(
            security_domain_backend_by_aid(&grandchild),
            Some(SecurityDomainObjectBackend::NullSecurityDomain)
        );
    }

    #[test]
    fn root_issuer_detached_and_sibling_visibility_follow_the_declared_tree() {
        let _registry_guard = reset_registry_test_state();
        let root_parent = top_level_parent_sd_aid();
        let root = root_security_domain_instance_aid();
        let issuer = Aid::from_array([0xA0, 0x10]);
        let child_a = Aid::from_array([0xA0, 0x11]);
        let grandchild_a = Aid::from_array([0xA0, 0x12]);
        let child_b = Aid::from_array([0xA0, 0x13]);
        let detached = Aid::from_array([0xA0, 0x14]);
        let detached_child = Aid::from_array([0xA0, 0x15]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            let mut insert = |parent, aid| {
                registry
                    .upsert_security_domain_object(
                        parent,
                        aid,
                        aid,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0x80, 0x00, 0x00],
                        &[],
                    )
                    .is_ok()
            };
            insert(root_parent, root)
                && insert(root, issuer)
                && insert(issuer, child_a)
                && insert(child_a, grandchild_a)
                && insert(issuer, child_b)
                && insert(root, detached)
                && insert(detached, detached_child)
        });

        let visible = |authority: Aid, target: Aid| {
            let object = find_any_object_by_aid_raw(&target).expect("declared Security Domain");
            security_domain_may_reach_object(&authority, &object)
        };
        for target in [
            root,
            issuer,
            child_a,
            grandchild_a,
            child_b,
            detached,
            detached_child,
        ] {
            assert!(visible(root, target));
        }
        assert!(visible(issuer, child_a));
        assert!(visible(issuer, grandchild_a));
        assert!(visible(issuer, child_b));
        assert!(!visible(issuer, root));
        assert!(!visible(issuer, detached));
        assert!(visible(child_a, grandchild_a));
        assert!(!visible(child_a, issuer));
        assert!(!visible(child_a, child_b));
        assert!(!visible(detached, issuer));
        assert!(visible(detached, detached_child));
    }

    #[test]
    fn registry_topology_rejects_privilege_escalation() {
        let _registry_guard = reset_registry_test_state();
        let root_parent = top_level_parent_sd_aid();
        let root = root_security_domain_instance_aid();
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    root_parent,
                    root,
                    root,
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    [0xA0, 0x00, 0x00],
                    &[],
                )
                .is_ok()
                && registry
                    .upsert_security_domain_object(
                        root,
                        OWNER_A,
                        OWNER_A,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0x80, 0x00, 0x00],
                        &[],
                    )
                    .is_ok()
        });
        assert!(validate_security_domain_registry_topology(
            &crate::registry::read()
        ));

        assert!({
            (crate::registry::edit()).upsert_security_domain_object(
                OWNER_A,
                OWNER_B,
                OWNER_B,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xA0, 0x00, 0x00],
                &[],
            )
        }
        .is_ok());
        assert!(!validate_security_domain_registry_topology(
            &crate::registry::read()
        ));
    }

    #[test]
    fn package_delete_requires_cumulative_flag_when_instances_depend_on_it() {
        let _registry_guard = reset_registry_test_state();
        let package = Aid::from_array([0xF0, 0x0D, 0x32]);
        let instance = Aid::from_array([0xF0, 0x0D, 0x33]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .insert_package_object(OWNER_A, package, package, &[0xCA, 0xFE])
                .is_ok()
                && registry
                    .upsert_instance_object(OWNER_A, instance, package, &[])
                    .is_ok()
        });

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_A, &package, false),
            Err(RegistryError::InvalidState)
        );
        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(registry.find_package_object(&OWNER_A, &package).is_some());
            assert!(registry.find_instance_object(&OWNER_A, &instance).is_some());
        }

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_A, &package, true),
            Ok(())
        );
        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(registry.find_package_object(&OWNER_A, &package).is_none());
            assert!(registry.find_instance_object(&OWNER_A, &instance).is_none());
        }
    }

    #[test]
    fn cumulative_delete_rejects_a_dependency_outside_the_authority_subtree() {
        let _registry_guard = reset_registry_test_state();
        let root_parent = top_level_parent_sd_aid();
        let package = Aid::from_array([0xF0, 0x0D, 0x3B]);
        let sibling_instance = Aid::from_array([0xF0, 0x0D, 0x3C]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    root_parent,
                    OWNER_A,
                    OWNER_A,
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    [0x80, 0x00, 0x00],
                    &[],
                )
                .is_ok()
                && registry
                    .upsert_security_domain_object(
                        root_parent,
                        OWNER_B,
                        OWNER_B,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0x80, 0x00, 0x00],
                        &[],
                    )
                    .is_ok()
                && registry
                    .insert_package_object(OWNER_A, package, package, &[0xCA, 0xFE])
                    .is_ok()
                && registry
                    .upsert_instance_object(OWNER_B, sibling_instance, package, &[])
                    .is_ok()
        });

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_A, &package, true),
            Err(RegistryError::AuthorityDenied)
        );
        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(registry.find_package_object(&OWNER_A, &package).is_some());
            assert!(registry
                .find_instance_object(&OWNER_B, &sibling_instance)
                .is_some());
        }
    }

    #[test]
    fn security_domain_cumulative_delete_removes_the_complete_subtree() {
        let _registry_guard = reset_registry_test_state();
        let root = top_level_parent_sd_aid();
        let child = Aid::from_array([0xF0, 0x0D, 0x34]);
        let grandchild = Aid::from_array([0xF0, 0x0D, 0x35]);
        let package = Aid::from_array([0xF0, 0x0D, 0x36]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    root,
                    child,
                    package,
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    [0, 0, 0],
                    &[],
                )
                .is_ok()
                && registry
                    .upsert_security_domain_object(
                        child,
                        grandchild,
                        package,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0, 0, 0],
                        &[],
                    )
                    .is_ok()
                && registry
                    .insert_package_object(grandchild, package, package, &[0xCA, 0xFE])
                    .is_ok()
        });

        assert_eq!(
            delete_visible_managed_object_under_authority(
                root_security_domain_instance_aid(),
                &child,
                false,
            ),
            Err(RegistryError::InvalidState)
        );
        assert_eq!(
            delete_visible_managed_object_under_authority(
                root_security_domain_instance_aid(),
                &child,
                true,
            ),
            Ok(())
        );
        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(registry
                .find_security_domain_object(&root, &child)
                .is_none());
            assert!(registry
                .find_security_domain_object(&child, &grandchild)
                .is_none());
            assert!(registry
                .find_package_object(&grandchild, &package)
                .is_none());
        }
    }

    #[test]
    fn deleting_active_security_domain_clears_its_registry_slot_reference() {
        let _registry_guard = reset_registry_test_state();
        let parent = top_level_parent_sd_aid();
        assert!({
            (crate::registry::edit()).upsert_security_domain_object(
                parent,
                OWNER_A,
                Aid::from_array([0xF0, 0x0D, 0x31]),
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0, 0, 0],
                &[],
            )
        }
        .is_ok());
        let slot = {
            (crate::registry::read())
                .find_index(&parent, ManagedObjectKind::SecurityDomain, &OWNER_A)
                .expect("Security Domain slot")
        };
        set_active_security_domain_instance_aid(OWNER_A);
        assert_eq!(ACTIVE_SECURITY_DOMAIN_SLOT.get(), Some(slot));

        assert_eq!(
            delete_visible_managed_object_under_authority(OWNER_A, &OWNER_A, false),
            Ok(())
        );
        assert_eq!(ACTIVE_SECURITY_DOMAIN_SLOT.get(), None);
        assert!({ (crate::registry::read()).resolve(slot).is_none() });
    }

    #[test]
    fn get_data_registry_fallback_is_parent_qualified() {
        let _registry_guard = reset_registry_test_state();
        let tag = 0xDF42;
        assert!(upsert_registry_data_object(OWNER_A, tag, &[0xA1, 0xA2]).is_ok());
        assert!(upsert_registry_data_object(OWNER_B, tag, &[0xB1, 0xB2, 0xB3]).is_ok());

        let mut out = [0u8; 8];
        let len = load_registry_data_object(&OWNER_A, tag, &mut out)
            .expect("OWNER_A data object should be visible under OWNER_A only");
        assert_eq!(len, 2);
        assert_eq!(&out[..len], &[0xA1, 0xA2]);

        let len = load_registry_data_object(&OWNER_B, tag, &mut out)
            .expect("OWNER_B data object should be visible under OWNER_B only");
        assert_eq!(len, 3);
        assert_eq!(&out[..len], &[0xB1, 0xB2, 0xB3]);

        assert!(load_registry_data_object(&top_level_parent_sd_aid(), tag, &mut out).is_err());
    }

    #[test]
    fn set_status_locks_and_unlocks_lifecycle_objects() {
        let _registry_guard = reset_registry_test_state();
        let root = top_level_parent_sd_aid();
        let package = Aid::from_array([0xF0, 0x0D, 0x10]);
        let instance = Aid::from_array([0xF0, 0x0D, 0x11]);
        let domain = Aid::from_array([0xF0, 0x0D, 0x12]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .insert_package_object(root, package, package, &[0xCA, 0xFE])
                .is_ok()
                && registry
                    .upsert_instance_object(root, instance, package, &[0xAA])
                    .is_ok()
                && registry
                    .upsert_security_domain_object(
                        root,
                        domain,
                        package,
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0xFF, 0xFF, 0xFF],
                        &[0x01],
                    )
                    .is_ok()
        });

        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_PACKAGE,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &package,
        )
        .is_ok());
        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_APPLICATION,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &instance,
        )
        .is_ok());
        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_SECURITY_DOMAIN,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &domain,
        )
        .is_ok());

        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(!registry
                .find_package_object(&root, &package)
                .expect("package")
                .may_instantiate_package());
            assert!(!registry
                .find_instance_object(&root, &instance)
                .expect("instance")
                .may_select());
            assert!(!registry
                .find_security_domain_object(&root, &domain)
                .expect("domain")
                .may_open_secure_channel());
        }

        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_PACKAGE,
            crate::security_domain::SET_STATUS_STATE_UNLOCK,
            &package,
        )
        .is_ok());
        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_APPLICATION,
            crate::security_domain::SET_STATUS_STATE_UNLOCK,
            &instance,
        )
        .is_ok());
        assert!(set_visible_managed_object_status(
            root_security_domain_instance_aid(),
            crate::security_domain::SET_STATUS_KIND_SECURITY_DOMAIN,
            crate::security_domain::SET_STATUS_STATE_UNLOCK,
            &domain,
        )
        .is_ok());

        {
            let registry_guard = crate::registry::read();
            let registry = &*registry_guard;
            assert!(registry
                .find_package_object(&root, &package)
                .expect("package")
                .may_instantiate_package());
            assert!(registry
                .find_instance_object(&root, &instance)
                .expect("instance")
                .may_select());
            assert!(registry
                .find_security_domain_object(&root, &domain)
                .expect("domain")
                .may_open_secure_channel());
        }
    }

    #[test]
    fn set_status_cannot_change_the_technical_root_lifecycle() {
        let _registry_guard = reset_registry_test_state();
        let root_parent = top_level_parent_sd_aid();
        let root = root_security_domain_instance_aid();
        assert!({
            (crate::registry::edit()).upsert_security_domain_object(
                root_parent,
                root,
                root,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF; 3],
                &[],
            )
        }
        .is_ok());

        assert!(set_visible_managed_object_status(
            root,
            crate::security_domain::SET_STATUS_KIND_SECURITY_DOMAIN,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &root,
        )
        .is_err());
        assert!({
            (crate::registry::read())
                .find_security_domain_object(&root_parent, &root)
                .expect("technical root")
                .may_open_secure_channel()
        });
    }

    #[test]
    fn set_status_does_not_target_key_objects() {
        let _registry_guard = reset_registry_test_state();
        let key_aid = scp03_key_object_instance_aid(0x01, 0x03, Scp03KeyUsage::Enc.as_byte());
        assert!({
            (crate::registry::edit()).upsert_key_object(
                OWNER_A,
                key_aid,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                0x01,
                0x03,
                Scp03KeyUsage::Enc.as_byte(),
                &sample_key(0x42),
            )
        }
        .is_ok());

        assert!(set_visible_managed_object_status(
            OWNER_A,
            0x04,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &key_aid,
        )
        .is_err());
        assert!(set_visible_managed_object_status(
            OWNER_A,
            crate::security_domain::SET_STATUS_KIND_APPLICATION,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &key_aid,
        )
        .is_err());
        assert_eq!(
            {
                (crate::registry::read())
                    .find_key_object(&OWNER_A, &key_aid)
                    .expect("key")
                    .key_state()
            },
            Some(KeyObjectState::Active)
        );
    }

    #[test]
    fn set_status_requires_authority_over_target_object() {
        let _registry_guard = reset_registry_test_state();
        let root = top_level_parent_sd_aid();
        let package = Aid::from_array([0xF0, 0x0D, 0x20]);
        assert!({
            let mut registry_guard = crate::registry::edit();
            let registry = &mut *registry_guard;
            registry
                .upsert_security_domain_object(
                    root,
                    OWNER_A,
                    Aid::from_array([0xF0, 0x0D, 0x21]),
                    SecurityDomainObjectBackend::KernelSecurityDomain,
                    [0x00, 0x00, 0x00],
                    &[0x01],
                )
                .is_ok()
                && registry
                    .upsert_security_domain_object(
                        root,
                        OWNER_B,
                        Aid::from_array([0xF0, 0x0D, 0x22]),
                        SecurityDomainObjectBackend::KernelSecurityDomain,
                        [0x00, 0x00, 0x00],
                        &[0x01],
                    )
                    .is_ok()
                && registry
                    .insert_package_object(OWNER_A, package, package, &[0xCA, 0xFE])
                    .is_ok()
        });

        assert!(set_visible_managed_object_status(
            OWNER_B,
            crate::security_domain::SET_STATUS_KIND_PACKAGE,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &package,
        )
        .is_err());
        assert!(set_visible_managed_object_status(
            OWNER_A,
            crate::security_domain::SET_STATUS_KIND_PACKAGE,
            crate::security_domain::SET_STATUS_STATE_LOCK,
            &package,
        )
        .is_ok());
    }

    #[test]
    fn delete_scp03_key_object_removes_one_key_tuple() {
        let _registry_guard = reset_registry_test_state();
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Enc,
            &sample_key(0xCC),
        )
        .is_ok());
        assert!(upsert_scp03_key_object(
            OWNER_A,
            0x01,
            0x03,
            Scp03KeyUsage::Mac,
            &sample_key(0xDD),
        )
        .is_ok());

        assert!(delete_scp03_key_object(OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc,).is_ok());
        let mut out = [0u8; SCP03_STATIC_KEY_LEN];
        assert!(
            load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Enc, &mut out).is_none()
        );
        assert!(
            load_scp03_key_material(&OWNER_A, 0x01, 0x03, Scp03KeyUsage::Mac, &mut out).is_some()
        );
    }
}
