//! Owns loaded image memory and the checked, kernel-resident invocation metadata.
#![deny(unsafe_op_in_unsafe_fn)]

#[path = "fae_descriptor.rs"]
mod descriptor;

use core::alloc::Layout;
use core::marker::PhantomData;

use rustlet_runtime::{
    ApduStatus, RustletCtx, SEApdu, SelectedAppDescriptor, SelectedAppVtable,
    SelectedSecurityDomainVtable,
};

use crate::apdu_manager;

#[derive(Clone, Copy)]
struct AppInvocation {
    entry_pc: usize,
    arg0: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    kind: oxi_core::core::isolation::AppCallKind,
    fault_return_value: usize,
}

pub struct LoadedFae {
    app_gp: usize,
    image: &'static [u8],
    shared_buffer: SharedRustletCtx,
    data_window: oxi_core::core::isolation::AppMemoryWindow,
    stack_window: oxi_core::core::isolation::AppMemoryWindow,
    isolation_plan: oxi_core::core::isolation::IsolationPlan,
    profile_kind: FaeProfileKind,
    started: bool,
    descriptor: Option<descriptor::Descriptor>,
    // This owner scrubs and frees the complete image allocation on every exit.
    _allocation: AppAllocation,
}

pub struct HandlerCallResult {
    pub status: ApduStatus,
    pub returned_normally: bool,
}

const FAE_MAGIC_NUMBER_AND_VERSION: u32 = 0xFAEC_0D10;
const FAE_ABI_DESCRIPTOR: u32 = 0xAC1D_A992;
const FAE_APPLICATION_PROFILE: u32 = 0xA99;
const FAE_SECURITY_DOMAIN_PROFILE: u32 = 0x5DC;
const FAE_MEMORY_UNIT: usize = 32;
const FAE_FOOTER_SIZE: usize = 28;
const FAE_FOOTER_MEMORY_REQUIREMENTS_OFFSET: isize = -28;
const FAE_FOOTER_PROFILE_OFFSET: isize = -24;
const FAE_FOOTER_CRC_OFFSET: isize = -20;
const FAE_FOOTER_EXTRA_FIELDS_OFFSET: isize = -16;
const FAE_FOOTER_ABI_OFFSET: isize = -12;
const FAE_FOOTER_ISA_OFFSET: isize = -8;
const FAE_FOOTER_MAGIC_OFFSET: isize = -4;

#[derive(Clone, Copy, PartialEq, Eq)]
enum FaeProfileKind {
    Application,
    SecurityDomain,
}

#[repr(C)]
struct ParsedFae {
    writable_len: usize,
    stack_len: usize,
    profile_kind: FaeProfileKind,
}

pub const APP_RAM_CAPACITY: usize = 8192;

struct AppAllocation {
    ptr: *mut u8,
    size: usize,
    align: usize,
}

struct ReservedAppMemory {
    allocation: AppAllocation,
    ram_size: usize,
    data_start: *mut u8,
    data_size: usize,
    stack_start: *mut u8,
    stack_size: usize,
}

pub struct SharedRustletCtx {
    ptr: *mut RustletCtx,
}

struct AbiInput;
struct AbiReady;
struct ReturnedState;

/// Typestate transaction for one Rustlet use of the shared secondary buffer.
///
/// Marker states are zero-sized and compile away. The transaction is neither
/// `Copy` nor `Clone`, so ABI preparation, execution, and returned-state access
/// must occur in order.
struct SharedRustletCall<'a, State> {
    shared: SharedAccess<'a>,
    _state: PhantomData<State>,
}

/// A descriptor carries an address, but cannot grant access without a lease.
impl SharedRustletCtx {
    /// # Safety
    /// `ptr` must address the live, initialized gate page (or an exclusively
    /// owned host test context) and remain valid for every descriptor/view use.
    /// All kernel access must use the page leases.
    pub(crate) unsafe fn new(ptr: *mut RustletCtx) -> Self {
        Self { ptr }
    }

    pub fn as_mut_ptr(&self) -> *mut RustletCtx {
        self.ptr
    }

    fn acquire(&self) -> SharedAccess<'_> {
        SharedAccess {
            ptr: self.ptr,
            lease: crate::shared_page::Lease::acquire(crate::shared_page::PAGE),
            _lifetime: PhantomData,
        }
    }

    #[cfg(test)]
    pub fn clear(&self) {
        self.acquire().clear();
    }
    pub fn clear_state(&self) {
        self.acquire().clear_state();
    }
    pub fn stage_state_from_registry(&self, state: &[u8]) -> bool {
        self.acquire().stage_state_from_registry(state)
    }
    /// Borrow state under an exclusive lease after validating its raw length.
    /// Returns None for malformed ABI state, without publishing or truncating it.
    pub fn state_bytes(&self) -> Option<SharedBytes<'_>> {
        let access = self.acquire();
        access.as_ref().try_state_bytes()?;
        Some(SharedBytes {
            access,
            state: true,
        })
    }
    pub fn outgoing_data(&self) -> SharedBytes<'_> {
        SharedBytes {
            access: self.acquire(),
            state: false,
        }
    }
    fn begin_handler_call(
        &self,
        state: impl FnOnce(&mut RustletCtx) -> bool,
    ) -> Option<SharedRustletCall<'_, AbiInput>> {
        self.acquire().begin_handler_call(state)
    }
}

/// Borrowed bytes retain the lease, including across registry persistence.
/// Dropping this view releases access; no reference can escape the view.
pub struct SharedBytes<'a> {
    access: SharedAccess<'a>,
    state: bool,
}

impl core::ops::Deref for SharedBytes<'_> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        if self.state {
            // Invariant: construction checked the length under this lease;
            // no kernel writer or Rustlet can change it while the view lives.
            self.access.as_ref().state_bytes()
        } else {
            self.access.as_ref().outgoing_data()
        }
    }
}

struct SharedAccess<'a> {
    ptr: *mut RustletCtx,
    lease: crate::shared_page::Lease,
    _lifetime: PhantomData<&'a SharedRustletCtx>,
}

impl<'a> SharedAccess<'a> {
    fn as_ref(&self) -> &RustletCtx {
        // SAFETY: the descriptor validates storage; this lease excludes all
        // other kernel views and Rustlet execution for the reference lifetime.
        unsafe { &*self.ptr }
    }
    fn as_mut(&mut self) -> &mut RustletCtx {
        // SAFETY: the exclusive lease and this mutable borrow bound the view.
        unsafe { &mut *self.ptr }
    }
    #[cfg(test)]
    fn reset(&mut self) {
        unsafe {
            oxi_core::core::secure_zero_raw(
                self.ptr.cast::<u8>(),
                core::mem::size_of::<RustletCtx>(),
            )
        };
    }

    /// Clears all command, response, status and serialized-state bytes.
    #[cfg(test)]
    pub fn clear(&mut self) {
        self.reset();
    }

    fn prepare_start(&mut self) {
        let buffer = self.as_mut();
        buffer.reset_control();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
    }

    fn stage_command(
        &mut self,
        header: rustlet_runtime::RustletApduHeader,
        incoming: &[u8],
    ) -> bool {
        let buffer = self.as_mut();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
        buffer.stage_command(header, incoming)
    }

    fn stage_existing_command(
        &mut self,
        header: rustlet_runtime::RustletApduHeader,
        incoming_len: usize,
    ) -> bool {
        let buffer = self.as_mut();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
        buffer.stage_existing_command(header, incoming_len)
    }

    pub fn stage_encoded_command(
        &mut self,
        mut header: rustlet_runtime::RustletApduHeader,
        encode: impl FnOnce(&mut [u8]) -> Option<usize>,
    ) -> bool {
        let buffer = self.as_mut();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
        let Some(incoming_len) = encode(&mut buffer.data) else {
            return false;
        };
        if incoming_len > rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX {
            return false;
        }
        header.lc = incoming_len as u8;
        header.le = incoming_len as u8;
        buffer.stage_preencoded_command(header, incoming_len)
    }

    /// Transfers the secondary half from kernel scratch ownership to ABI input.
    ///
    /// This is the mandatory transition before a Rustlet handler call. It
    /// removes any plaintext, ciphertext, MAC input, status, or state bytes
    /// left by the previous kernel-side use before publishing registry state.
    pub fn stage_state_from_registry(&mut self, state: &[u8]) -> bool {
        let buffer = self.as_mut();
        buffer.reset_control();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
        buffer.stage_state(state)
    }

    #[inline(always)]
    fn begin_handler_call(
        mut self,
        state: impl FnOnce(&mut RustletCtx) -> bool,
    ) -> Option<SharedRustletCall<'a, AbiInput>> {
        let buffer = self.as_mut();
        buffer.reset_control();
        buffer.set_version(rustlet_runtime::ABI_VERSION);
        state(buffer).then_some(SharedRustletCall {
            shared: self,
            _state: PhantomData,
        })
    }

    /// Scrubs the complete serialized-state capacity after kernel persistence.
    pub fn clear_state(&mut self) {
        self.as_mut().clear_state();
    }

    /// Validate under the resumed exclusive lease before exposing returned
    /// state or response. Failure discards both halves; callers retire the
    /// invocation and roll back through the existing abnormal-return path.
    fn validate_returned_state(
        mut self,
    ) -> Result<SharedRustletCall<'a, ReturnedState>, ApduStatus> {
        if self.as_ref().try_state_bytes().is_none() {
            self.as_mut().reset_control();
            oxi_core::core::secure_zero(&mut self.as_mut().data);
            return Err(ApduStatus::wrong_length());
        }
        Ok(SharedRustletCall {
            shared: self,
            _state: PhantomData,
        })
    }

    fn stage_command_from_apdu(&mut self, apdu: &mut apdu_manager::Apdu<'_>) -> bool {
        let header = apdu.header();
        let incoming_len = apdu.incoming_len();
        let header = rustlet_runtime::RustletApduHeader {
            cla: header.cla,
            ins: header.ins,
            p1: header.p1,
            p2: header.p2,
            lc: header.p3,
            le: header.p3,
        };
        // Compare raw addresses before forming references to possibly shared bytes.
        let shared_data = unsafe { core::ptr::addr_of!((*self.ptr).data) }.cast::<u8>();
        if core::ptr::eq(apdu.payload_ptr(), shared_data) {
            self.stage_existing_command(header, incoming_len)
        } else {
            self.stage_command(header, apdu.incoming_data())
        }
    }

    fn status(&self) -> ApduStatus {
        self.as_ref().status()
    }

    fn status_or(&self, fallback: ApduStatus) -> ApduStatus {
        let status = self.status();
        if status.sw1 == 0 && status.sw2 == 0 {
            fallback
        } else {
            status
        }
    }

    fn copy_outgoing_to_apdu(self, apdu: &mut apdu_manager::Apdu<'_>) -> bool {
        let outgoing_len = self.as_ref().outgoing_len();
        if outgoing_len == 0 {
            return true;
        }
        if outgoing_len > rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX {
            return false;
        }
        let shared_data = unsafe { core::ptr::addr_of!((*self.ptr).data) }.cast::<u8>();
        if core::ptr::eq(apdu.payload_ptr(), shared_data) {
            // Return ownership before the transport can expose the same bytes.
            drop(self);
            let _ = apdu.set_outgoing();
            apdu.set_outgoing_length(outgoing_len);
        } else {
            let _ = apdu.set_outgoing();
            apdu.set_outgoing_length(outgoing_len);
            apdu.buffer_mut()[..outgoing_len].copy_from_slice(self.as_ref().outgoing_data());
        }
        true
    }
}

impl<'a> SharedRustletCall<'a, AbiInput> {
    #[inline(always)]
    fn stage_apdu(
        mut self,
        apdu: &mut apdu_manager::Apdu<'_>,
    ) -> Option<SharedRustletCall<'a, AbiReady>> {
        self.shared
            .stage_command_from_apdu(apdu)
            .then_some(SharedRustletCall {
                shared: self.shared,
                _state: PhantomData,
            })
    }

    #[inline(always)]
    fn stage_encoded(
        mut self,
        header: rustlet_runtime::RustletApduHeader,
        encode: impl FnOnce(&mut [u8]) -> Option<usize>,
    ) -> Option<SharedRustletCall<'a, AbiReady>> {
        self.shared
            .stage_encoded_command(header, encode)
            .then_some(SharedRustletCall {
                shared: self.shared,
                _state: PhantomData,
            })
    }

    #[inline(always)]
    fn stage_existing(
        mut self,
        header: rustlet_runtime::RustletApduHeader,
        incoming_len: usize,
    ) -> Option<SharedRustletCall<'a, AbiReady>> {
        self.shared
            .stage_existing_command(header, incoming_len)
            .then_some(SharedRustletCall {
                shared: self.shared,
                _state: PhantomData,
            })
    }
}

impl<'a> SharedRustletCall<'a, AbiReady> {
    #[inline(always)]
    fn invoke_handler(
        self,
        loaded: &LoadedFae,
        target: (usize, usize),
    ) -> Result<(SharedRustletCall<'a, ReturnedState>, ApduStatus), ApduStatus> {
        let ptr = self.shared.ptr;
        let execution = self.shared.lease.delegate();
        let status_word = invoke_app(
            loaded,
            AppInvocation {
                entry_pc: target.0,
                arg0: target.1,
                arg1: ptr as usize,
                arg2: 0,
                arg3: 0,
                kind: oxi_core::core::isolation::AppCallKind::Handler,
                fault_return_value: ApduStatus::internal_error().to_word() as usize,
            },
        );
        // Collapse the large isolation error/register result before carrying
        // it through the returned-state validation boundary.
        let status_word = status_word
            .map(status_from_app_return)
            .unwrap_or_else(|_| ApduStatus::internal_error());
        let returned = SharedAccess {
            ptr,
            lease: execution.resume(),
            _lifetime: PhantomData,
        }
        .validate_returned_state()?;
        Ok((returned, status_word))
    }
}

impl SharedRustletCall<'_, ReturnedState> {
    #[inline(always)]
    fn copy_outgoing_to_apdu(self, apdu: &mut apdu_manager::Apdu<'_>) -> bool {
        self.shared.copy_outgoing_to_apdu(apdu)
    }

    #[inline(always)]
    fn status_or(&self, fallback: ApduStatus) -> ApduStatus {
        self.shared.status_or(fallback)
    }
}

/// Failure to prepare an executable in the current execution environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoadError {
    /// The executable or isolation configuration cannot be used.
    Unsupported,
    /// The required RAM allocation cannot be satisfied.
    InsufficientMemory,
}

/// Validates the executable and reserves its isolated execution memory.
///
/// Allocation failures remain distinguishable from format or isolation errors;
/// this function does not enter the Rustlet. `text` must be the complete,
/// page-aligned flash extent owned exclusively by this package. The caller
/// resolves that ownership from a validated C0DE block or dedicated embedded
/// storage; this function checks containment, not ownership of surrounding bytes.
// Keep parsing/allocation temporaries off MSP during later Rustlet entry.
#[inline(never)]
pub fn load(
    fae: &'static [u8],
    text: oxi_core::core::isolation::AppMemoryWindow,
) -> Result<LoadedFae, LoadError> {
    if !(fae.as_ptr() as usize).is_multiple_of(2) {
        return Err(LoadError::Unsupported);
    }
    let parsed = parse_fae(fae).ok_or(LoadError::Unsupported)?;
    if text.start > fae.as_ptr() as usize
        || text.start.checked_add(text.len).is_none_or(|end| {
            (fae.as_ptr() as usize)
                .checked_add(fae.len())
                .is_none_or(|fae_end| fae_end > end)
        })
    {
        return Err(LoadError::Unsupported);
    }
    let reserved = reserve_app_memory(parsed.writable_len, parsed.stack_len)?;
    let memory_layout = oxi_core::core::isolation::AppMemoryLayout {
        text,
        ram: oxi_core::core::isolation::AppMemoryWindow {
            start: reserved.allocation.ptr as usize,
            len: reserved.ram_size,
        },
    };
    let isolation_plan = match oxi_core::core::isolation::plan_app_regions(memory_layout) {
        Ok(plan) => plan,
        Err(_) => {
            drop(reserved);
            return Err(LoadError::Unsupported);
        }
    };
    let gate_region = match oxi_core::core::target::isolated_app_gate_region() {
        Some(region) => region,
        None => {
            drop(reserved);
            return Err(LoadError::Unsupported);
        }
    };

    Ok(LoadedFae {
        app_gp: reserved.data_start as usize,
        image: fae,
        // SAFETY: the target gate region is validated above and remains resident.
        shared_buffer: unsafe { SharedRustletCtx::new(gate_region.base as *mut RustletCtx) },
        data_window: oxi_core::core::isolation::AppMemoryWindow {
            start: reserved.data_start as usize,
            len: reserved.data_size,
        },
        stack_window: oxi_core::core::isolation::AppMemoryWindow {
            start: reserved.stack_start as usize,
            len: reserved.stack_size,
        },
        isolation_plan,
        profile_kind: parsed.profile_kind,
        started: false,
        descriptor: None,
        _allocation: reserved.allocation,
    })
}

/// Selects a loader-validated entry from this image's immutable kernel snapshot.
#[derive(Clone, Copy)]
pub(crate) enum Handler {
    Install,
    Process,
    SecurityDomain,
}

impl LoadedFae {
    pub(crate) fn shared_buffer(&self) -> &SharedRustletCtx {
        &self.shared_buffer
    }
    pub(crate) fn text_window(&self) -> oxi_core::core::isolation::AppMemoryWindow {
        oxi_core::core::isolation::AppMemoryWindow {
            start: self.image.as_ptr() as usize,
            len: self.image.len(),
        }
    }
    pub(crate) fn data_window(&self) -> oxi_core::core::isolation::AppMemoryWindow {
        self.data_window
    }
    pub(crate) fn stack_window(&self) -> oxi_core::core::isolation::AppMemoryWindow {
        self.stack_window
    }
    pub(crate) fn heap_window(&self) -> Option<oxi_core::core::isolation::AppMemoryWindow> {
        self.descriptor.as_ref().map(|d| d.heap)
    }
    pub(crate) fn is_security_domain(&self) -> bool {
        self.descriptor.as_ref().is_some_and(|d| d.sddispatch != 0)
    }
    fn handler(&self, kind: Handler) -> Option<(usize, usize)> {
        let descriptor = self.descriptor.as_ref()?;
        let pc = match kind {
            Handler::Install => descriptor.install,
            Handler::Process => descriptor.process,
            Handler::SecurityDomain => descriptor.sddispatch,
        };
        (pc != 0).then_some((pc, descriptor.state.get()))
    }
}

pub(crate) fn validate_fae_reader(len: usize, read_byte: impl FnMut(usize) -> Option<u8>) -> bool {
    decode_fae_metadata(len, read_byte).is_some()
}

pub fn unload(loaded: LoadedFae) {
    drop(loaded);
}

/// Runs startup and validates its descriptor, preserving a hardware-fault
/// diagnosis separately from an invalid or absent descriptor.
pub fn call_start(loaded: &mut LoadedFae) -> Result<(), ApduStatus> {
    if core::mem::replace(&mut loaded.started, true) {
        return Err(ApduStatus::conditions_not_satisfied());
    }
    let mut shared = loaded.shared_buffer.acquire();
    shared.prepare_start();
    let execution = shared.lease.delegate();
    let descriptor = invoke_app(
        loaded,
        AppInvocation {
            entry_pc: (loaded.image.as_ptr() as usize) | 1,
            arg0: loaded.shared_buffer.as_mut_ptr() as usize,
            arg1: 0,
            arg2: 0,
            arg3: 0,
            kind: oxi_core::core::isolation::AppCallKind::Start,
            fault_return_value: 0,
        },
    );
    drop(execution);
    let descriptor = descriptor.map_err(|_| ApduStatus::conditions_not_satisfied())?;
    if last_call_was_isolation_fault() {
        return Err(ApduStatus::isolation_fault());
    }
    if descriptor.r1 != oxi_core::core::isolation::AppReturnCode::Descriptor.word() {
        oxi_core::consoleln!(
            "rustlet start returned non-descriptor code {}",
            descriptor.r1
        );
        return Err(ApduStatus::conditions_not_satisfied());
    }
    let code = oxi_core::core::isolation::AppMemoryWindow {
        start: loaded.image.as_ptr() as usize,
        len: loaded.image.len() - FAE_FOOTER_SIZE,
    };
    // Read integers only: arbitrary Rustlet bytes may not form valid function
    // pointers. The validator checks alignment and containment before each read.
    // No Rustlet or IRQ executes while these words are inspected.
    let checked = descriptor::read(
        loaded.data_window,
        code,
        loaded.profile_kind == FaeProfileKind::SecurityDomain,
        descriptor.r0,
        |address| {
            // SAFETY: descriptor::read permits only aligned initialized words
            // inside this owned allocation. Integer bit patterns are all valid.
            Some(unsafe { core::ptr::read(address as *const usize) })
        },
    )
    .ok_or_else(ApduStatus::conditions_not_satisfied)?;
    loaded.descriptor = Some(checked);
    Ok(())
}

pub fn call_handler(
    loaded: &LoadedFae,
    handler: Handler,
    apdu: &mut apdu_manager::Apdu<'_>,
    serialized_state: impl FnOnce(&mut RustletCtx) -> bool,
) -> HandlerCallResult {
    let Some(target) = loaded.handler(handler) else {
        return HandlerCallResult {
            status: ApduStatus::conditions_not_satisfied(),
            returned_normally: false,
        };
    };
    apdu.release_payload();
    let Some(call) = loaded.shared_buffer.begin_handler_call(serialized_state) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };
    let Some(call) = call.stage_apdu(apdu) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };

    let (returned, status_word) = match call.invoke_handler(loaded, target) {
        Ok(result) => result,
        Err(status) => {
            return HandlerCallResult {
                status,
                returned_normally: false,
            }
        }
    };
    let returned_normally = matches!(
        oxi_core::core::isolation::last_app_return_kind(),
        Some(oxi_core::core::isolation::AppReturnKind::HandlerReturn)
    );
    let fallback = status_word;
    if last_call_was_isolation_fault() {
        return HandlerCallResult {
            status: ApduStatus::isolation_fault(),
            returned_normally: false,
        };
    }
    let status = if returned_normally {
        returned.status_or(fallback)
    } else {
        fallback
    };
    if !returned.copy_outgoing_to_apdu(apdu) {
        return HandlerCallResult {
            status: ApduStatus::internal_error(),
            returned_normally: false,
        };
    }
    HandlerCallResult {
        status,
        returned_normally,
    }
}

pub fn call_handler_with_encoded_command(
    loaded: &LoadedFae,
    handler: Handler,
    header: rustlet_runtime::RustletApduHeader,
    encode: impl FnOnce(&mut [u8]) -> Option<usize>,
    serialized_state: impl FnOnce(&mut RustletCtx) -> bool,
) -> HandlerCallResult {
    let Some(target) = loaded.handler(handler) else {
        return HandlerCallResult {
            status: ApduStatus::conditions_not_satisfied(),
            returned_normally: false,
        };
    };
    let Some(call) = loaded.shared_buffer.begin_handler_call(serialized_state) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };
    let Some(call) = call.stage_encoded(header, encode) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };

    let (returned, status_word) = match call.invoke_handler(loaded, target) {
        Ok(result) => result,
        Err(status) => {
            return HandlerCallResult {
                status,
                returned_normally: false,
            }
        }
    };
    let returned_normally = matches!(
        oxi_core::core::isolation::last_app_return_kind(),
        Some(oxi_core::core::isolation::AppReturnKind::HandlerReturn)
    );
    let fallback = status_word;
    HandlerCallResult {
        status: if returned_normally {
            returned.status_or(fallback)
        } else {
            fallback
        },
        returned_normally,
    }
}

pub fn call_handler_with_existing_command(
    loaded: &LoadedFae,
    handler: Handler,
    header: rustlet_runtime::RustletApduHeader,
    incoming_len: usize,
    serialized_state: impl FnOnce(&mut RustletCtx) -> bool,
) -> HandlerCallResult {
    let Some(target) = loaded.handler(handler) else {
        return HandlerCallResult {
            status: ApduStatus::conditions_not_satisfied(),
            returned_normally: false,
        };
    };
    let Some(call) = loaded.shared_buffer.begin_handler_call(serialized_state) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };
    let Some(call) = call.stage_existing(header, incoming_len) else {
        return HandlerCallResult {
            status: ApduStatus::wrong_length(),
            returned_normally: false,
        };
    };

    let (returned, status_word) = match call.invoke_handler(loaded, target) {
        Ok(result) => result,
        Err(status) => {
            return HandlerCallResult {
                status,
                returned_normally: false,
            }
        }
    };
    let returned_normally = matches!(
        oxi_core::core::isolation::last_app_return_kind(),
        Some(oxi_core::core::isolation::AppReturnKind::HandlerReturn)
    );
    let fallback = status_word;
    HandlerCallResult {
        status: if returned_normally {
            returned.status_or(fallback)
        } else {
            fallback
        },
        returned_normally,
    }
}

fn invoke_app(
    loaded: &LoadedFae,
    invocation: AppInvocation,
) -> oxi_core::core::isolation::IsolationResult<oxi_core::core::isolation::AppReturnRegisters> {
    // SAFETY: LoadedFae retains the initialized stack; no Rustlet executes or
    // holds a live Rust reference into it during this synchronous observer.
    unsafe { crate::kernel_main_app::before_rustlet(loaded.stack_window) };
    // SAFETY: the loaded image owns its validated code, GP, stack and plan.
    // The synchronous caller retains it until return; no Rust stack-buffer
    // reference survives across entry. Invocation supplies the checked ABI.
    let execution = unsafe {
        oxi_core::core::isolation::AppExecution::from_raw_parts(
            invocation.entry_pc,
            loaded.app_gp,
            [
                invocation.arg0,
                invocation.arg1,
                invocation.arg2,
                invocation.arg3,
            ],
            loaded.stack_window,
            &loaded.isolation_plan,
        )
    };
    let result = oxi_core::core::isolation::enter_app_in_session(
        &execution,
        invocation.kind,
        invocation.fault_return_value,
    );
    // SAFETY: LoadedFae retains the initialized stack; no Rustlet executes or
    // holds a live Rust reference into it during this synchronous observer.
    unsafe { crate::kernel_main_app::after_rustlet(loaded.stack_window) };
    unsafe {
        // The stack has no state that may survive an isolated entry. Scrub it
        // only after observers (notably the high-watermark monitor) have read
        // it, and before any later Rustlet can reuse the allocation.
        oxi_core::core::secure_zero_raw(
            loaded.stack_window.start as *mut u8,
            loaded.stack_window.len,
        );

        // Ordinary Rustlet instances serialize their complete persistent
        // state and drop their in-memory instance before a normal handler
        // return. Their heap is consequently scratch storage and must not
        // remain readable between APDUs. Rustlet Security Domains are the
        // deliberate exception: their non-serialized secure-channel session
        // state must remain resident until the channel or SD is torn down;
        // their complete allocation is still scrubbed by `unload`.
        if invocation.kind == oxi_core::core::isolation::AppCallKind::Handler
            && loaded.profile_kind == FaeProfileKind::Application
            && matches!(
                oxi_core::core::isolation::last_app_return_kind(),
                Some(oxi_core::core::isolation::AppReturnKind::HandlerReturn)
            )
        {
            if let Some(heap) = loaded.heap_window() {
                oxi_core::core::secure_zero_raw(heap.start as *mut u8, heap.len);
            }
        }
    }
    result
}

fn status_from_app_return(registers: oxi_core::core::isolation::AppReturnRegisters) -> ApduStatus {
    if last_call_was_isolation_fault() {
        ApduStatus::isolation_fault()
    } else {
        ApduStatus::from_word(registers.r0 as u32)
    }
}

fn last_call_was_isolation_fault() -> bool {
    matches!(
        oxi_core::core::isolation::last_app_return_kind(),
        Some(oxi_core::core::isolation::AppReturnKind::IsolationFault)
    )
}

// ABI layout is checked at compile time; descriptor validation reads these
// pointer-sized words without forming references to untrusted ABI structs.
const _: () = {
    use core::mem::{offset_of, size_of};
    const WORD: usize = size_of::<usize>();
    assert!(size_of::<SelectedAppDescriptor>() == 5 * WORD);
    assert!(offset_of!(SelectedAppDescriptor, heap) == 3 * WORD);
    assert!(offset_of!(SelectedAppDescriptor, vtable) == WORD);
    assert!(offset_of!(SelectedAppDescriptor, security_domain_vtable) == 2 * WORD);
    assert!(size_of::<SelectedAppVtable>() == 2 * WORD);
    assert!(offset_of!(SelectedAppVtable, process_apdu) == WORD);
    assert!(size_of::<SelectedSecurityDomainVtable>() == WORD);
};

fn parse_fae(fae: &[u8]) -> Option<ParsedFae> {
    let (writable_len, stack_len, profile_kind) =
        decode_fae_metadata(fae.len(), |offset| fae.get(offset).copied())?;

    Some(ParsedFae {
        writable_len,
        stack_len,
        profile_kind,
    })
}

fn decode_fae_metadata(
    len: usize,
    mut read_byte: impl FnMut(usize) -> Option<u8>,
) -> Option<(usize, usize, FaeProfileKind)> {
    if len < FAE_FOOTER_SIZE {
        return None;
    }
    let magic = read_u32_from(len, FAE_FOOTER_MAGIC_OFFSET, &mut read_byte)?;
    if magic != FAE_MAGIC_NUMBER_AND_VERSION {
        return None;
    }
    let isa = read_u32_from(len, FAE_FOOTER_ISA_OFFSET, &mut read_byte)?;
    if !fae_isa_matches_kernel(isa) {
        return None;
    }
    if read_u32_from(len, FAE_FOOTER_ABI_OFFSET, &mut read_byte)? != FAE_ABI_DESCRIPTOR
        || read_u32_from(len, FAE_FOOTER_EXTRA_FIELDS_OFFSET, &mut read_byte)? != 0
    {
        return None;
    }
    let stored_crc = read_u32_from(len, FAE_FOOTER_CRC_OFFSET, &mut read_byte)?;
    if fae_crc32_reader(len, &mut read_byte)? != stored_crc {
        return None;
    }

    let profile = read_u32_from(len, FAE_FOOTER_PROFILE_OFFSET, &mut read_byte)?;
    let profile_kind = match profile >> 20 {
        FAE_APPLICATION_PROFILE => FaeProfileKind::Application,
        FAE_SECURITY_DOMAIN_PROFILE => FaeProfileKind::SecurityDomain,
        _ => return None,
    };
    let minimum_version = profile & 0x000F_FFFF;
    if minimum_version > 0x0000_1000 || rustlet_runtime::ABI_VERSION < 1 {
        return None;
    }
    let requirements = read_u32_from(len, FAE_FOOTER_MEMORY_REQUIREMENTS_OFFSET, &mut read_byte)?;
    let writable_len = ((requirements >> 16) as usize).checked_mul(FAE_MEMORY_UNIT)?;
    let stack_len = ((requirements & 0xFFFF) as usize).checked_mul(FAE_MEMORY_UNIT)?;
    if stack_len < FAE_MEMORY_UNIT {
        return None;
    }
    Some((writable_len, stack_len, profile_kind))
}

fn read_u32_from(
    len: usize,
    offset_from_end: isize,
    read_byte: &mut impl FnMut(usize) -> Option<u8>,
) -> Option<u32> {
    let start = len.checked_add_signed(offset_from_end)?;
    Some(u32::from_le_bytes([
        read_byte(start)?,
        read_byte(start + 1)?,
        read_byte(start + 2)?,
        read_byte(start + 3)?,
    ]))
}

fn fae_isa_matches_kernel(descriptor: u32) -> bool {
    let family = (descriptor >> 24) as u8;
    let subgroup = (descriptor >> 16) as u8;
    let extra_words = descriptor & 0x0F;
    let expected_subgroup = if cfg!(oxide_se_board_raspi_pico) {
        0x03
    } else {
        0x02
    };
    family == 0x01 && subgroup == expected_subgroup && extra_words == 0
}

#[cfg(test)]
fn fae_crc32(fae: &[u8]) -> u32 {
    fae_crc32_reader(fae.len(), &mut |offset| fae.get(offset).copied())
        .expect("slice reader covers its complete FAE")
}

fn fae_crc32_reader(len: usize, read_byte: &mut impl FnMut(usize) -> Option<u8>) -> Option<u32> {
    let crc_start = len.checked_sub(20)?;
    let mut crc = 0xFFFF_FFFFu32;
    for index in 0..len {
        let byte = read_byte(index)?;
        let byte = if (crc_start..crc_start + 4).contains(&index) {
            0
        } else {
            byte
        };
        crc ^= u32::from(byte);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xEDB8_8320 & (0u32.wrapping_sub(crc & 1)));
        }
    }
    Some(!crc)
}

/// Page bounds for dedicated embedded image storage, including its static tail.
/// Dynamic packages must instead use their validated owning C0DE extent.
pub(crate) fn aligned_text_window(start: usize, len: usize) -> Option<(usize, usize)> {
    let end = start.checked_add(len)?;
    end.checked_add(oxi_core::core::isolation::APP_TEXT_REGION_SIZE - 1)?;
    let text_start = oxi_core::core::isolation::align_down(
        start,
        oxi_core::core::isolation::APP_TEXT_REGION_SIZE,
    );
    let text_end =
        oxi_core::core::isolation::align_up(end, oxi_core::core::isolation::APP_TEXT_REGION_SIZE);
    Some((text_start, text_end.checked_sub(text_start)?))
}

fn reserve_app_memory(
    writable_len: usize,
    stack_len: usize,
) -> Result<ReservedAppMemory, LoadError> {
    let region_policy = oxi_core::core::target::mpu_region_policy();
    if matches!(
        region_policy.model,
        oxi_core::core::target::MpuAlignmentModel::Unsupported
    ) {
        return Err(LoadError::Unsupported);
    }
    let useful_data_size = writable_len;
    if useful_data_size > APP_RAM_CAPACITY {
        return Err(LoadError::InsufficientMemory);
    }
    let block_size = app_ram_block_size(useful_data_size, stack_len)
        .ok_or(LoadError::InsufficientMemory)?
        .max(region_policy.min_region_granule);
    let block_layout = Layout::from_size_align(block_size, block_size)
        .map_err(|_| LoadError::InsufficientMemory)?;
    let block_ptr = oxi_core::core::alloc(block_layout);
    if block_ptr.is_null() {
        return Err(LoadError::InsufficientMemory);
    }
    unsafe {
        // Allocation is not an initialization boundary: a buddy block may
        // still contain another Rustlet's data from an earlier lifetime.
        oxi_core::core::secure_zero_raw(block_ptr, block_size);
    }

    // The allocator returns one MPU-ready buddy block. The downward-growing
    // stack occupies its low end; GP and writable Rustlet memory start exactly
    // at the upper stack boundary.
    let stack_start = block_ptr;
    let data_start = unsafe { block_ptr.add(stack_len) };

    Ok(ReservedAppMemory {
        allocation: AppAllocation {
            ptr: block_ptr,
            size: block_size,
            align: block_size,
        },
        ram_size: block_size,
        data_start,
        data_size: block_size - stack_len,
        stack_start,
        stack_size: stack_len,
    })
}

impl Drop for AppAllocation {
    fn drop(&mut self) {
        // SAFETY: this unique owner retains the original allocation and Layout;
        // no references into it outlive LoadedFae. Erase before returning memory.
        unsafe {
            oxi_core::core::secure_zero_raw(self.ptr, self.size);
            oxi_core::core::dealloc(self.ptr, self.layout());
        }
    }
}

impl AppAllocation {
    fn layout(&self) -> Layout {
        Layout::from_size_align(self.size, self.align)
            .expect("stored app allocation layout must remain valid")
    }
}

fn app_ram_block_size(writable_len: usize, stack_len: usize) -> Option<usize> {
    if stack_len < FAE_MEMORY_UNIT || !stack_len.is_multiple_of(FAE_MEMORY_UNIT) {
        return None;
    }
    stack_len
        .checked_add(writable_len)?
        .checked_next_power_of_two()
}

/// Diagnostic-only structural boundary probe; no MPU configuration is changed.
#[cfg(oxide_se_kernel_app_module = "integrity-test")]
pub(crate) fn integrity_mapping_probe() -> bool {
    use oxi_core::core::target::{self, MpuAlignmentModel};
    use oxi_core::core::{
        isolation::{self, AppMemoryLayout, AppMemoryWindow},
        mpu_cover,
    };
    let relaxed = target::mpu_region_policy().model == MpuAlignmentModel::Relaxed32Byte;
    for (address, size) in [(0x1001_0700, 50 * 256), (0x1001_b700, 146 * 256)] {
        let Ok(padding) = mpu_cover::mpu_cover_require_padding_for(address, size) else {
            return false;
        };
        let start = address + padding.before;
        let end = start + size + padding.after;
        let Ok(plan) = isolation::plan_app_regions(AppMemoryLayout {
            text: AppMemoryWindow {
                start,
                len: end - start,
            },
            ram: AppMemoryWindow {
                start: 0x2000_0000,
                len: 8192,
            },
        }) else {
            return false;
        };
        let contains = |c: &oxi_core::core::mpu::MpuRegionConfig, p: usize| {
            p >= c.base_addr
                && p < c.base_addr + c.size
                && (relaxed
                    || c.disabled_subregions & (1 << ((p - c.base_addr) / (c.size / 8))) == 0)
        };
        let code = || {
            plan.regions
                .iter()
                .flatten()
                .filter(|r| r.config.executable)
        };
        if code().count() > mpu_cover::CODE_REGIONS {
            return false;
        }
        for region in code() {
            let c = region.config;
            for page in (c.base_addr..c.base_addr + c.size).step_by(256) {
                if contains(&c, page) && (page < start || page >= end) {
                    return false;
                }
            }
        }
        for page in (start..end).step_by(256) {
            if !code().any(|r| contains(&r.config, page)) {
                return false;
            }
        }
    }
    true
}

#[cfg(oxide_se_kernel_app_module = "integrity-test")]
pub(crate) fn integrity_descriptor_probe() -> bool {
    use oxi_core::core::isolation::AppMemoryWindow;
    let data = AppMemoryWindow {
        start: 0x1000,
        len: 0x100,
    };
    let code = AppMemoryWindow {
        start: 0x2000,
        len: 0x40,
    };
    let word_size = core::mem::size_of::<usize>();
    let words = [
        0x1080,
        0x1000 + 5 * word_size,
        0,
        0x10c0,
        32,
        0x2001,
        0x2011,
        0x2021,
    ];
    let read = |words: &[usize; 8], address, sd| {
        descriptor::read(data, code, sd, address, |at| {
            words.get(at.checked_sub(data.start)? / word_size).copied()
        })
    };
    if read(&words, 0x1000, false).is_none() {
        return false;
    }
    for address in [0, 0x1001, 0x1100 - word_size, usize::MAX & !(word_size - 1)] {
        if read(&words, address, false).is_some() {
            return false;
        }
    }
    for (slot, value) in [
        (0, 0),
        (0, 0x1001),
        (0, 0x1100),
        (1, 0),
        (1, 0x1001),
        (1, 0x1100 - word_size),
        (2, 0x1000 + 7 * word_size),
        (3, 0x1000),
        (3, 0x1080),
        (3, 0x10c1),
        (4, 0),
        (4, usize::MAX),
        (5, 0),
        (5, 0x2000),
        (5, 0x2041),
        (6, 0x1fff),
    ] {
        let mut malformed = words;
        malformed[slot] = value;
        if read(&malformed, 0x1000, false).is_some() {
            return false;
        }
    }
    let mut sd = words;
    sd[2] = 0x1000 + 7 * word_size;
    if read(&words, 0x1000, true).is_some() || read(&sd, 0x1000, true).is_none() {
        return false;
    }
    for handler in [0, 0x2020, 0x2041] {
        sd[7] = handler;
        if read(&sd, 0x1000, true).is_some() {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{
        aligned_text_window, app_ram_block_size, fae_crc32, parse_fae, FaeProfileKind,
        SharedRustletCtx,
    };
    use rustlet_runtime::{ApduStatus, RustletApduHeader, RustletCtx, SEApdu};
    use std::vec;
    use std::vec::Vec;

    #[test]
    fn app_ram_block_contains_stack_then_writable_data() {
        let stack_len = 3072;
        let block_size = app_ram_block_size(4096, stack_len).expect("RAM block size");

        assert_eq!(block_size, 8192);
        assert_eq!(block_size - stack_len, 5120);
    }

    fn compact_fae(profile: u32, requirements: u32) -> Vec<u8> {
        let mut image = vec![0xAA; 32];
        image.extend_from_slice(&requirements.to_le_bytes());
        image.extend_from_slice(&profile.to_le_bytes());
        image.extend_from_slice(&0u32.to_le_bytes());
        image.extend_from_slice(&0u32.to_le_bytes());
        image.extend_from_slice(&0xAC1D_A992u32.to_le_bytes());
        image.extend_from_slice(&0x0102_0000u32.to_le_bytes());
        image.extend_from_slice(&0xFAEC_0D10u32.to_le_bytes());
        let crc = fae_crc32(&image);
        let crc_offset = image.len() - 20;
        image[crc_offset..crc_offset + 4].copy_from_slice(&crc.to_le_bytes());
        image
    }

    #[test]
    fn compact_fae_accepts_application_profile_and_decodes_memory() {
        let image = compact_fae(0xA990_1000, (11 << 16) | 64);
        let parsed = parse_fae(&image).expect("valid compact Rustlet FAE");

        assert_eq!(parsed.writable_len, 352);
        assert_eq!(parsed.stack_len, 2048);
        assert!(parsed.profile_kind == FaeProfileKind::Application);
    }

    #[test]
    fn compact_fae_accepts_security_domain_profile() {
        let image = compact_fae(0x5DC0_1000, (24 << 16) | 64);
        let parsed = parse_fae(&image).expect("valid compact Security Domain FAE");

        assert!(parsed.profile_kind == FaeProfileKind::SecurityDomain);
    }

    #[test]
    fn compact_fae_rejects_crc_and_legacy_abi() {
        let valid = compact_fae(0xA990_1000, (11 << 16) | 64);

        let mut bad_crc = valid.clone();
        bad_crc[0] ^= 1;
        assert!(parse_fae(&bad_crc).is_none());

        let mut legacy_abi = valid.clone();
        let abi_offset = legacy_abi.len() - 12;
        legacy_abi[abi_offset..abi_offset + 4].copy_from_slice(&0xFACA_DE16u32.to_le_bytes());
        let crc_offset = legacy_abi.len() - 20;
        legacy_abi[crc_offset..crc_offset + 4].fill(0);
        let crc = fae_crc32(&legacy_abi);
        legacy_abi[crc_offset..crc_offset + 4].copy_from_slice(&crc.to_le_bytes());
        assert!(parse_fae(&legacy_abi).is_none());
    }

    #[test]
    fn compact_fae_preserves_small_large_and_maximum_stack_requirements() {
        for units in [1, 32, 65, 96, 128, u16::MAX as u32] {
            let image = compact_fae(0xA990_1000, (11 << 16) | units);
            let parsed = parse_fae(&image).expect("stack is a format-valid request");
            assert_eq!(parsed.stack_len, units as usize * 32);
            assert_eq!(parsed.writable_len, 352);
        }
        assert_eq!(app_ram_block_size(352, 1024), Some(2048));
        assert_eq!(app_ram_block_size(352, 3072), Some(4096));
        assert_eq!(app_ram_block_size(352, 4096), Some(8192));
        assert!(parse_fae(&compact_fae(0xA990_1000, 11 << 16)).is_none());
        assert_eq!(app_ram_block_size(352, 0), None);
        assert_eq!(app_ram_block_size(352, 33), None);
        assert_eq!(app_ram_block_size(usize::MAX, 2048), None);
    }

    #[test]
    fn app_ram_block_rounds_the_complete_request_once() {
        assert_eq!(app_ram_block_size(1, 2048), Some(4096));
        assert_eq!(app_ram_block_size(2048, 2048), Some(4096));
        assert_eq!(app_ram_block_size(2049, 2048), Some(8192));
        assert_eq!(app_ram_block_size(8192, 2048), Some(16384));
    }

    #[test]
    fn aligned_text_window_keeps_aligned_fae_bounds() {
        assert_eq!(
            aligned_text_window(0x1000_0000, 4096),
            Some((0x1000_0000, 4096))
        );
    }

    #[test]
    fn page_rounding_does_not_expand_to_two_kibibytes() {
        assert_eq!(
            aligned_text_window(0x1000_000c, 4096),
            Some((0x1000_0000, 4352))
        );
    }

    #[test]
    fn shared_context_is_two_256_byte_buffers() {
        let ctx = RustletCtx::new();
        let base = &ctx as *const RustletCtx as usize;
        let data = ctx.data.as_ptr() as usize;

        assert_eq!(core::mem::size_of::<RustletCtx>(), 512);
        assert_eq!(rustlet_runtime::APDU_SHARED_REGION_SIZE, 512);
        assert_eq!(rustlet_runtime::RUSTLET_CONTROL_BUFFER_CAPACITY, 256);
        assert_eq!(rustlet_runtime::APDU_BUFFER_CAPACITY, 256);
        assert_eq!(rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX, 255);
        assert_eq!(rustlet_runtime::STATE_BUFFER_CAPACITY, 244);
        assert_eq!(data - base, 256);
    }

    #[test]
    fn shared_context_keeps_short_apdu_payload_limit() {
        let mut ctx = RustletCtx::new();
        let header = RustletApduHeader {
            cla: 0x80,
            ins: 0xE6,
            p1: 0x0C,
            p2: 0x00,
            lc: 0xFF,
            le: 0,
        };
        let accepted = [0xA5; rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX];
        let rejected = [0xA5; rustlet_runtime::APDU_BUFFER_CAPACITY];

        assert!(ctx.stage_command(header, &accepted));
        assert_eq!(ctx.incoming_data().len(), 255);
        assert!(!ctx.stage_command(header, &rejected));
    }

    #[test]
    fn forged_state_is_rejected_before_a_returned_view_can_publish_bytes() {
        let _lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        for len in [0u8, 244, 245, 255] {
            let mut ctx = RustletCtx::new();
            ctx.data.fill(0xde);
            ctx.state_bytes_mut().fill(0xa5);
            // SAFETY: the repr(C) StateSlice length byte immediately precedes
            // its storage, inside this exclusively owned initialized context.
            unsafe { ctx.state_bytes_mut().as_mut_ptr().sub(1).write(len) };
            // SAFETY: the local context outlives the descriptor and its views.
            let shared = unsafe { SharedRustletCtx::new(&mut ctx) };
            assert_eq!(shared.state_bytes().is_some(), len <= 244);
            match shared.acquire().validate_returned_state() {
                Ok(returned) => {
                    assert!(len <= 244);
                    assert_eq!(
                        returned.shared.as_ref().try_state_bytes().unwrap().len(),
                        usize::from(len)
                    );
                    assert_eq!(returned.shared.as_ref().data, [0xde; 256]);
                }
                Err(status) => {
                    assert!(len > 244);
                    assert_eq!(status.to_word(), ApduStatus::wrong_length().to_word());
                    assert!(shared.state_bytes().unwrap().is_empty());
                }
            }
            if len > 244 {
                assert!(ctx.data.iter().all(|b| *b == 0));
                assert!(ctx.state_bytes_mut().iter().all(|b| *b == 0));
            }
        }
    }

    #[test]
    fn shared_byte_views_retain_exclusive_access_until_dropped() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        let _lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let mut ctx = RustletCtx::new();
        assert!(ctx.stage_state(&[0x11, 0x22]));
        // SAFETY: this initialized local context outlives all descriptor views
        // and is accessed only through the descriptor until it is dropped.
        let shared = unsafe { SharedRustletCtx::new(&mut ctx) };
        let state = shared.state_bytes().unwrap();
        assert_eq!(&*state, &[0x11, 0x22]);
        assert!(catch_unwind(AssertUnwindSafe(|| shared.clear_state())).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| shared.outgoing_data())).is_err());
        assert_eq!(&*state, &[0x11, 0x22]);
        drop(state);
        shared.clear_state();
        assert!(shared.state_bytes().unwrap().is_empty());
    }

    #[test]
    fn clearing_shared_page_removes_payload_state_and_status() {
        let _lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let mut ctx = RustletCtx::new();
        assert!(ctx.stage_command(
            RustletApduHeader {
                cla: 0x80,
                ins: 0xE6,
                p1: 0x0C,
                p2: 0x00,
                lc: 3,
                le: 0,
            },
            &[0xAA, 0xBB, 0xCC],
        ));
        assert!(ctx.stage_state(&[0x11, 0x22]));
        ctx.set_status(ApduStatus {
            sw1: 0x91,
            sw2: 0x23,
        });

        unsafe { SharedRustletCtx::new(&mut ctx) }.clear();

        assert_eq!(ctx.version(), 0);
        assert_eq!(ctx.status().sw1, 0);
        assert_eq!(ctx.status().sw2, 0);
        assert!(ctx.incoming_data().is_empty());
        assert!(ctx.state_bytes().is_empty());
        assert!(ctx.data.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn staging_registry_state_clears_previous_secondary_scratch() {
        let _lock = crate::shared_page::TEST_PAGE_LOCK.lock().unwrap();
        let mut ctx = RustletCtx::new();
        unsafe {
            core::ptr::write_bytes(
                (&mut ctx as *mut RustletCtx).cast::<u8>(),
                0xA5,
                rustlet_runtime::RUSTLET_CONTROL_BUFFER_CAPACITY,
            );
        }

        assert!(unsafe { SharedRustletCtx::new(&mut ctx) }.stage_state_from_registry(&[0x11, 0x22]));

        assert_eq!(ctx.version(), rustlet_runtime::ABI_VERSION);
        assert_eq!(ctx.state_bytes(), &[0x11, 0x22]);
        assert!(ctx.state_bytes_mut()[2..].iter().all(|byte| *byte == 0));
        assert_eq!(ctx.status().sw1, 0);
        assert_eq!(ctx.status().sw2, 0);
    }
}
