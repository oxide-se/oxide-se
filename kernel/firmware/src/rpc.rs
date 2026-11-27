//! One opaque inter-Rustlet syscall. No service schema or Postcard decoding here.
//! The SVC snapshots the request into an owned child gateway and yields to the
//! existing privileged invocation loop. A single pending continuation is allowed.
use super::*;
use oxi_core::core::isolation::{AppCallKind, AppReturnCode};
use rustlet_runtime::syscall_abi::{RpcCallParams, RPC_ERROR};

const GATE_SIZE: usize = rustlet_runtime::APDU_SHARED_REGION_SIZE;
const IDENTITY_SIZE: usize = 17;
const MAX_REQUEST: usize = rustlet_runtime::APDU_PAYLOAD_LENGTH_MAX - IDENTITY_SIZE;

struct Gateway(*mut RustletCtx);
impl Gateway {
    fn allocate() -> Option<Self> {
        let layout = Layout::from_size_align(GATE_SIZE, GATE_SIZE).ok()?;
        let ptr = oxi_core::core::alloc(layout);
        if ptr.is_null() {
            return None;
        }
        // SAFETY: unique, aligned allocation; every context field accepts zero bits.
        unsafe {
            core::ptr::write_bytes(ptr, 0, GATE_SIZE);
        }
        Some(Self(ptr.cast()))
    }
}
impl Drop for Gateway {
    fn drop(&mut self) {
        // SAFETY: no image or gateway view survives this owner. Original layout.
        unsafe {
            oxi_core::core::secure_zero_raw(self.0.cast(), GATE_SIZE);
            oxi_core::core::dealloc(
                self.0.cast(),
                Layout::from_size_align(GATE_SIZE, GATE_SIZE).unwrap(),
            );
        }
    }
}

struct Pending {
    gateway: Gateway,
    params: RpcCallParams,
    parent: ActiveAppCall,
    pc: usize,
    sp: usize,
}
// SAFETY: owner-core invocation state; never accessed by interrupt observers.
static PENDING: KernelCell<Option<Pending>> = unsafe { KernelCell::new(None) };
static IN_CHILD: KernelCell<bool> = unsafe { KernelCell::new(false) };

fn error(status: rustlet_runtime::ApduStatus) -> usize {
    RPC_ERROR | status.to_word() as usize
}

/// Capture the hardware-stacked continuation only within the caller's private stack.
fn continuation(call: &ActiveAppCall) -> Option<(usize, usize)> {
    #[cfg(target_arch = "arm")]
    {
        let psp: usize;
        // SAFETY: invoked synchronously in the SVC handler, before returning to Thread mode.
        unsafe {
            core::arch::asm!("mrs {}, PSP", out(reg) psp, options(nomem, nostack, preserves_flags));
        }
        if !psp.is_multiple_of(8)
            || psp < call.stack_window.start
            || psp.checked_add(32)? > call.stack_window.end()
        {
            return None;
        }
        // SAFETY: the complete basic exception frame is inside the suspended caller stack.
        let pc = unsafe { core::ptr::read((psp + 24) as *const u32) } as usize;
        let xpsr = unsafe { core::ptr::read((psp + 28) as *const u32) };
        let sp = psp.checked_add(32 + if xpsr & (1 << 9) != 0 { 4 } else { 0 })?;
        if pc < call.text_window.start
            || pc >= call.text_window.end()
            || sp > call.stack_window.end()
            || !sp.is_multiple_of(8)
        {
            return None;
        }
        Some((pc, sp))
    }
    #[cfg(not(target_arch = "arm"))]
    {
        let _ = call;
        None
    }
}

pub(super) unsafe extern "C" fn call_syscall(
    address: usize,
    _: usize,
    _: usize,
    _: usize,
) -> usize {
    let denied = || error(rustlet_runtime::ApduStatus::conditions_not_satisfied());
    if IN_CHILD.get()
        || PENDING.borrow().is_some()
        || oxi_core::core::isolation::app_call_kind() != Some(AppCallKind::Handler)
        || SD_DISPATCH_INSTANCE.get().is_some()
    {
        return denied();
    }
    let Some(mut parent) = active_app_call() else {
        return denied();
    };
    if parent.caller.len == 0 || parent.caller.len > 16 {
        return denied();
    }
    let Some((pc, sp)) = continuation(&parent) else {
        return denied();
    };
    // SAFETY: the SVC has suspended the caller; its invocation owns these memory windows.
    let caller = parent.caller;
    let Some((mut memory, params)) =
        (unsafe { syscall_memory::Memory::request::<RpcCallParams>(&mut parent, address) })
    else {
        return denied();
    };
    if params.target.len == 0
        || params.target.len > 16
        || params.target.as_slice() == caller.as_slice()
        || params.request_len > MAX_REQUEST
        || params.capacity > 255
        || params.request_len > params.capacity
    {
        return denied();
    }
    if memory.write(params.buffer, params.capacity).is_none() {
        return denied();
    }
    let Some(input) = memory.read(params.buffer, params.request_len) else {
        return denied();
    };
    let Some(gateway) = Gateway::allocate() else {
        return error(rustlet_runtime::ApduStatus {
            sw1: 0x6a,
            sw2: 0x84,
        });
    };
    // SAFETY: independent exclusive gateway allocation; caller memory is only read.
    let ctx = unsafe { &mut *gateway.0 };
    ctx.data[IDENTITY_SIZE..IDENTITY_SIZE + input.len()].copy_from_slice(input);
    ctx.data[0] = caller.len;
    ctx.data[1..IDENTITY_SIZE].copy_from_slice(&caller.bytes);
    *PENDING.borrow_mut() = Some(Pending {
        gateway,
        params,
        parent,
        pc,
        sp,
    });
    oxi_core::core::isolation::request_return_registers(0, AppReturnCode::RpcSuspended.word());
    0
}

// The only registry mutation in this scope is the ephemeral child's own state.
// It is destroyed before rollback. Parent/SD heaps cannot have changed, and their
// live invocation borrows must not be reborrowed by the ordinary selection observer.
struct ChildRollback;
impl crate::registry::savepoint::RollbackObserver for ChildRollback {
    fn before_rollback(_: &crate::registry::savepoint::RollbackView) {}
    fn after_rollback(_: crate::registry::savepoint::InvalidatedSlots) {}
}

/// Finish an opaque request in privileged Thread mode, then return its continuation.
pub(crate) fn complete_rpc() -> (usize, usize, usize) {
    let mut pending = PENDING
        .replace(None)
        .expect("RPC suspension without request");
    let phase = RESTORE_PHASE.get();
    let reference = RESTORE_REFERENCE.get();
    let sd = SD_DISPATCH_INSTANCE.get();
    set_active_app_call(None);
    IN_CHILD.set(true);
    let result = oxi_core::core::syscall::without_app_allocator(|| {
        // SAFETY: the child owns a separate gateway; no caller page loan survives the SVC.
        unsafe { crate::shared_page::with_suspended_caller(|| execute(&mut pending)) }
    });
    IN_CHILD.set(false);
    set_active_app_call(Some(pending.parent));
    RESTORE_PHASE.set(phase);
    RESTORE_REFERENCE.set(reference);
    SD_DISPATCH_INSTANCE.set(sd);
    (pending.pc, pending.sp, result)
}

fn execute(pending: &mut Pending) -> usize {
    let scope = match crate::registry::savepoint::OperationScope::<ChildRollback>::begin(true) {
        Ok(scope) => scope,
        Err(err) => {
            return error(rustlet_runtime::ApduStatus {
                sw1: err.status().sw1,
                sw2: err.status().sw2,
            })
        }
    };
    let result = execute_child(pending);
    scope.finish(result & RPC_ERROR == 0);
    result
}

fn execute_child(pending: &mut Pending) -> usize {
    let denied = || error(rustlet_runtime::ApduStatus::conditions_not_satisfied());
    // Lookup does not invoke SD policy hooks: authorization of the operation is
    // the called application's responsibility, using the kernel-supplied identity.
    let Some(object) = find_any_object_by_aid_raw(&pending.params.target) else {
        return error(rustlet_runtime::ApduStatus::file_not_found());
    };
    if object.object_kind != ManagedObjectKind::Instance || !object.may_select() {
        return denied();
    }
    let Some(slot) = registry_index_for_object(&object) else {
        return denied();
    };
    drop(object);
    let Some(reference) = AppRegistryReference::from_instance(slot) else {
        return denied();
    };
    let Some(fae) = reference.fae() else {
        return denied();
    };
    let Some(text) = package_text_window(fae) else {
        return denied();
    };
    let mut loaded = match fae_runtime::load(fae, text) {
        Ok(loaded) => loaded,
        Err(fae_runtime::LoadError::InsufficientMemory) => {
            return error(rustlet_runtime::ApduStatus {
                sw1: 0x6a,
                sw2: 0x84,
            })
        }
        Err(_) => return denied(),
    };
    loaded.instance_aid = pending.params.target;
    // SAFETY: pending owns the gateway until after the loaded image is destroyed.
    unsafe {
        loaded.use_rpc_gateway(pending.gateway.0);
    }
    if let Err(status) = fae_runtime::call_start(&mut loaded) {
        return error(status);
    }
    let Some(heap) = loaded.heap_window() else {
        return denied();
    };
    let Some(mut metadata) =
        AllocatorMetadata::allocate(oxi_core::core::metadata_size_for_heap_size(heap.len))
    else {
        return error(rustlet_runtime::ApduStatus {
            sw1: 0x6a,
            sw2: 0x84,
        });
    };
    let mut allocator = oxi_core::core::HeapAllocatorState::new();
    // SAFETY: validated exclusive heap plus separately owned allocator metadata.
    if !unsafe {
        oxi_core::core::reset_heap(
            &mut allocator,
            heap.start as *mut u8,
            heap.len,
            metadata.as_mut_ptr(),
            metadata.len(),
        )
    } {
        return denied();
    }
    // Bootstrap is untrusted and may have overwritten the gateway. Recopy the
    // original immutable caller request and authoritative identity at handler entry.
    let caller = pending.parent.caller;
    let result = ActiveAppCallGuard::with_shared(&loaded, None, || {
        oxi_core::core::syscall::with_app_allocator(&mut allocator, || {
            fae_runtime::call_handler_with_encoded_command(
                &loaded,
                fae_runtime::Handler::Rpc,
                rustlet_runtime::RustletApduHeader {
                    cla: 0,
                    ins: 0,
                    p1: 0,
                    p2: 0,
                    lc: 0,
                    le: 0,
                },
                |out| {
                    // SAFETY: validated initialized request range retained by the suspended caller.
                    let input = if pending.params.request_len == 0 {
                        &[]
                    } else {
                        // SAFETY: the nonempty range was validated before suspending A.
                        unsafe {
                            core::slice::from_raw_parts(
                                pending.params.buffer,
                                pending.params.request_len,
                            )
                        }
                    };
                    out[0] = caller.len;
                    out[1..IDENTITY_SIZE].copy_from_slice(&caller.bytes);
                    out[IDENTITY_SIZE..IDENTITY_SIZE + input.len()].copy_from_slice(input);
                    Some(IDENTITY_SIZE + input.len())
                },
                |ctx| reference.stage_state(ctx),
            )
        })
    });
    if !result.returned_normally
        || result.status.to_word() != rustlet_runtime::ApduStatus::success().to_word()
    {
        return error(result.status);
    }
    let Some((sd, package, _, instance)) = reference.identity() else {
        return denied();
    };
    let Some(state) = loaded.shared_buffer().state_bytes() else {
        return denied();
    };
    let saved = crate::registry::edit().upsert_instance_object(sd, instance, package, &state);
    drop(state);
    if let Err(err) = saved {
        return error(rustlet_runtime::ApduStatus {
            sw1: err.status().sw1,
            sw2: err.status().sw2,
        });
    }
    let response = loaded.shared_buffer().outgoing_data();
    if response.len() > pending.params.capacity {
        return error(rustlet_runtime::ApduStatus::wrong_length());
    }
    // SAFETY: the entire output was validated at the SVC boundary and A has not
    // resumed; B's mappings never included A's private stack, heap or gateway.
    if !response.is_empty() {
        unsafe {
            core::ptr::copy_nonoverlapping(
                response.as_ptr(),
                pending.params.buffer,
                response.len(),
            );
        }
    }
    response.len()
}
