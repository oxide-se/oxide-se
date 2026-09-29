use crate::core::mpu::{self, MpuRegionConfig};
use core::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

pub const APP_TEXT_REGION_SIZE: usize = super::mpu_cover::GRANULE;
/// Shared APDU and state buffer size; this region contains no executable code.
pub const APP_GATE_REGION_SIZE: usize = 512;
pub const APP_REGION_BUDGET: usize = 6;
const APP_GATE_REGION: u8 = 0;
const APP_RECYCLABLE_KERNEL_NX_REGION_START: u8 = APP_REGION_BUDGET as u8 - 1;
const APP_RECYCLABLE_KERNEL_NX_REGION_END: u8 = APP_REGION_BUDGET as u8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppMemoryWindow {
    pub start: usize,
    pub len: usize,
}

impl AppMemoryWindow {
    pub const fn end(self) -> usize {
        self.start + self.len
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppMemoryLayout {
    pub text: AppMemoryWindow,
    pub ram: AppMemoryWindow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IsolationRegion {
    pub region: u8,
    pub config: MpuRegionConfig,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IsolationPlan {
    pub region_count: usize,
    pub regions: [Option<IsolationRegion>; APP_REGION_BUDGET],
}

/// MPU-region contribution of one application memory window.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegionWindowUsage {
    pub window: AppMemoryWindow,
    pub required_regions: usize,
}

/// Complete diagnostic returned when an application exceeds its MPU budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegionBudgetDiagnostic {
    pub required: usize,
    pub available: usize,
    pub text: RegionWindowUsage,
    pub ram: RegionWindowUsage,
}

/// Borrowed authority to enter one loader-validated Rustlet memory layout.
/// The plan is borrowed; buffers and the plan are never copied into this token.
/// Construction is the raw-memory boundary and the token stays on its owner core.
#[derive(Debug)]
pub struct AppExecution<'a> {
    entry_pc: usize,
    app_gp: usize,
    arg0: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    stack: AppMemoryWindow,
    plan: &'a IsolationPlan,
    _owner: core::marker::PhantomData<*mut ()>,
}

impl<'a> AppExecution<'a> {
    /// Binds a raw entry and stack to the lifetime of a validated loader plan.
    ///
    /// # Safety
    /// The owner core must retain the executable image, writable stack and all
    /// argument-reachable memory for `'a`. The plan must describe those resources
    /// with the intended isolation permissions. The stack must be aligned to
    /// eight bytes, contain at least an exception frame and have no live Rust
    /// references while the Rustlet uses it. Entry/GP and argument ABI must match
    /// the loaded image. All invocations must obey the serialized owner-core
    /// execution model; no concurrent invocation may use these resources.
    pub unsafe fn from_raw_parts(
        entry_pc: usize,
        app_gp: usize,
        args: [usize; 4],
        stack: AppMemoryWindow,
        plan: &'a IsolationPlan,
    ) -> Self {
        Self {
            entry_pc,
            app_gp,
            arg0: args[0],
            arg1: args[1],
            arg2: args[2],
            arg3: args[3],
            stack,
            plan,
            _owner: core::marker::PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppReturnRegisters {
    pub r0: usize,
    pub r1: usize,
}

/// Kernel-side classification returned alongside the app return value.
#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppReturnCode {
    Normal = 0,
    Descriptor = 1,
}

impl AppReturnCode {
    pub const fn word(self) -> usize {
        self as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppCallKind {
    Start,
    Handler,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppReturnKind {
    HandlerReturn,
    Exit,
    /// A recoverable hardware fault terminated isolated execution.
    IsolationFault,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecutionPhase {
    Kernel,
    Rustlet,
    KernelServingRustlet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppSession {
    pub kind: AppCallKind,
    pub plan: IsolationPlan,
    pub fault_return_value: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IsolationError {
    InvalidTextAddress,
    InvalidTextSize,
    InvalidRamAddress,
    InvalidRamSize,
    RegionBudgetExceeded(RegionBudgetDiagnostic),
    AppCallAlreadyActive,
    TargetUnsupported,
    MpuFailure(mpu::MpuError),
}

pub type IsolationResult<T> = Result<T, IsolationError>;
pub type ExitObserver = fn(AppExitEvent);

/// Fault snapshot captured by the target backend before the isolation layer
/// decides whether a fault is recoverable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryFaultInfo {
    /// Target-specific fault status used by the recovery path.
    pub status: u32,
    /// Best-effort primary fault address, when the target exposes one.
    pub address: Option<usize>,
    /// ARM HardFault Status Register, or zero when unavailable on the profile.
    pub hfsr: u32,
    /// ARM Configurable Fault Status Register, or zero on ARMv6-M profiles.
    pub cfsr: u32,
    /// ARM MemManage Fault Address Register when valid.
    pub mmfar: Option<usize>,
    /// ARM BusFault Address Register when valid.
    pub bfar: Option<usize>,
    /// Program counter saved in the exception frame.
    pub stacked_pc: Option<usize>,
    /// Link register saved in the exception frame.
    pub stacked_lr: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppFault {
    MemoryAccessViolation(MemoryFaultInfo),
    WatchdogTimeout,
    UnknownSyscall(crate::core::syscall::SyscallNumber),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppExitEvent {
    Requested { sw1: u8, sw2: u8 },
    Fault(AppFault),
}

// Invariant: one privileged core owns session publication and retirement.
// Interrupts may inspect an active session but cannot publish a replacement;
// fault/watchdog paths request a redirect and defer retirement to resume cleanup.
// Publish the scalar kind last, and retire it before allowing the next plan update.
static ACTIVE_SESSION_KIND: AtomicU8 = AtomicU8::new(0);
static ACTIVE_FAULT_RETURN_VALUE: AtomicUsize = AtomicUsize::new(0);
static mut ACTIVE_SESSION_PLAN: IsolationPlan = IsolationPlan {
    region_count: 0,
    regions: [None; APP_REGION_BUDGET],
};
static LAST_APP_RETURN_KIND: AtomicU8 = AtomicU8::new(0);
#[unsafe(no_mangle)]
static mut GPOS_CORE_EXECUTION_PHASE: u32 = ExecutionPhase::Kernel as u32;
#[unsafe(no_mangle)]
static mut GPOS_CORE_ACTIVE_TEXT_REGION_MASK: u32 = 0;
static mut EXIT_OBSERVER: Option<ExitObserver> = None;
static mut EXIT_OBSERVER_INSTALLED: bool = false;
static WATCHDOG_TICKS: core::sync::atomic::AtomicU32 = core::sync::atomic::AtomicU32::new(0);
const WATCHDOG_TIMEOUT_TICKS: u32 = 100;

fn publish_active_session(session: &AppSession) {
    // SAFETY: publication occurs only while no session is active. The plan is
    // fully written before the volatile kind makes it visible to readers.
    unsafe {
        core::ptr::write_volatile(core::ptr::addr_of_mut!(ACTIVE_SESSION_PLAN), session.plan);
    }
    ACTIVE_FAULT_RETURN_VALUE.store(session.fault_return_value, Ordering::Relaxed);
    // Release publishes the completed plan before readers inspect active metadata.
    ACTIVE_SESSION_KIND.store(
        match session.kind {
            AppCallKind::Start => 1,
            AppCallKind::Handler => 2,
        },
        Ordering::Release,
    );
}

fn for_each_active_region(mut visit: impl FnMut(IsolationRegion)) {
    if !app_call_active() {
        return;
    }
    // SAFETY: the active plan is immutable until resume cleanup retires the
    // session. These private visitors only program MPU registers; neither they
    // nor interrupt observers replace the plan while this traversal is active.
    // Read one entry at a time, without creating a reference to mutable static
    // storage or copying the complete plan into a transition's stack frame.
    unsafe {
        let plan = core::ptr::addr_of!(ACTIVE_SESSION_PLAN);
        let count = core::ptr::read_volatile(core::ptr::addr_of!((*plan).region_count));
        assert!(count <= APP_REGION_BUDGET);
        let regions = core::ptr::addr_of!((*plan).regions).cast::<Option<IsolationRegion>>();
        for index in 0..count {
            if let Some(region) = core::ptr::read_volatile(regions.add(index)) {
                visit(region);
            }
        }
    }
}

fn set_last_app_return_kind(kind: Option<AppReturnKind>) {
    LAST_APP_RETURN_KIND.store(
        match kind {
            None => 0,
            Some(AppReturnKind::HandlerReturn) => 1,
            Some(AppReturnKind::Exit) => 2,
            Some(AppReturnKind::IsolationFault) => 3,
        },
        Ordering::Relaxed,
    );
}

fn set_execution_phase(phase: ExecutionPhase) {
    unsafe {
        core::ptr::write_volatile(
            core::ptr::addr_of_mut!(GPOS_CORE_EXECUTION_PHASE),
            phase as u32,
        );
    }
}

fn exit_observer() -> Option<ExitObserver> {
    let installed =
        unsafe { core::ptr::read_volatile(core::ptr::addr_of!(EXIT_OBSERVER_INSTALLED)) };
    if !installed {
        return None;
    }

    unsafe { core::ptr::read_volatile(core::ptr::addr_of!(EXIT_OBSERVER)) }
}

fn set_exit_observer(observer: Option<ExitObserver>) {
    unsafe {
        core::ptr::write_volatile(core::ptr::addr_of_mut!(EXIT_OBSERVER), observer);
        core::ptr::write_volatile(
            core::ptr::addr_of_mut!(EXIT_OBSERVER_INSTALLED),
            observer.is_some(),
        );
    }
}

pub fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

pub fn align_down(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    value & !(align - 1)
}

pub fn plan_app_regions(layout: AppMemoryLayout) -> IsolationResult<IsolationPlan> {
    validate_layout(layout)?;
    let budget = region_budget_diagnostic(layout);
    if budget.required > budget.available {
        return Err(IsolationError::RegionBudgetExceeded(budget));
    }

    let mut plan = IsolationPlan {
        region_count: 0,
        regions: [None; APP_REGION_BUDGET],
    };

    let mut region = 1u8;
    for covered in super::mpu_cover::Cover::new(
        layout.text.start,
        layout.text.len,
        crate::core::target::mpu_region_policy().model,
    )
    .map_err(|_| IsolationError::InvalidTextSize)?
    {
        push_region(
            &mut plan,
            region,
            MpuRegionConfig {
                base_addr: covered.base,
                size: covered.size,
                access: mpu::MpuAccess::ReadOnly,
                privilege: mpu::MpuPrivilege::Unprivileged,
                executable: true,
                disabled_subregions: covered.disabled_subregions,
            },
            budget,
        )?;
        region += 1;
    }

    push_region(
        &mut plan,
        region,
        MpuRegionConfig {
            base_addr: layout.ram.start,
            size: layout.ram.len,
            access: mpu::MpuAccess::ReadWrite,
            privilege: mpu::MpuPrivilege::Unprivileged,
            executable: false,
            disabled_subregions: 0,
        },
        budget,
    )?;

    Ok(plan)
}

fn region_budget_diagnostic(layout: AppMemoryLayout) -> RegionBudgetDiagnostic {
    let text_regions = text_region_count(layout.text);
    let ram_regions = 1;
    RegionBudgetDiagnostic {
        required: text_regions + ram_regions,
        available: APP_REGION_BUDGET,
        text: RegionWindowUsage {
            window: layout.text,
            required_regions: text_regions,
        },
        ram: RegionWindowUsage {
            window: layout.ram,
            required_regions: ram_regions,
        },
    }
}

fn text_region_count(window: AppMemoryWindow) -> usize {
    super::mpu_cover::Cover::new(
        window.start,
        window.len,
        crate::core::target::mpu_region_policy().model,
    )
    .map(|cover| cover.count())
    .unwrap_or(APP_REGION_BUDGET + 1)
}

/// Enters a validated Rustlet as an ordinary handler.
pub fn enter_app(execution: &AppExecution<'_>) -> IsolationResult<AppReturnRegisters> {
    enter_app_in_session(execution, AppCallKind::Handler, 0)
}

pub fn initialize_runtime_hooks() {
    clear_active_state();
    set_execution_phase(ExecutionPhase::Kernel);
    set_exit_observer(None);
    crate::core::syscall::install_handler(
        rustlet_runtime::syscall_abi::RETURN_TO_KERNEL,
        app_return_syscall,
    );
}

/// Enter an isolated call with kernel-owned session metadata.
///
/// The owning core must serialize calls. An existing session is rejected before
/// any metadata changes; the published plan remains immutable until cleanup.
pub fn enter_app_in_session(
    execution: &AppExecution<'_>,
    kind: AppCallKind,
    fault_return_value: usize,
) -> IsolationResult<AppReturnRegisters> {
    if app_call_active() {
        return Err(IsolationError::AppCallAlreadyActive);
    }
    publish_active_session(&AppSession {
        kind,
        plan: *execution.plan,
        fault_return_value,
    });
    WATCHDOG_TICKS.store(1, core::sync::atomic::Ordering::Release);
    set_last_app_return_kind(None);

    if let Err(error) = program_mpu_regions(execution.plan, false) {
        clear_active_state();
        return Err(error);
    }

    crate::core::target::app_stack_overflow_protection(Some(execution.stack));

    // SAFETY: only the loader's unsafe constructor can supply this execution
    // token; its memory stays live throughout this synchronous transition.
    match unsafe {
        crate::core::target::run_isolated_app(
            execution.entry_pc,
            execution.app_gp,
            execution.arg0,
            execution.arg1,
            execution.arg2,
            execution.arg3,
            execution.stack.end(),
        )
    } {
        Some(value) => Ok(value),
        None => {
            finish_app_call();
            Err(IsolationError::TargetUnsupported)
        }
    }
}

pub fn request_return(value: usize) {
    request_return_registers(value, AppReturnCode::Normal.word());
}

pub fn request_return_registers(r0: usize, r1: usize) {
    crate::core::syscall::request_thread_redirect(app_resume_pc(), r0, r1);
}

/// Report whether an isolated call is active, including its kernel/SVC phases.
pub fn app_call_active() -> bool {
    app_call_kind().is_some()
}

/// Read the active call kind without copying its MPU plan.
pub fn app_call_kind() -> Option<AppCallKind> {
    match ACTIVE_SESSION_KIND.load(Ordering::Acquire) {
        1 => Some(AppCallKind::Start),
        2 => Some(AppCallKind::Handler),
        _ => None,
    }
}

pub fn last_app_return_kind() -> Option<AppReturnKind> {
    match LAST_APP_RETURN_KIND.load(Ordering::Relaxed) {
        1 => Some(AppReturnKind::HandlerReturn),
        2 => Some(AppReturnKind::Exit),
        3 => Some(AppReturnKind::IsolationFault),
        _ => None,
    }
}

/// Return the active call's fault status, or zero when no session is published.
pub fn current_fault_return_value() -> usize {
    if !app_call_active() {
        return 0;
    }
    ACTIVE_FAULT_RETURN_VALUE.load(Ordering::Relaxed)
}

pub fn install_exit_observer(observer: ExitObserver) {
    set_exit_observer(Some(observer));
}

pub fn handle_memory_fault() {
    if !app_call_active() {
        panic!("unexpected MemManage fault outside isolated app execution");
    }

    let fault = AppFault::MemoryAccessViolation(
        crate::core::target::last_mem_manage_fault().unwrap_or(MemoryFaultInfo {
            status: 0,
            address: None,
            hfsr: 0,
            cfsr: 0,
            mmfar: None,
            bfar: None,
            stacked_pc: None,
            stacked_lr: None,
        }),
    );
    set_last_app_return_kind(Some(AppReturnKind::IsolationFault));
    notify_exit(AppExitEvent::Fault(fault));
    request_return(current_fault_return_value());
}

/// Abandons an isolated invocation that issued an uninstalled SVC.
/// The target dispatcher must first establish an unprivileged Thread origin.
/// This uses the existing exit observer and kernel-return redirect, so cleanup
/// and registry rollback apply without resuming the offending instruction.
/// Panics when no isolated session is active: a kernel error is not contained
/// by borrowing an unrelated or nonexistent application's recovery context.
#[cfg(target_arch = "arm")]
pub(crate) fn handle_unknown_syscall(number: crate::core::syscall::SyscallNumber) {
    assert!(
        app_call_active(),
        "unknown syscall outside isolated execution"
    );
    set_last_app_return_kind(Some(AppReturnKind::Exit));
    notify_exit(AppExitEvent::Fault(AppFault::UnknownSyscall(number)));
    request_return(current_fault_return_value());
}

/// Advances the best-effort Rustlet watchdog from the 100 ms kernel tick.
///
/// SysTick deliberately remains below SVC priority, so time spent inside a
/// syscall is not counted by this first implementation.
pub fn watchdog_tick() {
    let ticks = WATCHDOG_TICKS.load(core::sync::atomic::Ordering::Acquire);
    if ticks == 0 || !app_call_active() {
        return;
    }
    if ticks >= WATCHDOG_TIMEOUT_TICKS {
        WATCHDOG_TICKS.store(0, core::sync::atomic::Ordering::Release);
        notify_exit(AppExitEvent::Fault(AppFault::WatchdogTimeout));
        request_return(current_fault_return_value());
    } else {
        WATCHDOG_TICKS.store(
            ticks.saturating_add(1),
            core::sync::atomic::Ordering::Release,
        );
    }
}

fn notify_exit(event: AppExitEvent) {
    if let Some(observer) = exit_observer() {
        observer(event);
    }
}

unsafe extern "C" fn app_return_syscall(
    arg0: usize,
    arg1: usize,
    arg2: usize,
    _arg3: usize,
) -> usize {
    match (
        app_call_kind(),
        rustlet_runtime::RuntimeReturnKind::from_word(arg2),
    ) {
        (Some(AppCallKind::Start), rustlet_runtime::RuntimeReturnKind::Descriptor) => {
            request_return_registers(arg0, AppReturnCode::Descriptor.word());
        }
        (Some(AppCallKind::Handler), rustlet_runtime::RuntimeReturnKind::HandlerReturn) => {
            set_last_app_return_kind(Some(AppReturnKind::HandlerReturn));
            let return_value = ((arg0 as u8) as usize) | (((arg1 as u8) as usize) << 8);
            request_return_registers(return_value, AppReturnCode::Normal.word());
        }
        (Some(AppCallKind::Handler), rustlet_runtime::RuntimeReturnKind::Exit) => {
            set_last_app_return_kind(Some(AppReturnKind::Exit));
            notify_exit(AppExitEvent::Requested {
                sw1: arg0 as u8,
                sw2: arg1 as u8,
            });
            let return_value = ((arg0 as u8) as usize) | (((arg1 as u8) as usize) << 8);
            request_return_registers(return_value, AppReturnCode::Normal.word());
        }
        _ => {}
    };
    0
}

fn validate_layout(layout: AppMemoryLayout) -> IsolationResult<()> {
    let region_policy = crate::core::target::mpu_region_policy();

    if layout.text.start == 0 {
        return Err(IsolationError::InvalidTextAddress);
    }
    if layout.text.len == 0 {
        return Err(IsolationError::InvalidTextSize);
    }
    if layout.text.start.checked_add(layout.text.len).is_none() {
        return Err(IsolationError::InvalidTextSize);
    }
    validate_text_window(layout.text)?;
    validate_ram_window(layout.ram, region_policy)?;
    Ok(())
}

fn validate_text_window(window: AppMemoryWindow) -> IsolationResult<()> {
    if !window.start.is_multiple_of(APP_TEXT_REGION_SIZE) {
        panic!(
            "invalid Rustlet text window: start=0x{:08x} is not aligned to {} bytes",
            window.start, APP_TEXT_REGION_SIZE
        );
    }
    if window.len == 0 {
        return Err(IsolationError::InvalidTextSize);
    }
    if !window.len.is_multiple_of(APP_TEXT_REGION_SIZE) {
        panic!(
            "invalid Rustlet text window: len={} is not a multiple of {} bytes",
            window.len, APP_TEXT_REGION_SIZE
        );
    }
    Ok(())
}

fn validate_ram_window(
    window: AppMemoryWindow,
    region_policy: crate::core::target::MpuRegionPolicy,
) -> IsolationResult<()> {
    if window.start == 0 {
        return Err(IsolationError::InvalidRamAddress);
    }
    if window.len == 0 {
        return Err(IsolationError::InvalidRamSize);
    }

    match region_policy.model {
        crate::core::target::MpuAlignmentModel::Unsupported => {
            Err(IsolationError::TargetUnsupported)
        }
        crate::core::target::MpuAlignmentModel::Relaxed32Byte => {
            if !window
                .start
                .is_multiple_of(region_policy.min_region_granule)
            {
                return Err(IsolationError::InvalidRamAddress);
            }
            if !window.len.is_multiple_of(region_policy.min_region_granule) {
                return Err(IsolationError::InvalidRamSize);
            }
            Ok(())
        }
        crate::core::target::MpuAlignmentModel::StrictPowerOfTwo => {
            if !window.len.is_power_of_two()
                || window.len < region_policy.min_region_granule
                || !window.start.is_multiple_of(window.len)
            {
                return Err(IsolationError::InvalidRamAddress);
            }
            Ok(())
        }
    }
}

fn push_region(
    plan: &mut IsolationPlan,
    region: u8,
    config: MpuRegionConfig,
    budget: RegionBudgetDiagnostic,
) -> IsolationResult<()> {
    if plan.region_count >= APP_REGION_BUDGET {
        return Err(IsolationError::RegionBudgetExceeded(budget));
    }

    plan.regions[plan.region_count] = Some(IsolationRegion { region, config });
    plan.region_count += 1;
    Ok(())
}

fn program_mpu_regions(plan: &IsolationPlan, app_text_executable: bool) -> IsolationResult<()> {
    for region in 0..=APP_REGION_BUDGET as u8 {
        mpu::unset_region(region).map_err(IsolationError::MpuFailure)?;
    }

    let mut text_region_mask = 0u32;
    for entry in plan.regions[..plan.region_count].iter().flatten() {
        let config = config_for_execution_phase(entry.config, app_text_executable);
        mpu::set_region(entry.region, &config).map_err(IsolationError::MpuFailure)?;
        if entry.config.executable {
            text_region_mask |= 1u32 << entry.region;
        }
    }
    unsafe {
        core::ptr::write_volatile(
            core::ptr::addr_of_mut!(GPOS_CORE_ACTIVE_TEXT_REGION_MASK),
            text_region_mask,
        );
    }

    configure_gate_region()?;
    mpu::enable().map_err(IsolationError::MpuFailure)
}

fn configure_gate_region() -> Result<(), IsolationError> {
    let gate_region =
        crate::core::target::isolated_app_gate_region().ok_or(IsolationError::TargetUnsupported)?;
    mpu::set_region(
        APP_GATE_REGION,
        &MpuRegionConfig {
            base_addr: gate_region.base,
            size: gate_region.size,
            access: mpu::MpuAccess::ReadWrite,
            privilege: mpu::MpuPrivilege::Unprivileged,
            // Entry uses SVC exception return; the shared ABI page is data only.
            executable: false,
            disabled_subregions: 0,
        },
    )
    .map_err(IsolationError::MpuFailure)
}

fn config_for_execution_phase(
    mut config: MpuRegionConfig,
    app_text_executable: bool,
) -> MpuRegionConfig {
    if config.executable {
        config.executable = app_text_executable;
    }
    config
}

#[inline(always)]
fn set_active_app_text_executable(executable: bool) {
    let mask =
        unsafe { core::ptr::read_volatile(core::ptr::addr_of!(GPOS_CORE_ACTIVE_TEXT_REGION_MASK)) };
    let mut pending = mask;
    let mut region = 0u8;
    while pending != 0 {
        if pending & 1 != 0 {
            unsafe {
                crate::core::target::mpu_set_region_executable_unchecked(region, executable);
            }
        }
        pending >>= 1;
        region += 1;
    }
}

#[inline(always)]
fn restore_recyclable_region_for_rustlet_execution() {
    if !app_call_active() {
        return;
    }
    #[cfg(oxide_se_target_armv8m)]
    configure_gate_region().expect("failed to restore ARMv8-M user gate");

    for_each_active_region(|entry| {
        // PMSAv8 forbids overlapping regions. Its kernel phase disables all
        // overlapping RAM windows; restore them from this plan, not a snapshot.
        if cfg!(oxide_se_target_armv8m)
            || (APP_RECYCLABLE_KERNEL_NX_REGION_START..=APP_RECYCLABLE_KERNEL_NX_REGION_END)
                .contains(&entry.region)
        {
            let config = config_for_execution_phase(entry.config, true);
            let _ = mpu::set_region(entry.region, &config);
        }
    });
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_isolation_enter_rustlet_execution() {
    // Invariant: the last userland MPU slots may be recycled by phase. While
    // kernel code runs they may carry privileged RAM-XN mappings; while Rustlet
    // code runs they may carry Rustlet text/RAM mappings. Restore the Rustlet
    // mappings after disabling kernel NX and before touching executable bits.
    crate::core::target::protect_kernel_nx(false);
    restore_recyclable_region_for_rustlet_execution();
    set_active_app_text_executable(true);
    set_execution_phase(ExecutionPhase::Rustlet);
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_isolation_enter_kernel_execution() -> u32 {
    let phase = unsafe { core::ptr::read_volatile(core::ptr::addr_of!(GPOS_CORE_EXECUTION_PHASE)) };
    if phase != ExecutionPhase::Rustlet as u32 {
        return 0;
    }
    set_active_app_text_executable(false);
    // Invariant: after this point the recyclable slots are no longer Rustlet
    // regions. They are immediately reclaimed as kernel NX regions where
    // supported. Region 7 remains the permanent kernel stack guard.
    crate::core::target::protect_kernel_nx(true);
    set_execution_phase(ExecutionPhase::KernelServingRustlet);
    1
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_isolation_resume_rustlet_execution() {
    let phase = unsafe { core::ptr::read_volatile(core::ptr::addr_of!(GPOS_CORE_EXECUTION_PHASE)) };
    if phase != ExecutionPhase::KernelServingRustlet as u32 {
        return;
    }
    crate::core::target::protect_kernel_nx(false);
    restore_recyclable_region_for_rustlet_execution();
    set_active_app_text_executable(true);
    set_execution_phase(ExecutionPhase::Rustlet);
}

fn clear_active_state() {
    WATCHDOG_TICKS.store(0, core::sync::atomic::Ordering::Release);
    // Retirement runs after MPU cleanup; the next publication replaces the plan.
    ACTIVE_SESSION_KIND.store(0, Ordering::Release);
}

fn app_resume_pc() -> usize {
    unsafe { oxi_core_resume_isolated_app_ptr() as usize }
}

#[unsafe(no_mangle)]
extern "C" fn oxi_core_isolation_resume_cleanup() {
    finish_app_call();
}

fn finish_app_call() {
    WATCHDOG_TICKS.store(0, core::sync::atomic::Ordering::Release);
    crate::core::target::app_stack_overflow_protection(None);
    if app_call_active() {
        for_each_active_region(|region| {
            if region.config.executable {
                let config = config_for_execution_phase(region.config, false);
                let _ = mpu::set_region(region.region, &config);
            } else {
                let _ = mpu::unset_region(region.region);
            }
        });
        let _ = mpu::unset_region(APP_GATE_REGION);
        let _ = mpu::enable();
    }

    clear_active_state();
    set_execution_phase(ExecutionPhase::Kernel);
}

unsafe extern "C" {
    fn oxi_core_resume_isolated_app_ptr() -> *const ();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn published_session_owns_its_plan_and_retirement_hides_all_metadata() {
        clear_active_state();
        assert!(!app_call_active());
        assert_eq!(app_call_kind(), None);
        assert_eq!(current_fault_return_value(), 0);
        for_each_active_region(|_| panic!("inactive plan must not be visited"));

        let region = IsolationRegion {
            region: 1,
            config: MpuRegionConfig {
                base_addr: 0x1000,
                size: 2048,
                access: mpu::MpuAccess::ReadOnly,
                privilege: mpu::MpuPrivilege::Unprivileged,
                executable: true,
                disabled_subregions: 0,
            },
        };
        let mut session = AppSession {
            kind: AppCallKind::Start,
            fault_return_value: 0x6f00,
            plan: IsolationPlan {
                region_count: 3,
                regions: [None; APP_REGION_BUDGET],
            },
        };
        session.plan.regions[0] = Some(region);
        session.plan.regions[2] = Some(IsolationRegion {
            region: 3,
            ..region
        });
        // Entries outside region_count must remain invisible.
        session.plan.regions[5] = Some(IsolationRegion {
            region: 6,
            ..region
        });
        publish_active_session(&session);
        session.plan.regions[0] = None;

        assert!(app_call_active());
        assert_eq!(app_call_kind(), Some(AppCallKind::Start));
        assert_eq!(current_fault_return_value(), 0x6f00);
        let mut visited = std::vec::Vec::new();
        for_each_active_region(|entry| visited.push(entry));
        assert_eq!(
            visited,
            [
                region,
                IsolationRegion {
                    region: 3,
                    ..region
                }
            ]
        );

        clear_active_state();
        assert!(!app_call_active());
        assert_eq!(app_call_kind(), None);
        assert_eq!(current_fault_return_value(), 0);
        for_each_active_region(|_| panic!("retired plan must not be visited"));

        session.kind = AppCallKind::Handler;
        session.fault_return_value = 0x6985;
        session.plan.region_count = 1;
        session.plan.regions[0] = Some(IsolationRegion {
            region: 2,
            ..region
        });
        publish_active_session(&session);
        visited.clear();
        for_each_active_region(|entry| visited.push(entry));
        assert_eq!(
            visited,
            [IsolationRegion {
                region: 2,
                ..region
            }]
        );
        assert_eq!(app_call_kind(), Some(AppCallKind::Handler));
        assert_eq!(current_fault_return_value(), 0x6985);
        clear_active_state();
    }

    #[test]
    fn strict_policy_accepts_single_power_of_two_ram_window() {
        let policy = crate::core::target::MpuRegionPolicy::strict_power_of_two();
        let window = AppMemoryWindow {
            start: 0x2000_1000,
            len: 4096,
        };

        assert_eq!(validate_ram_window(window, policy), Ok(()));
    }

    #[test]
    fn relaxed_policy_accepts_32_byte_multiple_window() {
        let policy = crate::core::target::MpuRegionPolicy::relaxed_32_byte();
        let window = AppMemoryWindow {
            start: 0x2000_1020,
            len: 32 * 37,
        };

        assert_eq!(validate_ram_window(window, policy), Ok(()));
    }

    #[test]
    #[should_panic(expected = "invalid Rustlet text window")]
    fn text_window_must_be_aligned_to_text_region_size() {
        let layout = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x2000_1001,
                len: APP_TEXT_REGION_SIZE,
            },
            ram: AppMemoryWindow {
                start: 0x2000_2000,
                len: 4096,
            },
        };

        let _ = validate_layout(layout);
    }

    #[test]
    fn app_plan_uses_one_region_for_the_complete_ram_block() {
        let layout = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x0800_0000,
                len: APP_TEXT_REGION_SIZE,
            },
            ram: AppMemoryWindow {
                start: 0x2000_0000,
                len: 8192,
            },
        };

        let plan = plan_app_regions(layout).expect("valid isolation plan");
        assert_eq!(plan.region_count, 2);
        assert_eq!(
            plan.regions[1].expect("RAM region").config,
            MpuRegionConfig {
                base_addr: 0x2000_0000,
                size: 8192,
                access: mpu::MpuAccess::ReadWrite,
                privilege: mpu::MpuPrivilege::Unprivileged,
                executable: false,
                disabled_subregions: 0,
            }
        );
    }

    #[test]
    fn region_budget_diagnostic_reports_required_slots_and_windows() {
        let layout = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x0803_6e00,
                len: 291 * 256,
            },
            ram: AppMemoryWindow {
                start: 0x2000_0000,
                len: 8192,
            },
        };

        assert_eq!(
            plan_app_regions(layout),
            Err(IsolationError::RegionBudgetExceeded(
                RegionBudgetDiagnostic {
                    required: 7,
                    available: APP_REGION_BUDGET,
                    text: RegionWindowUsage {
                        window: layout.text,
                        required_regions: 6,
                    },
                    ram: RegionWindowUsage {
                        window: layout.ram,
                        required_regions: 1,
                    },
                }
            ))
        );
    }

    #[test]
    fn region_budget_accepts_exactly_available_slots() {
        let layout = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x0803_6e00,
                len: 290 * 256,
            },
            ram: AppMemoryWindow {
                start: 0x2000_0000,
                len: 8192,
            },
        };

        let plan = plan_app_regions(layout).expect("layout fits exactly");
        assert_eq!(plan.region_count, APP_REGION_BUDGET);
    }

    #[test]
    fn region_budget_reflects_text_alignment_packing() {
        let aligned = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x0800_0000,
                len: 16 * 1024,
            },
            ram: AppMemoryWindow {
                start: 0x2000_0000,
                len: 4096,
            },
        };
        let shifted = AppMemoryLayout {
            text: AppMemoryWindow {
                start: 0x0800_0800,
                len: 16 * 1024,
            },
            ram: aligned.ram,
        };

        assert_eq!(region_budget_diagnostic(aligned).text.required_regions, 1);
        assert_eq!(region_budget_diagnostic(shifted).text.required_regions, 2);
    }

    #[test]
    fn kernel_phase_changes_only_executable_regions_to_xn() {
        let text = MpuRegionConfig {
            base_addr: 0x0800_0000,
            size: APP_TEXT_REGION_SIZE,
            access: mpu::MpuAccess::ReadOnly,
            privilege: mpu::MpuPrivilege::Unprivileged,
            executable: true,
            disabled_subregions: 0,
        };
        let data = MpuRegionConfig {
            base_addr: 0x2000_1000,
            size: 1024,
            access: mpu::MpuAccess::ReadWrite,
            privilege: mpu::MpuPrivilege::Unprivileged,
            executable: false,
            disabled_subregions: 0,
        };

        assert!(!config_for_execution_phase(text, false).executable);
        assert!(config_for_execution_phase(text, true).executable);
        assert_eq!(config_for_execution_phase(data, true), data);
        assert_eq!(config_for_execution_phase(data, false), data);
    }
}
