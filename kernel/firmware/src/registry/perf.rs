//! Opt-in intrinsic registry timing. Inclusive scopes are NOT additive.
//! Owner-core calls are serialized; no tracing or transport in measured scopes.
use crate::kernel_cell::KernelCell;
use core::sync::atomic::{AtomicBool, Ordering};
use oxi_core::core::target::monotonic_ticks;

#[repr(usize)]
#[derive(Clone, Copy)]
pub enum Metric {
    Recovery,
    Scan,
    DecodeBoss,
    DecodeObject,
    Allocate,
    Program,
    Erase,
    Publish,
    PrepareObject,
    PrepareLoad,
    AppendLoad,
    FinalizeLoad,
    BeginTransaction,
    Commit,
    Rollback,
    Savepoint,
    AcceptSavepoint,
    RollbackSavepoint,
    WriteData,
    ReadData,
    Delete,
    StageData,
    InitializeArea,
}
pub const COUNT: usize = 23;

#[derive(Clone, Copy)]
pub struct Sample {
    pub calls: u32,
    pub total: u64,
    pub min: u32,
    pub max: u32,
    pub last: u32,
}
impl Sample {
    const EMPTY: Self = Self {
        calls: 0,
        total: 0,
        min: u32::MAX,
        max: 0,
        last: 0,
    };
}
// SAFETY: diagnostic state is accessed by the serialized privileged owner core.
static SAMPLES: KernelCell<[Sample; COUNT]> = unsafe { KernelCell::new([Sample::EMPTY; COUNT]) };
static ENABLED: AtomicBool = AtomicBool::new(true);
pub fn enable(value: bool) {
    ENABLED.store(value, Ordering::Relaxed);
}
pub struct Scope {
    enabled: bool,
    metric: Metric,
    start: u32,
}
pub fn start(metric: Metric) -> Scope {
    Scope {
        enabled: ENABLED.load(Ordering::Relaxed),
        metric,
        start: monotonic_ticks(),
    }
}
impl Drop for Scope {
    fn drop(&mut self) {
        if !self.enabled {
            return;
        }
        let elapsed = monotonic_ticks().wrapping_sub(self.start);
        let mut samples = SAMPLES.borrow_mut();
        let sample = &mut samples[self.metric as usize];
        sample.calls = sample.calls.saturating_add(1);
        sample.total = sample.total.saturating_add(elapsed as u64);
        sample.min = sample.min.min(elapsed);
        sample.max = sample.max.max(elapsed);
        sample.last = elapsed;
    }
}
pub fn sample(index: usize) -> Option<Sample> {
    SAMPLES.borrow().get(index).copied()
}
pub fn clear() {
    *SAMPLES.borrow_mut() = [Sample::EMPTY; COUNT];
}
