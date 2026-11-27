//! Nested operation boundaries. Acceptance retains snapshot roots for the
//! enclosing transaction; neither acceptance nor rollback publishes flash.

use core::marker::PhantomData;

use super::state::OBJECT_REGISTRY;
use crate::registry::objects::{RegistrySavepoint, DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY};

pub(crate) type InvalidatedSlots = [bool; DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY];

/// Read-only description supplied immediately before local rollback.
/// Runtime observers can request reconstruction before the old slots return.
pub(crate) struct RollbackView<'a>(Option<&'a [u8]>);

impl RollbackView<'_> {
    pub(crate) fn touches(&self, slot: usize) -> bool {
        self.0.is_some_and(|bytes| {
            OBJECT_REGISTRY.borrow().image.slot(slot)
                != super::image::plaintext_entry(bytes, slot).expect("authenticated rollback entry")
        })
    }
}

/// Policy notifications run outside registry borrows, in their historical order.
/// Observers must not mutate the registry or call back into userland.
pub(crate) trait RollbackObserver {
    fn before_rollback(view: &RollbackView);
    fn after_rollback(invalidated: InvalidatedSlots);
}

/// Scopes must be consumed/dropped in stack order before their owner finalizes.
/// Disabled scopes and scopes outside a transaction are inert for compatibility.
pub(crate) struct OperationScope<H: RollbackObserver> {
    point: Option<RegistrySavepoint>,
    observer: PhantomData<H>,
}

impl<H: RollbackObserver> OperationScope<H> {
    pub(crate) fn begin(enabled: bool) -> super::objects::RegistryResult<Self> {
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Savepoint);
        let point = if enabled && OBJECT_REGISTRY.borrow().transaction_active() {
            Some(OBJECT_REGISTRY.borrow_mut().savepoint()?)
        } else {
            None
        };
        Ok(Self {
            point,
            observer: PhantomData,
        })
    }

    /// Retain this scope's changes, still subject to outer rollback.
    pub(crate) fn accept(mut self) {
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        let _timing = crate::registry::perf::start(crate::registry::perf::Metric::AcceptSavepoint);
        if let Some(point) = self.point.take() {
            OBJECT_REGISTRY.borrow_mut().finish_savepoint(point, true);
        }
    }

    /// Restore this scope and notify the caller about rebound object slots.
    pub(crate) fn rollback(mut self) {
        self.rollback_pending();
    }

    /// Compatibility adapter for callers with an existing retain decision.
    pub(crate) fn finish(self, retain: bool) {
        if retain {
            self.accept();
        } else {
            self.rollback();
        }
    }

    fn rollback_pending(&mut self) {
        if let Some(point) = self.point.take() {
            #[cfg(oxide_se_kernel_app_module = "registry-test")]
            let _timing =
                crate::registry::perf::start(crate::registry::perf::Metric::RollbackSavepoint);
            let root = OBJECT_REGISTRY.borrow().rollback_root(&point);
            let invalidated = if let Some(root) = root {
                let (invalidated, retired) =
                    super::retention::fatal(super::publication::with_snapshot(root, |bytes| {
                        H::before_rollback(&RollbackView(Some(bytes)));
                        OBJECT_REGISTRY.borrow_mut().restore_savepoint(point, bytes)
                    }));
                super::retention::fatal(retired.finish(&OBJECT_REGISTRY.borrow()));
                invalidated
            } else {
                H::before_rollback(&RollbackView(None));
                OBJECT_REGISTRY.borrow_mut().finish_savepoint(point, false)
            };
            H::after_rollback(invalidated);
        }
    }
}

impl<H: RollbackObserver> Drop for OperationScope<H> {
    fn drop(&mut self) {
        self.rollback_pending();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::transaction;
    use rustlet_runtime::Aid;
    use std::sync::Mutex;

    static EVENTS: Mutex<std::vec::Vec<&'static str>> = Mutex::new(std::vec::Vec::new());

    struct Observer;

    fn assert_value(expected: &[u8]) {
        let registry = OBJECT_REGISTRY.borrow();
        assert_eq!(
            registry
                .find_data_object(&Aid::new(&[1]), &Aid::new(&[2]))
                .unwrap()
                .data_bytes(),
            Some(expected)
        );
    }

    impl RollbackObserver for Observer {
        fn before_rollback(view: &RollbackView) {
            assert!(view.touches(0));
            assert!(view.touches(1));
            assert_value(b"new");
            EVENTS.lock().unwrap().push("before");
        }

        fn after_rollback(invalidated: InvalidatedSlots) {
            assert_value(b"old");
            assert!(!invalidated[0]); // Same identity, different bytes.
            assert!(invalidated[1]); // An inserted identity disappeared.
            assert_eq!(OBJECT_REGISTRY.borrow().len(), 1);
            EVENTS.lock().unwrap().push("after");
        }
    }

    #[test]
    fn rollback_observers_surround_restoration_without_holding_registry_borrows() {
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        EVENTS.lock().unwrap().clear();
        OBJECT_REGISTRY
            .borrow_mut()
            .upsert_data_object(Aid::new(&[1]), Aid::new(&[2]), b"old")
            .unwrap();
        transaction::begin_transaction().unwrap();
        let outer = OperationScope::<Observer>::begin(true).unwrap();
        let inner = OperationScope::<Observer>::begin(true).unwrap();
        for (id, bytes) in [(2, b"new".as_slice()), (3, b"inserted".as_slice())] {
            OBJECT_REGISTRY
                .borrow_mut()
                .upsert_data_object(Aid::new(&[1]), Aid::new(&[id]), bytes)
                .unwrap();
        }
        inner.accept();
        assert!(EVENTS.lock().unwrap().is_empty());
        super::super::testing::take_snapshot_reads();
        outer.rollback();
        assert_eq!(
            super::super::testing::take_snapshot_reads(),
            1,
            "observers and restore share one snapshot read"
        );
        assert_eq!(*EVENTS.lock().unwrap(), ["before", "after"]);
        assert!(transaction::transaction_active());
        transaction::rollback_transaction();
    }
}
