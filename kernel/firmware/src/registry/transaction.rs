//! Top-level transaction lifecycle, independent of APDU/session policy.
//!
//! The privileged owner core serializes calls. Begin starts a fresh failure
//! scope; nested operations use savepoints. Commit and rollback require all
//! operation scopes to have finished. Reset does not execute these functions.

use super::publication::publish_persistent_registry_after_mutation;
use super::savepoint::{OperationScope, RollbackObserver};
use super::state::OBJECT_REGISTRY;
use crate::kernel_cell::KernelCell;
use crate::registry::objects::RegistryResult;

// SAFETY: privileged owner-core state; IRQ handlers never access it.
static ABORT_REQUESTED: KernelCell<bool> = unsafe { KernelCell::new(false) };

/// Successful finalization does not necessarily mean a durable publication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CommitOutcome {
    /// Changes retained, including clean transactions and volatile-only modes.
    Retained,
    /// A sticky abort request prevented publication and restored the RAM view.
    Aborted,
}

/// Open a fresh transaction. Already-active transactions return InvalidState.
/// As in the historical APDU entry, the abort latch is cleared before begin;
/// callers must use savepoints, not this function, for nested operations.
pub(crate) fn begin_transaction() -> RegistryResult {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::BeginTransaction);
    *ABORT_REQUESTED.borrow_mut() = false;
    OBJECT_REGISTRY.borrow_mut().begin_transaction()
}

pub(crate) fn transaction_active() -> bool {
    OBJECT_REGISTRY.borrow().transaction_active()
}

/// Request deferred, sticky abandonment. Does not immediately restore objects.
pub(crate) fn request_abort() {
    *ABORT_REQUESTED.borrow_mut() = true;
}

/// Attempt one publication for a dirty, non-aborted transaction, then close it.
/// On publication error, restore RAM and propagate the error. This does not
/// imply physical undo of flash bytes or settle the VerifyFailed proof obligation.
pub(crate) fn commit_transaction() -> RegistryResult<CommitOutcome> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Commit);
    commit_transaction_with(publish_persistent_registry_after_mutation)
}

/// Same lifecycle with an injected publisher for host characterization.
pub(crate) fn commit_transaction_with(
    publish: impl FnOnce() -> RegistryResult,
) -> RegistryResult<CommitOutcome> {
    let aborted = { *ABORT_REQUESTED.borrow() };
    let result = if !aborted && OBJECT_REGISTRY.borrow_mut().transaction_dirty() {
        publish()
    } else {
        Ok(())
    };
    if aborted || result.is_err() {
        rollback_transaction();
    } else {
        retire_snapshots_after_publication();
    }
    result.map(|()| {
        if aborted {
            CommitOutcome::Aborted
        } else {
            CommitOutcome::Retained
        }
    })
}

/// Reload the rollback root and close the transaction; no flash writes.
/// Runtime/session cleanup belongs to the caller. Harmless if already closed.
pub(crate) fn rollback_transaction() {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Rollback);
    OBJECT_REGISTRY.borrow_mut().finish_transaction(false);
}

/// Release transaction snapshot roots only. This function never publishes a snapshot.
fn retire_snapshots_after_publication() {
    OBJECT_REGISTRY.borrow_mut().finish_transaction(true);
}

/// Hooks preserve the owner's policy when an operation creates a transaction.
/// Nested operations neither start nor finish the enclosing transaction.
pub(crate) trait OperationOwner: RollbackObserver {
    fn begin_owned_transaction() -> RegistryResult;
    fn finish_owned_transaction() -> RegistryResult<CommitOutcome>;
}

struct TransactionOwner(bool);

impl Drop for TransactionOwner {
    fn drop(&mut self) {
        if self.0 {
            rollback_transaction();
        }
    }
}

/// Join the current transaction or own a temporary one, with a local savepoint.
/// A returned operation error and host unwind restore its local changes. Reset
/// is different: it discards RAM without running the guards. An owned transaction
/// abandoned at finalization returns InvalidState, never the operation value.
/// Joined operations remain provisional until their external owner finalizes.
pub(crate) fn run_operation<H: OperationOwner, T>(
    operation: impl FnOnce() -> RegistryResult<T>,
) -> RegistryResult<T> {
    let owns_transaction = !transaction_active();
    if owns_transaction {
        H::begin_owned_transaction()?;
    }
    let mut owner = TransactionOwner(owns_transaction);
    let scope = OperationScope::<H>::begin(true)?;
    let result = operation();
    scope.finish(result.is_ok());
    if owner.0 && result.is_ok() {
        let outcome = H::finish_owned_transaction()?;
        owner.0 = false;
        // Finalization closed the transaction, but an abort did not retain
        // the operation's changes. Never return its successful value.
        if outcome == CommitOutcome::Aborted {
            return Err(super::objects::RegistryError::InvalidState);
        }
    }
    result
}

#[cfg(test)]
pub(crate) fn reset_abort_for_test() {
    *ABORT_REQUESTED.borrow_mut() = false;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::objects::RegistryError;
    use rustlet_runtime::Aid;

    fn seed(value: &[u8]) {
        OBJECT_REGISTRY
            .borrow_mut()
            .upsert_data_object(Aid::new(&[1]), Aid::new(&[2]), value)
            .unwrap();
    }

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

    #[test]
    fn commit_outcome_distinguishes_retention_abort_and_publication_error() {
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        seed(b"old");
        begin_transaction().unwrap();
        seed(b"retained");
        let mut publications = 0;
        assert_eq!(
            commit_transaction_with(|| {
                publications += 1;
                Ok(())
            }),
            Ok(CommitOutcome::Retained)
        );
        assert_eq!(publications, 1);
        assert!(!transaction_active());
        assert_value(b"retained");

        begin_transaction().unwrap();
        seed(b"aborted");
        request_abort();
        assert_eq!(
            commit_transaction_with(|| panic!("abort cannot publish")),
            Ok(CommitOutcome::Aborted)
        );
        assert!(!transaction_active());
        assert_value(b"retained");

        begin_transaction().unwrap();
        seed(b"failed");
        assert_eq!(
            commit_transaction_with(|| Err(RegistryError::Persistence)),
            Err(RegistryError::Persistence)
        );
        assert!(!transaction_active());
        assert_value(b"retained");
    }

    #[test]
    fn explicit_rollback_restores_objects_and_allows_a_fresh_transaction() {
        let _guard = crate::selected_app::tests::reset_registry_test_state();
        seed(b"old");
        begin_transaction().unwrap();
        seed(b"tentative");
        rollback_transaction();
        rollback_transaction(); // Historical no-op on a closed journal.
        assert_value(b"old");
        assert!(!transaction_active());
        begin_transaction().unwrap();
        assert_eq!(
            commit_transaction_with(|| panic!("clean transaction cannot publish")),
            Ok(CommitOutcome::Retained)
        );
    }
}
