//! Serialized access to the current registry view and typed staged mutations.
//!
//! Reads include provisional changes. Mutation methods preserve the object model's
//! snapshot-before-change semantics and never publish. Callers own a transaction or
//! use `transaction::run_operation`; bootstrap remains a separate internal path.
//! The guard preserves existing borrow lifetimes and cannot expose raw mutable
//! registry storage or transaction lifecycle methods in production.
use super::objects::*;
use super::state::OBJECT_REGISTRY;
use crate::kernel_cell::{KernelRef, KernelRefMut};
use core::ops::Deref;
use rustlet_runtime::Aid;

type KernelRegistry = Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>;

/// Borrow the current view, including provisional writes, without copying it.
/// `resolve`, `find_*` and `entries` retain their existing lookup/order contracts.
pub(crate) fn read() -> KernelRef<'static, KernelRegistry> {
    OBJECT_REGISTRY.borrow()
}

/// A decoded object is transient; its loan keeps backing pages live until the
/// access ends. It never becomes a resident per-object metadata cache.
pub(crate) struct ObjectRead {
    object: ObjectView,
    _loan: KernelRef<'static, KernelRegistry>,
}
impl Deref for ObjectRead {
    type Target = ObjectView;
    fn deref(&self) -> &ObjectView {
        &self.object
    }
}
pub(crate) fn read_object(
    lookup: impl FnOnce(&KernelRegistry) -> Option<ObjectView>,
) -> Option<ObjectRead> {
    let loan = read();
    let object = lookup(&loan)?;
    Some(ObjectRead {
        object,
        _loan: loan,
    })
}

/// Borrow typed mutation operations; this does not open or commit a transaction.
pub(crate) fn edit() -> Mutation {
    Mutation(OBJECT_REGISTRY.borrow_mut())
}

pub(crate) struct Mutation(KernelRefMut<'static, KernelRegistry>);
impl Deref for Mutation {
    type Target = KernelRegistry;
    fn deref(&self) -> &KernelRegistry {
        &self.0
    }
}
impl Mutation {
    pub(crate) fn insert_package_object(
        &mut self,
        parent_sd_aid: Aid,
        package_aid: Aid,
        applet_aid: Aid,
        binary_code: &'static [u8],
    ) -> RegistryResult {
        self.0
            .insert_package_object(parent_sd_aid, package_aid, applet_aid, binary_code)
    }
    pub(crate) fn set_package_state(
        &mut self,
        parent_sd_aid: &Aid,
        package_aid: &Aid,
        package_state: PackageObjectState,
    ) -> RegistryResult {
        self.0
            .set_package_state(parent_sd_aid, package_aid, package_state)
    }
    pub(crate) fn upsert_security_domain_object(
        &mut self,
        parent_sd_aid: Aid,
        instance_aid: Aid,
        package_aid: Aid,
        backend: SecurityDomainObjectBackend,
        privilege_bytes: [u8; 3],
        serialized_state: &[u8],
    ) -> RegistryResult {
        self.0.upsert_security_domain_object(
            parent_sd_aid,
            instance_aid,
            package_aid,
            backend,
            privilege_bytes,
            serialized_state,
        )
    }
    pub(crate) fn set_security_domain_state(
        &mut self,
        parent_sd_aid: &Aid,
        instance_aid: &Aid,
        object_state: SecurityDomainObjectState,
    ) -> RegistryResult {
        self.0
            .set_security_domain_state(parent_sd_aid, instance_aid, object_state)
    }
    pub(crate) fn upsert_instance_object(
        &mut self,
        parent_sd_aid: Aid,
        instance_aid: Aid,
        package_aid: Aid,
        serialized_state: &[u8],
    ) -> RegistryResult {
        self.0
            .upsert_instance_object(parent_sd_aid, instance_aid, package_aid, serialized_state)
    }
    pub(crate) fn set_instance_state(
        &mut self,
        parent_sd_aid: &Aid,
        instance_aid: &Aid,
        instance_state: InstanceObjectState,
    ) -> RegistryResult {
        self.0
            .set_instance_state(parent_sd_aid, instance_aid, instance_state)
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn upsert_key_object(
        &mut self,
        parent_sd_aid: Aid,
        object_aid: Aid,
        key_type: KeyObjectType,
        key_state: KeyObjectState,
        key_version: u8,
        key_id: u8,
        key_usage: u8,
        raw_key_bytes: &[u8],
    ) -> RegistryResult {
        self.0.upsert_key_object(
            parent_sd_aid,
            object_aid,
            key_type,
            key_state,
            key_version,
            key_id,
            key_usage,
            raw_key_bytes,
        )
    }
    // Part of the typed facade; some firmware profiles only use this in tests.
    #[allow(dead_code)]
    pub(crate) fn set_key_state(
        &mut self,
        parent_sd_aid: &Aid,
        object_aid: &Aid,
        key_state: KeyObjectState,
    ) -> RegistryResult {
        self.0.set_key_state(parent_sd_aid, object_aid, key_state)
    }
    pub(crate) fn attach_prepared_data_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        reservation: super::payload::DataReservation,
    ) -> RegistryResult {
        reservation.attach(&mut self.0, parent, aid)
    }
    #[cfg(not(test))]
    pub(crate) fn attach_volatile_data_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        content: super::content::Content,
    ) -> RegistryResult {
        self.0.attach_volatile_data_object(parent, aid, content)
    }

    #[allow(dead_code)] // Used by test and registry-test firmware profiles.
    pub(crate) fn upsert_data_object(
        &mut self,
        parent_sd_aid: Aid,
        object_aid: Aid,
        data: &[u8],
    ) -> RegistryResult {
        #[cfg(oxide_se_kernel_app_module = "registry-test")]
        let _timing = crate::registry::perf::start(crate::registry::perf::Metric::StageData);
        self.0.upsert_data_object(parent_sd_aid, object_aid, data)
    }
    pub(crate) fn delete_object(
        &mut self,
        parent_sd_aid: &Aid,
        object_kind: ManagedObjectKind,
        object_aid: &Aid,
    ) -> RegistryResult {
        self.0.delete_object(parent_sd_aid, object_kind, object_aid)
    }
    pub(crate) fn clone_scp03_keys(
        &mut self,
        source_sd_aid: Aid,
        target_sd_aid: Aid,
    ) -> RegistryResult {
        self.0.clone_scp03_keys(source_sd_aid, target_sd_aid)
    }
}
// Existing characterization fixtures may reset and inspect the compact registry.
// This escape hatch is absent from firmware builds.
#[cfg(test)]
impl core::ops::DerefMut for Mutation {
    fn deref_mut(&mut self) -> &mut KernelRegistry {
        &mut self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn facade_reads_staged_changes_and_rollback_restores_previous_identity() {
        let _lock = crate::selected_app::tests::reset_registry_test_state();
        let owner = Aid::from_array([0xF0, 1]);
        let aid = Aid::from_array([0xF0, 2]);
        edit().upsert_data_object(owner, aid, b"before").unwrap();
        super::super::begin_transaction().unwrap();
        edit()
            .delete_object(&owner, ManagedObjectKind::Data, &aid)
            .unwrap();
        let replacement = Aid::from_array([0xF0, 3]);
        edit()
            .upsert_data_object(owner, replacement, b"pending")
            .unwrap();
        assert!(read().find_data_object(&owner, &aid).is_none());
        assert_eq!(
            read()
                .find_data_object(&owner, &replacement)
                .unwrap()
                .data_bytes(),
            Some(&b"pending"[..])
        );
        super::super::transaction::rollback_transaction();
        assert!(read().find_data_object(&owner, &replacement).is_none());
        assert_eq!(
            read().find_data_object(&owner, &aid).unwrap().data_bytes(),
            Some(&b"before"[..])
        );
    }

    #[test]
    fn rejected_typed_write_keeps_prior_staged_changes() {
        let _lock = crate::selected_app::tests::reset_registry_test_state();
        let owner = Aid::from_array([0xF0, 1]);
        let aid = Aid::from_array([0xF0, 2]);
        super::super::begin_transaction().unwrap();
        edit().upsert_data_object(owner, aid, b"accepted").unwrap();
        let oversized = [0u8; rustlet_runtime::STATE_BUFFER_CAPACITY + 1];
        assert_eq!(
            edit().upsert_data_object(owner, aid, &oversized),
            Err(RegistryError::Capacity)
        );
        assert_eq!(
            read().find_data_object(&owner, &aid).unwrap().data_bytes(),
            Some(&b"accepted"[..])
        );
        assert!(read().transaction_active());
        super::super::transaction::rollback_transaction();
    }
}
