//! Registry initialization in a fresh volatile context after reset.
//! This is not a runtime reset and never claims durability from its return.
use super::publication::{
    publish_persistent_registry_after_predeployment, set_persistence_bootstrap_in_progress,
};
use super::recovery::restore_persistent_registry_if_available;
use rustlet_runtime::Aid;

/// Runtime/bootstrap effects remain with the kernel application owner.
pub(crate) trait BootPolicy {
    fn install_runtime_hooks();
    fn activate_root(aid: Aid);
    fn bootstrap_root();
    fn bootstrap_plan();
}
/// Preserve seed -> runtime hooks -> recovery/bootstrap order exactly.
pub(crate) fn init_on_reset<P: BootPolicy>() {
    seed_embedded_objects();
    P::install_runtime_hooks();
    ensure_predeployment_initialized::<P>();
}
fn seed_embedded_objects() {
    #[cfg(not(test))]
    if super::volatile::enabled() {
        super::volatile::clear();
    }
    {
        let mut registry_guard = super::state::OBJECT_REGISTRY.borrow_mut();
        let registry = &mut *registry_guard;
        registry.clear();
        let security_domain_aid = rustlet_runtime::Aid::new(&[]);
        crate::embedded_apps::for_each_embedded_registry_seed(|seed| {
            let _ = registry.insert_package_object(
                security_domain_aid,
                seed.package_aid,
                seed.applet_aid,
                seed.fae,
            );
        });
    }
}

fn ensure_predeployment_initialized<P: BootPolicy>() {
    if restore_persistent_registry_if_available() {
        P::activate_root(crate::predeployment::root_instance_aid());
        return;
    }

    let root_instance_aid = crate::predeployment::root_instance_aid();
    if super::operations::read()
        .find_any_object(&root_instance_aid)
        .is_none()
    {
        set_persistence_bootstrap_in_progress(true);
        P::bootstrap_root();
        P::bootstrap_plan();
        set_persistence_bootstrap_in_progress(false);
        publish_persistent_registry_after_predeployment();
    } else {
        P::activate_root(root_instance_aid);
    }
}
