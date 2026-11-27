//! Materialize provisional snapshots separately from publishing the durable root.
use super::state::{OBJECT_REGISTRY, PERSISTENCE_RUNTIME_STATE};
use super::storage::PERSISTENCE_PAGE_BUFFER;
use super::{
    format as f,
    image::{Address, Entry, Image},
    objects::{Registry, RegistryError, RegistryResult},
    pages::Pages,
};
#[cfg(not(test))]
use super::{state::USED_PAGES, storage::PERSISTENCE_PAGE_BUFFER_SIZE};

pub(crate) fn set_persistence_bootstrap_in_progress(value: bool) {
    super::state::PERSISTENCE_BOOTSTRAP_IN_PROGRESS.set(value);
}
pub(crate) fn persistence_bootstrap_in_progress() -> bool {
    super::state::PERSISTENCE_BOOTSTRAP_IN_PROGRESS.get()
}
pub(crate) fn publish_persistent_registry_after_predeployment() {
    #[cfg(not(test))]
    if super::volatile::enabled() {
        return;
    }
    complete_initial_publication(
        publish_persistent_registry_after_mutation,
        super::storage::write_persistence_area_marker_page,
    )
    .expect("initial registry publication and marker");
}

fn complete_initial_publication(
    publish: impl FnOnce() -> RegistryResult,
    mark: impl FnOnce() -> bool,
) -> RegistryResult {
    publish()?;
    // Invariant: the marker becomes recognizable only after the first durable
    // journal root. Before that, reset restarts bootstrap from erased storage.
    if !mark() {
        super::storage::freeze();
        return Err(RegistryError::Persistence);
    }
    Ok(())
}

pub(crate) fn publish_persistent_registry_after_mutation() -> RegistryResult {
    if persistence_bootstrap_in_progress() {
        return Ok(());
    }
    #[cfg(test)]
    {
        let mut registry = OBJECT_REGISTRY.borrow_mut();
        registry.current = Some(write_snapshot(&mut registry, None)?);
        return Ok(());
    }
    #[cfg(not(test))]
    {
        if super::volatile::enabled() {
            return Ok(());
        }
        super::storage::require_writable()?;
        let mut registry = OBJECT_REGISTRY.borrow_mut();
        let root = match registry.current {
            Some(root) => root,
            None => write_snapshot(&mut registry, None)?,
        };
        // The image is now materialized even if journal publication fails.
        // Rollback must retire this provisional BOSS as well as its bodies.
        registry.current = Some(root);
        let area = super::physical::read_area().ok_or(RegistryError::Persistence)?;
        let offset = root.offset_in(super::references::base(), area.len(), 32)?;
        if PERSISTENCE_RUNTIME_STATE
            .borrow()
            .latest_registry
            .is_some_and(|r| r.offset == offset)
        {
            return Ok(());
        }
        let boss = f::decode_registry_block_at(area, offset, super::physical::logical_page_size())
            .map_err(|_| RegistryError::Persistence)?;
        // Only this call makes the snapshot a reset-recovery root.
        preserve_load(|| {
            super::journal::append(area, super::physical::logical_page_size(), offset)
        })?;
        let mut state = PERSISTENCE_RUNTIME_STATE.borrow_mut();
        state.latest_registry = Some(f::PersistentRange::new(offset, boss.total_len));
        state.mutation_counter = boss.mutation_counter;
        registry.current = Some(root);
        drop(state);

        Ok(())
    }
}
pub(crate) fn ensure_persistence_runtime_state(area: &[u8], page: usize) -> bool {
    if PERSISTENCE_RUNTIME_STATE.borrow().initialized {
        return true;
    }
    let Ok(latest) = super::journal::latest(area, page) else {
        return false;
    };
    super::state::initialize_persistence_runtime_state(
        latest.map(|b| f::PersistentRange::new(b.offset, b.total_len)),
        latest.map_or(0, |b| b.mutation_counter),
        latest.map_or(page, |b| b.offset + b.total_len),
    );
    true
}
pub(crate) fn with_snapshot<T>(
    root: Address,
    f: impl FnOnce(&[u8]) -> RegistryResult<T>,
) -> RegistryResult<T> {
    #[cfg(test)]
    {
        super::testing::with_snapshot(root, f)
    }
    #[cfg(not(test))]
    {
        if super::volatile::enabled() {
            return super::volatile::with_snapshot(root, f);
        }
        let area = super::physical::read_area().ok_or(RegistryError::Persistence)?;
        let offset = root.offset_in(super::references::base(), area.len(), 32)?;
        with_scratch(|scratch| {
            let bytes = f::decrypt_registry_image(
                area,
                offset,
                super::physical::logical_page_size(),
                scratch,
            )
            .map_err(|_| RegistryError::Persistence)?;
            f(bytes)
        })
    }
}
pub(crate) fn restore_snapshot<const N: usize>(
    root: Address,
    image: &mut Image<N>,
) -> RegistryResult {
    with_snapshot(root, |bytes| image.restore(bytes))
}
pub(crate) fn write_snapshot<const N: usize>(
    registry: &mut Registry<N>,
    extra: Option<Entry>,
) -> RegistryResult<Address> {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Publish);
    #[cfg(test)]
    {
        let _ = extra;
        return super::testing::save(&registry.image);
    }
    #[cfg(not(test))]
    {
        if super::volatile::enabled() {
            return super::volatile::save(&registry.image);
        }
        super::storage::require_writable()?;
        let area = super::physical::read_area().ok_or(RegistryError::Persistence)?;
        let page = super::physical::logical_page_size();
        if !super::storage::ensure_persistence_area_initialized(area, page)
            || !ensure_persistence_runtime_state(area, page)
        {
            return Err(RegistryError::Persistence);
        }
        let total = f::registry_block_total_len(registry.image.entries().len(), page)
            .map_err(|_| RegistryError::Capacity)?;
        if total > PERSISTENCE_PAGE_BUFFER_SIZE {
            return Err(RegistryError::Capacity);
        }
        let pages = &USED_PAGES;
        ensure_protection(registry, area, page, pages)?;
        let _ = extra; // Newly prepared bodies already own their reserved pages.
        let generation = PERSISTENCE_RUNTIME_STATE
            .borrow()
            .mutation_counter
            .checked_add(1)
            .ok_or(RegistryError::Persistence)?;
        let offset = super::storage::reserve_persistent_span(area, page, total, pages)?;
        let result = with_scratch(|scratch| {
            scratch[..total].fill(0);
            let useful = registry.image.encode(&mut scratch[32..total])?;
            scratch[..4].copy_from_slice(&f::REGISTRY_BLOCK_MAGIC.to_le_bytes());
            scratch[4..8].copy_from_slice(&(useful as u32).to_le_bytes());
            let seed =
                super::data_crypto::reserve_seed().map_err(|_| RegistryError::Persistence)?;
            scratch[8..16].copy_from_slice(&seed.to_le_bytes());
            scratch[32..40].copy_from_slice(&(generation as u64).to_le_bytes());
            super::boss_crypto::encrypt(offset, seed, &mut scratch[32..total])
                .map_err(|_| RegistryError::Persistence)?;
            f::seal_block(offset, &mut scratch[..total]).map_err(|_| RegistryError::Persistence)?;
            super::storage::write_persistent_block(offset, &scratch[..total])
        });
        if let Err(error) = result {
            // Preserve possibly programmed pages until reset after uncertainty.
            if super::storage::require_writable().is_ok() {
                super::retention::release_unattached(
                    pages,
                    f::PersistentRange::new(offset, total),
                )?;
            }
            return Err(error);
        }
        pages.rehome(
            f::PersistentRange::new(offset, total),
            registry.snapshots.snapshot_owner(),
        )?;
        super::header_auth::remember_publication(offset);
        registry.image.set_generation(generation as u64);
        Address::new(super::references::base() + offset as u32)
    }
}
fn preserve_load<T>(f: impl FnOnce() -> RegistryResult<T>) -> RegistryResult<T> {
    // Publication may append/rotate the journal while LOAD retains a partial
    // physical page. Preserve it for the entire operation, not only BOSS encoding.
    let mut saved = alloc::vec::Vec::new();
    if super::state::dynamic_package_load_in_progress() {
        let page = super::physical::logical_page_size();
        saved
            .try_reserve_exact(page)
            .map_err(|_| RegistryError::Capacity)?;
        saved.extend_from_slice(&PERSISTENCE_PAGE_BUFFER.borrow()[..page]);
    }
    let result = f();
    if !saved.is_empty() {
        PERSISTENCE_PAGE_BUFFER.borrow_mut()[..saved.len()].copy_from_slice(&saved);
        oxi_core::core::secure_zero(&mut saved);
    }
    result
}
fn with_scratch<T>(f: impl FnOnce(&mut [u8]) -> RegistryResult<T>) -> RegistryResult<T> {
    preserve_load(|| {
        let mut scratch = PERSISTENCE_PAGE_BUFFER.borrow_mut();
        let result = f(&mut *scratch);
        oxi_core::core::secure_zero(&mut *scratch);
        result
    })
}

/// Initialization only. Normal allocations use the maintained bitmap unchanged.
pub(crate) fn ensure_protection<const N: usize>(
    registry: &Registry<N>,
    area: &[u8],
    page: usize,
    pages: &Pages,
) -> RegistryResult {
    if pages.initialized() {
        return Ok(());
    }
    if !ensure_persistence_runtime_state(area, page) {
        return Err(RegistryError::Persistence);
    }
    pages.reset(page, area.len())?;
    #[cfg(not(test))]
    if let Err(error) = super::retention::visit_live(registry, |range| pages.retain(range)) {
        pages.invalidate(); // A partial initialization must never authorize allocation.
        return Err(error);
    }
    #[cfg(test)]
    let _ = registry;
    Ok(())
}

#[cfg(test)]
mod bootstrap_tests {
    use super::*;
    use core::cell::Cell;

    #[test]
    fn initialization_marker_requires_successful_publication() {
        let published = Cell::new(false);
        let marked = Cell::new(false);
        assert_eq!(
            complete_initial_publication(
                || Err(RegistryError::Persistence),
                || {
                    marked.set(true);
                    true
                },
            ),
            Err(RegistryError::Persistence)
        );
        assert!(!marked.get());
        complete_initial_publication(
            || {
                published.set(true);
                Ok(())
            },
            || {
                assert!(published.get());
                marked.set(true);
                true
            },
        )
        .unwrap();
        assert!(marked.get());
    }

    #[test]
    fn marker_failure_freezes_after_publication() {
        super::super::storage::reset_freeze_for_test();
        assert_eq!(
            complete_initial_publication(|| Ok(()), || false),
            Err(RegistryError::Persistence)
        );
        assert_eq!(
            super::super::storage::require_writable(),
            Err(RegistryError::Persistence)
        );
        super::super::storage::reset_freeze_for_test();
    }
}
