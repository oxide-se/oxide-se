//! Incremental ownership of pages. Scope exits transfer or release their pages.
//! External collection marks the current image and pending LOAD using a temporary
//! mask in the existing payload scratch, never a second resident table.
use super::objects::{Registry, RegistryResult};
#[cfg(not(test))]
use super::{
    format::{self as f, PersistentRange},
    image::{Address, Entry},
    objects::RegistryError,
    pages, state,
};

#[cfg(not(test))]
fn roots<const N: usize>(registry: &Registry<N>) -> impl Iterator<Item = Address> + '_ {
    let durable = state::PERSISTENCE_RUNTIME_STATE
        .borrow()
        .latest_registry
        .and_then(|r| Address::new(super::references::base() + r.offset as u32).ok());
    durable
        .into_iter()
        .chain(registry.snapshots.roots())
        .chain(registry.current)
}
#[cfg(not(test))]
fn root_range(root: Address) -> RegistryResult<PersistentRange> {
    let area = super::physical::read_area().ok_or(RegistryError::Persistence)?;
    let offset = root.offset_in(super::references::base(), area.len(), 32)?;
    // Roots were authenticated at creation/recovery. This structural view avoids
    // a CBC read of the generation merely to obtain the protected extent.
    let boss =
        f::decode_registry_block_known(area, offset, super::physical::logical_page_size(), 0)
            .map_err(|_| RegistryError::Persistence)?;
    Ok(PersistentRange::new(offset, boss.total_len))
}
#[cfg(not(test))]
fn entry_range(entry: Entry) -> RegistryResult<Option<PersistentRange>> {
    if entry.is_empty() {
        return Ok(None);
    }
    let reference = super::references::reference(entry.address().get());
    if reference.space != f::PersistentSpace::RegistryFlash {
        return if entry.kind().kind() == f::PersistentObjectKind::Package {
            Ok(None)
        } else {
            Err(RegistryError::Persistence)
        };
    }
    let area = super::physical::read_area().ok_or(RegistryError::Persistence)?;
    let block = f::decode_object_block_trusted(
        area,
        reference.offset as usize,
        super::physical::logical_page_size(),
    )
    .map_err(|_| RegistryError::Persistence)?;
    Ok(Some(PersistentRange::new(block.offset, block.total_len)))
}
#[cfg(not(test))]
pub(crate) fn visit_live<const N: usize>(
    registry: &Registry<N>,
    mut visit: impl FnMut(PersistentRange) -> RegistryResult,
) -> RegistryResult {
    let page = super::physical::logical_page_size();
    visit(PersistentRange::new(0, page))?;
    if let Some(load) = *state::DYNAMIC_LOAD_CONTEXT.borrow() {
        visit(PersistentRange::new(
            load.payload.reserved_offset,
            load.payload.block_total_len,
        ))?;
    }
    for (index, root) in roots(registry).enumerate() {
        if roots(registry).take(index).any(|old| old == root) {
            continue;
        }
        visit(root_range(root)?)?;
        if Some(root) == registry.current {
            continue;
        } // Current image already in RAM.
        super::publication::with_snapshot(root, |bytes| {
            for raw in bytes[8..].chunks_exact(super::image::ENTRY_LEN) {
                if let Some(range) = entry_range(Entry::decode(raw)?)? {
                    visit(range)?;
                }
            }
            Ok(())
        })?;
    }
    for entry in registry.image.entries() {
        if let Some(range) = entry_range(*entry)? {
            visit(range)?;
        }
    }
    Ok(())
}

/// Deferred until BOSS plaintext scratch is released. No root scan at local exit.
pub(crate) struct ScopeRelease {
    depth: usize,
    accept: bool,
}
impl ScopeRelease {
    pub(crate) fn new(depth: usize, accept: bool) -> Self {
        Self { depth, accept }
    }
    pub(crate) fn finish<const N: usize>(self, registry: &Registry<N>) -> RegistryResult {
        #[cfg(not(test))]
        {
            if super::volatile::enabled() {
                return super::volatile::collect(registry);
            }
            if super::storage::require_writable().is_err() {
                state::USED_PAGES.set_depth(self.depth - 1);
                return Ok(()); // No release after an uncertain physical outcome.
            }
            state::USED_PAGES.finish_scope(self.depth, self.accept);
            if self.depth == 1 {
                collect(registry)?;
            }
        }
        #[cfg(test)]
        let _ = (self.depth, self.accept, registry);
        Ok(())
    }
}

/// Collection at external close uses only the current RAM image and clear
/// extents. Old snapshot graphs are intentionally not visited.
pub(crate) fn collect<const N: usize>(registry: &Registry<N>) -> RegistryResult {
    #[cfg(not(test))]
    {
        if registry.snapshots.depth() != 0
            || super::storage::require_writable().is_err()
            || !state::USED_PAGES.initialized()
            || !state::USED_PAGES.collection_needed()
        {
            return Ok(());
        }
        let durable = state::PERSISTENCE_RUNTIME_STATE
            .borrow()
            .latest_registry
            .and_then(|r| Address::new(super::references::base() + r.offset as u32).ok());
        // During bootstrap an unpublished image may not describe the durable
        // graph. Retain conservatively until a successful publication.
        if durable.is_some() && durable != registry.current {
            return Ok(());
        }
        let mut scratch = state::PERSISTENCE_PAYLOAD_BUFFER.borrow_mut();
        let mask = &mut scratch[..pages::MASK_BYTES];
        mask.fill(0);
        let page = super::physical::logical_page_size();
        let mut mark = |r| pages::update_mask(mask, page, r, true);
        let result = (|| {
            mark(PersistentRange::new(0, page))?;
            if let Some(root) = registry.current {
                mark(root_range(root)?)?;
            }
            if let Some(load) = *state::DYNAMIC_LOAD_CONTEXT.borrow() {
                mark(PersistentRange::new(
                    load.payload.reserved_offset,
                    load.payload.block_total_len,
                ))?;
            }
            for entry in registry.image.entries() {
                if let Some(range) = entry_range(*entry)? {
                    mark(range)?;
                }
            }
            Ok(())
        })();
        if result.is_ok() {
            state::USED_PAGES.collect(mask);
        }
        oxi_core::core::secure_zero(mask);
        result
    }
    #[cfg(test)]
    {
        let _ = registry;
        Ok(())
    }
}

pub(crate) fn fatal<T>(result: RegistryResult<T>) -> T {
    result
        .inspect_err(|_| super::storage::freeze())
        .expect("fatal: registry page ownership or snapshot failure")
}

/// Keep reservations after an uncertain physical outcome, including LOAD cleanup.
pub(crate) fn release_unattached(
    pages: &super::pages::Pages,
    range: super::format::PersistentRange,
) -> RegistryResult {
    if super::storage::require_writable().is_err() {
        return Ok(());
    }
    pages.release(range)
}
