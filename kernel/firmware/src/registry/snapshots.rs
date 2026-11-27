//! Bounded rollback roots backed by flash or by volatile storage on flashless targets.

use super::image::Address;
use super::objects::{RegistryError, RegistryResult};

pub(crate) const MAX_DEPTH: usize = 6;

/// A scope token cannot be copied. Callers must finish scopes in LIFO order.
pub(crate) struct Boundary(u8);

/// `None` means the boundary still denotes the current, unmaterialized image.
/// All such boundaries share one view, and are resolved by one synchronous save.
pub(crate) struct Snapshots {
    roots: [Option<Address>; MAX_DEPTH],
    depth: u8,
}

impl Snapshots {
    pub(crate) const fn new() -> Self {
        Self {
            roots: [None; MAX_DEPTH],
            depth: 0,
        }
    }

    pub(crate) fn needs_snapshot(&self) -> bool {
        self.roots[..self.depth()].iter().any(Option::is_none)
    }

    /// A pre-state snapshot must survive rollback of its earliest dependent scope.
    pub(crate) fn snapshot_owner(&self) -> usize {
        self.roots[..self.depth()]
            .iter()
            .position(Option::is_none)
            .unwrap_or(self.depth())
    }

    pub(crate) fn depth(&self) -> usize {
        self.depth as usize
    }

    pub(crate) fn roots(&self) -> impl Iterator<Item = Address> + '_ {
        self.roots[..self.depth()].iter().flatten().copied()
    }

    /// The caller's current root is Some only if the complete current image is
    /// already protected in its backing store. Merely opening a scope never writes flash.
    pub(crate) fn begin(&mut self, current: Option<Address>) -> RegistryResult<Boundary> {
        if self.depth() == MAX_DEPTH {
            return Err(RegistryError::Capacity);
        }
        self.roots[self.depth()] = current;
        self.depth += 1;
        Ok(Boundary(self.depth))
    }

    /// Invariant: before mutating the registry, every active rollback boundary
    /// that depends on the current view has a complete, protected snapshot.
    /// Snapshot preparation failure leaves the registry unchanged.
    ///
    /// `save` must finish storing AND protecting before returning an address.
    /// This method is called by the image's barrier, before its actual mutation.
    pub(crate) fn before_change(
        &mut self,
        save: impl FnOnce() -> RegistryResult<Address>,
    ) -> RegistryResult {
        let depth = self.depth();
        if self.roots[..depth].iter().any(Option::is_none) {
            let root = save()?;
            for unresolved in self.roots[..depth].iter_mut().filter(|root| root.is_none()) {
                *unresolved = Some(root);
            }
        }
        Ok(())
    }

    pub(crate) fn accept(&mut self, point: Boundary) -> RegistryResult {
        self.check(&point)?;
        self.pop();
        Ok(())
    }

    /// Resolve and reload before dropping the root. Failure retains it for
    /// diagnostics/fatal handling; it must never make its pages recyclable.
    pub(crate) fn rollback(
        &mut self,
        point: Boundary,
        current: Option<Address>,
        reload: impl FnOnce(Address) -> RegistryResult,
    ) -> RegistryResult<Option<Address>> {
        self.check(&point)?;
        let root = self.roots[self.depth() - 1];
        if let Some(root) = root {
            if current != Some(root) {
                reload(root)?;
            }
        }
        self.pop();
        Ok(root.or(current))
    }

    pub(crate) fn root(&self, point: &Boundary) -> RegistryResult<Option<Address>> {
        if point.0 == 0 || point.0 > self.depth {
            return Err(RegistryError::InvalidState);
        }
        Ok(self.roots[point.0 as usize - 1])
    }
    pub(crate) fn outer_root(&self) -> Option<Address> {
        if self.depth == 0 {
            None
        } else {
            self.roots[0]
        }
    }
    pub(crate) fn reset(&mut self) {
        self.roots.fill(None);
        self.depth = 0;
    }

    fn check(&self, point: &Boundary) -> RegistryResult {
        if self.depth == 0 || point.0 != self.depth {
            return Err(RegistryError::InvalidState);
        }
        Ok(())
    }

    fn pop(&mut self) {
        self.depth -= 1;
        self.roots[self.depth()] = None;
    }
}

const _: () = assert!(core::mem::size_of::<Snapshots>() == 28);
const _: () = assert!(core::mem::size_of::<crate::kernel_cell::KernelCell<Snapshots>>() == 32);

#[cfg(test)]
mod tests {
    use super::*;

    fn address(n: u32) -> Address {
        Address::new(0x1000_0000 + n * 256).unwrap()
    }

    #[test]
    fn six_boundaries_share_one_save_and_seventh_is_rejected_before_work() {
        let mut stack = Snapshots::new();
        let mut points = std::vec::Vec::new();
        for _ in 0..6 {
            points.push(stack.begin(None).unwrap());
        }
        assert!(matches!(stack.begin(None), Err(RegistryError::Capacity)));
        let mut writes = 0;
        stack
            .before_change(|| {
                writes += 1;
                Ok(address(1))
            })
            .unwrap();
        stack
            .before_change(|| panic!("same boundaries already have roots"))
            .unwrap();
        assert_eq!(writes, 1);
        assert_eq!(stack.roots().collect::<std::vec::Vec<_>>(), [address(1); 6]);
        while let Some(point) = points.pop() {
            stack.accept(point).unwrap();
        }
        assert_eq!(stack.depth(), 0);
    }

    #[test]
    fn neutral_scope_does_not_write_or_reload() {
        for current in [None, Some(address(1))] {
            let mut stack = Snapshots::new();
            let point = stack.begin(current).unwrap();
            assert_eq!(
                stack.rollback(point, current, |_| panic!("unchanged")),
                Ok(current)
            );
        }
    }

    #[test]
    fn nested_accept_keeps_outer_rollback_and_only_changed_views_need_snapshots() {
        let mut stack = Snapshots::new();
        let outer = stack.begin(Some(address(1))).unwrap();
        stack
            .before_change(|| panic!("outer already saved"))
            .unwrap();
        let inner = stack.begin(None).unwrap();
        stack.before_change(|| Ok(address(2))).unwrap();
        stack.accept(inner).unwrap();
        assert_eq!(stack.roots().collect::<std::vec::Vec<_>>(), [address(1)]);
        let mut loaded = None;
        assert_eq!(
            stack.rollback(outer, None, |root| {
                loaded = Some(root);
                Ok(())
            }),
            Ok(Some(address(1)))
        );
        assert_eq!(loaded, Some(address(1)));
    }

    #[test]
    fn save_failure_preserves_unresolved_boundaries() {
        let mut stack = Snapshots::new();
        let _point = stack.begin(None).unwrap();
        assert_eq!(
            stack.before_change(|| Err(RegistryError::Persistence)),
            Err(RegistryError::Persistence)
        );
        assert_eq!(stack.depth(), 1);
        assert_eq!(stack.roots().count(), 0);
        stack.before_change(|| Ok(address(2))).unwrap();
        assert_eq!(stack.roots().collect::<std::vec::Vec<_>>(), [address(2)]);
    }

    #[test]
    fn reload_failure_retains_protected_root_and_depth() {
        let mut stack = Snapshots::new();
        let point = stack.begin(Some(address(1))).unwrap();
        assert_eq!(
            stack.rollback(point, None, |_| Err(RegistryError::Persistence)),
            Err(RegistryError::Persistence)
        );
        assert_eq!(stack.depth(), 1);
        assert_eq!(stack.roots().collect::<std::vec::Vec<_>>(), [address(1)]);
    }
}
