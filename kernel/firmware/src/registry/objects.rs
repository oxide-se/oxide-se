#![forbid(unsafe_code)]

//! Polymorphic kernel object registry.
//!
//! The compact image stores identities, lifecycle and flash addresses. ObjectView
//! decodes metadata only for the duration of an authenticated access. These
//! administrative objects make up the kernel-side
//! GlobalPlatform model:
//! - Security Domains
//! - loaded Rustlet packages
//! - installed Rustlet instances
//! - cryptographic key objects
//! - generic management data objects
//!
//! Every entry is attached to one parent Security Domain AID and one object
//! AID, then interpreted according to its [`ManagedObjectKind`]. This gives us
//! one uniform registry while still allowing each object family to expose its
//! own payload:
//! - Security Domains carry their package binding, base privilege bytes and
//!   serialized administrative state.
//! - Packages carry the embedded binary code that can later be instantiated.
//! - Instances carry their package binding and serialized application state.
//! - Keys carry typed raw bytes plus protocol-specific metadata.
//! - Data objects carry Security-Domain-scoped management bytes such as values
//!   stored through `STORE DATA` and returned through `GET DATA`.
//!
//! The registry intentionally models "what exists" rather than "how it was
//! created". Installation, secure-channel policy and APDU routing are handled
//! by higher layers.

use super::content::Content;
use rustlet_runtime::Aid;

/// Capacity budget used by the kernel-wide object registry.
///
/// This must cover the root Security Domain, predeployed packages, dynamically
/// installed instances and administrative key objects during one boot.
pub const DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY: usize = super::image::CAPACITY;

/// Failure of a registry mutation, retained until the command encodes its SW.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// The referenced object does not exist.
    NotFound,
    /// The management authority cannot act on the referenced object.
    AuthorityDenied,
    /// The object's lifecycle or dependencies prevent this operation.
    InvalidState,
    /// The supplied object representation is invalid.
    InvalidData,
    /// The bounded registry, payload storage or flash allocator is full.
    Capacity,
    /// The caller's output buffer cannot hold the requested object.
    OutputTooSmall,
    /// Persistent storage could not be read, erased, programmed or verified.
    Persistence,
}

/// Successful completion of a registry mutation, or its specific cause.
pub type RegistryResult<T = ()> = Result<T, RegistryError>;

impl RegistryError {
    /// Encodes the cause; the GP boundary applies command-specific restrictions.
    pub(crate) const fn status(self) -> crate::apdu_manager::ApduStatus {
        use crate::apdu_manager::ApduStatus;
        match self {
            Self::NotFound => ApduStatus::referenced_data_not_found(),
            Self::AuthorityDenied => ApduStatus::security_status_not_satisfied(),
            Self::InvalidState => ApduStatus::conditions_not_satisfied(),
            Self::InvalidData => ApduStatus::wrong_data(),
            Self::Capacity => ApduStatus::insufficient_memory(),
            Self::OutputTooSmall => ApduStatus::wrong_length(),
            Self::Persistence => ApduStatus::memory_failure(),
        }
    }
}

/// Declares which functional family one registry object belongs to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ManagedObjectKind {
    SecurityDomain,
    Package,
    Instance,
    Key,
    Data,
}

/// Distinguishes the backend used by one registered Security Domain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
// The suffix is intentional: these names are serialized configuration concepts
// and remain unambiguous when displayed without their enum path.
#[allow(clippy::enum_variant_names)]
pub enum SecurityDomainObjectBackend {
    NullSecurityDomain,
    KernelSecurityDomain,
    RustletSecurityDomain,
}

/// Declares the concrete key-object format stored in one registry entry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyObjectType {
    Scp03Static,
    Scp11SdEckaPrivate,
    Scp11CaKlocPublic,
}

/// Lifecycle state for one registry key object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeyObjectState {
    Active,
    Locked,
}

/// Lifecycle state for one loaded package object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PackageObjectState {
    Loaded,
    Locked,
}

/// Lifecycle state for one ordinary Rustlet instance object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum InstanceObjectState {
    Selectable,
    Locked,
}

/// Lifecycle state for one Security Domain instance object.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SecurityDomainObjectState {
    Selectable,
    Locked,
}

#[derive(Clone)]
pub enum ObjectPayload {
    SecurityDomain {
        package_aid: Aid,
        backend: SecurityDomainObjectBackend,
        object_state: SecurityDomainObjectState,
        #[allow(dead_code)]
        privilege_bytes: [u8; 3],
        serialized_state: Content,
        serialized_state_len: usize,
    },
    Package {
        package_state: PackageObjectState,
        applet_aid: Aid,
        binary_code: &'static [u8],
    },
    Instance {
        instance_state: InstanceObjectState,
        package_aid: Aid,
        serialized_state: Content,
        serialized_state_len: usize,
    },
    Key {
        key_type: KeyObjectType,
        key_state: KeyObjectState,
        key_version: u8,
        key_id: u8,
        key_usage: u8,
        raw_key_bytes: Content,
        raw_key_len: usize,
    },
    /// Immutable flash payload, authenticated on first access.
    FlashData { data: super::data_crypto::DataRef },
    /// Owned fallback for host tests and targets without persistent flash.
    #[allow(dead_code)]
    Data { bytes: Content, len: usize },
}

/// One stored registry object.
///
/// The common header is always meaningful:
/// - `parent_sd_aid`
/// - `object_kind`
/// - `object_aid`
///
/// The remaining fields are interpreted according to `object_kind`.
#[derive(Clone)]
pub struct ObjectView {
    pub parent_sd_aid: Aid,
    pub object_kind: ManagedObjectKind,
    pub object_aid: Aid,
    pub payload: ObjectPayload,
}

impl ObjectView {
    pub(super) fn persistent_content(&self) -> Option<&Content> {
        match &self.payload {
            ObjectPayload::SecurityDomain {
                serialized_state, ..
            }
            | ObjectPayload::Instance {
                serialized_state, ..
            } => Some(serialized_state),
            ObjectPayload::Key { raw_key_bytes, .. } => Some(raw_key_bytes),
            _ => None,
        }
    }
    pub fn package_aid(&self) -> Option<Aid> {
        match self.payload {
            ObjectPayload::SecurityDomain { package_aid, .. }
            | ObjectPayload::Instance { package_aid, .. } => Some(package_aid),
            ObjectPayload::Package { .. }
            | ObjectPayload::Key { .. }
            | ObjectPayload::FlashData { .. }
            | ObjectPayload::Data { .. } => None,
        }
    }

    pub fn package_applet_aid(&self) -> Option<Aid> {
        match self.payload {
            ObjectPayload::Package { applet_aid, .. } => Some(applet_aid),
            _ => None,
        }
    }

    pub fn package_binary_code(&self) -> Option<&'static [u8]> {
        match self.payload {
            ObjectPayload::Package { binary_code, .. } => Some(binary_code),
            _ => None,
        }
    }

    pub fn package_state(&self) -> Option<PackageObjectState> {
        match self.payload {
            ObjectPayload::Package { package_state, .. } => Some(package_state),
            _ => None,
        }
    }

    /// Returns whether the package can be used by `INSTALL [for install]`.
    pub fn may_instantiate_package(&self) -> bool {
        self.package_state() == Some(PackageObjectState::Loaded)
    }

    pub fn security_domain_state(&self) -> Option<SecurityDomainObjectState> {
        match self.payload {
            ObjectPayload::SecurityDomain { object_state, .. } => Some(object_state),
            _ => None,
        }
    }

    pub fn instance_state(&self) -> Option<InstanceObjectState> {
        match self.payload {
            ObjectPayload::Instance { instance_state, .. } => Some(instance_state),
            _ => None,
        }
    }

    /// Returns whether this object can become the selected application context.
    pub fn may_select(&self) -> bool {
        match self.payload {
            ObjectPayload::SecurityDomain { object_state, .. } => {
                object_state == SecurityDomainObjectState::Selectable
            }
            ObjectPayload::Instance { instance_state, .. } => {
                instance_state == InstanceObjectState::Selectable
            }
            ObjectPayload::Package { .. }
            | ObjectPayload::Key { .. }
            | ObjectPayload::FlashData { .. }
            | ObjectPayload::Data { .. } => false,
        }
    }

    /// Returns whether this Security Domain can authorize SCP establishment.
    pub fn may_open_secure_channel(&self) -> bool {
        self.security_domain_state() == Some(SecurityDomainObjectState::Selectable)
    }

    pub fn security_domain_backend(&self) -> Option<SecurityDomainObjectBackend> {
        match self.payload {
            ObjectPayload::SecurityDomain { backend, .. } => Some(backend),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn serialized_state(&self) -> Option<&[u8]> {
        match &self.payload {
            ObjectPayload::SecurityDomain {
                serialized_state,
                serialized_state_len,
                ..
            }
            | ObjectPayload::Instance {
                serialized_state,
                serialized_state_len,
                ..
            } => serialized_state
                .clear_bytes()
                .map(|bytes| &bytes[..*serialized_state_len]),
            _ => None,
        }
    }

    pub fn security_domain_privilege_bytes(&self) -> Option<[u8; 3]> {
        match self.payload {
            ObjectPayload::SecurityDomain {
                privilege_bytes, ..
            } => Some(privilege_bytes),
            _ => None,
        }
    }

    #[cfg(test)]
    pub fn key_data(&self) -> Option<(KeyObjectType, u8, u8, u8, &[u8])> {
        match &self.payload {
            ObjectPayload::Key {
                key_type,
                key_state: _,
                key_version,
                key_id,
                key_usage,
                raw_key_bytes,
                raw_key_len,
            } => Some((
                *key_type,
                *key_version,
                *key_id,
                *key_usage,
                raw_key_bytes.clear_bytes()?.get(..*raw_key_len)?,
            )),
            _ => None,
        }
    }

    pub fn key_state(&self) -> Option<KeyObjectState> {
        match self.payload {
            ObjectPayload::Key { key_state, .. } => Some(key_state),
            _ => None,
        }
    }

    pub(crate) fn stage_state_into(&self, context: &mut rustlet_runtime::RustletCtx) -> bool {
        if !matches!(
            self.object_kind,
            ManagedObjectKind::Instance | ManagedObjectKind::SecurityDomain
        ) {
            return false;
        }
        let Ok(len) = self.content_len() else {
            return false;
        };
        context.set_state_len(0);
        let out = context.state_bytes_mut();
        if len > out.len() {
            context.clear_state();
            return false;
        }
        if self.read_range(0, &mut out[..len]) != Ok(len) {
            context.clear_state();
            return false;
        }
        out[len..].fill(0);
        context.set_state_len(len)
    }

    pub fn key_metadata(&self) -> Option<(KeyObjectType, u8, u8, u8, usize)> {
        match &self.payload {
            ObjectPayload::Key {
                key_type,
                key_version,
                key_id,
                key_usage,
                raw_key_len,
                ..
            } => Some((*key_type, *key_version, *key_id, *key_usage, *raw_key_len)),
            _ => None,
        }
    }
    /// Logical content length, excluding the persistent metadata prefix.
    pub fn content_len(&self) -> RegistryResult<usize> {
        match &self.payload {
            ObjectPayload::FlashData { data } => Ok(data.len()),
            ObjectPayload::Data { bytes, .. } => Ok(bytes.len()),
            _ => self
                .persistent_content()
                .map(Content::len)
                .ok_or(RegistryError::InvalidState),
        }
    }
    pub(crate) fn data_matches_generated(
        &self,
        len: usize,
        byte: impl FnMut(usize) -> u8,
    ) -> RegistryResult<bool> {
        match &self.payload {
            ObjectPayload::FlashData { data } => Content::Encrypted {
                data: *data,
                start: 0,
            }
            .matches_generated(len, byte),
            ObjectPayload::Data { bytes, .. } => bytes.matches_generated(len, byte),
            _ => Err(RegistryError::InvalidState),
        }
    }

    /// Extract at most out.len() bytes, directly into caller storage. No cache.
    /// Returns zero at EOF and rejects start beyond EOF without changing out.
    /// The caller must check authority before using this privileged internal API.
    pub fn read_range(&self, start: usize, out: &mut [u8]) -> RegistryResult<usize> {
        match &self.payload {
            ObjectPayload::FlashData { data } => data.read_range(start, out),
            ObjectPayload::Data { bytes, .. } => bytes.read_range(start, out),
            _ => self
                .persistent_content()
                .ok_or(RegistryError::InvalidState)?
                .read_range(start, out),
        }
    }

    #[cfg(test)]
    pub fn data_bytes(&self) -> Option<&[u8]> {
        match &self.payload {
            ObjectPayload::Data { bytes, len } => bytes.clear_bytes().map(|bytes| &bytes[..*len]),
            ObjectPayload::FlashData { .. } => None,
            _ => None,
        }
    }
}

/// One canonical table and a bounded stack of rollback roots. The backing
/// store owns object metadata and old versions.
pub struct Registry<const N: usize> {
    pub(crate) image: super::image::Image<N>,
    pub(crate) snapshots: super::snapshots::Snapshots,
    pub(crate) current: Option<super::image::Address>,
    outer: Option<RegistrySavepoint>,
}
pub(crate) struct RegistrySavepoint(super::snapshots::Boundary);
impl<const N: usize> Default for Registry<N> {
    fn default() -> Self {
        Self::new()
    }
}
impl<const N: usize> Registry<N> {
    pub const fn new() -> Self {
        Self {
            image: super::image::Image::new(),
            snapshots: super::snapshots::Snapshots::new(),
            current: None,
            outer: None,
        }
    }
    pub fn clear(&mut self) {
        self.image.clear();
        self.snapshots.reset();
        self.current = None;
        self.outer = None;
        #[cfg(not(test))]
        if !super::volatile::enabled() {
            super::state::USED_PAGES.set_depth(0);
        }
    }
    #[allow(dead_code)] // Also used by diagnostic firmware profiles.
    pub fn len(&self) -> usize {
        self.image
            .entries()
            .iter()
            .filter(|e| !e.is_empty())
            .count()
    }
    #[allow(dead_code)] // Also used by diagnostic firmware profiles.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub(crate) fn begin_transaction(&mut self) -> RegistryResult {
        if self.outer.is_some() {
            return Err(RegistryError::InvalidState);
        }
        self.outer = Some(RegistrySavepoint(self.snapshots.begin(self.current)?));
        #[cfg(not(test))]
        if !super::volatile::enabled() {
            super::state::USED_PAGES.set_depth(self.snapshots.depth());
        }
        Ok(())
    }
    pub(crate) fn transaction_active(&self) -> bool {
        self.outer.is_some()
    }
    pub(crate) fn transaction_dirty(&self) -> bool {
        self.transaction_active() && self.current != self.snapshots.outer_root()
    }
    pub(crate) fn savepoint(&mut self) -> RegistryResult<RegistrySavepoint> {
        if !self.transaction_active() {
            return Err(RegistryError::InvalidState);
        }
        let point = RegistrySavepoint(self.snapshots.begin(self.current)?);
        #[cfg(not(test))]
        if !super::volatile::enabled() {
            super::state::USED_PAGES.set_depth(self.snapshots.depth());
        }
        Ok(point)
    }
    pub(crate) fn rollback_root(&self, point: &RegistrySavepoint) -> Option<super::image::Address> {
        self.snapshots
            .root(&point.0)
            .expect("active registry scope")
            .filter(|root| Some(*root) != self.current)
    }
    /// The observer and restoration share this single authenticated plaintext.
    /// The returned scope release runs after releasing BOSS scratch.
    pub(crate) fn restore_savepoint(
        &mut self,
        point: RegistrySavepoint,
        bytes: &[u8],
    ) -> RegistryResult<([bool; N], super::retention::ScopeRelease)> {
        let mut invalidated = [false; N];
        for (slot, invalid) in invalidated.iter_mut().enumerate() {
            let before = self.image.slot(slot);
            let after =
                super::image::plaintext_entry(bytes, slot).expect("authenticated rollback root");
            *invalid = match (before, after) {
                (None, None) => false,
                (Some(a), Some(b)) => {
                    a.object() != b.object()
                        || a.parent() != b.parent()
                        || a.kind().kind() != b.kind().kind()
                        || (a != b
                            && matches!(
                                a.kind().kind(),
                                super::format::PersistentObjectKind::Instance
                                    | super::format::PersistentObjectKind::SecurityDomain
                            )
                            && super::recovery::open_entry(a)
                                .expect("authenticated current object")
                                .package_aid()
                                != super::recovery::open_entry(b)
                                    .expect("authenticated rollback object")
                                    .package_aid())
                }
                _ => true,
            };
        }

        let retired = super::retention::ScopeRelease::new(self.snapshots.depth(), false);
        let image = &mut self.image;
        self.current = self
            .snapshots
            .rollback(point.0, self.current, |_| image.restore(bytes))?;
        Ok((invalidated, retired))
    }
    pub(crate) fn finish_savepoint(&mut self, point: RegistrySavepoint, retain: bool) -> [bool; N] {
        let root = self
            .snapshots
            .root(&point.0)
            .expect("active registry scope");
        if retain || self.rollback_root(&point).is_none() {
            let release = super::retention::ScopeRelease::new(self.snapshots.depth(), retain);
            self.snapshots.accept(point.0).expect("LIFO registry scope");
            super::retention::fatal(release.finish(self));
            return [false; N];
        }
        let (invalidated, retired) =
            super::retention::fatal(super::publication::with_snapshot(root.unwrap(), |bytes| {
                self.restore_savepoint(point, bytes)
            }));
        super::retention::fatal(retired.finish(self));
        invalidated
    }
    fn replace_slot(&mut self, slot: usize, entry: super::image::Entry) -> RegistryResult {
        #[cfg(not(test))]
        if !super::volatile::enabled() {
            super::state::USED_PAGES.changed();
        }
        self.current = None;
        self.image.write_slot(slot, entry);
        // Obsolete versions remain owned until the outer collection. No old
        // BOSS needs decoding to retire a single replacement.
        Ok(())
    }
    pub(crate) fn finish_transaction(&mut self, retain: bool) {
        if let Some(point) = self.outer.take() {
            self.finish_savepoint(point, retain);
        }
    }
    pub(crate) fn before_change(&mut self, extra: Option<super::image::Entry>) -> RegistryResult {
        super::storage::require_writable()?;
        if self.snapshots.needs_snapshot() {
            // Invariant: before mutating the registry, every active rollback boundary
            // that depends on the current view has a complete, protected snapshot.
            // Snapshot preparation failure leaves the registry unchanged.
            let root = super::publication::write_snapshot(self, extra)?;
            self.snapshots.before_change(|| Ok(root))?;
            self.current = Some(root);
        }
        Ok(())
    }
    pub fn find_index(&self, parent: &Aid, kind: ManagedObjectKind, aid: &Aid) -> Option<usize> {
        (0..N).find(|&slot| {
            self.image.slot(slot).is_some_and(|e| {
                e.parent() == *parent
                    && e.object() == *aid
                    && super::state::runtime_object_kind(e.kind().kind()) == kind
            })
        })
    }
    pub fn find_any_index(&self, aid: &Aid) -> Option<usize> {
        let rank = |kind| match kind {
            ManagedObjectKind::SecurityDomain => 4,
            ManagedObjectKind::Instance => 3,
            ManagedObjectKind::Package => 2,
            ManagedObjectKind::Key => 1,
            ManagedObjectKind::Data => 0,
        };
        let mut best = None;
        for i in 0..N {
            if let Some(e) = self.image.slot(i).filter(|e| e.object() == *aid) {
                let r = rank(super::state::runtime_object_kind(e.kind().kind()));
                if best.is_none_or(|(_, old)| r > old) {
                    best = Some((i, r));
                }
            }
        }
        best.map(|(i, _)| i)
    }
    /// Identity/topology belongs to the authenticated compact image. Querying it
    /// must never open or decrypt an object's independently authenticated body.
    pub(crate) fn identity(&self, index: usize) -> Option<&super::image::Entry> {
        self.image
            .entries()
            .get(index)
            .filter(|entry| !entry.is_empty())
    }
    pub(crate) fn find_identity(&self, aid: &Aid) -> Option<&super::image::Entry> {
        self.identity(self.find_any_index(aid)?)
    }
    pub(crate) fn identity_kind(&self, index: usize) -> Option<ManagedObjectKind> {
        self.identity(index)
            .map(|entry| super::state::runtime_object_kind(entry.kind().kind()))
    }
    pub(crate) fn find_kind_index(&self, kind: ManagedObjectKind, aid: &Aid) -> Option<usize> {
        (0..N).find(|&index| {
            self.identity(index).is_some_and(|entry| {
                entry.object() == *aid && self.identity_kind(index) == Some(kind)
            })
        })
    }
    pub fn resolve(&self, index: usize) -> Option<ObjectView> {
        super::recovery::open_entry(self.image.slot(index)?).ok()
    }
    pub fn entries(&self) -> impl Iterator<Item = ObjectView> + '_ {
        (0..N).filter_map(|i| self.resolve(i))
    }
    pub fn find_any_object(&self, aid: &Aid) -> Option<ObjectView> {
        self.resolve(self.find_any_index(aid)?)
    }
    fn find(&self, parent: &Aid, kind: ManagedObjectKind, aid: &Aid) -> Option<ObjectView> {
        self.resolve(self.find_index(parent, kind, aid)?)
    }
    #[allow(dead_code)] // Also used by diagnostic firmware profiles.
    pub fn find_package_object(&self, p: &Aid, a: &Aid) -> Option<ObjectView> {
        self.find(p, ManagedObjectKind::Package, a)
    }
    pub fn find_security_domain_object(&self, p: &Aid, a: &Aid) -> Option<ObjectView> {
        self.find(p, ManagedObjectKind::SecurityDomain, a)
    }
    pub fn find_instance_object(&self, p: &Aid, a: &Aid) -> Option<ObjectView> {
        self.find(p, ManagedObjectKind::Instance, a)
    }
    pub fn find_key_object(&self, p: &Aid, a: &Aid) -> Option<ObjectView> {
        self.find(p, ManagedObjectKind::Key, a)
    }
    pub fn find_data_object(&self, p: &Aid, a: &Aid) -> Option<ObjectView> {
        self.find(p, ManagedObjectKind::Data, a)
    }
    fn slot_for(&self, parent: &Aid, kind: ManagedObjectKind, aid: &Aid) -> RegistryResult<usize> {
        if let Some(i) = self.find_index(parent, kind, aid) {
            return Ok(i);
        }
        if !matches!(kind, ManagedObjectKind::Key | ManagedObjectKind::Data)
            && self.image.entries().iter().any(|e| {
                !e.is_empty()
                    && e.object() == *aid
                    && super::state::runtime_object_kind(e.kind().kind()) == kind
            })
        {
            return Err(RegistryError::InvalidState);
        }
        (0..N)
            .find(|&i| self.image.slot(i).is_none())
            .ok_or(RegistryError::Capacity)
    }
    pub(crate) fn attach_restored_object(&mut self, object: ObjectView) -> RegistryResult {
        let slot = self.slot_for(
            &object.parent_sd_aid,
            object.object_kind,
            &object.object_aid,
        )?;
        let entry = super::recovery::entry_for_view(&object)?;
        if self.image.slot(slot) == Some(entry) {
            return Ok(());
        }
        self.before_change(Some(entry))?;
        self.replace_slot(slot, entry)
    }
    pub fn insert_package_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        applet: Aid,
        binary: &'static [u8],
    ) -> RegistryResult {
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::Package,
            payload: ObjectPayload::Package {
                package_state: PackageObjectState::Loaded,
                applet_aid: applet,
                binary_code: binary,
            },
        })
    }
    fn set_state(
        &mut self,
        parent: &Aid,
        kind: ManagedObjectKind,
        aid: &Aid,
        state: u16,
    ) -> RegistryResult {
        let slot = self
            .find_index(parent, kind, aid)
            .ok_or(RegistryError::NotFound)?;
        let old = self.image.slot(slot).unwrap();
        if old.kind().state_bits() == state {
            return Ok(());
        }
        let entry = super::image::Entry::new(
            old.object(),
            old.parent(),
            super::format::PersistentKindWord::new(old.kind().kind(), state),
            old.address(),
        )?;
        self.before_change(None)?;
        self.replace_slot(slot, entry)
    }
    pub fn set_package_state(&mut self, p: &Aid, a: &Aid, s: PackageObjectState) -> RegistryResult {
        self.set_state(
            p,
            ManagedObjectKind::Package,
            a,
            u16::from(s == PackageObjectState::Locked),
        )
    }
    pub fn set_instance_state(
        &mut self,
        p: &Aid,
        a: &Aid,
        s: InstanceObjectState,
    ) -> RegistryResult {
        self.set_state(
            p,
            ManagedObjectKind::Instance,
            a,
            u16::from(s == InstanceObjectState::Locked),
        )
    }
    pub fn set_security_domain_state(
        &mut self,
        p: &Aid,
        a: &Aid,
        s: SecurityDomainObjectState,
    ) -> RegistryResult {
        self.set_state(
            p,
            ManagedObjectKind::SecurityDomain,
            a,
            u16::from(s == SecurityDomainObjectState::Locked),
        )
    }
    pub fn set_key_state(&mut self, p: &Aid, a: &Aid, s: KeyObjectState) -> RegistryResult {
        self.set_state(
            p,
            ManagedObjectKind::Key,
            a,
            u16::from(s == KeyObjectState::Locked),
        )
    }
    pub fn upsert_instance_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        package: Aid,
        bytes: &[u8],
    ) -> RegistryResult {
        if bytes.len() > rustlet_runtime::STATE_BUFFER_CAPACITY {
            return Err(RegistryError::Capacity);
        }
        self.slot_for(&parent, ManagedObjectKind::Instance, &aid)?;
        let old = self.find_instance_object(&parent, &aid);
        if old.as_ref().is_some_and(|o| {
            o.package_aid() == Some(package)
                && o.persistent_content().is_some_and(|c| c.matches(bytes))
        }) {
            return Ok(());
        }
        self.before_change(None)?;
        let mut prefix = [0; 21];
        prefix[..17].copy_from_slice(&super::format::PersistentAid::from_aid(&package).encoded());
        prefix[17..].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        let content = Content::store(self, super::format::ENCRYPTED_STATE_MAGIC, &prefix, bytes)?;
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::Instance,
            payload: ObjectPayload::Instance {
                instance_state: old
                    .and_then(|o| o.instance_state())
                    .unwrap_or(InstanceObjectState::Selectable),
                package_aid: package,
                serialized_state: content,
                serialized_state_len: bytes.len(),
            },
        })
    }
    pub fn upsert_security_domain_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        package: Aid,
        backend: SecurityDomainObjectBackend,
        privileges: [u8; 3],
        bytes: &[u8],
    ) -> RegistryResult {
        if bytes.len() > rustlet_runtime::STATE_BUFFER_CAPACITY {
            return Err(RegistryError::Capacity);
        }
        self.slot_for(&parent, ManagedObjectKind::SecurityDomain, &aid)?;
        let Some(object_state) = self
            .security_domain_state_for_upsert(&parent, &aid, &package, backend, privileges, bytes)
        else {
            return Ok(());
        };
        self.before_change(None)?;
        let mut prefix = [0; 25];
        prefix[..17].copy_from_slice(&super::format::PersistentAid::from_aid(&package).encoded());
        prefix[17] = super::format::encode_security_domain_backend(backend);
        prefix[18..21].copy_from_slice(&privileges);
        prefix[21..].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        let content = Content::store(self, super::format::ENCRYPTED_STATE_MAGIC, &prefix, bytes)?;
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::SecurityDomain,
            payload: ObjectPayload::SecurityDomain {
                object_state,
                package_aid: package,
                backend,
                privilege_bytes: privileges,
                serialized_state: content,
                serialized_state_len: bytes.len(),
            },
        })
    }
    // An unchanged object needs no snapshot. Otherwise only its lifecycle state
    // needs to survive into snapshot creation.
    #[inline(never)]
    fn security_domain_state_for_upsert(
        &self,
        parent: &Aid,
        aid: &Aid,
        package: &Aid,
        backend: SecurityDomainObjectBackend,
        privileges: [u8; 3],
        bytes: &[u8],
    ) -> Option<SecurityDomainObjectState> {
        let old = self.find_security_domain_object(parent, aid);
        if old.as_ref().is_some_and(|o| {
            o.package_aid() == Some(*package)
                && o.security_domain_backend() == Some(backend)
                && o.security_domain_privilege_bytes() == Some(privileges)
                && o.persistent_content().is_some_and(|c| c.matches(bytes))
        }) {
            return None;
        }
        Some(
            old.and_then(|o| o.security_domain_state())
                .unwrap_or(SecurityDomainObjectState::Selectable),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn upsert_key_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        key_type: KeyObjectType,
        key_state: KeyObjectState,
        version: u8,
        id: u8,
        usage: u8,
        bytes: &[u8],
    ) -> RegistryResult {
        if bytes.len() > rustlet_runtime::STATE_BUFFER_CAPACITY {
            return Err(RegistryError::Capacity);
        }
        self.slot_for(&parent, ManagedObjectKind::Key, &aid)?;
        if self.find_key_object(&parent, &aid).is_some_and(|o| {
            o.key_metadata() == Some((key_type, version, id, usage, bytes.len()))
                && o.key_state() == Some(key_state)
                && o.persistent_content().is_some_and(|c| c.matches(bytes))
        }) {
            return Ok(());
        }
        self.before_change(None)?;
        let mut prefix = [0; 9];
        prefix[0] = super::format::encode_key_type(key_type);
        prefix[1] = super::format::encode_key_state(key_state);
        prefix[2] = version;
        prefix[3] = id;
        prefix[4] = usage;
        prefix[5..].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
        let content = Content::store(self, super::format::ENCRYPTED_KEY_MAGIC, &prefix, bytes)?;
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::Key,
            payload: ObjectPayload::Key {
                key_type,
                key_state,
                key_version: version,
                key_id: id,
                key_usage: usage,
                raw_key_bytes: content,
                raw_key_len: bytes.len(),
            },
        })
    }
    pub(crate) fn upsert_flash_data_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        data: super::data_crypto::DataRef,
    ) -> RegistryResult {
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::Data,
            payload: ObjectPayload::FlashData { data },
        })
    }
    pub fn upsert_data_object(&mut self, parent: Aid, aid: Aid, bytes: &[u8]) -> RegistryResult {
        if bytes.len() > rustlet_runtime::STATE_BUFFER_CAPACITY {
            return Err(RegistryError::Capacity);
        }
        self.slot_for(&parent, ManagedObjectKind::Data, &aid)?;
        if self
            .find_data_object(&parent, &aid)
            .is_some_and(|o| match o.payload {
                ObjectPayload::Data {
                    bytes: ref content, ..
                } => content.matches(bytes),
                ObjectPayload::FlashData { data } => {
                    Content::Encrypted { data, start: 0 }.matches(bytes)
                }
                _ => false,
            })
        {
            return Ok(());
        }
        self.before_change(None)?;
        let content = Content::store(self, super::format::ENCRYPTED_DATA_MAGIC, &[], bytes)?;
        if let Content::Encrypted { data, .. } = content {
            return self.upsert_flash_data_object(parent, aid, data);
        }
        self.attach_volatile_data_object(parent, aid, content)
    }

    pub(crate) fn attach_volatile_data_object(
        &mut self,
        parent: Aid,
        aid: Aid,
        content: Content,
    ) -> RegistryResult {
        let len = content.len();
        self.attach_restored_object(ObjectView {
            parent_sd_aid: parent,
            object_aid: aid,
            object_kind: ManagedObjectKind::Data,
            payload: ObjectPayload::Data {
                bytes: content,
                len,
            },
        })
    }

    pub fn delete_object(
        &mut self,
        parent: &Aid,
        kind: ManagedObjectKind,
        aid: &Aid,
    ) -> RegistryResult {
        let slot = self
            .find_index(parent, kind, aid)
            .ok_or(RegistryError::NotFound)?;
        self.before_change(None)?;
        self.replace_slot(slot, super::image::Entry::EMPTY)
    }
    pub fn clone_scp03_keys(&mut self, source: Aid, target: Aid) -> RegistryResult {
        let mut any = false;
        for i in 0..N {
            let Some(mut object) = self.resolve(i) else {
                continue;
            };
            if object.parent_sd_aid != source
                || !matches!(
                    object.payload,
                    ObjectPayload::Key {
                        key_type: KeyObjectType::Scp03Static,
                        ..
                    }
                )
            {
                continue;
            }
            object.parent_sd_aid = target;
            self.attach_restored_object(object)?;
            any = true;
        }
        if any {
            Ok(())
        } else {
            Err(RegistryError::NotFound)
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    fn aid(bytes: &[u8]) -> Aid {
        Aid::new(bytes)
    }

    #[test]
    fn rollback_invalidates_rebound_package_but_not_changed_instance_bytes() {
        let mut registry = Registry::<3>::new();
        let parent = aid(&[1]);
        let object = aid(&[2]);
        let package = aid(&[3]);
        registry
            .upsert_instance_object(parent, object, package, b"old")
            .unwrap();
        registry.begin_transaction().unwrap();
        let point = registry.savepoint().unwrap();
        registry
            .upsert_instance_object(parent, object, package, b"new")
            .unwrap();
        assert!(!registry.finish_savepoint(point, false)[0]);
        let point = registry.savepoint().unwrap();
        registry
            .upsert_instance_object(parent, object, aid(&[4]), b"new")
            .unwrap();
        assert!(registry.finish_savepoint(point, false)[0]);
        assert!(registry.resolve(0).unwrap().package_aid() == Some(package));
        registry.finish_transaction(false);
    }

    #[test]
    fn compact_capacity_and_nested_roots_replace_all_old_versions() {
        let mut registry = Registry::<63>::new();
        let parent = aid(&[1]);
        for id in 0..63 {
            registry
                .upsert_data_object(parent, aid(&[id]), &[id])
                .unwrap();
        }
        assert_eq!(registry.len(), 63);
        assert_eq!(
            registry.upsert_data_object(parent, aid(&[63]), &[63]),
            Err(RegistryError::Capacity)
        );
        registry.begin_transaction().unwrap();
        let mut points = alloc::vec::Vec::new();
        for _ in 0..5 {
            points.push(registry.savepoint().unwrap());
        }
        assert!(matches!(registry.savepoint(), Err(RegistryError::Capacity)));
        registry
            .upsert_data_object(parent, aid(&[3]), b"tentative")
            .unwrap();
        assert_eq!(registry.snapshots.roots().count(), 6);
        let first = registry.snapshots.roots().next().unwrap();
        assert!(registry.snapshots.roots().all(|root| root == first));
        registry.finish_savepoint(points.pop().unwrap(), false);
        assert_eq!(
            registry
                .find_data_object(&parent, &aid(&[3]))
                .unwrap()
                .data_bytes(),
            Some(&[3][..])
        );
        while let Some(point) = points.pop() {
            registry.finish_savepoint(point, true);
        }
        registry.finish_transaction(false);
        assert_eq!(registry.len(), 63);
        assert_eq!(core::mem::size_of::<Registry<63>>(), 2568);
    }

    #[test]
    fn nested_checkpoint_restores_a_provisional_view_without_publishing_it() {
        let mut registry = Registry::<3>::new();
        let parent = aid(&[1]);
        let object = aid(&[2]);
        registry
            .upsert_data_object(parent, object, b"durable")
            .unwrap();
        let durable = super::super::publication::write_snapshot(&mut registry, None).unwrap();
        registry.current = Some(durable);
        registry.begin_transaction().unwrap();
        registry
            .upsert_data_object(parent, object, b"outer")
            .unwrap();
        let inner = registry.savepoint().unwrap();
        registry
            .upsert_data_object(parent, object, b"inner")
            .unwrap();
        registry.finish_savepoint(inner, false);
        assert_eq!(
            registry
                .find_data_object(&parent, &object)
                .unwrap()
                .data_bytes(),
            Some(&b"outer"[..])
        );
        assert!(registry.transaction_dirty());
        // A reset discards the pending view and stack, recovering only the
        // durable journal root, not the newer provisional snapshot.
        registry.clear();
        super::super::publication::restore_snapshot(durable, &mut registry.image).unwrap();
        registry.current = Some(durable);
        assert!(!registry.transaction_active());
        assert_eq!(
            registry
                .find_data_object(&parent, &object)
                .unwrap()
                .data_bytes(),
            Some(&b"durable"[..])
        );
    }

    #[test]
    fn range_api_extracts_logical_key_and_state_bytes_and_rejects_packages() {
        let mut registry = Registry::<5>::new();
        let owner = aid(&[1]);
        registry
            .upsert_key_object(
                owner,
                aid(&[2]),
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                2,
                3,
                b"abcdef",
            )
            .unwrap();
        registry
            .upsert_instance_object(owner, aid(&[3]), aid(&[5]), b"abcdef")
            .unwrap();
        registry
            .upsert_security_domain_object(
                owner,
                aid(&[4]),
                aid(&[5]),
                SecurityDomainObjectBackend::RustletSecurityDomain,
                [0x80, 0, 0],
                b"abcdef",
            )
            .unwrap();
        registry
            .insert_package_object(owner, aid(&[5]), aid(&[6]), b"LOAD")
            .unwrap();
        for object in registry.entries() {
            let mut output = [0xa5; 3];
            if object.object_kind == ManagedObjectKind::Package {
                assert_eq!(object.content_len(), Err(RegistryError::InvalidState));
                assert_eq!(
                    object.read_range(0, &mut output),
                    Err(RegistryError::InvalidState)
                );
            } else {
                assert_eq!(object.content_len(), Ok(6));
                assert_eq!(object.read_range(2, &mut output), Ok(3));
                assert_eq!(&output, b"cde");
                assert_eq!(object.read_range(5, &mut output), Ok(1));
                assert_eq!(&output, b"fde");
                assert_eq!(object.read_range(6, &mut output), Ok(0));
                assert_eq!(
                    object.read_range(7, &mut output),
                    Err(RegistryError::InvalidData)
                );
            }
        }
    }

    #[test]
    fn repeated_neutral_sd_hooks_do_not_grow_the_apdu_journal() {
        let mut registry: Registry<4> = Registry::new();
        let owner = aid(&[1]);
        let package = aid(&[2]);
        let sd = aid(&[3]);
        let app = aid(&[4]);
        registry
            .upsert_security_domain_object(
                owner,
                sd,
                package,
                SecurityDomainObjectBackend::RustletSecurityDomain,
                [0x80, 0, 0],
                &[1],
            )
            .unwrap();
        registry
            .set_security_domain_state(&owner, &sd, SecurityDomainObjectState::Locked)
            .unwrap();
        registry
            .upsert_instance_object(owner, app, package, &[2])
            .unwrap();
        registry.begin_transaction().unwrap();
        for _ in 0..64 {
            let point = registry.savepoint().unwrap();
            registry
                .upsert_security_domain_object(
                    owner,
                    sd,
                    package,
                    SecurityDomainObjectBackend::RustletSecurityDomain,
                    [0x80, 0, 0],
                    &[1],
                )
                .unwrap();
            registry
                .upsert_instance_object(owner, app, package, &[2])
                .unwrap();
            registry.finish_savepoint(point, true);
        }
        assert!(!registry.transaction_dirty());
        registry
            .upsert_security_domain_object(
                owner,
                sd,
                package,
                SecurityDomainObjectBackend::RustletSecurityDomain,
                [0x80, 0, 0],
                &[3],
            )
            .unwrap();
        assert!(registry.transaction_dirty());
        assert_eq!(
            registry
                .find_security_domain_object(&owner, &sd)
                .unwrap()
                .security_domain_state(),
            Some(SecurityDomainObjectState::Locked)
        );
        registry.finish_transaction(false);
        let restored = registry.find_security_domain_object(&owner, &sd).unwrap();
        assert_eq!(
            restored.security_domain_state(),
            Some(SecurityDomainObjectState::Locked)
        );
        assert_eq!(restored.serialized_state(), Some(&[1][..]));
    }

    #[test]
    fn exhausted_capacity_preserves_existing_object_and_allows_replacement() {
        let mut registry = Registry::<1>::new();
        let owner = Aid::from_array([1]);
        let first = Aid::from_array([2]);
        let second = Aid::from_array([3]);
        assert_eq!(registry.upsert_data_object(owner, first, &[7]), Ok(()));
        assert_eq!(
            registry.upsert_data_object(owner, second, &[8]),
            Err(RegistryError::Capacity)
        );
        assert!(registry.find_data_object(&owner, &second).is_none());
        assert_eq!(
            registry
                .find_data_object(&owner, &first)
                .unwrap()
                .data_bytes(),
            Some([7].as_slice())
        );
        assert_eq!(registry.upsert_data_object(owner, first, &[9]), Ok(()));
        assert_eq!(
            registry.delete_object(&owner, ManagedObjectKind::Data, &second),
            Err(RegistryError::NotFound)
        );
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn flash_data_can_be_large_and_replaced_by_inline_data() {
        let data = [0x5a; 32768];
        let mut area = alloc::vec![0; 33024];
        super::super::format::encode_object_block(
            super::super::format::ENCRYPTED_DATA_MAGIC,
            &data,
            256,
            &mut area,
        )
        .unwrap();
        let area = alloc::boxed::Box::leak(area.into_boxed_slice());
        let reference = super::super::data_crypto::DataRef::from_structural(area, 0, 256).unwrap();
        let mut registry = Registry::<4>::new();
        let parent = Aid::from_array([1]);
        let aid = Aid::from_array([2]);
        assert!(registry
            .upsert_flash_data_object(parent, aid, reference)
            .is_ok());
        let object = registry.find_data_object(&parent, &aid).unwrap();
        assert_eq!(object.content_len(), Ok(data.len()));
        let mut out = [0; 31];
        assert_eq!(object.read_range(16379, &mut out), Ok(31));
        assert_eq!(out, [0x5a; 31]);
        assert_eq!(registry.len(), 1);
        assert!(registry.upsert_data_object(parent, aid, &[7, 8]).is_ok());
        assert_eq!(
            registry
                .find_data_object(&parent, &aid)
                .unwrap()
                .data_bytes(),
            Some([7, 8].as_slice())
        );
        assert_eq!(registry.len(), 1);
    }

    #[test]
    fn package_and_instance_can_share_same_aid() {
        let mut registry: Registry<8> = Registry::new();
        let shared = aid(&[0x01]);
        assert!(registry
            .insert_package_object(aid(&[]), shared, shared, &[0xCA, 0xFE])
            .is_ok());
        assert!(registry
            .upsert_instance_object(aid(&[]), shared, shared, &[0xAA])
            .is_ok());
        let resolved = registry.find_any_object(&shared).expect("shared object");
        assert_eq!(resolved.object_kind, ManagedObjectKind::Instance);
    }

    #[test]
    fn package_aids_are_globally_unique() {
        let mut registry: Registry<8> = Registry::new();
        let package = aid(&[0x01]);
        assert!(registry
            .insert_package_object(aid(&[]), package, package, &[0x01])
            .is_ok());
        assert!(registry
            .insert_package_object(aid(&[0x02]), package, package, &[0x02])
            .is_err());
    }

    #[test]
    fn keys_are_parent_qualified() {
        let mut registry: Registry<8> = Registry::new();
        let key = aid(&[0x4B]);
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xAA]
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                aid(&[0x02]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xBB]
            )
            .is_ok());
        let a = registry
            .find_key_object(&aid(&[0x01]), &key)
            .expect("key a");
        let b = registry
            .find_key_object(&aid(&[0x02]), &key)
            .expect("key b");
        assert_eq!(a.key_state(), Some(KeyObjectState::Active));
        assert_eq!(b.key_state(), Some(KeyObjectState::Active));
        assert_eq!(a.key_data().expect("key a data").4[0], 0xAA);
        assert_eq!(b.key_data().expect("key b data").4[0], 0xBB);
    }

    #[test]
    fn key_upsert_can_rotate_state_and_material() {
        let mut registry: Registry<4> = Registry::new();
        let key = aid(&[0x4B]);
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xAA]
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Locked,
                1,
                3,
                1,
                &[0xBB]
            )
            .is_ok());
        let stored = registry
            .find_key_object(&aid(&[0x01]), &key)
            .expect("rotated key");
        assert_eq!(stored.key_state(), Some(KeyObjectState::Locked));
        assert_eq!(stored.key_data().expect("key data").4, &[0xBB]);
    }

    #[test]
    fn default_lifecycle_states_allow_their_normal_operation_families() {
        let mut registry: Registry<8> = Registry::new();
        let parent = aid(&[0x10]);
        let package = aid(&[0x20]);
        let instance = aid(&[0x30]);
        let domain = aid(&[0x40]);
        let key = aid(&[0x4B]);

        assert!(registry
            .insert_package_object(parent, package, package, &[0xCA, 0xFE])
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, instance, package, &[0xAA])
            .is_ok());
        assert!(registry
            .upsert_security_domain_object(
                parent,
                domain,
                package,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF, 0xFF, 0xFF],
                &[0x01],
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                parent,
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xBB],
            )
            .is_ok());

        assert!(registry
            .find_package_object(&parent, &package)
            .expect("package")
            .may_instantiate_package());
        assert!(registry
            .find_instance_object(&parent, &instance)
            .expect("instance")
            .may_select());
        let domain_object = registry
            .find_security_domain_object(&parent, &domain)
            .expect("security domain");
        assert!(domain_object.may_select());
        assert!(domain_object.may_open_secure_channel());
        assert_eq!(
            registry
                .find_key_object(&parent, &key)
                .expect("key")
                .key_state(),
            Some(KeyObjectState::Active)
        );
    }

    #[test]
    fn locked_lifecycle_states_block_their_normal_operation_families() {
        let mut registry: Registry<8> = Registry::new();
        let parent = aid(&[0x10]);
        let package = aid(&[0x20]);
        let instance = aid(&[0x30]);
        let domain = aid(&[0x40]);
        let key = aid(&[0x4B]);

        assert!(registry
            .insert_package_object(parent, package, package, &[0xCA, 0xFE])
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, instance, package, &[0xAA])
            .is_ok());
        assert!(registry
            .upsert_security_domain_object(
                parent,
                domain,
                package,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF, 0xFF, 0xFF],
                &[0x01],
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                parent,
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xBB],
            )
            .is_ok());

        assert!(registry
            .set_package_state(&parent, &package, PackageObjectState::Locked)
            .is_ok());
        assert!(registry
            .set_instance_state(&parent, &instance, InstanceObjectState::Locked)
            .is_ok());
        assert!(registry
            .set_security_domain_state(&parent, &domain, SecurityDomainObjectState::Locked,)
            .is_ok());
        assert!(registry
            .set_key_state(&parent, &key, KeyObjectState::Locked)
            .is_ok());

        assert!(!registry
            .find_package_object(&parent, &package)
            .expect("package")
            .may_instantiate_package());
        assert!(!registry
            .find_instance_object(&parent, &instance)
            .expect("instance")
            .may_select());
        let domain_object = registry
            .find_security_domain_object(&parent, &domain)
            .expect("security domain");
        assert!(!domain_object.may_select());
        assert!(!domain_object.may_open_secure_channel());
        assert_eq!(
            registry
                .find_key_object(&parent, &key)
                .expect("key")
                .key_state(),
            Some(KeyObjectState::Locked)
        );
    }

    #[test]
    fn clone_scp03_keys_copies_only_key_objects() {
        let mut registry: Registry<8> = Registry::new();
        let source = aid(&[0x10]);
        let target = aid(&[0x20]);
        let key = aid(&[0x4B, 0x01]);
        assert!(registry
            .upsert_key_object(
                source,
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &[0xCC]
            )
            .is_ok());
        assert!(registry
            .upsert_instance_object(source, aid(&[0x33]), aid(&[0x44]), &[0xDD])
            .is_ok());
        assert!(registry.clone_scp03_keys(source, target).is_ok());
        assert!(registry.find_key_object(&target, &key).is_some());
        assert!(registry
            .find_instance_object(&target, &aid(&[0x33]))
            .is_none());
    }

    #[test]
    fn upserting_instance_updates_existing_state() {
        let mut registry: Registry<8> = Registry::new();
        let parent = aid(&[0x10]);
        let instance = aid(&[0x20]);
        let package = aid(&[0x30]);
        assert!(registry
            .upsert_instance_object(parent, instance, package, &[0xAA])
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, instance, package, &[0xBB, 0xCC])
            .is_ok());
        let stored = registry
            .find_instance_object(&parent, &instance)
            .expect("updated instance");
        assert_eq!(
            stored.serialized_state().expect("instance state"),
            &[0xBB, 0xCC]
        );
    }

    #[test]
    fn upserting_security_domain_preserves_backend_and_privileges() {
        let mut registry: Registry<8> = Registry::new();
        let parent = aid(&[0x01]);
        let instance = aid(&[0x02]);
        let package = aid(&[0x03]);
        assert!(registry
            .upsert_security_domain_object(
                parent,
                instance,
                package,
                SecurityDomainObjectBackend::KernelSecurityDomain,
                [0xFF, 0xEE, 0xDD],
                &[0x10, 0x20, 0x30],
            )
            .is_ok());
        let stored = registry
            .find_security_domain_object(&parent, &instance)
            .expect("security domain");
        assert_eq!(
            stored.security_domain_backend(),
            Some(SecurityDomainObjectBackend::KernelSecurityDomain)
        );
        let ObjectPayload::SecurityDomain {
            privilege_bytes, ..
        } = stored.payload
        else {
            panic!("expected security domain payload");
        };
        assert_eq!(privilege_bytes, [0xFF, 0xEE, 0xDD]);
        assert_eq!(
            stored.serialized_state().expect("sd state"),
            &[0x10, 0x20, 0x30]
        );
    }

    #[test]
    fn security_domain_and_instance_can_share_same_aid_with_sd_priority() {
        let mut registry: Registry<8> = Registry::new();
        let parent = aid(&[0x01]);
        let shared = aid(&[0x02]);
        assert!(registry
            .upsert_security_domain_object(
                parent,
                shared,
                aid(&[0x03]),
                SecurityDomainObjectBackend::NullSecurityDomain,
                [0, 0, 0],
                &[0xAA],
            )
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, shared, aid(&[0x04]), &[0xBB])
            .is_ok());
        let resolved = registry
            .find_any_object(&shared)
            .expect("resolved shared aid");
        assert_eq!(resolved.object_kind, ManagedObjectKind::SecurityDomain);
    }

    #[test]
    fn find_any_object_prefers_security_domain_over_instance_and_package() {
        let mut registry: Registry<8> = Registry::new();
        let shared = aid(&[0x42]);
        let parent = aid(&[0x01]);
        assert!(registry
            .insert_package_object(parent, shared, shared, &[0x01])
            .is_ok());
        assert!(registry
            .upsert_instance_object(parent, shared, aid(&[0x02]), &[0x02])
            .is_ok());
        let before_sd = registry.find_any_object(&shared).expect("instance chosen");
        assert_eq!(before_sd.object_kind, ManagedObjectKind::Instance);
        assert!(registry
            .upsert_security_domain_object(
                parent,
                shared,
                aid(&[0x03]),
                SecurityDomainObjectBackend::RustletSecurityDomain,
                [1, 2, 3],
                &[0x03],
            )
            .is_ok());
        let resolved = registry.find_any_object(&shared).expect("sd chosen");
        assert_eq!(resolved.object_kind, ManagedObjectKind::SecurityDomain);
    }

    #[test]
    fn oversized_instance_state_is_rejected() {
        let mut registry: Registry<4> = Registry::new();
        let too_large = [0xAA; rustlet_runtime::STATE_BUFFER_CAPACITY + 1];
        assert!(registry
            .upsert_instance_object(aid(&[0x01]), aid(&[0x02]), aid(&[0x03]), &too_large,)
            .is_err());
    }

    #[test]
    fn oversized_key_payload_is_rejected() {
        let mut registry: Registry<4> = Registry::new();
        let too_large = [0x55; rustlet_runtime::STATE_BUFFER_CAPACITY + 1];
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                aid(&[0x4B]),
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                3,
                1,
                &too_large,
            )
            .is_err());
    }

    #[test]
    fn data_objects_are_parent_qualified() {
        let mut registry: Registry<8> = Registry::new();
        let object_aid = aid(&[0x44, 0x41, 0x54, 0x41, 0xDF, 0x01]);
        assert!(registry
            .upsert_data_object(aid(&[0x01]), object_aid, b"one")
            .is_ok());
        assert!(registry
            .upsert_data_object(aid(&[0x02]), object_aid, b"two")
            .is_ok());
        let first = registry
            .find_data_object(&aid(&[0x01]), &object_aid)
            .expect("first data object");
        let second = registry
            .find_data_object(&aid(&[0x02]), &object_aid)
            .expect("second data object");
        assert_eq!(first.data_bytes(), Some(b"one".as_slice()));
        assert_eq!(second.data_bytes(), Some(b"two".as_slice()));
    }

    #[test]
    fn data_objects_do_not_shadow_selectable_objects() {
        let mut registry: Registry<8> = Registry::new();
        let shared = aid(&[0x44, 0x41, 0x54, 0x41, 0xDF, 0x01]);
        assert!(registry
            .upsert_data_object(aid(&[0x01]), shared, b"data")
            .is_ok());
        assert!(registry
            .insert_package_object(aid(&[0x01]), shared, shared, &[0xCA, 0xFE])
            .is_ok());
        let resolved = registry
            .find_any_object(&shared)
            .expect("selectable object wins");
        assert_eq!(resolved.object_kind, ManagedObjectKind::Package);
    }

    #[test]
    fn delete_object_is_parent_qualified_for_keys() {
        let mut registry: Registry<8> = Registry::new();
        let key = aid(&[0x4B, 0x45, 0x59, 0x01, 0x01, 0x01]);
        assert!(registry
            .upsert_key_object(
                aid(&[0x01]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                1,
                1,
                &[0xAA]
            )
            .is_ok());
        assert!(registry
            .upsert_key_object(
                aid(&[0x02]),
                key,
                KeyObjectType::Scp03Static,
                KeyObjectState::Active,
                1,
                1,
                1,
                &[0xBB]
            )
            .is_ok());

        assert!(registry
            .delete_object(&aid(&[0x01]), ManagedObjectKind::Key, &key)
            .is_ok());
        assert!(registry.find_key_object(&aid(&[0x01]), &key).is_none());
        let remaining = registry
            .find_key_object(&aid(&[0x02]), &key)
            .expect("second parent key remains");
        assert_eq!(remaining.key_data().expect("key data").4, &[0xBB]);
    }

    #[test]
    fn delete_object_preserves_other_slots_and_reuses_tombstone() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x01]), aid(&[0x01]), &[0x01])
            .is_ok());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x02]), aid(&[0x02]), &[0x02])
            .is_ok());
        assert_eq!(registry.len(), 2);
        let first = registry
            .find_index(&aid(&[]), ManagedObjectKind::Package, &aid(&[0x01]))
            .expect("first index");
        let second = registry
            .find_index(&aid(&[]), ManagedObjectKind::Package, &aid(&[0x02]))
            .expect("second index");

        assert!(registry
            .delete_object(&aid(&[]), ManagedObjectKind::Package, &aid(&[0x01]))
            .is_ok());
        assert_eq!(registry.len(), 1);
        assert!(registry.resolve(first).is_none());
        assert!(registry.resolve(second).map(|object| object.object_aid) == Some(aid(&[0x02])));
        assert!(registry.find_any_object(&aid(&[0x01])).is_none());
        assert!(registry.find_any_object(&aid(&[0x02])).is_some());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x03]), aid(&[0x03]), &[0x03])
            .is_ok());
        assert!(registry.find_any_object(&aid(&[0x03])).is_some());
        let replacement = registry
            .find_index(&aid(&[]), ManagedObjectKind::Package, &aid(&[0x03]))
            .expect("replacement index");
        assert_eq!(replacement, first);
    }

    #[test]
    fn capacity_limit_is_enforced() {
        let mut registry: Registry<2> = Registry::new();
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x01]), aid(&[0x01]), &[0x01])
            .is_ok());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x02]), aid(&[0x02]), &[0x02])
            .is_ok());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x03]), aid(&[0x03]), &[0x03])
            .is_err());
    }

    #[test]
    fn clear_resets_registry() {
        let mut registry: Registry<4> = Registry::new();
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x01]), aid(&[0x01]), &[0x01])
            .is_ok());
        registry.clear();
        assert!(registry.find_any_object(&aid(&[0x01])).is_none());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x02]), aid(&[0x02]), &[0x02])
            .is_ok());
    }

    #[test]
    fn entries_iterates_live_objects_in_stable_slot_order() {
        let mut registry: Registry<4> = Registry::new();
        assert!(registry.is_empty());
        assert!(registry
            .insert_package_object(aid(&[]), aid(&[0x01]), aid(&[0x01]), &[0x01])
            .is_ok());
        assert!(registry
            .upsert_instance_object(aid(&[]), aid(&[0x02]), aid(&[0x01]), &[0xAA])
            .is_ok());
        assert_eq!(registry.len(), 2);
        let mut entries = registry.entries();
        assert!(entries.next().map(|entry| entry.object_aid) == Some(aid(&[0x01])));
        assert!(entries.next().map(|entry| entry.object_aid) == Some(aid(&[0x02])));
        assert!(entries.next().is_none());
    }

    #[test]
    fn default_kernel_capacity_covers_rustlet_test_all_footprint() {
        let mut registry: Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY> = Registry::new();
        let root = aid(&[]);

        let package_aids = [
            aid(&[0x10]),
            aid(&[0x11]),
            aid(&[0x12]),
            aid(&[0x13]),
            aid(&[0x14]),
            aid(&[0x15]),
            aid(&[0x16]),
            aid(&[0x17]),
            aid(&[0x18]),
            aid(&[0x19]),
            aid(&[0x1A]),
        ];
        for package_aid in package_aids {
            assert!(registry
                .insert_package_object(root, package_aid, package_aid, &[0xAA])
                .is_ok());
        }

        assert!(registry
            .upsert_security_domain_object(
                root,
                aid(&[0x01]),
                aid(&[0x01]),
                SecurityDomainObjectBackend::NullSecurityDomain,
                [0xFF, 0xFF, 0xFF],
                &[0x03, 0xFF, 0xFF, 0xFF],
            )
            .is_ok());

        let instances = [
            (aid(&[0x10]), aid(&[0x10])),
            (aid(&[0x11]), aid(&[0x11])),
            (aid(&[0x12]), aid(&[0x12])),
            (aid(&[0x13]), aid(&[0x13])),
            (aid(&[0x14]), aid(&[0x14])),
            (aid(&[0x14]), aid(&[0x1B])),
            (aid(&[0x15]), aid(&[0x15])),
            (aid(&[0x15]), aid(&[0x1C])),
            (aid(&[0x16]), aid(&[0x16])),
            (aid(&[0x17]), aid(&[0x17])),
            (aid(&[0x18]), aid(&[0x18])),
            (aid(&[0x19]), aid(&[0x19])),
            (aid(&[0x1A]), aid(&[0x1A])),
        ];
        for (package_aid, instance_aid) in instances {
            assert!(registry
                .upsert_instance_object(root, instance_aid, package_aid, &[0x42])
                .is_ok());
        }
    }
}

#[cfg(test)]
mod flash_reference_tests {
    use super::*;
    use rustlet_runtime::Aid;

    #[test]
    fn flash_content_survives_rollback_as_a_reference() {
        static FIRST: [u8; 3] = [1, 2, 3];
        static SECOND: [u8; 3] = [4, 5, 6];
        let owner = Aid::new(&[1]);
        let aid = Aid::new(&[2]);
        let mut registry = Registry::<4>::new();
        registry
            .upsert_instance_object(owner, aid, aid, &FIRST)
            .unwrap();
        let slot = registry
            .find_index(&owner, ManagedObjectKind::Instance, &aid)
            .unwrap();
        let mut object = registry.resolve(slot).unwrap();
        if let ObjectPayload::Instance {
            serialized_state, ..
        } = &mut object.payload
        {
            *serialized_state = Content::Flash {
                bytes: &FIRST,
                offset: 256,
                total: 256,
            };
        }
        registry.attach_restored_object(object).unwrap();
        registry.begin_transaction().unwrap();
        registry
            .upsert_instance_object(owner, aid, aid, &SECOND)
            .unwrap();
        assert_eq!(registry.snapshots.roots().count(), 1);
        registry.finish_transaction(false);
        let restored = registry.find_instance_object(&owner, &aid).unwrap();
        assert_eq!(
            restored.serialized_state().unwrap().as_ptr(),
            FIRST.as_ptr()
        );
    }

    #[test]
    fn entries_do_not_reserve_body_capacity() {
        assert!(core::mem::size_of::<ObjectView>() < rustlet_runtime::STATE_BUFFER_CAPACITY);
        let content = Content::volatile(&[1, 2, 3]);
        let snapshot = content.clone();
        assert_eq!(
            content.clear_bytes().unwrap().as_ptr(),
            snapshot.clear_bytes().unwrap().as_ptr()
        );
    }
}
