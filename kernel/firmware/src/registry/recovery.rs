//! Boot loads only the authenticated compact BOSS. Object bodies are opened on demand.
use super::state::{initialize_persistence_runtime_state, OBJECT_REGISTRY};
use super::storage::persistent_registry_area_bytes;
use super::{
    format as registry_persistence,
    image::{Address, Entry},
    objects::*,
};
use crate::predeployment::root_instance_aid as root_security_domain_instance_aid;
fn top_level_parent_sd_aid() -> rustlet_runtime::Aid {
    rustlet_runtime::Aid::new(&[])
}

// Release the recovery frame before the caller authenticates the active domain.
#[inline(never)]
pub(crate) fn restore_persistent_registry_if_available() -> bool {
    #[cfg(oxide_se_kernel_app_module = "registry-test")]
    let _timing = crate::registry::perf::start(crate::registry::perf::Metric::Recovery);
    let Some(area) = persistent_registry_area_bytes() else {
        return false;
    };
    if !registry_persistence::has_persistence_area_marker(area) {
        return false;
    }
    let page = super::physical::logical_page_size();
    let boss = super::journal::latest(area, page)
        .expect("fatal: corrupt registry journal")
        .expect("fatal: initialized registry has no durable root");
    let root = Address::new(super::references::base() + boss.offset as u32).expect("flash root");
    let mut registry = OBJECT_REGISTRY.borrow_mut();
    super::publication::restore_snapshot(root, &mut registry.image)
        .expect("fatal: invalid compact registry");
    registry.current = Some(root);
    assert!(
        validate_boot_topology(&registry),
        "fatal: invalid registry topology"
    );
    initialize_persistence_runtime_state(
        Some(registry_persistence::PersistentRange::new(
            boss.offset,
            boss.total_len,
        )),
        boss.mutation_counter,
        boss.offset + boss.total_len,
    );
    // Rebuild ownership from the authenticated image and clear structural extents;
    // do not authenticate/decrypt object bodies at boot.
    super::publication::ensure_protection(&registry, area, page, &super::state::USED_PAGES)
        .expect("fatal: invalid recovered page ownership");
    super::header_auth::remember_publication(boss.offset);
    true
}
fn validate_boot_topology(registry: &Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>) -> bool {
    use registry_persistence::PersistentObjectKind::SecurityDomain;
    let entries = registry.image.entries();
    let domains = || {
        entries
            .iter()
            .filter(|e| !e.is_empty() && e.kind().kind() == SecurityDomain)
    };
    let root = root_security_domain_instance_aid();
    if !domains().any(|e| e.object() == root && e.parent() == top_level_parent_sd_aid()) {
        return false;
    }
    for domain in domains() {
        let mut cursor = domain.object();
        let mut remaining = DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY;
        while cursor != root {
            if remaining == 0 {
                return false;
            }
            let Some(entry) = domains().find(|e| e.object() == cursor) else {
                return false;
            };
            cursor = entry.parent();
            remaining -= 1;
        }
    }
    true
}

pub(crate) fn entry_for_view(object: &ObjectView) -> RegistryResult<Entry> {
    #[cfg(test)]
    let address = super::testing::store_object(object.clone());
    #[cfg(not(test))]
    let address = if super::volatile::enabled() {
        super::volatile::store_object(object)?
    } else {
        let raw = if let Some(range) = object.persistent_content().and_then(|c| c.range()) {
            super::references::base()
                .checked_add(range.offset as u32)
                .ok_or(RegistryError::Persistence)?
        } else if let ObjectPayload::FlashData { data } = object.payload {
            super::references::base()
                .checked_add(data.offset() as u32)
                .ok_or(RegistryError::Persistence)?
        } else if let Some(binary) = object.package_binary_code() {
            let addr = binary.as_ptr() as usize;
            let area = super::physical::persistence_area();
            let end = area.start + area.page_count * super::physical::logical_page_size();
            if addr >= area.start && addr < end {
                addr.checked_sub(32).ok_or(RegistryError::Persistence)? as u32
            } else {
                u32::try_from(addr).map_err(|_| RegistryError::Persistence)?
            }
        } else {
            return Err(RegistryError::Persistence);
        };
        Address::new(raw)?
    };
    let entry = registry_persistence::PersistentRegistryEntry::from_registry_object(
        object,
        super::references::reference(address.get()),
    );
    Entry::new(
        object.object_aid,
        object.parent_sd_aid,
        entry.kind_word,
        address,
    )
}

pub(crate) fn open_entry(entry: Entry) -> RegistryResult<ObjectView> {
    #[cfg(test)]
    let volatile = super::testing::object(entry.address());
    #[cfg(not(test))]
    let volatile = if super::volatile::enabled() {
        Some(super::volatile::object(entry)?)
    } else {
        None
    };
    if let Some(mut object) = volatile {
        object.parent_sd_aid = entry.parent();
        object.object_aid = entry.object();
        match &mut object.payload {
            ObjectPayload::Package { package_state, .. } => {
                *package_state =
                    registry_persistence::decode_package_state(entry.kind().state_bits())
                        .map_err(|_| RegistryError::InvalidData)?
            }
            ObjectPayload::Instance { instance_state, .. } => {
                *instance_state =
                    registry_persistence::decode_instance_state(entry.kind().state_bits())
                        .map_err(|_| RegistryError::InvalidData)?
            }
            ObjectPayload::SecurityDomain { object_state, .. } => {
                *object_state =
                    registry_persistence::decode_security_domain_state(entry.kind().state_bits())
                        .map_err(|_| RegistryError::InvalidData)?
            }
            ObjectPayload::Key { key_state, .. } => {
                *key_state = if entry.kind().state_bits() == 0 {
                    KeyObjectState::Active
                } else {
                    KeyObjectState::Locked
                }
            }
            _ => {}
        }
        return Ok(object);
    }
    let persisted = registry_persistence::PersistentRegistryEntry::decode(entry.bytes())
        .map_err(|_| RegistryError::InvalidData)?;
    use registry_persistence::PersistentObjectKind;
    if matches!(
        persisted.kind_word.kind(),
        PersistentObjectKind::SecurityDomain
            | PersistentObjectKind::Instance
            | PersistentObjectKind::Key
    ) {
        return open_encrypted_metadata(
            persistent_registry_area_bytes().ok_or(RegistryError::Persistence)?,
            super::physical::logical_page_size(),
            persisted,
        )
        .ok_or(RegistryError::Persistence);
    }
    open_package_or_data(entry, persisted)
}

#[inline(never)]
fn open_package_or_data(
    entry: Entry,
    persisted: registry_persistence::PersistentRegistryEntry,
) -> RegistryResult<ObjectView> {
    if persisted.kind_word.kind() == registry_persistence::PersistentObjectKind::Package
        && persisted.data_ref.space != registry_persistence::PersistentSpace::RegistryFlash
    {
        let mut found = None;
        crate::embedded_apps::for_each_embedded_registry_seed(|seed| {
            if seed.fae.as_ptr() as usize == entry.address().get() as usize
                && seed.package_aid == entry.object()
            {
                found = Some(ObjectView {
                    parent_sd_aid: entry.parent(),
                    object_aid: entry.object(),
                    object_kind: ManagedObjectKind::Package,
                    payload: ObjectPayload::Package {
                        package_state: registry_persistence::decode_package_state(
                            entry.kind().state_bits(),
                        )
                        .unwrap(),
                        applet_aid: seed.applet_aid,
                        binary_code: seed.fae,
                    },
                });
            }
        });
        return found.ok_or(RegistryError::Persistence);
    }
    let area = persistent_registry_area_bytes().ok_or(RegistryError::Persistence)?;
    let page = super::physical::logical_page_size();
    let block = persistent_payload_block(area, page, persisted.data_ref)
        .ok_or(RegistryError::Persistence)?;
    let payload = match persisted.kind_word.kind() {
        registry_persistence::PersistentObjectKind::Package
            if block.magic == registry_persistence::PACKAGE_BLOCK_MAGIC =>
        {
            ObjectPayload::Package {
                package_state: registry_persistence::decode_package_state(
                    entry.kind().state_bits(),
                )
                .unwrap(),
                applet_aid: entry.object(),
                binary_code: block.payload,
            }
        }
        registry_persistence::PersistentObjectKind::Data
            if block.magic == registry_persistence::ENCRYPTED_DATA_MAGIC =>
        {
            ObjectPayload::FlashData {
                data: super::data_crypto::DataRef::from_structural(area, block.offset, page)
                    .map_err(|_| RegistryError::Persistence)?,
            }
        }
        _ => return Err(RegistryError::Persistence),
    };
    Ok(ObjectView {
        parent_sd_aid: entry.parent(),
        object_aid: entry.object(),
        object_kind: super::state::runtime_object_kind(entry.kind().kind()),
        payload,
    })
}
/// Diagnostic access keeps absolute-address conversion inside the registry.
#[cfg(oxide_se_kernel_app_module = "integrity-test")]
pub(crate) fn persistent_payload_at_address(
    area: &[u8],
    page: usize,
    address: Address,
) -> Option<registry_persistence::ObjectBlockView<'_>> {
    persistent_payload_block(area, page, super::references::reference(address.get()))
}

pub(crate) fn persistent_payload_block(
    area: &[u8],
    page: usize,
    reference: registry_persistence::PersistentRef,
) -> Option<registry_persistence::ObjectBlockView<'_>> {
    if reference.space != registry_persistence::PersistentSpace::RegistryFlash {
        return None;
    }
    registry_persistence::decode_object_block_at(area, reference.offset as usize, page).ok()
}
fn structural_payload_block(
    area: &[u8],
    page: usize,
    reference: registry_persistence::PersistentRef,
) -> Option<registry_persistence::ObjectBlockView<'_>> {
    persistent_payload_block(area, page, reference)
}
#[cfg(test)]
fn restore_encrypted_metadata(
    registry: &mut Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>,
    area: &'static [u8],
    page: usize,
    entry: registry_persistence::PersistentRegistryEntry,
) -> Option<()> {
    registry
        .attach_restored_object(open_encrypted_metadata(area, page, entry)?)
        .ok()
}
#[cfg(test)]
pub(crate) fn validate_security_domain_registry_topology(
    registry: &Registry<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>,
) -> bool {
    let root_aid = root_security_domain_instance_aid();
    let empty_parent = top_level_parent_sd_aid();
    let Some(root) = registry.entries().find(|object| {
        object.object_kind == ManagedObjectKind::SecurityDomain && object.object_aid == root_aid
    }) else {
        return false;
    };
    if root.parent_sd_aid != empty_parent {
        return false;
    }

    for domain in registry
        .entries()
        .filter(|object| object.object_kind == ManagedObjectKind::SecurityDomain)
    {
        if domain.object_aid == root_aid {
            continue;
        }
        if domain.parent_sd_aid == empty_parent {
            return false;
        }
        let Some(parent) = registry.entries().find(|candidate| {
            candidate.object_kind == ManagedObjectKind::SecurityDomain
                && candidate.object_aid == domain.parent_sd_aid
        }) else {
            return false;
        };
        let Some(parent_privileges) = parent.security_domain_privilege_bytes().and_then(|bytes| {
            crate::security_domain::SecurityDomainPrivileges::from_install_bytes(&bytes)
        }) else {
            return false;
        };
        let Some(child_privileges) = domain.security_domain_privilege_bytes().and_then(|bytes| {
            crate::security_domain::SecurityDomainPrivileges::from_install_bytes(&bytes)
        }) else {
            return false;
        };
        if !parent_privileges.contains(child_privileges) {
            return false;
        }

        let mut cursor = parent;
        let mut remaining = DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY;
        while cursor.object_aid != root_aid {
            if remaining == 0 || cursor.parent_sd_aid == empty_parent {
                return false;
            }
            let Some(next) = registry.entries().find(|candidate| {
                candidate.object_kind == ManagedObjectKind::SecurityDomain
                    && candidate.object_aid == cursor.parent_sd_aid
            }) else {
                return false;
            };
            cursor = next;
            remaining -= 1;
        }
    }
    true
}
const SECURITY_DOMAIN_PREFIX_LEN: usize = 25;

pub(crate) fn security_domain_backend(entry: Entry) -> Option<SecurityDomainObjectBackend> {
    #[cfg(not(test))]
    if super::volatile::enabled() {
        return super::volatile::object(entry)
            .ok()?
            .security_domain_backend();
    }
    #[cfg(test)]
    if let Some(object) = super::testing::object(entry.address()) {
        if object.object_kind != ManagedObjectKind::SecurityDomain {
            return None;
        }
        registry_persistence::decode_security_domain_state(entry.kind().state_bits()).ok()?;
        return object.security_domain_backend();
    }
    let persisted = registry_persistence::PersistentRegistryEntry::decode(entry.bytes()).ok()?;
    read_security_domain_backend(
        persistent_registry_area_bytes()?,
        super::physical::logical_page_size(),
        persisted,
    )
}

fn read_security_domain_backend(
    area: &'static [u8],
    page_size: usize,
    entry: registry_persistence::PersistentRegistryEntry,
) -> Option<SecurityDomainObjectBackend> {
    use registry_persistence as f;
    if entry.kind_word.kind() != f::PersistentObjectKind::SecurityDomain {
        return None;
    }
    let mut prefix = [0; SECURITY_DOMAIN_PREFIX_LEN];
    read_encrypted_prefix(
        area,
        page_size,
        entry.data_ref,
        f::ENCRYPTED_STATE_MAGIC,
        &mut prefix,
    )?;
    let (_, backend, _) = decode_security_domain_fields(&prefix, entry.kind_word.state_bits())?;
    Some(backend)
}

fn decode_security_domain_fields(
    prefix: &[u8; SECURITY_DOMAIN_PREFIX_LEN],
    state_bits: u16,
) -> Option<(
    rustlet_runtime::Aid,
    SecurityDomainObjectBackend,
    SecurityDomainObjectState,
)> {
    use registry_persistence as f;
    let package_aid = f::PersistentAid::from_encoded(prefix[..17].try_into().ok()?).ok()?;
    let backend = f::decode_security_domain_backend(prefix[17]).ok()?;
    let state = f::decode_security_domain_state(state_bits).ok()?;
    Some((package_aid.as_aid(), backend, state))
}

#[inline(never)]
fn read_encrypted_prefix(
    area: &'static [u8],
    page_size: usize,
    reference: registry_persistence::PersistentRef,
    magic: u32,
    prefix: &mut [u8],
) -> Option<(super::data_crypto::DataRef, usize)> {
    let block = structural_payload_block(area, page_size, reference)?;
    if block.magic != magic {
        return None;
    }
    let data = super::data_crypto::DataRef::from_structural(area, block.offset, page_size).ok()?;
    data.authenticate().ok()?;
    let prefix_len = prefix.len();
    if data.read_range_unchecked(0, prefix).ok()? != prefix_len {
        return None;
    }
    let len = u32::from_le_bytes(prefix[prefix_len - 4..].try_into().ok()?) as usize;
    let body_start = prefix_len.div_ceil(16) * 16;
    if len > rustlet_runtime::STATE_BUFFER_CAPACITY || body_start.checked_add(len)? != data.len() {
        return None;
    }
    Some((data, len))
}

fn open_encrypted_metadata(
    area: &'static [u8],
    page_size: usize,
    entry: registry_persistence::PersistentRegistryEntry,
) -> Option<ObjectView> {
    use super::{content::Content, format as f, objects::ObjectPayload as P};
    use crate::registry::objects::ObjectView;
    let kind = entry.kind_word.kind();
    let (magic, prefix_len) = match kind {
        f::PersistentObjectKind::SecurityDomain => {
            (f::ENCRYPTED_STATE_MAGIC, SECURITY_DOMAIN_PREFIX_LEN)
        }
        f::PersistentObjectKind::Instance => (f::ENCRYPTED_STATE_MAGIC, 21),
        f::PersistentObjectKind::Key => (f::ENCRYPTED_KEY_MAGIC, 9),
        _ => return None,
    };
    let mut prefix = [0u8; SECURITY_DOMAIN_PREFIX_LEN];
    let (data, len) = read_encrypted_prefix(
        area,
        page_size,
        entry.data_ref,
        magic,
        &mut prefix[..prefix_len],
    )?;
    let body_start = prefix_len.div_ceil(16) * 16;
    let content = Content::Encrypted {
        data,
        start: body_start,
    };
    let payload = match kind {
        f::PersistentObjectKind::SecurityDomain => {
            let (package_aid, backend, object_state) =
                decode_security_domain_fields(&prefix, entry.kind_word.state_bits())?;
            P::SecurityDomain {
                package_aid,
                backend,
                privilege_bytes: prefix[18..21].try_into().ok()?,
                object_state,
                serialized_state: content,
                serialized_state_len: len,
            }
        }
        f::PersistentObjectKind::Instance => P::Instance {
            package_aid: f::PersistentAid::from_encoded(prefix[..17].try_into().ok()?)
                .ok()?
                .as_aid(),
            instance_state: f::decode_instance_state(entry.kind_word.state_bits()).ok()?,
            serialized_state: content,
            serialized_state_len: len,
        },
        f::PersistentObjectKind::Key => {
            // Lifecycle is authoritative in the BOSS; immutable key bytes may predate it.
            f::decode_key_state(prefix[1]).ok()?;
            let key_state = match entry.kind_word.state_bits() {
                0 => KeyObjectState::Active,
                1 => KeyObjectState::Locked,
                _ => return None,
            };
            P::Key {
                key_type: f::decode_key_type(prefix[0]).ok()?,
                key_state,
                key_version: prefix[2],
                key_id: prefix[3],
                key_usage: prefix[4],
                raw_key_bytes: content,
                raw_key_len: len,
            }
        }
        _ => return None,
    };
    Some(ObjectView {
        parent_sd_aid: entry.parent_sd_aid.as_aid(),
        object_aid: entry.object_aid.as_aid(),
        object_kind: super::state::runtime_object_kind(kind),
        payload,
    })
}

#[cfg(test)]
mod encrypted_recovery_tests {
    use super::super::format as f;
    use super::*;
    use crate::registry::objects::{KeyObjectState, KeyObjectType};

    #[test]
    fn backend_lookup_requires_authenticated_and_valid_domain_metadata() {
        const PAGE: usize = 256;
        let mut entry = f::PersistentRegistryEntry {
            parent_sd_aid: f::PersistentAid::EMPTY,
            object_aid: f::PersistentAid::from_aid(&rustlet_runtime::Aid::new(&[2])),
            kind_word: f::PersistentKindWord::new(f::PersistentObjectKind::SecurityDomain, 0),
            data_ref: f::PersistentRef::new(f::PersistentSpace::RegistryFlash, 0, PAGE as u32),
        };
        let object_area = |plaintext: &[u8], magic, tamper| {
            let mut area = alloc::vec![0xff; PAGE * 2];
            f::encode_object_block_at(PAGE, magic, plaintext, PAGE, &mut area[PAGE..]).unwrap();
            if tamper {
                area[PAGE + 32] ^= 1;
            }
            let area: &'static [u8] = alloc::boxed::Box::leak(area.into_boxed_slice());
            area
        };
        let mut plaintext = [0u8; 32];
        for (encoded, backend) in [
            (0, SecurityDomainObjectBackend::NullSecurityDomain),
            (1, SecurityDomainObjectBackend::KernelSecurityDomain),
            (2, SecurityDomainObjectBackend::RustletSecurityDomain),
        ] {
            plaintext[17] = encoded;
            let area = object_area(&plaintext, f::ENCRYPTED_STATE_MAGIC, false);
            assert_eq!(
                read_security_domain_backend(area, PAGE, entry),
                Some(backend)
            );
            assert_eq!(
                open_encrypted_metadata(area, PAGE, entry)
                    .unwrap()
                    .security_domain_backend(),
                Some(backend)
            );
        }
        for (index, wrong) in [(0, 17), (17, 3), (21, 1)] {
            let mut invalid = plaintext;
            invalid[index] = wrong;
            let area = object_area(&invalid, f::ENCRYPTED_STATE_MAGIC, false);
            assert!(read_security_domain_backend(area, PAGE, entry).is_none());
            assert!(open_encrypted_metadata(area, PAGE, entry).is_none());
        }
        for (magic, tamper) in [
            (f::ENCRYPTED_KEY_MAGIC, false),
            (f::ENCRYPTED_STATE_MAGIC, true),
        ] {
            let area = object_area(&plaintext, magic, tamper);
            assert!(read_security_domain_backend(area, PAGE, entry).is_none());
        }
        let area = object_area(&plaintext, f::ENCRYPTED_STATE_MAGIC, false);
        entry.kind_word = f::PersistentKindWord::new(f::PersistentObjectKind::SecurityDomain, 2);
        assert!(read_security_domain_backend(area, PAGE, entry).is_none());
        entry.kind_word = f::PersistentKindWord::new(f::PersistentObjectKind::Instance, 0);
        assert!(read_security_domain_backend(area, PAGE, entry).is_none());
    }

    #[test]
    fn boss_lifecycle_overrides_older_key_body_without_rewriting_it() {
        let owner = rustlet_runtime::Aid::new(&[1]);
        let aid = rustlet_runtime::Aid::new(&[2]);
        let mut source = Registry::<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>::new();
        source
            .upsert_key_object(
                owner,
                aid,
                KeyObjectType::Scp03Static,
                KeyObjectState::Locked,
                1,
                1,
                1,
                &[0x5a; 16],
            )
            .unwrap();
        let object = source.find_key_object(&owner, &aid).unwrap();
        let mut plaintext = [0u8; 64];
        let (_, len) = f::encode_registry_object_payload(&object, &mut plaintext).unwrap();
        let mut area = alloc::vec![0xff; 512];
        plaintext.copy_within(9..len, 16);
        plaintext[9..16].fill(0xff);
        f::encode_object_block_at(
            256,
            f::ENCRYPTED_KEY_MAGIC,
            &plaintext[..len + 7],
            256,
            &mut area[256..],
        )
        .unwrap();
        let area = alloc::boxed::Box::leak(area.into_boxed_slice());
        let mut entry = f::PersistentRegistryEntry::from_registry_object(
            &object,
            f::PersistentRef::new(f::PersistentSpace::RegistryFlash, 0, 256),
        );
        entry.kind_word = f::PersistentKindWord::new(f::PersistentObjectKind::Key, 0);
        let mut restored = Registry::<DEFAULT_KERNEL_OBJECT_REGISTRY_CAPACITY>::new();
        restore_encrypted_metadata(&mut restored, area, 256, entry).unwrap();
        let object = restored.find_key_object(&owner, &aid).unwrap();
        assert_eq!(object.key_state(), Some(KeyObjectState::Active));
        let mut out = [0; 16];
        assert_eq!(object.read_range(0, &mut out), Ok(16));
        assert_eq!(out, [0x5a; 16]);
        assert_eq!(
            object.persistent_content().unwrap().range().unwrap().offset,
            256
        );
    }
}
