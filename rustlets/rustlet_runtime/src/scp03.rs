//! Reusable SCP03 helpers for Rustlet Security Domains.
//!
//! [`S16Session`] owns the protocol mechanics for the common AES-128/S16
//! profile. A Security Domain still decides which commands it claims, which
//! instance owns the keys, and which management policy it exposes.

use crate::{
    Algorithm, ApduStatus, Cipher, CipherMode, ExternalAuthenticate, InitializeUpdate, Mac,
    MacAlgorithm, PlainResponse, RandomAlgorithm, RandomData, RustletCtx, SecurityLevel,
    Uninitialized, WrappedCommand,
};

const CHALLENGE_LEN: usize = 16;
const CRYPTOGRAM_LEN: usize = 16;
const MAC_LEN: usize = 16;
const STATE_INITIALIZED: u8 = 1;
const STATE_AUTHENTICATED: u8 = 2;
const KEY_USAGE_ENC: u8 = 1;
const KEY_USAGE_MAC: u8 = 2;
const KDF_CARD_CRYPTOGRAM: u8 = 0;
const KDF_HOST_CRYPTOGRAM: u8 = 1;
const KDF_S_ENC: u8 = 4;
const KDF_S_MAC: u8 = 6;
const KDF_S_RMAC: u8 = 7;

/// Manifest key identity used by the S16 tutorial engine.
#[derive(Clone, Copy)]
pub struct S16Keyset {
    /// Version selected when INITIALIZE UPDATE uses the version wildcard.
    pub default_version: u8,
    /// Identifier reported in the INITIALIZE UPDATE response.
    pub resolved_id: u8,
}

/// Serializable, RAM-only SCP03 S16 session state.
///
/// The type intentionally keeps key material private. Its methods compute all
/// replay-state changes locally and publish them only after the complete
/// operation succeeds.
#[derive(Default, crate::serde::Serialize, crate::serde::Deserialize)]
#[serde(crate = "crate::serde")]
pub struct S16Session {
    state: u8,
    security_level_bits: u8,
    expected_host_cryptogram: [u8; 16],
    session_enc_key: [u8; 16],
    session_mac_key: [u8; 16],
    session_rmac_key: [u8; 16],
    command_mac_chain: [u8; 16],
    response_mac_chain: [u8; 16],
    #[serde(with = "crate::postcard::fixint::le")]
    command_enc_counter: u32,
    #[serde(with = "crate::postcard::fixint::le")]
    response_enc_counter: u32,
}

impl S16Session {
    /// Serialized upper bound used by the runtime rollback snapshot.
    pub const SERIALIZED_LEN: usize = 122;

    /// Returns whether EXTERNAL AUTHENTICATE completed successfully.
    pub fn is_open(&self) -> bool {
        self.state == STATE_AUTHENTICATED
    }

    /// Returns the negotiated secure-messaging level.
    pub fn security_level(&self) -> SecurityLevel {
        SecurityLevel::from_bits(self.security_level_bits)
    }

    /// Returns the active command MAC length, or zero while closed.
    pub fn mac_len(&self) -> usize {
        if self.is_open() {
            MAC_LEN
        } else {
            0
        }
    }

    /// Clears all derived keys, cryptograms, chains and counters.
    pub fn reset(&mut self) {
        self.state = 0;
        self.security_level_bits = 0;
        self.expected_host_cryptogram.fill(0);
        self.session_enc_key.fill(0);
        self.session_mac_key.fill(0);
        self.session_rmac_key.fill(0);
        self.command_mac_chain.fill(0);
        self.response_mac_chain.fill(0);
        self.command_enc_counter = 0;
        self.response_enc_counter = 0;
    }

    /// Starts SCP03 S16 and returns the 44-byte INITIALIZE UPDATE response.
    pub fn initialize_update(
        &mut self,
        ctx: &mut RustletCtx,
        command: &InitializeUpdate<'_>,
        keyset: S16Keyset,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        self.reset();
        if command.host_challenge.len() != CHALLENGE_LEN {
            return Err(ApduStatus::wrong_length());
        }
        // GlobalPlatform mandates P2=0. The runtime interprets that identifier
        // as a wildcard within the selected Security Domain's key registry.
        if command.key_id != 0 {
            return Err(ApduStatus::incorrect_p1_p2());
        }
        let key_version = if command.key_version == 0 {
            keyset.default_version
        } else {
            command.key_version
        };
        let mut card_challenge = [0u8; CHALLENGE_LEN];
        RandomData::get_instance(RandomAlgorithm::SecureRandom)
            .and_then(|mut random| random.generate_data(&mut card_challenge))
            .map_err(crypto_error_to_status)?;
        let material =
            derive_material(ctx, command.host_challenge, &card_challenge, key_version, 0)?;
        let response_len = 12 + CHALLENGE_LEN + CRYPTOGRAM_LEN;
        if out.len() < response_len {
            return Err(ApduStatus::wrong_length());
        }
        out[..response_len].fill(0);
        out[10] = key_version;
        out[11] = keyset.resolved_id;
        out[12..28].copy_from_slice(&card_challenge);
        out[28..44].copy_from_slice(&material.card_cryptogram);

        self.state = STATE_INITIALIZED;
        self.expected_host_cryptogram = material.host_cryptogram;
        self.session_enc_key = material.session_enc_key;
        self.session_mac_key = material.session_mac_key;
        self.session_rmac_key = material.session_rmac_key;
        Ok(response_len)
    }

    /// Verifies EXTERNAL AUTHENTICATE and publishes the open state atomically.
    pub fn external_authenticate(
        &mut self,
        ctx: &mut RustletCtx,
        command: &ExternalAuthenticate<'_>,
    ) -> Result<SecurityLevel, ApduStatus> {
        if self.state != STATE_INITIALIZED {
            return Err(ApduStatus::conditions_not_satisfied());
        }
        let level = command.security_level;
        if !is_supported_security_level(level) || command.cla != 0x84 || command.p2 != 0 {
            self.reset();
            return Err(ApduStatus::incorrect_p1_p2());
        }
        if command.authentication_data.len() != CRYPTOGRAM_LEN + MAC_LEN {
            self.reset();
            return Err(ApduStatus::wrong_length());
        }
        let (host_cryptogram, received_mac) = command.authentication_data.split_at(CRYPTOGRAM_LEN);
        let header = [command.cla, 0x82, level.bits(), command.p2, 32];
        let initial_chain = compute_external_authenticate_cmac(
            ctx,
            &self.session_mac_key,
            &header,
            host_cryptogram,
        )?;
        if !constant_time_eq(host_cryptogram, &self.expected_host_cryptogram)
            || !constant_time_eq(received_mac, &initial_chain)
        {
            self.reset();
            return Err(ApduStatus::authentication_failed());
        }
        self.security_level_bits = level.bits();
        self.command_mac_chain = initial_chain;
        self.response_mac_chain = initial_chain;
        self.state = STATE_AUTHENTICATED;
        Ok(level)
    }

    /// Verifies and optionally decrypts one protected command.
    pub fn unwrap_command(
        &mut self,
        ctx: &mut RustletCtx,
        command: &WrappedCommand<'_>,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        let level = self.security_level();
        if !self.is_open() || !uses_command_mac(level) || command.mac.len() != MAC_LEN {
            return Err(ApduStatus::conditions_not_satisfied());
        }
        let next_chain = compute_chained_cmac(
            ctx,
            &self.session_mac_key,
            &self.command_mac_chain,
            command.authenticated,
        )?;
        if !constant_time_eq(command.mac, &next_chain) {
            return Err(ApduStatus::conditions_not_satisfied());
        }
        let mut next_counter = self.command_enc_counter;
        let plain_len = if uses_command_encryption(level) && !command.data.is_empty() {
            let iv = next_encryption_iv(ctx, &self.session_enc_key, &mut next_counter, 1)?;
            decrypt_iso9797_m2(ctx, &self.session_enc_key, &iv, command.data, out)?
        } else {
            if command.data.len() > out.len() {
                return Err(ApduStatus::wrong_length());
            }
            out[..command.data.len()].copy_from_slice(command.data);
            command.data.len()
        };
        self.command_mac_chain = next_chain;
        self.command_enc_counter = next_counter;
        Ok(plain_len)
    }

    /// Optionally encrypts and authenticates one protected response.
    pub fn wrap_response(
        &mut self,
        ctx: &mut RustletCtx,
        response: &PlainResponse<'_>,
        out: &mut [u8],
    ) -> Result<usize, ApduStatus> {
        let level = self.security_level();
        if !self.is_open() || !uses_response_mac(level) {
            return Err(ApduStatus::conditions_not_satisfied());
        }
        let data_offset = 4usize;
        if out.len() < data_offset {
            return Err(ApduStatus::wrong_length());
        }
        let mut next_counter = self.response_enc_counter;
        let payload_len = if uses_response_encryption(level) && !response.data.is_empty() {
            let iv = next_encryption_iv(ctx, &self.session_enc_key, &mut next_counter, 2)?;
            encrypt_iso9797_m2(
                ctx,
                &self.session_enc_key,
                &iv,
                response.data,
                &mut out[data_offset..],
            )?
        } else {
            let end = data_offset
                .checked_add(response.data.len())
                .ok_or_else(ApduStatus::wrong_length)?;
            let destination = out
                .get_mut(data_offset..end)
                .ok_or_else(ApduStatus::wrong_length)?;
            destination.copy_from_slice(response.data);
            response.data.len()
        };
        let mac_offset = data_offset
            .checked_add(payload_len)
            .ok_or_else(ApduStatus::wrong_length)?;
        let total_len = mac_offset
            .checked_add(MAC_LEN)
            .ok_or_else(ApduStatus::wrong_length)?;
        if total_len > out.len() {
            return Err(ApduStatus::wrong_length());
        }
        let next_chain = compute_chained_response_cmac(
            ctx,
            &self.session_rmac_key,
            &self.response_mac_chain,
            &out[data_offset..mac_offset],
            response.status,
        )?;
        out[0..2].copy_from_slice(&(payload_len as u16).to_be_bytes());
        out[2] = 0;
        out[3] = MAC_LEN as u8;
        out[mac_offset..total_len].copy_from_slice(&next_chain);
        self.response_mac_chain = next_chain;
        self.response_enc_counter = next_counter;
        Ok(total_len)
    }
}

struct DerivedMaterial {
    card_cryptogram: [u8; 16],
    host_cryptogram: [u8; 16],
    session_enc_key: [u8; 16],
    session_mac_key: [u8; 16],
    session_rmac_key: [u8; 16],
}

fn derive_material(
    ctx: &mut RustletCtx,
    host_challenge: &[u8],
    card_challenge: &[u8; 16],
    key_version: u8,
    key_id: u8,
) -> Result<DerivedMaterial, ApduStatus> {
    let mut enc_key = [0u8; 16];
    let mut mac_key = [0u8; 16];
    let enc_len = ctx
        .load_scp03_key_material(key_version, key_id, KEY_USAGE_ENC, &mut enc_key)
        .map_err(|_| ApduStatus::referenced_data_not_found())?;
    let mac_len = ctx
        .load_scp03_key_material(key_version, key_id, KEY_USAGE_MAC, &mut mac_key)
        .map_err(|_| ApduStatus::referenced_data_not_found())?;
    if enc_len != 16 || mac_len != 16 {
        return Err(ApduStatus::referenced_data_not_found());
    }
    let mut context = [0u8; 32];
    context[..16].copy_from_slice(host_challenge);
    context[16..].copy_from_slice(card_challenge);
    let session_enc_key = kdf::<16>(ctx, KDF_S_ENC, &context, &enc_key)?;
    let session_mac_key = kdf::<16>(ctx, KDF_S_MAC, &context, &mac_key)?;
    let session_rmac_key = kdf::<16>(ctx, KDF_S_RMAC, &context, &mac_key)?;
    Ok(DerivedMaterial {
        card_cryptogram: kdf::<16>(ctx, KDF_CARD_CRYPTOGRAM, &context, &session_mac_key)?,
        host_cryptogram: kdf::<16>(ctx, KDF_HOST_CRYPTOGRAM, &context, &session_mac_key)?,
        session_enc_key,
        session_mac_key,
        session_rmac_key,
    })
}

/// Implements the SCP03 CMAC-based derivation function.
pub fn kdf<const N: usize>(
    ctx: &mut RustletCtx,
    derivation_constant: u8,
    context: &[u8],
    key: &[u8; 16],
) -> Result<[u8; N], ApduStatus> {
    let mut provider = ctx.crypto();
    let mut mac = Mac::<Uninitialized>::new(&mut provider)
        .init(key, MacAlgorithm::AesCmac)
        .map_err(crypto_error_to_status)?;
    mac.update(&[0u8; 11]).map_err(crypto_error_to_status)?;
    mac.update(&[derivation_constant])
        .map_err(crypto_error_to_status)?;
    mac.update(&[0]).map_err(crypto_error_to_status)?;
    mac.update(&((N as u16) * 8).to_be_bytes())
        .map_err(crypto_error_to_status)?;
    mac.update(&[1]).map_err(crypto_error_to_status)?;
    mac.update(context).map_err(crypto_error_to_status)?;
    let tag = mac.compute().map_err(crypto_error_to_status)?;
    let mut out = [0u8; N];
    out.copy_from_slice(&tag.as_ref()[..N]);
    Ok(out)
}

/// Computes a chained command CMAC without mutating the caller's chain.
pub fn compute_chained_cmac(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    chain: &[u8; 16],
    input: &[u8],
) -> Result<[u8; 16], ApduStatus> {
    let mut message = [0u8; 256];
    let len = 16usize
        .checked_add(input.len())
        .filter(|len| *len <= message.len())
        .ok_or_else(ApduStatus::wrong_length)?;
    message[..16].copy_from_slice(chain);
    message[16..len].copy_from_slice(input);
    let mut provider = ctx.crypto();
    let tag = provider
        .compute_mac(key, MacAlgorithm::AesCmac, &message[..len])
        .map_err(crypto_error_to_status)?;
    let mut out = [0u8; 16];
    out.copy_from_slice(tag.as_ref());
    Ok(out)
}

/// Computes R-MAC over protected data followed by SW1-SW2.
pub fn compute_chained_response_cmac(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    chain: &[u8; 16],
    data: &[u8],
    status: ApduStatus,
) -> Result<[u8; 16], ApduStatus> {
    let mut provider = ctx.crypto();
    let mut mac = Mac::<Uninitialized>::new(&mut provider)
        .init(key, MacAlgorithm::AesCmac)
        .map_err(crypto_error_to_status)?;
    mac.update(chain).map_err(crypto_error_to_status)?;
    mac.update(data).map_err(crypto_error_to_status)?;
    mac.update(&[status.sw1, status.sw2])
        .map_err(crypto_error_to_status)?;
    let tag = mac.compute().map_err(crypto_error_to_status)?;
    let mut out = [0u8; 16];
    out.copy_from_slice(tag.as_ref());
    Ok(out)
}

/// Computes the C-MAC protecting EXTERNAL AUTHENTICATE.
pub fn compute_external_authenticate_cmac(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    header: &[u8; 5],
    host_cryptogram: &[u8],
) -> Result<[u8; 16], ApduStatus> {
    let mut provider = ctx.crypto();
    let mut mac = Mac::<Uninitialized>::new(&mut provider)
        .init(key, MacAlgorithm::AesCmac)
        .map_err(crypto_error_to_status)?;
    mac.update(&[0u8; 16]).map_err(crypto_error_to_status)?;
    mac.update(header).map_err(crypto_error_to_status)?;
    mac.update(host_cryptogram)
        .map_err(crypto_error_to_status)?;
    let tag = mac.compute().map_err(crypto_error_to_status)?;
    let mut out = [0u8; 16];
    out.copy_from_slice(tag.as_ref());
    Ok(out)
}

/// Derives an SCP03 CBC IV and advances only the supplied temporary counter.
pub fn next_encryption_iv(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    counter: &mut u32,
    direction: u8,
) -> Result<[u8; 16], ApduStatus> {
    advance_counter(counter)?;
    let mut block = [0u8; 16];
    block[0] = direction;
    block[12..].copy_from_slice(&counter.to_be_bytes());
    let mut provider = ctx.crypto();
    let cipher = Cipher::<Uninitialized>::new(&mut provider)
        .init(
            key,
            &[0u8; 16],
            CipherMode::Encrypt,
            Algorithm::Aes128EcbNoPadding,
        )
        .map_err(crypto_error_to_status)?;
    let mut out = [0u8; 16];
    let len = cipher
        .finish(&block, &mut out)
        .map_err(crypto_error_to_status)?;
    if len != out.len() {
        return Err(ApduStatus::conditions_not_satisfied());
    }
    Ok(out)
}

/// Decrypts and validates one ISO9797-M2 padded payload.
pub fn decrypt_iso9797_m2(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    iv: &[u8; 16],
    input: &[u8],
    out: &mut [u8],
) -> Result<usize, ApduStatus> {
    let mut provider = ctx.crypto();
    let cipher = Cipher::<Uninitialized>::new(&mut provider)
        .init(key, iv, CipherMode::Decrypt, Algorithm::Aes128CbcIso9797M2)
        .map_err(crypto_error_to_status)?;
    cipher.finish(input, out).map_err(crypto_error_to_status)
}

/// Encrypts one ISO9797-M2 padded payload.
pub fn encrypt_iso9797_m2(
    ctx: &mut RustletCtx,
    key: &[u8; 16],
    iv: &[u8; 16],
    input: &[u8],
    out: &mut [u8],
) -> Result<usize, ApduStatus> {
    let mut provider = ctx.crypto();
    let cipher = Cipher::<Uninitialized>::new(&mut provider)
        .init(key, iv, CipherMode::Encrypt, Algorithm::Aes128CbcIso9797M2)
        .map_err(crypto_error_to_status)?;
    cipher.finish(input, out).map_err(crypto_error_to_status)
}

/// Constant-time equality for fixed protocol fields.
pub fn constant_time_eq(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    left.iter()
        .zip(right)
        .fold(0u8, |difference, (left, right)| difference | (left ^ right))
        == 0
}

fn is_supported_security_level(level: SecurityLevel) -> bool {
    matches!(level.bits(), 0x01 | 0x03 | 0x11 | 0x13 | 0x33)
}

fn uses_command_mac(level: SecurityLevel) -> bool {
    level.bits() & SecurityLevel::C_MAC.bits() != 0
}

fn uses_command_encryption(level: SecurityLevel) -> bool {
    level.bits() & SecurityLevel::C_ENC.bits() != 0
}

fn uses_response_mac(level: SecurityLevel) -> bool {
    level.bits() & SecurityLevel::R_MAC.bits() != 0
}

fn uses_response_encryption(level: SecurityLevel) -> bool {
    level.bits() & SecurityLevel::R_ENC.bits() != 0
}

fn crypto_error_to_status(_error: crate::CryptoError) -> ApduStatus {
    ApduStatus::conditions_not_satisfied()
}

fn advance_counter(counter: &mut u32) -> Result<(), ApduStatus> {
    let next = counter
        .checked_add(1)
        .ok_or_else(ApduStatus::conditions_not_satisfied)?;
    *counter = next;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serialized_session_fits_the_runtime_rollback_gate() {
        let mut storage = [0u8; 244];
        let serialized = crate::postcard::to_slice(&S16Session::default(), &mut storage).unwrap();
        assert!(serialized.len() <= S16Session::SERIALIZED_LEN);
        assert!(serialized.len() <= storage.len());
    }

    #[test]
    fn counter_overflow_does_not_advance_state() {
        let mut counter = u32::MAX;
        assert!(advance_counter(&mut counter).is_err());
        assert_eq!(counter, u32::MAX);
    }
}
