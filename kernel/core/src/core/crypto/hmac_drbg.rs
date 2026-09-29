#![forbid(unsafe_code)]
//! Internal HMAC-DRBG/SHA-256 mechanism; entropy policy belongs to its caller.

use super::{CryptoError, CryptoResult};
use crate::core::secure_zero;
use hmac::{digest::FixedOutput, Hmac, Mac};
use sha2::Sha256;

// Source: NIST SP 800-90A Rev. 1, sections 10.1.2.2--10.1.2.5.
// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
// Implement the standard Update, Instantiate, Reseed and Generate operations.
// This internal subset has no personalization or additional input. The caller
// supplies entropy and a nonce, and must enforce their entropy requirements.
// No Clone/Debug/serialization: RNG state must not enter Rustlet persistence.
pub(crate) struct HmacDrbg {
    key: [u8; 32],
    value: [u8; 32],
    reseed_counter: u64,
}

impl HmacDrbg {
    pub(crate) const fn new() -> Self {
        Self {
            key: [0; 32],
            value: [0; 32],
            reseed_counter: 0,
        }
    }

    pub(crate) fn clear(&mut self) {
        secure_zero(&mut self.key);
        secure_zero(&mut self.value);
        self.reseed_counter = 0;
    }

    fn update(&mut self, data: &[&[u8]]) {
        let nonempty = data.iter().any(|part| !part.is_empty());
        for separator in 0..=u8::from(nonempty) {
            let mut mac = Hmac::<Sha256>::new_from_slice(&self.key).expect("32-byte HMAC key");
            mac.update(&self.value);
            mac.update(&[separator]);
            for part in data {
                mac.update(part);
            }
            mac.finalize_into((&mut self.key).into());
            self.advance();
        }
    }

    fn advance(&mut self) {
        let mut mac = Hmac::<Sha256>::new_from_slice(&self.key).expect("32-byte HMAC key");
        mac.update(&self.value);
        mac.finalize_into((&mut self.value).into());
    }

    pub(crate) fn instantiate(&mut self, entropy: &[u8], nonce: &[u8]) -> CryptoResult<()> {
        self.clear();
        if entropy.len() < 32 || nonce.len() < 16 {
            return Err(CryptoError::EntropyUnavailable);
        }
        self.value.fill(1);
        self.update(&[entropy, nonce]);
        self.reseed_counter = 1;
        Ok(())
    }

    pub(crate) fn reseed(&mut self, entropy: &[u8]) -> CryptoResult<()> {
        if self.reseed_counter == 0 || entropy.len() < 32 {
            return Err(CryptoError::EntropyUnavailable);
        }
        self.update(&[entropy]);
        self.reseed_counter = 1;
        Ok(())
    }

    pub(crate) fn generate(&mut self, out: &mut [u8]) -> CryptoResult<()> {
        // SP 800-90A Table 2: at most 2^19 bits per request, 2^48 requests
        // between reseeds. The Pico2 wrapper uses much smaller limits.
        if self.reseed_counter == 0 || self.reseed_counter > (1u64 << 48) {
            secure_zero(out);
            return Err(CryptoError::EntropyUnavailable);
        }
        if out.len() > 65536 {
            secure_zero(out);
            return Err(CryptoError::InvalidOutputLength);
        }
        for chunk in out.chunks_mut(32) {
            self.advance();
            chunk.copy_from_slice(&self.value[..chunk.len()]);
        }
        // Never retain the last output as the next generation's exposed state.
        self.update(&[]);
        self.reseed_counter += 1;
        Ok(())
    }
}

impl Drop for HmacDrbg {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(s: &str) -> std::vec::Vec<u8> {
        s.as_bytes()
            .chunks_exact(2)
            .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
            .collect()
    }

    // Source: NIST CAVP drbgtestvectors.zip, HMAC_DRBG.rsp, SHA-256,
    // entropy=256 bits, nonce=128 bits, no personalization/additional input.
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip
    // Test all 15 vectors for each reseed mode, including both Generate calls.
    #[test]
    fn nist_cavp_vectors() {
        for (mode, vectors) in [
            (0, include_str!("hmac_drbg_tests/no_reseed.rsp")),
            (1, include_str!("hmac_drbg_tests/pr_false.rsp")),
            (2, include_str!("hmac_drbg_tests/pr_true.rsp")),
        ] {
            assert_eq!(vectors.matches("COUNT = ").count(), 15);
            for case in vectors.split("COUNT = ").skip(1) {
                let fields: std::vec::Vec<_> =
                    case.lines().filter_map(|l| l.split_once(" = ")).collect();
                let values = |name| -> std::vec::Vec<std::vec::Vec<u8>> {
                    fields
                        .iter()
                        .filter(|(k, _)| *k == name)
                        .map(|(_, v)| hex(v))
                        .collect()
                };
                let mut drbg = HmacDrbg::new();
                drbg.instantiate(&values("EntropyInput")[0], &values("Nonce")[0])
                    .unwrap();
                if mode == 1 {
                    drbg.reseed(&values("EntropyInputReseed")[0]).unwrap();
                }
                let expected = &values("ReturnedBits")[0];
                let mut out = std::vec![0; expected.len()];
                for i in 0..2 {
                    if mode == 2 {
                        drbg.reseed(&values("EntropyInputPR")[i]).unwrap();
                    }
                    drbg.generate(&mut out).unwrap();
                }
                assert_eq!(
                    &out,
                    expected,
                    "mode={mode}, case={}",
                    case.lines().next().unwrap()
                );
            }
        }
    }

    #[test]
    fn refuses_unseeded_or_expired_state_and_clears_output() {
        let mut rng = HmacDrbg::new();
        let mut out = [0xff; 7];
        assert_eq!(rng.generate(&mut out), Err(CryptoError::EntropyUnavailable));
        assert_eq!(out, [0; 7]);
        rng.instantiate(&[0x31; 32], &[0x72; 16]).unwrap();
        rng.reseed_counter = (1 << 48) + 1;
        assert_eq!(rng.generate(&mut out), Err(CryptoError::EntropyUnavailable));
        rng.reseed(&[0x42; 32]).unwrap();
        rng.generate(&mut out).unwrap();
        rng.clear();
        assert_eq!(rng.key, [0; 32]);
        assert_eq!(rng.value, [0; 32]);
        assert_eq!(rng.reseed_counter, 0);
    }

    #[test]
    fn request_limit_and_partial_blocks() {
        let mut rng = HmacDrbg::new();
        assert!(rng.instantiate(&[0; 31], &[0; 16]).is_err());
        assert!(rng.instantiate(&[0; 32], &[0; 15]).is_err());
        rng.instantiate(&[0x31; 32], &[0x72; 16]).unwrap();
        assert!(rng.generate(&mut std::vec![0; 65537]).is_err());
        for len in [1, 31, 32, 33, 255, 1024] {
            let mut out = std::vec![0; len];
            rng.generate(&mut out).unwrap();
            assert!(out.iter().any(|b| *b != 0));
        }
    }
}
