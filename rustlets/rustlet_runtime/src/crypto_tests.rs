use super::*;

#[derive(Default)]
struct ObservingBackend {
    calls: usize,
    expected_key: usize,
    expected_iv: usize,
    fail: bool,
}

impl CryptoBackend for ObservingBackend {
    fn cipher_do_final(
        &mut self,
        parameters: &CipherReady<'_>,
        input: &[u8],
        output: &mut [u8],
    ) -> Result<usize, CryptoError> {
        // Verify that the session lends the original storage, not a copied key/IV.
        assert_eq!(parameters.key().as_ptr() as usize, self.expected_key);
        assert_eq!(parameters.iv().as_ptr() as usize, self.expected_iv);
        assert_eq!(parameters.mode(), CipherMode::Encrypt);
        assert_eq!(parameters.algorithm(), Algorithm::Aes128CbcNoPadding);
        self.calls += 1;
        if self.fail {
            return Err(CryptoError::PermissionDenied);
        }
        output[..input.len()].copy_from_slice(input);
        Ok(input.len())
    }

    fn mac_compute(
        &mut self,
        _: &[u8],
        _: MacAlgorithm,
        _: &[u8],
        _: &mut [u8; MAC_TAG_SIZE],
    ) -> Result<(), CryptoError> {
        unreachable!("cipher session must not invoke MAC services")
    }

    fn mac_verify(
        &mut self,
        _: &[u8],
        _: MacAlgorithm,
        _: &[u8],
        _: &[u8],
    ) -> Result<bool, CryptoError> {
        unreachable!("cipher session must not invoke MAC services")
    }
}

#[test]
fn cipher_borrows_original_storage_and_releases_it_on_error_or_success() {
    let mut backend = ObservingBackend::default();
    for fail in [true, false] {
        let mut key = [0x12; 16];
        let mut iv = [0x34; 16];
        backend.expected_key = key.as_ptr() as usize;
        backend.expected_iv = iv.as_ptr() as usize;
        backend.fail = fail;
        let mut output = [0x55; 16];
        let session = Cipher::new(&mut backend)
            .init(
                &key,
                &iv,
                CipherMode::Encrypt,
                Algorithm::Aes128CbcNoPadding,
            )
            .unwrap();
        let result = session.finish(&[0xAB; 16], &mut output);
        if fail {
            assert_eq!(result, Err(CryptoError::PermissionDenied));
            assert_eq!(output, [0x55; 16]);
        } else {
            assert_eq!(result, Ok(16));
            assert_eq!(output, [0xAB; 16]);
        }
        // These writes compile because finalization released both input loans.
        key.fill(0);
        iv.fill(0);
    }
    assert_eq!(backend.calls, 2);
}

#[test]
fn invalid_parameters_do_not_call_the_backend() {
    let mut backend = ObservingBackend::default();
    assert!(matches!(
        Cipher::new(&mut backend).init(
            &[0; 16],
            &[0; 15],
            CipherMode::Encrypt,
            Algorithm::Aes128CbcNoPadding
        ),
        Err(CryptoError::InvalidBufferLength)
    ));
    assert!(matches!(
        Cipher::new(&mut backend).init(
            &[0; 16],
            &[0; 16],
            CipherMode::Encrypt,
            Algorithm::Aes256CbcNoPadding
        ),
        Err(CryptoError::InvalidKeyLength)
    ));
    assert_eq!(backend.calls, 0);
}

#[test]
fn abandoned_session_has_no_backend_effect_and_update_preserves_it() {
    let mut backend = ObservingBackend::default();
    let key = [0; 16];
    let iv = [0; 16];
    {
        let mut session = Cipher::new(&mut backend)
            .init(
                &key,
                &iv,
                CipherMode::Encrypt,
                Algorithm::Aes128CbcNoPadding,
            )
            .unwrap();
        let mut output = [0x77; 16];
        assert_eq!(
            session.update(&[0; 16], &mut output),
            Err(CryptoError::Unsupported)
        );
        assert_eq!(output, [0x77; 16]);
    }
    assert_eq!(backend.calls, 0);
    backend.expected_key = key.as_ptr() as usize;
    backend.expected_iv = iv.as_ptr() as usize;
    let session = Cipher::new(&mut backend)
        .init(
            &key,
            &iv,
            CipherMode::Encrypt,
            Algorithm::Aes128CbcNoPadding,
        )
        .unwrap();
    assert_eq!(session.finish(&[0; 16], &mut [0; 16]), Ok(16));
}
