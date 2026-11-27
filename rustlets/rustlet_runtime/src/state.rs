//! Separate durable and selection-scoped state, encoded independently.
use crate::ApduStatus;

/// Typed data owned by the runtime for the lifetime of a selection.
/// Only `persistent` is written to the registry. Session snapshots stay in RAM.
pub struct State<P, S = ()> {
    /// Transaction-owned data serialized into the registry.
    pub persistent: P,
    /// Volatile data retained until deselection, reset or terminal failure.
    pub session: S,
}

#[doc(hidden)]
pub trait PostcardState: serde::Serialize + for<'de> serde::Deserialize<'de> + Sized {
    fn load_postcard_state(&mut self, state: &[u8]) -> Result<(), ApduStatus> {
        *self = postcard::from_bytes(state).map_err(|_| ApduStatus::wrong_data())?;
        Ok(())
    }

    fn save_postcard_state(&self, out: &mut [u8]) -> Result<usize, ApduStatus> {
        let encoded = postcard::to_slice(self, out).map_err(|_| ApduStatus::wrong_length())?;
        Ok(encoded.len())
    }
}

impl<T> PostcardState for T where T: serde::Serialize + for<'de> serde::Deserialize<'de> + Sized {}

#[cfg(any(feature = "runtime", test))]
impl<P, S: PostcardState> State<P, S> {
    pub(crate) fn save_session(&self, out: &mut [u8]) -> Result<usize, ApduStatus> {
        self.session.save_postcard_state(out)
    }

    pub(crate) fn load_session(&mut self, bytes: &[u8]) -> Result<(), ApduStatus> {
        let (session, remaining) =
            postcard::take_from_bytes(bytes).map_err(|_| ApduStatus::wrong_data())?;
        if !remaining.is_empty() {
            return Err(ApduStatus::wrong_data());
        }
        self.session = session;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[derive(Default, serde::Serialize, serde::Deserialize, PartialEq, Debug)]
    struct Persistent {
        counter: u8,
    }
    #[derive(Default, serde::Serialize, serde::Deserialize, PartialEq, Debug)]
    struct Session {
        secret: [u8; 16],
        counter: u32,
    }

    #[test]
    fn registry_and_session_snapshots_are_separate() {
        let original = State {
            persistent: Persistent { counter: 7 },
            session: Session {
                secret: [0xA5; 16],
                counter: 123456,
            },
        };
        let mut registry = [0; 244];
        let n = original
            .persistent
            .save_postcard_state(&mut registry)
            .map_err(|status| status.to_word())
            .unwrap();
        assert_eq!(&registry[..n], &[7]);
        let mut bytes = [0; 244];
        let n = original
            .save_session(&mut bytes)
            .map_err(|status| status.to_word())
            .unwrap();
        let mut rebuilt = State {
            persistent: Persistent { counter: 6 },
            session: Session::default(),
        };
        rebuilt
            .load_session(&bytes[..n])
            .map_err(|status| status.to_word())
            .unwrap();
        assert_eq!(rebuilt.persistent.counter, 6);
        assert_eq!(rebuilt.session, original.session);
    }

    #[test]
    fn empty_states_have_a_valid_zero_length_encoding() {
        let mut state = State {
            persistent: (),
            session: (),
        };
        assert_eq!(
            state
                .persistent
                .save_postcard_state(&mut [])
                .map_err(|status| status.to_word())
                .unwrap(),
            0
        );
        assert_eq!(
            state
                .save_session(&mut [])
                .map_err(|status| status.to_word())
                .unwrap(),
            0
        );
        state
            .load_session(&[])
            .map_err(|status| status.to_word())
            .unwrap();
        assert_eq!(
            state
                .load_session(&[1])
                .err()
                .map(|status| status.to_word()),
            Some(ApduStatus::wrong_data().to_word())
        );
    }

    #[test]
    fn session_codec_rejects_overflow_truncation_and_trailing_bytes() {
        let mut state = State {
            persistent: (),
            session: Session {
                secret: [0x5A; 16],
                counter: u32::MAX,
            },
        };
        let mut bytes = [0; 244];
        assert_eq!(
            state
                .save_session(&mut bytes[..16])
                .err()
                .map(|status| status.to_word()),
            Some(ApduStatus::wrong_length().to_word())
        );
        let n = state
            .save_session(&mut bytes)
            .map_err(|status| status.to_word())
            .unwrap();
        assert_eq!(
            state
                .load_session(&bytes[..n - 1])
                .err()
                .map(|status| status.to_word()),
            Some(ApduStatus::wrong_data().to_word())
        );
        assert_eq!(
            state
                .load_session(&bytes[..n + 1])
                .err()
                .map(|status| status.to_word()),
            Some(ApduStatus::wrong_data().to_word())
        );
        assert_eq!(state.session.counter, u32::MAX);
        assert_eq!(state.session.secret, [0x5A; 16]);
    }
}
