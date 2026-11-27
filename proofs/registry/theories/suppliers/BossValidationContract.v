From Coq Require Import List Bool NArith.
From OxideSE.Registry Require Import FlashSpec BossDecodingContract.
Import ListNotations.

(* C10 -> C5 / L13,L17: existing pre-append observations and provider predicate.
   Offered observations: envelope/internal-format booleans, optional CMAC result,
   optional decrypted generation. None is a returned crypto error, NOT reset.
   Caller: a successful joint logical decode for the very same flash/id.
   Guarantees below do not force crypto success; cache hit still decrypts.
   Rust (distributed): format.rs::decode_registry_block_at/internal,
   header_auth.rs::verify_inner, boss_crypto generation decrypt and conversions.
   Requires concrete read/crypto/configuration to realize observe; no autonomous
   provider module or infallible logical decoder is asserted. Cache mutation,
   XIP eligibility, read_area/offset_in/latest and publication stay with clients.
   check_boss_before_append and its proofs remain PreAppendValidation;
   BossCheckAPI/caller/callee/update remain FreerPreAppend, unchanged.
   Interruptions are separate existing relations, not normal provider replies. *)

Inductive boss_check_event :=
 | CheckEnvelope | AuthenticationCacheHit | ComputeAuthentication
 | CheckInternalFormat | DecryptGeneration | ConvertGeneration.

Inductive boss_check_error :=
 | EnvelopeRejected | AuthenticationError | AuthenticationRejected
 | InternalFormatRejected | GenerationError | GenerationOverflow.

Inductive boss_check_result :=
 | BossCheckFailed (reason:boss_check_error)
 | BossCheckReady (generation:N).

Record boss_check_observations := BossCheckObservations {
 envelope_ok : bool;
 authentication_reply : option bool;
 internal_format_ok : bool;
 generation_reply : option N
}.

Definition boss_check_provider (read:generation_decoder)
    (observe:flash->nat->boss_check_observations) :=
 forall f id d n, read f id=Some (d,n) ->
 envelope_ok (observe f id)=true /\
 internal_format_ok (observe f id)=true /\
 authentication_reply (observe f id)<>Some false /\
 (forall value,generation_reply (observe f id)=Some value -> value=counter_value n).
