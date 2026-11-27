From Coq Require Import List.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority TransactionBoundary.
Import ListNotations.

(* C10 certified-incarnation locality, with the SAME persistent_certificate
   witness owned by TransactionBoundary. Offered: preserve one successful decode
   when its BOSS and resolved Data extents are unchanged. Requires ranges and a
   successful earlier decode; says nothing about changed bytes at a reused id.
   Rust (distributed): format.rs::decode_registry_block_at/trusted/known,
   recovery.rs::open_entry, references.rs and retention.rs range resolution.
   Realization must justify all bytes/key-context consulted. No autonomous Rust
   reader trait is claimed, no second certificate/table/history is introduced.
   Read failures and physical interruptions belong to the operational services;
   this predicate does not turn a logical decode into an infallible Rust call.
   Dependency on TransactionBoundary is intentional: extracting its certificate
   and receipt structures belongs to a different structural refactoring. *)

Definition incarnation_reader_local ranges (decode:flash->nat->option recovery_decoding) c :=
 forall before after,
 decode before (certificate_id c)=Some (certificate_decoded c) ->
 unchanged (certificate_ranges ranges c) before after ->
 decode after (certificate_id c)=Some (certificate_decoded c).
