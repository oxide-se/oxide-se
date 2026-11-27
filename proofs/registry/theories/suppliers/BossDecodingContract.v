From Coq Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority JournalHistory.
Import ListNotations.

(* C10 / L13,L17,L21: logical BOSS reader laws, not an operational API.
   Offered: decode : flash -> relative offset -> option recovery_decoding;
   joint read : full flash -> relative offset -> option (decoding * u32).
   Caller: the antecedent decode/read succeeded; locality additionally requires
   unchanged BOSS bytes. Guarantees: first projection agrees, same local result,
   decoded address is contained, and the logical journal validator accepts.
   No update, authority preservation, successful crypto call or interruption
   semantics is asserted here. Errors/Reset/Fatal remain with the callers.
   Rust (distributed): format.rs::decode_registry_block_at/trusted/known,
   decrypt_registry_image, image.rs::Image::restore, journal.rs::validate.
   Projection: recovery_decoding is the compact image and BOSS extent, NOT
   proof that the Data callback's requested logical bytes were written.
   Requires in the concrete implementation: mapped reads, format checks and
   crypto; these are not yet a typed required-services API in this family.
   Realization of these exact predicates is open; no Rust-conformance axiom. *)

Record decoded_counter := DecodedCounter {
 counter_value : N;
 counter_u32 : (counter_value <= 4294967295)%N
}.

Definition generation_decoder := flash -> nat -> option (recovery_decoding * decoded_counter).

Definition generation_decoding_matches sector decode (read:generation_decoder) :=
 forall f id, option_map fst (read f id)=decode (object_flash sector f) id.

Definition generation_decoding_local sector (read:generation_decoder) :=
 forall before after id d n,read before id=Some (d,n) ->
 unchanged [recovered_boss d] (object_flash sector before) (object_flash sector after) ->
 read after id=Some (d,n).

Definition decoding_address_contract (decode:flash->nat->option recovery_decoding) :=
 forall f id d, decode f id=Some d -> contains (recovered_boss d) id.

Definition validator_accepts_decoded sector (decode:flash->nat->option recovery_decoding) (validate:flash->N->bool) :=
 forall f id d, decode (object_flash sector f) id=Some d -> validate f (N.of_nat id)=true.
