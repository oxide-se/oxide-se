From Coq Require Import List NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage PreparedAuthority
 PublicationPreparation PreparationOutcomes BossDecodingContract.
Import ListNotations.

(* C5 -> C10 / L13: local encoder round-trip contract.
   Offered: an image/generation/extent-indexed list of writer_command, plus the
   predicate below about a COMPLETE execution on the admitted erased extent.
   Requires: the existing writer_execution and erased_object_extent; it does
   not choose next, reserve, rehome, install, publish, or add a receipt.
   Other writer replies and cuts impose no success postcondition in this law.
   Rust (direct caller, distributed realization): publication.rs::write_snapshot,
   image.rs::Image::encode, format.rs::encode_registry_block_at,
   boss_crypto/header_auth and physical page writes. The logical plan projects
   their emitted commands; the joint reader projects decoded compact bytes and
   generation. Realizing this law and the emitted plan remains open.
   No new interpreter/API or probabilistic crypto assumption is introduced. *)

Definition boss_generation_plan := list compact_slot -> N -> extent -> list writer_command.

Definition boss_generation_format g sector (encode:boss_generation_plan) (read:generation_decoder) :=
 forall image number r before result,
 erased_object_extent sector before r ->
 writer_execution g sector r true before (encode image number r) result ->
 writer_end result=WriterComplete ->
 exists decoded counter,
 read (writer_flash result) (offset r)=Some (decoded,counter) /\
 recovered_boss decoded=r /\ recovered_image decoded=image /\ counter_value counter=number.
