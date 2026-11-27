From Coq Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority CompactUpdates AllocationAdmission.
Import ListNotations.

(* C10 geometry/admission laws. Witness: the EXISTING decoded extent/image and
   caller-supplied resolver ranges : compact_entry -> list extent.
   Successful decode guarantees the existing numeric range checks for BOSS and
   resolved references; the allocation law bounds/page-aligns the BOSS end.
   range_check and its error type are moved only because decoded_numeric_contract
   uses them. Reserve/release/rehome implementations and proofs stay in their
   original layer. Numeric validity does not assert freedom or release rights.
   Rust (distributed): format.rs offset/length/page checks, Image::restore,
   recovery.rs::entry_for_view/open_entry, references.rs and retention helpers;
   pages.rs range checks. Concrete usize/conversions and mapping configuration
   must realize these predicates. Relative bounds do not imply absolute Address
   validity. No table/flash mutation or transaction invariant is promised.
   Errors from actual readers and their interruptions remain operationally
   represented by their clients, not by this successful-decoding implication. *)

Definition extent_end r := offset r + span r.

Inductive ram_reservation_error := TableUninitialized | RangeOverflow | TableCapacity | PageOccupied.

Definition range_check (initialized:bool) word_max r :=
 if initialized then
   if Nat.leb (offset r+span r) word_max then
     if Nat.leb (AllocationAdmission.page_limit r) 1024 then None else Some TableCapacity
   else Some RangeOverflow
 else Some TableUninitialized.

Definition range_numeric word_max r := range_check true word_max r=None.

Definition decoded_numeric_contract word_max ranges (decode:flash->nat->option recovery_decoding) :=
 forall f id d, decode f id=Some d ->
 Forall (range_numeric word_max)
   (recovered_boss d::image_dependencies ranges (recovered_image d)).

Definition decoded_allocation_geometry pages (decode:flash->nat->option recovery_decoding) :=
 forall f id d,decode f id=Some d ->
 extent_end (recovered_boss d)<=pages*256 /\
 extent_end (recovered_boss d) mod 256=0.
