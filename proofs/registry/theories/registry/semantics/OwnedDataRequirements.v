From Stdlib Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage PreparedAuthority JournalHistory JournalRequests JournalReachableShape JournalRawOrder AllocationAdmission FreerAllocationAdmission RecycledWriter PreAppendValidation IncarnationBoundary IncarnationReaderContract BossDecodingContract DecodedGeometryContract.

Section Requirements.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable pages : nat.
Variable validate : flash -> N -> bool.

Definition owned_data_suppliers word_max base : Prop :=
 journal_geometry g sector 256 /\ sector mod 8=0 /\
 validator_accepts_decoded sector decode validate /\
 (forall c,incarnation_reader_local ranges decode c) /\
 marker_header_covered marker /\ journal_object_mapping data_len pages /\ mapped_pages pages /\
 decoding_address_contract decode /\ range_numeric word_max marker /\
 decoded_numeric_contract word_max ranges decode /\ 1024*256<=word_max /\
 area_start g+area_length g<=2*sector+1024*256 /\ decoded_allocation_geometry pages decode /\
 mapped_registry_base base.
End Requirements.
