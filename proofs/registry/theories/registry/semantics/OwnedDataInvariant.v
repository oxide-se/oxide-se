From Stdlib Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage PreparedAuthority JournalHistory JournalReachableShape JournalRawOrder TransactionBoundary FreerGlobalDataTrace FreerAllocationAdmission BossDecodingContract RecycledWriter IncarnationBoundary.

Section OwnerInvariant.
Variable sector : nat.
Variable data_len : N.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable pages : nat.
Local Notation Safe v o := (boundary_safe sector data_len v o marker ranges decode pages).

Record owner_invariants valid view (state:execution_boundary) : Prop := OwnerInvariants {
 owner_safe : Safe valid view state;
 owner_raw : raw_order sector 256 data_len (boundary_journal state);
 owner_pages : page_metadata_coherent state;
 owner_runtime : runtime_metadata_coherent state;
 owner_generation : generation_decoding_matches sector decode (counter_decoder (snd state));
 owner_generation_local : generation_decoding_local sector (counter_decoder (snd state));
 owner_counter : counter_metadata_coherent state;
 owner_allocation : allocation_metadata_coherent state;
 owner_range : allocation_range_origin sector pages decode (snd state);
 owner_append_bound : allocation_append_bound pages (snd state);
 owner_latest : ordinary_latest_coherent state;
 owner_structure : external_structure marker state;
 owner_marker : persistence_marker_recognized sector (control_image (journal_control (boundary_journal state)))
}.

Definition owned_data_entry word_max valid view f h a old d s e : Prop :=
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) /\
 phase_numeric word_max marker ranges (snd (fst ((Logged (Ready f) h a,IdleBoundary old d s),e))) /\ delivered_owner_closed e.
End OwnerInvariant.
