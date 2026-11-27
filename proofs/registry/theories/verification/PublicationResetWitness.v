From Coq Require Import List Arith NArith Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalHistory JournalReachableShape
  JournalWriteEntry JournalFlashBridge JournalAppendAuthority DataEpisode.
Import ListNotations.

(* An operational witness: a completed programming command can reset instead
   of returning. COMPLETED is the local slot-byte check, not a selection or
   recovery premise. Numeric slot-fit proofs can supply it via
   successful_candidate_completed. *)
Theorem completed_program_publication_cut g sector data_len boss_ok initial before after slot candidate history acks :
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok candidate)
    initial (Logged (Writing before slot candidate) history acks) ->
  program_step g before (8*slot/256*256) (candidate_buffer 256 before slot candidate) Success after ->
  candidate_completed after slot candidate=true ->
  publication_reset_prefix g sector data_len boss_ok candidate initial
    (Logged (Boot after) (candidate::history) acks).
Proof.
  intros PREFIX PROGRAM COMPLETE.
  exists (Logged (Writing before slot candidate) history acks).
  split; [exact PREFIX|]. split; [reflexivity|]. split; [|exact I].
  pose proof (program_completed_before_reset _ _ _ _ _ PROGRAM) as RESET.
  pose proof (record_step g sector 256 data_len boss_ok _ _ history acks
    (candidate_program g sector 256 data_len boss_ok before after slot candidate Reset RESET)) as STEP.
  cbn [publication_history_after acknowledgement_history_after control_image] in STEP.
  unfold record_candidate in STEP. rewrite COMPLETE in STEP. exact STEP.
Qed.
