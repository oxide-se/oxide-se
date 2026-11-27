From Coq Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec JournalComplement JournalWriteEntry JournalScan
  JournalIndex JournalAppendSelection JournalFreeze JournalRecoveryTrace.

(* Physical completion, a journal error return, the pending return and caller
   acknowledgement are separate events. This bridge uses the proved
   no-rotation selection result; it does not assert that Rust implements the
   witness transitions. *)
Section AppendFreezeBridge.
Variable g : geometry.
Variable sector page index aligned within : nat.
Variable d data_len : N.
Variable boss_ok : N -> bool.
Variable s : witness.
Variable after : flash.
Hypothesis Hsector8 : sector mod 8 = 0.
Hypothesis Hpage : 8 <= page.
Hypothesis Haddr : aligned + within = 8*index.
Hypothesis Hwithin : within + 8 <= page.
Hypothesis Hfirst :
  first_empty_slot (sector_bytes (image s) 0 sector) = Some index.
Hypothesis Hshape : erased_suffix (sector_bytes (image s) 0 sector).
Hypothesis Hprogram :
  program_step g (image s) aligned
    (write_entry_page (image s) aligned page within (code_bytes d))
    Success after.
Hypothesis Hd : u32 d.
Hypothesis Hrange : (N.of_nat page <= d < data_len)%N.
Hypothesis Halign : (d mod N.of_nat page = 0)%N.
Hypothesis Hboss : boss_ok d = true.

Lemma physical_completion_selects_D :
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes after 0 sector) = Some (index,d).
Proof.
  eapply successful_nonrotation_append_selects; eauto.
Qed.

Theorem normal_append_return_can_ack_D :
  frozen s = false -> boot_ready s = true ->
  normal_step g boss_ok data_len (N.of_nat page) sector s
    (set_pending s after d) /\
  normal_step g boss_ok data_len (N.of_nat page) sector
    (set_pending s after d) (acknowledge (set_pending s after d) d) /\
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes after 0 sector) = Some (index,d) /\
  acks (acknowledge (set_pending s after d) d) = d :: acks s.
Proof.
  intros Hfree Hready. repeat split.
  - eapply final_program_ok; eauto.
  - apply append_ack; simpl; try reflexivity. exact Hready.
  - exact physical_completion_selects_D.
Qed.

Theorem completed_program_error_can_publish_without_ack :
  frozen s = false ->
  normal_step g boss_ok data_len (N.of_nat page) sector s
    (freeze_with s after) /\
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes after 0 sector) = Some (index,d) /\
  frozen (freeze_with s after) = true /\
  acks (freeze_with s after) = acks s.
Proof.
  intro Hfree. repeat split.
  - eapply program_error; [exact Hfree|].
    eapply program_completed_can_return_verify_failed; exact Hprogram.
  - exact physical_completion_selects_D.
Qed.

Theorem completed_readback_error_can_publish_without_ack :
  frozen s = false ->
  normal_step g boss_ok data_len (N.of_nat page) sector s
    (freeze_with s after) /\
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes after 0 sector) = Some (index,d) /\
  acks (freeze_with s after) = acks s.
Proof.
  intro Hfree. repeat split.
  - eapply program_readback_error; eauto.
  - exact physical_completion_selects_D.
Qed.

Theorem completed_unacknowledged_D_survives_reset_if_backup_clean :
  JournalRecoveryTrace.clean_backup sector after ->
  recovered boss_ok data_len (N.of_nat page) sector
    (reset_to_boot (freeze_with s after) after) d.
Proof.
  intro Hclean. unfold recovered, reset_to_boot, freeze_with. simpl.
  split.
  - exists index. exact physical_completion_selects_D.
  - exact Hclean.
Qed.
End AppendFreezeBridge.
