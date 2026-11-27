From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalRotationOnePass.
Import ListNotations.

(* One invocation of latest, with arbitrarily many resets and later retries.
   The physical state is not rolled back on Reset or VerifyFailed. The model
   uses the first backup slot for validation, as journal.rs does; the dirty
   test covers the entire secondary sector. Scanning the primary is separate. *)
Section Recovery.
Variable g : geometry.
Variable sector page old_slot : nat.
Variable a data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hsector : sector_size g = sector.
Hypothesis Hpage : page_size g = page.
Hypothesis Hsize : 16 <= page <= sector.
Hypothesis Hold : old_slot + 8 <= sector.
Hypothesis Ha : u32 a.
Hypothesis Hrange : (N.of_nat page <= a < data_len)%N.
Hypothesis Halign : (a mod N.of_nat page = 0)%N.
Hypothesis Hboss : boss_ok a = true.

Definition primary_A f :=
  flash_slot f old_slot = code_bytes a \/ flash_slot f 0 = code_bytes a.
Definition backup_A f := flash_slot f sector = code_bytes a.
Definition backup_above_A f :=
  slot_byte_subset (code_bytes a) (flash_slot f sector).
Definition recoverable_A f := primary_A f \/ backup_A f.
Definition dirty_backup f :=
  exists i, i < sector /\ f (sector+i) <> 255%N.
Definition clean_backup f :=
  forall i, i < sector -> f (sector+i) = 255%N.
Definition checked_backup f :=
  validated_slot boss_ok (flash_slot f sector) data_len (N.of_nat page).

Inductive phase := RotCopy | RotErasePrimary | RotRestorePrimary |
  RotEraseSecondary | RotAppend | Inspect | ErasePrimary | RestorePrimary |
  EraseSecondary | Done | ReturnedError.
Record state := State { phase_of : phase; flash_of : flash }.

Definition phase_safe (s : state) :=
  match phase_of s with
  | RotCopy => flash_slot (flash_of s) old_slot = code_bytes a
  | RotErasePrimary | RotRestorePrimary => backup_A (flash_of s)
  | RotEraseSecondary | RotAppend =>
      flash_slot (flash_of s) 0 = code_bytes a
  | ErasePrimary | RestorePrimary => backup_A (flash_of s)
  | EraseSecondary | Done => primary_A (flash_of s)
  | Inspect | ReturnedError => True
  end.
Definition recovery_invariant (s : state) :=
  valid_flash (flash_of s) /\ backup_above_A (flash_of s) /\
  recoverable_A (flash_of s) /\ phase_safe s.

Definition restored_buffer f := write_entry_page f 0 page 0 (code_bytes a).
Definition copied_buffer f := write_entry_page f sector page 0 (code_bytes a).
Definition appended_buffer (c : N) f :=
  write_entry_page f 0 page 8 (code_bytes c).

Lemma backup_exact_above f : backup_A f -> backup_above_A f.
Proof.
  intro Hbackup. unfold backup_above_A. rewrite Hbackup.
  intros i Hi. unfold word_subset. rewrite N.land_diag. reflexivity.
Qed.

Inductive recovery_step : state -> state -> Prop :=
| inspect_valid f b :
    dirty_backup f -> checked_backup f = Some b ->
    recovery_step (State Inspect f) (State ErasePrimary f)
| inspect_invalid f :
    dirty_backup f -> checked_backup f = None ->
    recovery_step (State Inspect f) (State EraseSecondary f)
| inspect_clean f :
    clean_backup f ->
    recovery_step (State Inspect f) (State Done f)
| erase_primary f f' result :
    erase_step g f 0 result f' ->
    recovery_step (State ErasePrimary f)
      (State (match result with Success => RestorePrimary |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| restore_primary f f' result :
    program_step g f 0 (restored_buffer f) result f' ->
    recovery_step (State RestorePrimary f)
      (State (match result with Success => EraseSecondary |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| erase_secondary f f' result :
    erase_step g f sector result f' ->
    recovery_step (State EraseSecondary f)
      (State (match result with Success => Done |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| retry_after_error f :
    recovery_step (State ReturnedError f) (State Inspect f).

Lemma checked_backup_exact f b :
  backup_above_A f -> checked_backup f = Some b -> backup_A f.
Proof.
  intros Habove Hchecked.
  pose proof (validated_backup_only_requested_address boss_ok a
    (flash_slot f sector) data_len (N.of_nat page) b
    Ha Habove Hchecked) as Hb. subst b.
  unfold checked_backup, validated_slot in Hchecked.
  destruct (decode_slot (flash_slot f sector) data_len (N.of_nat page))
    as [found|] eqn:Hdecode; try discriminate.
  destruct (boss_ok found); inversion Hchecked; subst found.
  pose proof (decode_slot_sound _ _ _ _ Hdecode) as [_ [_ [_ Heq]]].
  symmetry. exact Heq.
Qed.

Lemma backup_A_checked f : backup_A f -> checked_backup f = Some a.
Proof.
  intro Hbackup. unfold checked_backup. rewrite Hbackup.
  unfold validated_slot.
  rewrite (decode_code_bytes a data_len (N.of_nat page)
    Ha Hrange Halign), Hboss. reflexivity.
Qed.

Lemma invalid_backup_primary f :
  recoverable_A f -> checked_backup f = None -> primary_A f.
Proof.
  intros [Hprimary|Hbackup] Hnone; [exact Hprimary|].
  rewrite (backup_A_checked f Hbackup) in Hnone. discriminate.
Qed.

Lemma clean_backup_slot f :
  clean_backup f -> flash_slot f sector = repeat 255%N 8.
Proof.
  intro Hclean. apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. rewrite length_map, length_seq, repeat_length.
    reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite flash_slot_nth by exact Hi.
    rewrite (nth_indep (repeat 255%N 8) 0%N 255%N)
      by (rewrite repeat_length; lia).
    rewrite nth_repeat. apply Hclean. lia.
Qed.

Lemma clean_backup_not_A f : clean_backup f -> ~ backup_A f.
Proof.
  intros Hclean Hbackup.
  pose proof (backup_A_checked f Hbackup) as Hchecked.
  unfold checked_backup, validated_slot in Hchecked.
  rewrite (clean_backup_slot f Hclean) in Hchecked.
  rewrite erased_slot_invalid in Hchecked. discriminate.
Qed.

Lemma clean_backup_primary f :
  recoverable_A f -> clean_backup f -> primary_A f.
Proof.
  intros [Hprimary|Hbackup] Hclean; [exact Hprimary|].
  exfalso. exact (clean_backup_not_A f Hclean Hbackup).
Qed.

Lemma primary_survives_secondary_erase f f' result :
  erase_step g f sector result f' -> primary_A f -> primary_A f'.
Proof.
  intros Hstep [Holdcode|Hrestored]; [left|right];
    rewrite (erase_preserves_outside_slot _ _ _ _ _ _ Hstep);
    try assumption.
  - left. lia.
  - left. lia.
Qed.

Lemma backup_above_after_secondary_erase f f' result :
  valid_flash f -> backup_above_A f ->
  erase_step g f sector result f' -> backup_above_A f'.
Proof.
  intros Hvalid Habove Hstep.
  eapply slot_byte_subset_trans; [exact Habove|].
  pose proof (erase_slot_monotone_any_outcome g f sector result f' 0
    Hstep (fun i _ => Hvalid (sector+i)) ltac:(rewrite Hsector; lia))
    as Hmono.
  rewrite Nat.add_0_r in Hmono. exact Hmono.
Qed.

Theorem recovery_step_preserves_invariant s s' :
  recovery_invariant s -> recovery_step s s' -> recovery_invariant s'.
Proof.
  intros [Hvalid [Habove [Hrecover Hphase]]] Hstep.
  inversion Hstep; subst; simpl in *.
  - repeat split; try assumption.
    eapply checked_backup_exact; eauto.
  - repeat split; try assumption.
    eapply invalid_backup_primary; eauto.
  - repeat split; try assumption.
    eapply clean_backup_primary; eauto.
  - assert (Hb' : backup_A f')
      by (eapply primary_erase_preserves_backup; eauto).
    destruct result; simpl; repeat split;
      try (eapply erase_step_preserves_valid_flash; eauto);
      try (apply backup_exact_above; exact Hb');
      try (right; exact Hb');
      try exact Hb'.
  - assert (Hb' : backup_A f').
    { eapply (restore_cut_preserves_backup g sector page old_slot a
        Hsector Hpage Hsize Hold f f' result); eauto. }
    destruct result; simpl; repeat split;
      try (eapply program_step_preserves_valid_flash; eauto);
      try (apply backup_exact_above; exact Hb');
      try (right; exact Hb');
      try exact Hb'.
    + right. eapply (completed_restore_establishes_primary g sector page
        old_slot a Hsector Hpage Hsize Hold f f'); eauto.
  - destruct result; simpl; repeat split;
      try (eapply erase_step_preserves_valid_flash; eauto);
      try (eapply backup_above_after_secondary_erase; eauto);
      try (left; eapply primary_survives_secondary_erase; eauto);
      try (eapply primary_survives_secondary_erase; eauto).
  - repeat split; assumption.
Qed.

Theorem repeated_recovery_preserves_authority s s' :
  recovery_invariant s ->
  clos_refl_trans state recovery_step s s' ->
  recovery_invariant s' /\ recoverable_A (flash_of s').
Proof.
  intros Hinitial Htrace.
  induction Htrace.
  - pose proof (recovery_step_preserves_invariant _ _ Hinitial H) as Hnext.
    split; [exact Hnext|exact (proj1 (proj2 (proj2 Hnext)))].
  - split; [exact Hinitial|exact (proj1 (proj2 (proj2 Hinitial)))].
  - pose proof (IHHtrace1 Hinitial) as [Hmid _].
    exact (IHHtrace2 Hmid).
Qed.

Theorem uninterrupted_valid_backup_recovery_reaches_done f f1 f2 f3 :
  dirty_backup f -> checked_backup f = Some a ->
  erase_step g f 0 Success f1 ->
  program_step g f1 0 (restored_buffer f1) Success f2 ->
  erase_step g f2 sector Success f3 ->
  clos_refl_trans state recovery_step (State Inspect f) (State Done f3).
Proof.
  intros Hdirty Hchecked Herase Hrestore Hclear.
  eapply rt_trans.
  - apply rt_step. apply inspect_valid with (b:=a); assumption.
  - eapply rt_trans.
    + apply rt_step. apply erase_primary. exact Herase.
    + eapply rt_trans.
      * apply rt_step. apply restore_primary. exact Hrestore.
      * apply rt_step. apply (erase_secondary f2 f3 Success). exact Hclear.
Qed.

Theorem uninterrupted_invalid_backup_recovery_reaches_done f f' :
  dirty_backup f -> checked_backup f = None ->
  erase_step g f sector Success f' ->
  clos_refl_trans state recovery_step (State Inspect f) (State Done f').
Proof.
  intros Hdirty Hchecked Herase.
  eapply rt_trans.
  - apply rt_step. apply inspect_invalid; assumption.
  - apply rt_step. apply (erase_secondary f f' Success). exact Herase.
Qed.

(* [append] first performs these five physical commands. An interrupted
   command enters [Inspect], not its former continuation. A returned error
   leaves the reached image available to a later caller of [latest]. *)
Inductive rotation_step (c : N) : state -> state -> Prop :=
| copy_A f f' result :
    program_step g f sector (copied_buffer f) result f' ->
    rotation_step c (State RotCopy f)
      (State (match result with Success => RotErasePrimary |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| rot_erase_primary f f' result :
    erase_step g f 0 result f' ->
    rotation_step c (State RotErasePrimary f)
      (State (match result with Success => RotRestorePrimary |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| rot_restore_primary f f' result :
    program_step g f 0 (restored_buffer f) result f' ->
    rotation_step c (State RotRestorePrimary f)
      (State (match result with Success => RotEraseSecondary |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| rot_erase_secondary f f' result :
    erase_step g f sector result f' ->
    rotation_step c (State RotEraseSecondary f)
      (State (match result with Success => RotAppend |
              VerifyFailed => ReturnedError | Reset => Inspect end) f')
| append_C f f' result :
    program_step g f 0 (appended_buffer c f) result f' ->
    rotation_step c (State RotAppend f)
      (State (match result with Success => Done |
              VerifyFailed => ReturnedError | Reset => Inspect end) f').

Lemma successful_final_append_slot_complete c f f' :
  program_step g f 0 (appended_buffer c f) Success f' ->
  flash_slot f' 8 = code_bytes c.
Proof.
  intro Hstep.
  assert (Hbound : 8 + 8 <= length (appended_buffer c f)).
  { unfold appended_buffer. rewrite write_entry_page_length. lia. }
  pose proof (success_program_slot_exact _ _ _ _ _ 8 Hstep Hbound) as Hslot.
  rewrite Nat.add_0_l in Hslot. rewrite Hslot.
  unfold appended_buffer.
  apply write_entry_page_target_slot; [apply code_bytes_length|lia].
Qed.

Lemma copy_above_A f f' result :
  program_step g f sector (copied_buffer f) result f' ->
  backup_above_A f'.
Proof.
  intro Hstep. unfold backup_above_A, copied_buffer in *.
  pose proof (program_slot_requested_only_any_outcome g f sector
    (write_entry_page f sector page 0 (code_bytes a)) result f' 0
    Hstep ltac:(rewrite write_entry_page_length; lia)) as Hslot.
  rewrite Nat.add_0_r in Hslot.
  rewrite (write_entry_page_target_slot f sector page 0 (code_bytes a)
    (code_bytes_length a) ltac:(lia)) in Hslot.
  exact Hslot.
Qed.

Lemma primary_write_preserves_backup f f' result data :
  program_step g f 0 data result f' ->
  length data = page ->
  flash_slot f' sector = flash_slot f sector.
Proof.
  intros Hstep Hlen. apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    apply (program_locality _ _ _ _ _ _ Hstep).
    right. rewrite Hlen. lia.
Qed.

Theorem rotation_step_preserves_invariant c s s' :
  recovery_invariant s -> rotation_step c s s' -> recovery_invariant s'.
Proof.
  intros [Hvalid [Habove [Hrecover Hphase]]] Hstep.
  inversion Hstep; subst; simpl in *.
  - assert (Hold' : flash_slot f' old_slot = code_bytes a)
      by (eapply copy_cut_preserves_old; eauto).
    assert (Habove' : backup_above_A f') by (eapply copy_above_A; eauto).
    destruct result; simpl; repeat split;
      try (eapply program_step_preserves_valid_flash; eauto);
      try exact Habove';
      try (left; left; exact Hold').
    eapply completed_copy_establishes_backup; eauto.
  - assert (Hb' : backup_A f')
      by (eapply primary_erase_preserves_backup; eauto).
    destruct result; simpl; repeat split;
      try (eapply erase_step_preserves_valid_flash; eauto);
      try (apply backup_exact_above; exact Hb');
      try (right; exact Hb');
      try exact Hb'.
  - assert (Hb' : backup_A f')
      by (eapply (restore_cut_preserves_backup g sector page old_slot a
        Hsector Hpage Hsize Hold f f' result); eauto).
    destruct result; simpl; repeat split;
      try (eapply program_step_preserves_valid_flash; eauto);
      try (apply backup_exact_above; exact Hb');
      try (right; exact Hb');
      try exact Hb'.
    eapply (completed_restore_establishes_primary g sector page old_slot a
      Hsector Hpage Hsize Hold f f'); eauto.
  - assert (Hp' : flash_slot f' 0 = code_bytes a)
      by (eapply secondary_erase_preserves_primary; eauto).
    assert (Habove' : backup_above_A f')
      by (eapply backup_above_after_secondary_erase; eauto).
    destruct result; simpl; repeat split;
      try (eapply erase_step_preserves_valid_flash; eauto);
      try exact Habove';
      try (left; right; exact Hp');
      try exact Hp'.
  - assert (Hp' : flash_slot f' 0 = code_bytes a).
    { unfold appended_buffer in H.
      eapply (append_cut_preserves_primary_A g sector page old_slot a c
        Hsector Hpage Hsize Hold f f' result); eauto. }
    assert (Habove' : backup_above_A f').
    { unfold backup_above_A in *.
      rewrite (primary_write_preserves_backup f f' result
        (appended_buffer c f) H
        ltac:(unfold appended_buffer; rewrite write_entry_page_length; reflexivity)).
      exact Habove. }
    destruct result; simpl; repeat split;
      try (eapply program_step_preserves_valid_flash; eauto);
      try exact Habove';
      try (left; right; exact Hp');
      try (right; exact Hp').
Qed.

Inductive protocol_step (c : N) : state -> state -> Prop :=
| from_rotation s s' : rotation_step c s s' -> protocol_step c s s'
| from_recovery s s' : recovery_step s s' -> protocol_step c s s'.

Theorem protocol_step_preserves_invariant c s s' :
  recovery_invariant s -> protocol_step c s s' -> recovery_invariant s'.
Proof.
  intros Hsafe Hstep. destruct Hstep.
  - eapply rotation_step_preserves_invariant; eauto.
  - eapply recovery_step_preserves_invariant; eauto.
Qed.

Theorem initial_rotation_invariant f :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  recovery_invariant (State RotCopy f).
Proof.
  intros Hvalid Holdcode Herased. unfold recovery_invariant.
  simpl. repeat split.
  - exact Hvalid.
  - unfold backup_above_A. rewrite Herased. apply erased_slot_above_code.
  - left. left. exact Holdcode.
  - exact Holdcode.
Qed.

Theorem arbitrary_rotation_and_recovery_preserve_A c f s :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  clos_refl_trans state (protocol_step c) (State RotCopy f) s ->
  recovery_invariant s /\ recoverable_A (flash_of s).
Proof.
  intros Hvalid Holdcode Herased Htrace.
  assert (Hinitial : recovery_invariant (State RotCopy f))
    by (apply initial_rotation_invariant; assumption).
  revert Hinitial. induction Htrace; intro Hinitial.
  - pose proof (protocol_step_preserves_invariant c _ _ Hinitial H)
      as Hnext.
    split; [exact Hnext|exact (proj1 (proj2 (proj2 Hnext)))].
  - split; [exact Hinitial|exact (proj1 (proj2 (proj2 Hinitial)))].
  - pose proof (IHHtrace1 Hinitial) as [Hmid _].
    exact (IHHtrace2 Hmid).
Qed.

Theorem arbitrary_trace_backup_cannot_retarget c f s b :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  clos_refl_trans state (protocol_step c) (State RotCopy f) s ->
  checked_backup (flash_of s) = Some b -> b = a.
Proof.
  intros Hvalid Holdcode Herased Htrace Hchecked.
  pose proof (arbitrary_rotation_and_recovery_preserve_A c f s
    Hvalid Holdcode Herased Htrace) as [Hinv _].
  destruct Hinv as [_ [Habove _]].
  eapply validated_backup_only_requested_address; eauto.
Qed.

(* The secondary is fully erased before the final append, and every path
   reaching Done has a clean secondary. This is a phase property, not a flash
   contract premise. Returned errors and resets do not satisfy Done. *)
Definition clean_at_append_or_done (s : state) : Prop :=
  match phase_of s with
  | RotAppend | Done => clean_backup (flash_of s)
  | _ => True
  end.

Lemma primary_program_preserves_clean f f' data result :
  length data = page ->
  program_step g f 0 data result f' ->
  clean_backup f -> clean_backup f'.
Proof.
  intros Hlen Hstep Hclean i Hi.
  rewrite (program_locality _ _ _ _ _ _ Hstep (sector+i)).
  - apply Hclean. exact Hi.
  - right. rewrite Hlen. lia.
Qed.

Lemma successful_secondary_erase_cleans f f' :
  erase_step g f sector Success f' -> clean_backup f'.
Proof.
  intros Hstep i Hi.
  inversion Hstep as [after Hrequest Hframe Herased | |]; subst.
  apply Herased. exact Hi.
Qed.

Theorem protocol_step_preserves_clean_phase c s s' :
  clean_at_append_or_done s ->
  protocol_step c s s' ->
  clean_at_append_or_done s'.
Proof.
  intros Hclean Hstep. destruct Hstep as [s0 s1 Hrot|s0 s1 Hrec].
  - inversion Hrot; subst; destruct result; simpl in *;
      try exact I; try assumption.
    + eapply successful_secondary_erase_cleans; eauto.
    + eapply primary_program_preserves_clean; eauto.
      unfold appended_buffer. apply write_entry_page_length.
  - inversion Hrec; subst; simpl in *; try exact I; try assumption;
      try (destruct result; simpl in *; try exact I; try assumption).
    eapply successful_secondary_erase_cleans; eauto.
Qed.

Lemma arbitrary_trace_preserves_clean_phase c s s' :
  clean_at_append_or_done s ->
  clos_refl_trans state (protocol_step c) s s' ->
  clean_at_append_or_done s'.
Proof.
  intros Hinitial Htrace. induction Htrace.
  - exact (protocol_step_preserves_clean_phase c _ _ Hinitial H).
  - exact Hinitial.
  - apply IHHtrace2. apply IHHtrace1. exact Hinitial.
Qed.

Theorem arbitrary_trace_done_has_clean_secondary c f f' :
  clos_refl_trans state (protocol_step c)
    (State RotCopy f) (State Done f') ->
  clean_backup f'.
Proof.
  intro Htrace.
  apply (arbitrary_trace_preserves_clean_phase c
    (State RotCopy f) (State Done f')); [exact I|exact Htrace].
Qed.

End Recovery.
