From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalRecoveryTrace
  JournalAppendSelection JournalIndex JournalRequests.
Import ListNotations.

(* Physical shape facts used at the boundary between recovery and append.
   A partially erased primary need not have this shape. *)
Section PhaseShape.
Variable g : geometry.
Variable sector page old_slot : nat.
Variable a c data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hsector : sector_size g = sector.
Hypothesis Hpage : page_size g = page.
Hypothesis Hsize : 16 <= page <= sector.
Hypothesis Hsector8 : sector mod 8 = 0.
Hypothesis Hold : old_slot + 8 <= sector.
Hypothesis Ha : u32 a.
Hypothesis Hrange : (N.of_nat page <= a < data_len)%N.
Hypothesis Halign : (a mod N.of_nat page = 0)%N.
Hypothesis Hboss : boss_ok a = true.

Definition shape f := erased_suffix (sector_bytes f 0 sector).
Definition single f :=
  flash_slot f 0 = code_bytes a /\
  forall j, 0 < j < sector / 8 ->
    flash_slot f (8*j) = repeat 255%N 8.
Definition backup f := JournalRecoveryTrace.backup_A sector a f.
Definition clean f := JournalRecoveryTrace.clean_backup sector f.

Lemma primary_image_same f f' :
  (forall p, p < sector -> f' p = f p) ->
  sector_bytes f' 0 sector = sector_bytes f 0 sector.
Proof.
  intro Hsame. unfold sector_bytes.
  apply map_ext_in. intros p Hin.
  apply in_seq in Hin. simpl in Hin. apply Hsame. lia.
Qed.

Lemma shape_same f f' :
  (forall p, p < sector -> f' p = f p) -> shape f -> shape f'.
Proof.
  intros Hsame Hshape. unfold shape in *.
  rewrite (primary_image_same f f' Hsame). exact Hshape.
Qed.

Lemma single_same f f' :
  (forall p, p < sector -> f' p = f p) -> single f -> single f'.
Proof.
  intros Hsame [Hzero Htail]. split.
  - unfold flash_slot in *. rewrite (map_ext_in f' f (seq 0 8)).
    + exact Hzero.
    + intros p Hin. apply in_seq in Hin. apply Hsame. lia.
  - intros j Hj. unfold flash_slot in *. rewrite (map_ext_in f' f (seq (8*j) 8)).
    + exact (Htail j Hj).
    + intros p Hin. apply in_seq in Hin.
      pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv.
      apply Hsame. lia.
Qed.

Lemma secondary_program_same f f' result :
  program_step g f sector
    (JournalRecoveryTrace.copied_buffer sector page a f) result f' ->
  forall p, p < sector -> f' p = f p.
Proof.
  intros Hstep p Hp. apply (program_locality _ _ _ _ _ _ Hstep).
  left. exact Hp.
Qed.

Lemma secondary_erase_same f f' result :
  erase_step g f sector result f' ->
  forall p, p < sector -> f' p = f p.
Proof.
  intros Hstep p Hp. apply (erase_locality _ _ _ _ _ Hstep).
  left. exact Hp.
Qed.

Lemma single_implies_shape f : single f -> shape f.
Proof.
  intros [Hzero Htail].
  exact (proj2 (first_empty_after_single_entry f sector a data_len
    (N.of_nat page) ltac:(lia) Hsector8 Hzero Ha Hrange Halign Htail)).
Qed.

Lemma restore_after_erase_single f f' :
  erased f 0 sector ->
  program_step g f 0
    (JournalRecoveryTrace.restored_buffer page a f) Success f' ->
  single f'.
Proof.
  intros Herased Hstep. split.
  - assert (Hfit : 8 <= length
      (JournalRecoveryTrace.restored_buffer page a f)).
    { unfold JournalRecoveryTrace.restored_buffer.
      rewrite write_entry_page_length. lia. }
    pose proof (success_program_slot_exact _ _ _ _ _ 0 Hstep Hfit) as Hslot.
    rewrite Nat.add_0_r in Hslot. rewrite Hslot.
    unfold JournalRecoveryTrace.restored_buffer.
    apply write_entry_page_target_slot; [apply code_bytes_length|lia].
  - intros j Hj.
    assert (Hfit : 8*j+8 <= sector).
    { pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv. lia. }
    rewrite (page_write_preserves_other_slot_any g f f' 0 page 0
      (code_bytes a) 0 j Success ltac:(lia) ltac:(lia) Hstep).
    eapply erased_primary_slot; eauto.
Qed.

(* The phase invariant records exactly where holes may occur: the backup is
   then complete, and the caller cannot use the primary until repair. *)
Definition phase_shape (s : JournalRecoveryTrace.state) : Prop :=
  let f := JournalRecoveryTrace.flash_of s in
  match JournalRecoveryTrace.phase_of s with
  | JournalRecoveryTrace.RotCopy => shape f /\ clean f
  | JournalRecoveryTrace.RotErasePrimary => shape f
  | JournalRecoveryTrace.RotRestorePrimary |
    JournalRecoveryTrace.RestorePrimary => erased f 0 sector
  | JournalRecoveryTrace.RotEraseSecondary |
    JournalRecoveryTrace.RotAppend => single f
  | JournalRecoveryTrace.Inspect |
    JournalRecoveryTrace.ReturnedError => shape f \/ backup f
  | JournalRecoveryTrace.ErasePrimary => backup f
  | JournalRecoveryTrace.EraseSecondary |
    JournalRecoveryTrace.Done => shape f
  end.

Lemma primary_erase_keeps_backup f f' result :
  erase_step g f 0 result f' -> backup f -> backup f'.
Proof.
  intros Hstep Hb. unfold backup in *.
  unfold JournalRecoveryTrace.backup_A in *.
  rewrite (erase_preserves_outside_slot _ _ _ _ _ _ Hstep).
  - exact Hb.
  - right. lia.
Qed.

Lemma primary_restore_keeps_backup f f' result :
  program_step g f 0
    (JournalRecoveryTrace.restored_buffer page a f) result f' ->
  backup f -> backup f'.
Proof.
  intros Hstep Hb. unfold backup, JournalRecoveryTrace.backup_A in *.
  unfold flash_slot in *. rewrite (map_ext_in f' f (seq sector 8)).
  - exact Hb.
  - intros p Hin. apply in_seq in Hin.
    apply (program_locality _ _ _ _ _ _ Hstep). right.
    unfold JournalRecoveryTrace.restored_buffer.
    rewrite write_entry_page_length. lia.
Qed.

Lemma single_after_secondary_erase f f' result :
  erase_step g f sector result f' -> single f -> single f'.
Proof.
  intros Hstep. eapply single_same.
  exact (secondary_erase_same f f' result Hstep).
Qed.

Lemma shape_after_secondary_erase f f' result :
  erase_step g f sector result f' -> shape f -> shape f'.
Proof.
  intros Hstep. eapply shape_same.
  exact (secondary_erase_same f f' result Hstep).
Qed.

Lemma shape_after_secondary_copy f f' result :
  program_step g f sector
    (JournalRecoveryTrace.copied_buffer sector page a f) result f' ->
  shape f -> shape f'.
Proof.
  intros Hstep. eapply shape_same.
  exact (secondary_program_same f f' result Hstep).
Qed.

Lemma append_after_single_shape f f' result :
  single f ->
  program_step g f 0
    (JournalRecoveryTrace.appended_buffer page c f) result f' ->
  shape f'.
Proof.
  intros Hsingle Hstep.
  destruct Hsingle as [Hzero Htail].
  destruct (first_empty_after_single_entry f sector a data_len
    (N.of_nat page) ltac:(lia) Hsector8 Hzero Ha Hrange Halign Htail)
    as [Hfirst Hshape].
  unfold shape in *.
  eapply (any_outcome_nonrotation_preserves_erased_suffix
    g f f' sector page 1 0 8 c result); eauto; lia.
Qed.

Theorem protocol_step_preserves_phase_shape s s' :
  JournalRecoveryTrace.recovery_invariant sector old_slot a s ->
  phase_shape s ->
  JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c s s' ->
  phase_shape s'.
Proof.
  intros Hinv Hshape Hstep.
  destruct Hinv as [_ [Habove [_ Hsafe]]].
  destruct Hstep as [s0 s1 Hrot|s0 s1 Hrec].
  - inversion Hrot; subst s0 s1; unfold phase_shape in Hshape |- *; cbn in Hshape |- *.
    + destruct Hshape as [Hshape Hclean].
      assert (Hnext : shape f')
        by (eapply shape_after_secondary_copy; eauto).
      destruct result; cbn; auto.
    + assert (Hb : backup f')
        by (eapply primary_erase_keeps_backup; eauto).
      destruct result; cbn; auto.
      rewrite <- Hsector. eapply erase_success_contents; eauto.
    + assert (Hb : backup f')
        by (eapply primary_restore_keeps_backup; eauto).
      destruct result; cbn; auto.
      eapply restore_after_erase_single; eauto.
    + assert (Hs : single f')
        by (eapply single_after_secondary_erase; eauto).
      destruct result; cbn; auto using single_implies_shape.
    + assert (Hs : shape f')
        by (eapply append_after_single_shape; eauto).
      destruct result; cbn; auto.
  - inversion Hrec; subst s0 s1; unfold phase_shape in Hshape |- *; cbn in Hshape |- *.
    + eapply JournalRecoveryTrace.checked_backup_exact; eauto.
    + destruct Hshape as [Hs|Hb]; [exact Hs|].
      rewrite (JournalRecoveryTrace.backup_A_checked sector page a
        data_len boss_ok Ha Hrange Halign Hboss f Hb) in H0. discriminate.
    + destruct Hshape as [Hs|Hb]; [exact Hs|].
      exfalso. exact (JournalRecoveryTrace.clean_backup_not_A
        g sector page old_slot a data_len boss_ok Hsector Hpage Hsize Hold
        Ha Hrange Halign Hboss f H Hb).
    + assert (Hb : backup f')
        by (eapply primary_erase_keeps_backup; eauto).
      destruct result; cbn; auto.
      rewrite <- Hsector. eapply erase_success_contents; eauto.
    + assert (Hb : backup f')
        by (eapply primary_restore_keeps_backup; eauto).
      destruct result; cbn; auto.
      apply single_implies_shape. eapply restore_after_erase_single; eauto.
    + assert (Hs : shape f')
        by (eapply shape_after_secondary_erase; eauto).
      destruct result; cbn; auto.
    + exact Hshape.
Qed.

Theorem arbitrary_protocol_trace_preserves_phase_shape s s' :
  JournalRecoveryTrace.recovery_invariant sector old_slot a s ->
  phase_shape s ->
  clos_refl_trans JournalRecoveryTrace.state
    (JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c)
    s s' ->
  JournalRecoveryTrace.recovery_invariant sector old_slot a s' /\ phase_shape s'.
Proof.
  intros Hinv Hshape Htrace. induction Htrace.
  - split.
    + eapply (JournalRecoveryTrace.protocol_step_preserves_invariant
        g sector page old_slot a data_len boss_ok Hsector Hpage Hsize Hold
        Ha Hrange Halign Hboss); eauto.
    + eapply protocol_step_preserves_phase_shape; eauto.
  - auto.
  - destruct (IHHtrace1 Hinv Hshape) as [Hmid Hmidshape].
    exact (IHHtrace2 Hmid Hmidshape).
Qed.

Theorem completed_rotation_recovery_establishes_shape f f' :
  valid_flash f -> flash_slot f old_slot = code_bytes a ->
  JournalRecoveryTrace.clean_backup sector f -> shape f ->
  clos_refl_trans JournalRecoveryTrace.state
    (JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c)
    (JournalRecoveryTrace.State JournalRecoveryTrace.RotCopy f)
    (JournalRecoveryTrace.State JournalRecoveryTrace.Done f') ->
  shape f' /\ JournalRecoveryTrace.clean_backup sector f'.
Proof.
  intros Hv Holdcode Hclean Hshape Htrace. split.
  - apply (proj2 (arbitrary_protocol_trace_preserves_phase_shape _ _
      (JournalRecoveryTrace.initial_rotation_invariant sector old_slot a f Hv
        Holdcode (JournalRecoveryTrace.clean_backup_slot g sector page old_slot a data_len
          Hsector Hpage Hsize Hold Hrange Halign f Hclean))
      (conj Hshape Hclean) Htrace)).
  - eapply JournalRecoveryTrace.arbitrary_trace_done_has_clean_secondary;
      eauto.
Qed.

Definition next_request_valid (s : JournalRecoveryTrace.state) :=
  let f := JournalRecoveryTrace.flash_of s in
  match JournalRecoveryTrace.phase_of s with
  | JournalRecoveryTrace.RotCopy => program_request g f sector
      (JournalRecoveryTrace.copied_buffer sector page a f)
  | JournalRecoveryTrace.RotErasePrimary | JournalRecoveryTrace.ErasePrimary =>
      erase_request g 0
  | JournalRecoveryTrace.RotRestorePrimary | JournalRecoveryTrace.RestorePrimary =>
      program_request g f 0 (JournalRecoveryTrace.restored_buffer page a f)
  | JournalRecoveryTrace.RotEraseSecondary | JournalRecoveryTrace.EraseSecondary =>
      erase_request g sector
  | JournalRecoveryTrace.RotAppend => program_request g f 0
      (JournalRecoveryTrace.appended_buffer page c f)
  | _ => True
  end.

Theorem phase_invariant_establishes_requests s :
  journal_geometry g sector page ->
  JournalRecoveryTrace.recovery_invariant sector old_slot a s ->
  phase_shape s -> next_request_valid s.
Proof.
  intros Hgeom [Hv Hrest] Hshape.
  destruct s as [p f]. destruct p;
    unfold next_request_valid, phase_shape in *; cbn in *; try exact I.
  - eapply backup_copy_request; eauto. exact (proj2 Hshape).
  - eapply primary_erase_request; eauto.
  - eapply primary_restore_request; eauto.
  - eapply secondary_erase_request; eauto.
  - eapply second_slot_write_request; eauto.
    destruct Hshape as [_ Htail]. apply (Htail 1).
    change (0 < 1 < sector/8).
    assert (2 <= sector/8) by (apply Nat.div_le_lower_bound; lia). lia.
  - eapply primary_erase_request; eauto.
  - eapply primary_restore_request; eauto.
  - eapply secondary_erase_request; eauto.
Qed.

Theorem reset_between_commands_preserves_phase_shape s :
  JournalRecoveryTrace.recovery_invariant sector old_slot a s ->
  phase_shape s ->
  JournalRecoveryTrace.recovery_invariant sector old_slot a
    (JournalRecoveryTrace.State JournalRecoveryTrace.Inspect
      (JournalRecoveryTrace.flash_of s)) /\
  phase_shape (JournalRecoveryTrace.State JournalRecoveryTrace.Inspect
      (JournalRecoveryTrace.flash_of s)).
Proof.
  intros [Hv [Hb [Hr Hsafe]]] Hshape. split.
  - repeat split; assumption.
  - destruct s as [p f]. destruct p;
      unfold phase_shape, JournalRecoveryTrace.phase_safe in *; cbn in *;
      auto using single_implies_shape.
    left. exact (proj1 Hshape).
Qed.

End PhaseShape.
