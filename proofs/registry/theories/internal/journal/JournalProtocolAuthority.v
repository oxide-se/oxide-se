From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import FlashSpec JournalComplement JournalFlashBridge
  JournalWriteEntry JournalScan JournalIndex JournalAppendSelection JournalAppendAuthority
  JournalRecoveryTrace JournalPhaseShape.
Import ListNotations.

Section Authority.
Variable g : geometry.
Variable sector page old_slot : nat.
Variable a d data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hsector : sector_size g = sector.
Hypothesis Hpage : page_size g = page.
Hypothesis Hsize : 16 <= page <= sector.
Hypothesis Hsector8 : sector mod 8 = 0.
Hypothesis Hold : old_slot+8 <= sector.
Hypothesis Ha : u32 a.
Hypothesis Har : (N.of_nat page <= a < data_len)%N.
Hypothesis Haal : (a mod N.of_nat page = 0)%N.
Hypothesis Hab : boss_ok a = true.
Hypothesis Hd : u32 d.
Hypothesis Hdr : (N.of_nat page <= d < data_len)%N.
Hypothesis Hdal : (d mod N.of_nat page = 0)%N.
Hypothesis Hdb : boss_ok d = true.

Definition observed f := option_map snd
  (latest_in_model boss_ok data_len (N.of_nat page) (sector_bytes f 0 sector)).

Lemma observed_single f : JournalPhaseShape.single sector a f -> observed f = Some a.
Proof.
  intros [Hz Htail].
  assert (Hscan : latest_in_model boss_ok data_len (N.of_nat page)
      (sector_bytes f 0 sector) = Some (0,a)).
  { apply complete_slot_physically_published; try assumption.
    - unfold sector_bytes. rewrite length_map, length_seq.
      assert (1 <= sector/8) by (apply Nat.div_le_lower_bound; lia). lia.
    - rewrite physical_slot_of_flash by lia. exact Hz.
    - intros j Hj. unfold sector_bytes in Hj.
      rewrite length_map, length_seq in Hj.
      unfold checked_slot. rewrite physical_slot_of_flash.
      + rewrite Nat.add_0_l, (Htail j Hj), erased_slot_invalid. reflexivity.
      + pose proof (Nat.div_mod sector 8 ltac:(lia)). lia. }
  unfold observed. rewrite Hscan. reflexivity.
Qed.

Lemma observed_secondary_program f f' result :
  program_step g f sector (copied_buffer sector page a f) result f' ->
  observed f' = observed f.
Proof.
  intro Hstep. unfold observed.
  rewrite (JournalPhaseShape.primary_image_same g sector page old_slot a data_len
    Hsector Hpage Hsize Hsector8 Hold Har Haal f f').
  - reflexivity.
  - intros p Hp. apply (program_locality _ _ _ _ _ _ Hstep). left. exact Hp.
Qed.

Lemma observed_secondary_erase f f' result :
  erase_step g f sector result f' -> observed f' = observed f.
Proof.
  intro Hstep. unfold observed.
  rewrite (JournalPhaseShape.primary_image_same g sector page old_slot a data_len
    Hsector Hpage Hsize Hsector8 Hold Har Haal f f').
  - reflexivity.
  - intros p Hp. apply (erase_locality _ _ _ _ _ Hstep). left. exact Hp.
Qed.

Definition phase_authority current (s : JournalRecoveryTrace.state) :=
  let f := flash_of s in
  match phase_of s with
  | RotCopy | RotErasePrimary | EraseSecondary =>
      current = Some a /\ observed f = current
  | RotRestorePrimary | RotEraseSecondary | RotAppend |
    ErasePrimary | RestorePrimary => current = Some a
  | Inspect | ReturnedError =>
      (current = Some a /\ (backup_A sector a f \/ observed f = current)) \/
      (clean_backup sector f /\ observed f = current)
  | Done => observed f = current
  end.

Definition protocol_authority_after current s s' :=
  match phase_of s with
  | RotAppend => authority_after_candidate current (flash_of s') 1 d
  | _ => current
  end.

Lemma clean_not_dirty f : clean_backup sector f -> ~ dirty_backup sector f.
Proof. intros Hclean [i [Hi Hne]]. apply Hne. apply Hclean. exact Hi. Qed.

Theorem protocol_step_preserves_authority current s s' :
  recovery_invariant sector old_slot a s ->
  JournalPhaseShape.phase_shape sector a s ->
  clean_at_append_or_done sector s ->
  phase_authority current s ->
  protocol_step g sector page a data_len boss_ok d s s' ->
  phase_authority (protocol_authority_after current s s') s'.
Proof.
  intros Hinv Hshape Hclean Hauth Hstep.
  destruct Hinv as [Hv [Habove [Hrec Hsafe]]].
  destruct Hstep as [s0 s1 Hrot|s0 s1 Hrecover].
  - inversion Hrot; subst s0 s1;
      unfold phase_authority, protocol_authority_after in *; cbn in Hauth |- *.
    + destruct Hauth as [Hcur Hscan].
      assert (Hscan' : observed f' = current).
      { rewrite (observed_secondary_program _ _ _ H). exact Hscan. }
      destruct result; cbn; auto.
    + assert (Hb' : backup_A sector a f').
      { eapply (JournalPhaseShape.primary_erase_keeps_backup g sector page old_slot a data_len
          Hsector Hpage Hsize Hsector8 Hold Har Haal);
          eauto. }
      destruct Hauth as [Hcur Hscan]. destruct result; cbn; auto.
    + assert (Hb' : backup_A sector a f').
      { eapply (JournalPhaseShape.primary_restore_keeps_backup g sector page old_slot a data_len
          Hsector Hpage Hsize Hsector8 Hold Har Haal);
          eauto. }
      destruct result; cbn; auto.
    + assert (Hscan : observed f = Some a).
      { apply observed_single. exact Hshape. }
      assert (Hscan' : observed f' = current).
      { rewrite (observed_secondary_erase _ _ _ H), Hscan. symmetry. exact Hauth. }
      destruct result; cbn; auto.
    + change (JournalPhaseShape.single sector a f) in Hshape.
      destruct Hshape as [Hz Htail].
      destruct (first_empty_after_single_entry f sector a data_len
        (N.of_nat page) ltac:(lia) Hsector8 Hz Ha Har Haal Htail)
        as [Hfirst Hsuffix].
      assert (Hscan : observed f = current).
      { rewrite (observed_single f (conj Hz Htail)). symmetry. exact Hauth. }
      assert (Hscan' : observed f' = authority_after_candidate current f' 1 d).
      { unfold observed in *. rewrite <- Hscan.
        eapply (any_candidate_outcome_updates_authority g f f' sector page
          1 0 8 d data_len boss_ok result); eauto; lia. }
      assert (Hclean' : clean_backup sector f').
      { intros i Hi. eapply (primary_page_write_preserves_clean_secondary
          g f f' sector page 0 8 d result); eauto; lia. }
      destruct result; cbn; auto.
  - inversion Hrecover; subst s0 s1;
      unfold phase_authority, protocol_authority_after in *; cbn in Hauth |- *.
    + destruct Hauth as [[Hcur _]|[Hcl _]]; [exact Hcur|].
      exfalso. exact (clean_not_dirty f Hcl H).
    + destruct Hauth as [[Hcur [Hbackup|Hscan]]|[Hcl Hscan]].
      * rewrite (backup_A_checked sector page a data_len boss_ok
          Ha Har Haal Hab f Hbackup) in H0. discriminate.
      * auto.
      * exfalso. exact (clean_not_dirty f Hcl H).
    + destruct Hauth as [[Hcur [Hbackup|Hscan]]|[Hcl Hscan]]; auto.
      exfalso. exact (clean_backup_not_A g sector page old_slot a data_len
        boss_ok Hsector Hpage Hsize Hold Ha Har Haal Hab f H Hbackup).
    + assert (Hb' : backup_A sector a f').
      { eapply (JournalPhaseShape.primary_erase_keeps_backup g sector page old_slot a data_len
          Hsector Hpage Hsize Hsector8 Hold Har Haal); eauto. }
      destruct result; cbn; auto.
    + assert (Hb' : backup_A sector a f').
      { eapply (JournalPhaseShape.primary_restore_keeps_backup g sector page old_slot a data_len
          Hsector Hpage Hsize Hsector8 Hold Har Haal);
          eauto. }
      destruct result; cbn; auto.
      split; [exact Hauth|]. rewrite Hauth. apply observed_single.
      eapply (JournalPhaseShape.restore_after_erase_single g sector page old_slot a data_len
        Hsector Hpage Hsize Hsector8 Hold Har Haal);
        eauto. exact Hshape.
    + destruct Hauth as [Hcur Hscan].
      assert (Hscan' : observed f' = current).
      { rewrite (observed_secondary_erase _ _ _ H). exact Hscan. }
      destruct result; cbn; auto.
    + exact Hauth.
Qed.

Theorem reset_preserves_authority current s :
  recovery_invariant sector old_slot a s ->
  JournalPhaseShape.phase_shape sector a s ->
  clean_at_append_or_done sector s -> phase_authority current s ->
  phase_authority current (State Inspect (flash_of s)).
Proof.
  intros [_ [_ [_ Hsafe]]] Hshape Hclean Hauth.
  destruct s as [p f]. destruct p;
    unfold phase_authority, phase_safe, clean_at_append_or_done in *;
    cbn [phase_of flash_of] in *; try tauto.
  - left. split; [exact Hauth|]. right. rewrite Hauth.
    apply observed_single. exact Hshape.
  - left. split; [exact Hauth|]. right. rewrite Hauth.
    apply observed_single. exact Hshape.
Qed.

End Authority.
