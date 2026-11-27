From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement
  JournalFlashBridge JournalScan JournalIndex JournalRecoveryTrace.

(* Composition of the trace's physical preservation result with the reverse
   scan.  It yields existence of a selected validated slot, not its freshness:
   the latter is false if the caller continues after a returned journal error. *)
Section TraceScan.
Variable g : geometry.
Variable sector page old_slot old_index : nat.
Variable a data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hsector : sector_size g = sector.
Hypothesis Hpage : page_size g = page.
Hypothesis Hsize : 16 <= page <= sector.
Hypothesis Hold : old_slot + 8 <= sector.
Hypothesis Hindex : old_slot = 8 * old_index.
Hypothesis Hsector8 : sector mod 8 = 0.
Hypothesis Ha : u32 a.
Hypothesis Hrange : (N.of_nat page <= a < data_len)%N.
Hypothesis Halign : (a mod N.of_nat page = 0)%N.
Hypothesis Hboss : boss_ok a = true.

Lemma primary_A_checked f :
  JournalRecoveryTrace.primary_A old_slot a f ->
  exists index,
    index < sector / 8 /\
    checked_slot boss_ok data_len (N.of_nat page)
      (sector_bytes f 0 sector) index = Some a.
Proof.
  intros [Holdslot|Hzeroslot].
  - exists old_index. split.
    + assert (sector = 8 * (sector / 8)).
      { apply Nat.Div0.div_exact; lia. } lia.
    + unfold checked_slot.
      rewrite (physical_slot_of_flash f 0 sector old_index)
        by (subst old_slot; lia).
      replace (0 + 8 * old_index) with old_slot by lia.
      rewrite Holdslot.
      rewrite (decode_code_bytes a data_len (N.of_nat page)
        Ha Hrange Halign), Hboss. reflexivity.
  - exists 0. split.
    + assert (1 <= sector / 8).
      { apply Nat.div_le_lower_bound; lia. } lia.
    + unfold checked_slot.
      rewrite (physical_slot_of_flash f 0 sector 0) by lia.
      simpl. rewrite Hzeroslot.
      rewrite (decode_code_bytes a data_len (N.of_nat page)
        Ha Hrange Halign), Hboss. reflexivity.
Qed.

Theorem done_trace_yields_some_validated_primary f f' c :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  clos_refl_trans JournalRecoveryTrace.state
    (JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c)
    (JournalRecoveryTrace.State JournalRecoveryTrace.RotCopy f)
    (JournalRecoveryTrace.State JournalRecoveryTrace.Done f') ->
  exists index offset,
    latest_in_model boss_ok data_len (N.of_nat page)
      (sector_bytes f' 0 sector) = Some (index, offset).
Proof.
  intros Hvalid Holdslot Herased Htrace.
  pose proof (JournalRecoveryTrace.arbitrary_rotation_and_recovery_preserve_A
    g sector page old_slot a data_len boss_ok
    Hsector Hpage Hsize Hold Ha Hrange Halign Hboss
    c f (JournalRecoveryTrace.State JournalRecoveryTrace.Done f')
    Hvalid Holdslot Herased Htrace) as [Hinv _].
  destruct Hinv as [_ [_ [_ Hphase]]]. simpl in Hphase.
  destruct (primary_A_checked f' Hphase) as [j [Hj Hchecked]].
  eapply latest_scan_some_if_checked; eauto.
  unfold sector_bytes. rewrite length_map, length_seq. exact Hj.
Qed.

Theorem done_trace_yields_validated_primary_and_clean_secondary f f' c :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  clos_refl_trans JournalRecoveryTrace.state
    (JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c)
    (JournalRecoveryTrace.State JournalRecoveryTrace.RotCopy f)
    (JournalRecoveryTrace.State JournalRecoveryTrace.Done f') ->
  (exists index offset,
    latest_in_model boss_ok data_len (N.of_nat page)
      (sector_bytes f' 0 sector) = Some (index, offset)) /\
  JournalRecoveryTrace.clean_backup sector f'.
Proof.
  intros Hvalid Holdslot Herased Htrace. split.
  - eapply done_trace_yields_some_validated_primary; eauto.
  - eapply JournalRecoveryTrace.arbitrary_trace_done_has_clean_secondary;
      eauto.
Qed.
End TraceScan.
