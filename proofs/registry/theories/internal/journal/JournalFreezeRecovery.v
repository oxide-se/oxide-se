From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement
  JournalFlashBridge JournalRecoveryTrace JournalTraceScan JournalScan
  JournalIndex JournalFreeze.
Import ListNotations.

(* Bridge from a successful, possibly repeatedly interrupted [latest] trace
   to the boot gate. This proves a model certificate; correspondence of the
   actual Rust boot path and BOSS decoder remains a separate obligation. *)
Section FreezeRecovery.
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

Definition boot_state (f : flash) (history : list N) : witness :=
  Witness f false false None history [] 0.

Theorem completed_latest_opens_boot_gate f f' c history :
  valid_flash f ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f sector = repeat 255%N 8 ->
  clos_refl_trans JournalRecoveryTrace.state
    (JournalRecoveryTrace.protocol_step g sector page a data_len boss_ok c)
    (JournalRecoveryTrace.State JournalRecoveryTrace.RotCopy f)
    (JournalRecoveryTrace.State JournalRecoveryTrace.Done f') ->
  exists selected,
    recovered boss_ok data_len (N.of_nat page) sector
      (boot_state f' history) selected /\
    normal_step g boss_ok data_len (N.of_nat page) sector
      (boot_state f' history)
      (Witness f' false true None history [] 0).
Proof.
  intros Hvalid Holdslot Herased Htrace.
  pose proof (JournalTraceScan.done_trace_yields_validated_primary_and_clean_secondary
    g sector page old_slot old_index a data_len boss_ok
    Hsector Hpage Hsize Hold Hindex Hsector8 Ha Hrange Halign Hboss
    f f' c Hvalid Holdslot Herased Htrace) as
    [[index [selected Hscan]] Hclean].
  exists selected. split.
  - unfold recovered, boot_state. simpl. split.
    + exists index. exact Hscan.
    + exact Hclean.
  - apply recovery_complete with (a:=selected); simpl; try reflexivity.
    unfold recovered, boot_state. simpl. split.
    + exists index. exact Hscan.
    + exact Hclean.
Qed.

(* Conditional freshness across a reset whose successful [latest] observes an
   already clean backup. The premise that an acknowledged append established
   [latest_in = D] is a registry implementation obligation, not a flash axiom. *)
Theorem clean_selected_reset_keeps_address f history index selected :
  JournalRecoveryTrace.clean_backup sector f ->
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f 0 sector) = Some (index, selected) ->
  recovered boss_ok data_len (N.of_nat page) sector
    (reset_to_boot (boot_state f history) f) selected /\
  (forall other,
    recovered boss_ok data_len (N.of_nat page) sector
      (reset_to_boot (boot_state f history) f) other ->
    other = selected).
Proof.
  intros Hclean Hscan. split.
  - unfold recovered, reset_to_boot, boot_state. simpl. split.
    + exists index. exact Hscan.
    + exact Hclean.
  - intros other Hother.
    unfold recovered, reset_to_boot, boot_state in Hother.
    simpl in Hother. destruct Hother as [[j Hj] _].
    rewrite Hscan in Hj. inversion Hj. reflexivity.
Qed.

(* The missing registry invariant is precisely the scan premise below:
   an acknowledged newest D must remain the selected valid primary slot.
   The theorem isolates what the clean-backup and scan lemmas can conclude,
   without presenting that premise as an established property of [append]. *)
Corollary acknowledged_D_does_not_recover_A_when_selected
    f history index d a_old :
  d <> a_old ->
  JournalRecoveryTrace.clean_backup sector f ->
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f 0 sector) = Some (index, d) ->
  ~ recovered boss_ok data_len (N.of_nat page) sector
      (reset_to_boot (boot_state f (d :: history)) f) a_old.
Proof.
  intros Hneq Hclean Hscan Hrecovered.
  destruct (clean_selected_reset_keeps_address f (d :: history) index d
    Hclean Hscan) as [_ Hunique].
  apply Hneq. symmetry. apply Hunique. exact Hrecovered.
Qed.
End FreezeRecovery.
