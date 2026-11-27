From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry.

(* Relative addresses: primary starts at zero, secondary at [sector]. The
   theorems below compose actual page-program and sector-erase relations.
   They do not treat a slot, page, or sector as atomic. A separate reachable
   state proof must cover all early exits and repeated recovery invocations. *)
Section Rotation.
Variable g : geometry.
Variable sector page old_slot : nat.
Variable a c : N.
Hypothesis Hsector : sector_size g = sector.
Hypothesis Hpage : page_size g = page.
Hypothesis Hsize : 16 <= page <= sector.
Hypothesis Hold : old_slot + 8 <= sector.
Hypothesis Ha : u32 a.

Definition backup_buffer f := write_entry_page f sector page 0 (code_bytes a).
Definition restore_buffer f := write_entry_page f 0 page 0 (code_bytes a).
Definition append_buffer f := write_entry_page f 0 page 8 (code_bytes c).

Lemma copy_cut_preserves_old f f' result :
  program_step g f sector (backup_buffer f) result f' ->
  flash_slot f old_slot = code_bytes a ->
  flash_slot f' old_slot = code_bytes a.
Proof.
  intros Hstep Holdcode.
  rewrite (write_entry_preserves_other_page _ _ _ _ _ _ _ _ _
    Hstep (or_introl Hold)).
  exact Holdcode.
Qed.

Lemma completed_copy_establishes_backup f f' :
  program_step g f sector (backup_buffer f) Success f' ->
  flash_slot f' sector = code_bytes a.
Proof.
  intro Hstep. unfold backup_buffer in Hstep.
  assert (Hbound : 0 + 8 <=
    length (write_entry_page f sector page 0 (code_bytes a)))
    by (rewrite write_entry_page_length; lia).
  pose proof (success_program_slot_exact _ _ _ _ _ 0 Hstep Hbound)
    as Hslot.
  rewrite Nat.add_0_r in Hslot. rewrite Hslot.
  apply write_entry_page_target_slot; [apply code_bytes_length|lia].
Qed.

Lemma primary_erase_preserves_backup f f' result :
  erase_step g f 0 result f' ->
  flash_slot f sector = code_bytes a ->
  flash_slot f' sector = code_bytes a.
Proof.
  intros Hstep Hbackup.
  rewrite (erase_preserves_outside_slot _ _ _ _ _ _ Hstep).
  - exact Hbackup.
  - right. rewrite Hsector. lia.
Qed.

Lemma completed_restore_establishes_primary f f' :
  program_step g f 0 (restore_buffer f) Success f' ->
  flash_slot f' 0 = code_bytes a.
Proof.
  intro Hstep. unfold restore_buffer in Hstep.
  assert (Hbound : 0 + 8 <=
    length (write_entry_page f 0 page 0 (code_bytes a)))
    by (rewrite write_entry_page_length; lia).
  pose proof (success_program_slot_exact _ _ _ _ _ 0 Hstep Hbound)
    as Hslot.
  simpl in Hslot. rewrite Hslot.
  apply write_entry_page_target_slot; [apply code_bytes_length|lia].
Qed.

Lemma restore_cut_preserves_backup f f' result :
  program_step g f 0 (restore_buffer f) result f' ->
  flash_slot f sector = code_bytes a ->
  flash_slot f' sector = code_bytes a.
Proof.
  intros Hstep Hbackup. unfold restore_buffer in Hstep.
  assert (Houtside : sector + 8 <= 0 \/ 0 + page <= sector)
    by (right; lia).
  rewrite (write_entry_preserves_other_page g f f' 0 page 0
    (code_bytes a) result sector Hstep Houtside).
  exact Hbackup.
Qed.

Lemma secondary_erase_preserves_primary f f' result :
  erase_step g f sector result f' ->
  flash_slot f 0 = code_bytes a ->
  flash_slot f' 0 = code_bytes a.
Proof.
  intros Hstep Hprimary.
  rewrite (erase_preserves_outside_slot _ _ _ _ _ _ Hstep).
  - exact Hprimary.
  - left. lia.
Qed.

Lemma append_cut_preserves_primary_A f f' result :
  program_step g f 0 (append_buffer f) result f' ->
  flash_slot f 0 = code_bytes a ->
  flash_slot f' 0 = code_bytes a.
Proof.
  intros Hstep Hprimary. unfold append_buffer in Hstep.
  assert (Hslot : 0 + 8 <= page) by lia.
  assert (Hdisjoint : 0 + 8 <= 8 \/ 8 + 8 <= 0)
    by (left; lia).
  pose proof (write_entry_preserves_disjoint_slot g f f' 0 page 8
    (code_bytes c) result 0 Hstep Hslot Hdisjoint) as Hpres.
  simpl in Hpres. rewrite Hpres.
  exact Hprimary.
Qed.

Theorem successful_rotation_prefix_and_any_final_append
    f0 f1 f2 f3 f4 f5 result_append :
  flash_slot f0 old_slot = code_bytes a ->
  program_step g f0 sector (backup_buffer f0) Success f1 ->
  erase_step g f1 0 Success f2 ->
  program_step g f2 0 (restore_buffer f2) Success f3 ->
  erase_step g f3 sector Success f4 ->
  program_step g f4 0 (append_buffer f4) result_append f5 ->
  flash_slot f1 old_slot = code_bytes a /\
  flash_slot f1 sector = code_bytes a /\
  flash_slot f2 sector = code_bytes a /\
  flash_slot f3 0 = code_bytes a /\
  flash_slot f4 0 = code_bytes a /\
  flash_slot f5 0 = code_bytes a.
Proof.
  intros Hinitial Hcopy Herase Hrestore Herase2 Happend.
  pose proof (copy_cut_preserves_old _ _ _ Hcopy Hinitial) as Hold1.
  pose proof (completed_copy_establishes_backup _ _ Hcopy) as Hb1.
  pose proof (primary_erase_preserves_backup _ _ _ Herase Hb1) as Hb2.
  pose proof (completed_restore_establishes_primary _ _ Hrestore) as Hp3.
  pose proof (secondary_erase_preserves_primary _ _ _ Herase2 Hp3) as Hp4.
  pose proof (append_cut_preserves_primary_A _ _ _ Happend Hp4) as Hp5.
  repeat split; assumption.
Qed.

Theorem completed_recovery_from_valid_backup f0 f1 f2 f3 result_erase :
  flash_slot f0 sector = code_bytes a ->
  erase_step g f0 0 Success f1 ->
  program_step g f1 0 (restore_buffer f1) Success f2 ->
  erase_step g f2 sector result_erase f3 ->
  flash_slot f1 sector = code_bytes a /\
  flash_slot f2 0 = code_bytes a /\
  flash_slot f3 0 = code_bytes a.
Proof.
  intros Hbackup Herase Hrestore Herase2.
  pose proof (primary_erase_preserves_backup _ _ _ Herase Hbackup) as Hb1.
  pose proof (completed_restore_establishes_primary _ _ Hrestore) as Hp2.
  pose proof (secondary_erase_preserves_primary _ _ _ Herase2 Hp2) as Hp3.
  repeat split; assumption.
Qed.

Theorem recovery_secondary_erase_when_backup_rejected f f' result :
  flash_slot f 0 = code_bytes a ->
  erase_step g f sector result f' ->
  flash_slot f' 0 = code_bytes a.
Proof.
  intros Hprimary Hstep.
  eapply secondary_erase_preserves_primary; eauto.
Qed.

End Rotation.
