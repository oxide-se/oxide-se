From Coq Require Import List Arith NArith Lia Bool.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement JournalScan
  JournalIndex JournalWriteEntry.
Import ListNotations.

(* Historical pre-b1dad23 caller continuation. The physical images and flash
   outcomes remain possible, but JournalFreeze.old_D_after_error_is_excluded
   proves that the new volatile freeze gate forbids the second append before
   reset. This module intentionally does not import that gate.

   A minimal, page-aligned instance of the real two-sector control flow.
   The same suffix occurs with 256-byte pages and a 4096-byte sector after
   the primary has been filled by successful publications.  The BOSS
   predicate states only that the two already written blocks validate. *)
Definition stale_page : nat := 64.
Definition stale_sector : nat := 64.
Definition stale_A : N := 512%N.
Definition stale_D : N := 576%N.
Definition stale_boss_ok (a : N) :=
  N.eqb a stale_A || N.eqb a stale_D.
Definition stale_ff n := repeat 255%N n.
Definition stale_full_primary :=
  concat (map code_bytes [64%N;128%N;192%N;256%N;
                          320%N;384%N;448%N;stale_A]).
Definition stale_restored_primary := code_bytes stale_A ++ stale_ff 56.
Definition stale_new_primary :=
  code_bytes stale_A ++ code_bytes stale_D ++ stale_ff 48.
Definition stale_backup := code_bytes stale_A ++ stale_ff 56.
Definition stale_cleared := stale_ff 64.

(* The first invocation of append sees a full primary. After its returned
   secondary-erase error, the next invocation sees slot 1 erased. *)
Theorem stale_first_append_rotates :
  length stale_full_primary = stale_sector /\
  first_empty_slot stale_full_primary = None.
Proof. vm_compute. split; reflexivity. Qed.

Theorem stale_initial_latest_is_A :
  latest_in_model stale_boss_ok 704%N 64%N stale_full_primary =
    Some (7%nat, stale_A).
Proof. vm_compute. reflexivity. Qed.

Theorem stale_second_append_skips_rotation :
  length stale_restored_primary = stale_sector /\
  first_empty_slot stale_restored_primary = Some 1%nat /\
  physical_slot stale_restored_primary 1 = stale_ff 8.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The returned error is compatible with an entirely unchanged secondary.
   This is a physical outcome of a valid erase request, not argument rejection
   and not a reset. *)
Definition stale_geometry : geometry :=
  {| area_start := 0; area_length := 128;
     page_size := 64; sector_size := 64 |}.
Definition stale_after_error_flash : flash :=
  fun p => nth p (stale_restored_primary ++ stale_backup) 255%N.

Lemma stale_after_error_valid : valid_flash stale_after_error_flash.
Proof.
  intro p. unfold stale_after_error_flash.
  destruct (lt_dec p (length (stale_restored_primary ++ stale_backup))).
  - apply (proj1 (Forall_nth valid_byte
      (stale_restored_primary ++ stale_backup))).
    + vm_compute. repeat constructor; unfold valid_byte; lia.
    + exact l.
  - rewrite nth_overflow by lia. unfold valid_byte. lia.
Qed.

Lemma stale_slot_one_erased : erased_target stale_after_error_flash 0 8.
Proof.
  intros i Hi. assert (i < 8) by exact Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

Theorem stale_second_append_program_request :
  program_request stale_geometry stale_after_error_flash 0
    (write_entry_page stale_after_error_flash 0 64 8
      (code_bytes stale_D)).
Proof.
  apply write_entry_code_request.
  - reflexivity.
  - reflexivity.
  - unfold FlashSpec.within, stale_geometry. simpl. lia.
  - exact stale_after_error_valid.
  - lia.
  - exact stale_slot_one_erased.
Qed.

Definition stale_D_page :=
  write_entry_page stale_after_error_flash 0 64 8 (code_bytes stale_D).
Definition stale_after_D_flash : flash :=
  fun p => if p <? 64 then nth p stale_D_page 255%N
           else stale_after_error_flash p.

Theorem stale_D_program_success_is_permitted :
  program_step stale_geometry stale_after_error_flash 0 stale_D_page
    Success stale_after_D_flash.
Proof.
  apply program_success.
  - exact stale_second_append_program_request.
  - unfold frame, stale_after_D_flash. intros p [Hbefore|Hafter].
    + lia.
    + unfold stale_D_page in Hafter.
      rewrite write_entry_page_length in Hafter. simpl in Hafter.
      apply Nat.ltb_ge in Hafter. rewrite Hafter. reflexivity.
  - unfold programmed, stale_after_D_flash. intros i b Hnth.
    rewrite Nat.add_0_l.
    assert (Hi : i < 64).
    { assert (Hi' : i < length stale_D_page).
      { apply (proj1 (nth_error_Some stale_D_page i)). congruence. }
      unfold stale_D_page in Hi'.
      rewrite write_entry_page_length in Hi'. exact Hi'. }
    apply Nat.ltb_lt in Hi. rewrite Hi.
    exact (nth_error_nth stale_D_page i 255%N Hnth).
Qed.

Theorem stale_success_image_is_new_primary :
  sector_bytes stale_after_D_flash 0 stale_sector = stale_new_primary.
Proof. vm_compute. reflexivity. Qed.
Theorem stale_secondary_erase_request :
  erase_request stale_geometry stale_sector.
Proof. vm_compute. lia. Qed.
Theorem stale_secondary_erase_may_fail_without_effect f :
  valid_flash f ->
  erase_step stale_geometry f stale_sector VerifyFailed f.
Proof.
  intro Hvalid. apply erase_no_effect_error_allowed;
    [exact Hvalid|exact stale_secondary_erase_request].
Qed.

(* Before restart, a successfully programmed D is the highest validated
   primary slot. Recovery sees valid backup A, erases the whole primary,
   restores A at slot 0, and clears the secondary. *)
Theorem stale_acknowledged_D_selected_before_reset :
  latest_in_model stale_boss_ok 704%N 64%N stale_new_primary =
    Some (1%nat, stale_D).
Proof. vm_compute. reflexivity. Qed.
Theorem stale_physical_success_selects_D :
  latest_in_model stale_boss_ok 704%N 64%N
    (sector_bytes stale_after_D_flash 0 stale_sector) =
      Some (1%nat, stale_D).
Proof.
  rewrite stale_success_image_is_new_primary.
  exact stale_acknowledged_D_selected_before_reset.
Qed.
Theorem stale_backup_validates_A :
  latest_in_model stale_boss_ok 704%N 64%N stale_backup =
    Some (0%nat, stale_A).
Proof. vm_compute. reflexivity. Qed.
Theorem stale_recovery_selects_A :
  latest_in_model stale_boss_ok 704%N 64%N stale_restored_primary =
    Some (0%nat, stale_A).
Proof. vm_compute. reflexivity. Qed.
Theorem stale_authority_regression :
  stale_A <> stale_D /\
  latest_in_model stale_boss_ok 704%N 64%N stale_new_primary =
    Some (1%nat, stale_D) /\
  latest_in_model stale_boss_ok 704%N 64%N stale_restored_primary =
    Some (0%nat, stale_A).
Proof.
  split; [discriminate|].
  split; [exact stale_acknowledged_D_selected_before_reset|
          exact stale_recovery_selects_A].
Qed.
