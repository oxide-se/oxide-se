From Coq Require Import List Arith NArith Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalStaleBackup JournalScan
  JournalIndex.
Import ListNotations.

(* Volatile registry control state around the existing FreerDPS flash effect.
   [acks] is ghost history of observed publication successes, not firmware RAM.
   [held] abstracts reserved page identities; its reference closure is open. *)
Record witness := Witness {
  image : flash;
  frozen : bool;
  boot_ready : bool;
  pending_ack : option N;
  acks : list N;
  held : list nat;
  scope_depth : nat
}.

Definition set_image (s : witness) (f : flash) : witness :=
  Witness f (frozen s) (boot_ready s) (pending_ack s) (acks s) (held s)
    (scope_depth s).
Definition set_pending (s : witness) (f : flash) (a : N) : witness :=
  Witness f false (boot_ready s) (Some a) (acks s) (held s)
    (scope_depth s).
Definition freeze_with (s : witness) (f : flash) : witness :=
  Witness f true (boot_ready s) None (acks s) (held s) (scope_depth s).
Definition acknowledge (s : witness) (a : N) : witness :=
  Witness (image s) false (boot_ready s) None (a :: acks s) (held s)
    (scope_depth s).
Definition reset_to_boot (s : witness) (f : flash) : witness :=
  Witness f false false None (acks s) [] 0.
Definition close_scope (s : witness) : witness :=
  Witness (image s) (frozen s) (boot_ready s) (pending_ack s)
    (acks s) (held s) (Nat.pred (scope_depth s)).

(* This is the *observable boot certificate* required before a new append.
   Deriving it from every concrete Rust recovery path is a separate obligation. *)
Definition recovered (boss_ok : N -> bool) (data_len page : N)
    (sector : nat) (s : witness) (a : N) : Prop :=
  (exists index,
    latest_in_model boss_ok data_len page
      (sector_bytes (image s) 0 sector) = Some (index, a)) /\
  (forall i, i < sector -> image s (sector+i) = 255%N).

(* The final page program and readback are distinguished from intermediate
   copy/restore calls. The Rust-to-[final_program_ok] bridge must show that
   this particular successful write is the append's last operation. *)
Inductive normal_step (g : geometry) (boss_ok : N -> bool)
    (data_len page : N) (sector : nat) : witness -> witness -> Prop :=
| program_ok s addr data after :
    frozen s = false ->
    program_step g (image s) addr data Success after ->
    normal_step g boss_ok data_len page sector s (set_image s after)
| program_error s addr data after :
    frozen s = false ->
    program_step g (image s) addr data VerifyFailed after ->
    normal_step g boss_ok data_len page sector s (freeze_with s after)
| program_readback_error s addr data after :
    frozen s = false ->
    program_step g (image s) addr data Success after ->
    normal_step g boss_ok data_len page sector s (freeze_with s after)
| erase_ok s addr after :
    frozen s = false ->
    erase_step g (image s) addr Success after ->
    normal_step g boss_ok data_len page sector s (set_image s after)
| erase_error s addr after :
    frozen s = false ->
    erase_step g (image s) addr VerifyFailed after ->
    normal_step g boss_ok data_len page sector s (freeze_with s after)
| final_program_ok s addr data after a :
    frozen s = false -> boot_ready s = true ->
    program_step g (image s) addr data Success after ->
    normal_step g boss_ok data_len page sector s (set_pending s after a)
| append_ack s a :
    frozen s = false -> boot_ready s = true ->
    pending_ack s = Some a ->
    normal_step g boss_ok data_len page sector s (acknowledge s a)
| recovery_complete s a :
    frozen s = false -> boot_ready s = false ->
    recovered boss_ok data_len page sector s a ->
    normal_step g boss_ok data_len page sector s
      (Witness (image s) false true None (acks s) (held s)
        (scope_depth s))
| rejected_before_physical s :
    normal_step g boss_ok data_len page sector s s
| blocked_journal_call s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s s
| blocked_physical_call s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s s
| blocked_allocation s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s s
| close_ram_scope_while_frozen s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s (close_scope s)
| skip_collect_while_frozen s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s s
| retain_unattached_while_frozen s :
    frozen s = true ->
    normal_step g boss_ok data_len page sector s s.

(* Reset abandons the continuation. It clears only volatile control state;
   the reached flash is whatever the lower relation permits. *)
Inductive interrupt_step (g : geometry) : witness -> witness -> Prop :=
| reset_between_calls s :
    interrupt_step g s (reset_to_boot s (image s))
| reset_during_program s addr data after :
    frozen s = false ->
    program_step g (image s) addr data Reset after ->
    interrupt_step g s (reset_to_boot s after)
| reset_during_erase s addr after :
    frozen s = false ->
    erase_step g (image s) addr Reset after ->
    interrupt_step g s (reset_to_boot s after).

Theorem returned_program_error_freezes g boss_ok data_len page sector
    s addr data after :
  frozen s = false ->
  program_step g (image s) addr data VerifyFailed after ->
  normal_step g boss_ok data_len page sector s (freeze_with s after) /\
  frozen (freeze_with s after) = true.
Proof.
  intros Hfree Hstep. split; [eapply program_error; eauto|reflexivity].
Qed.

Theorem physically_complete_program_error_still_freezes g boss_ok data_len
    page sector s addr data after :
  frozen s = false ->
  program_step g (image s) addr data Success after ->
  normal_step g boss_ok data_len page sector s (freeze_with s after) /\
  image (freeze_with s after) = after /\
  pending_ack (freeze_with s after) = None.
Proof.
  intros Hfree Hsuccess. split.
  - eapply program_error; [exact Hfree|].
    eapply program_completed_can_return_verify_failed; eauto.
  - split; reflexivity.
Qed.

Theorem completed_program_readback_error_freezes g boss_ok data_len page sector
    s addr data after :
  frozen s = false ->
  program_step g (image s) addr data Success after ->
  normal_step g boss_ok data_len page sector s (freeze_with s after) /\
  image (freeze_with s after) = after /\
  frozen (freeze_with s after) = true.
Proof.
  intros Hfree Hstep. split.
  - eapply program_readback_error; eauto.
  - split; reflexivity.
Qed.

Theorem returned_erase_error_freezes g boss_ok data_len page sector
    s addr after :
  frozen s = false ->
  erase_step g (image s) addr VerifyFailed after ->
  normal_step g boss_ok data_len page sector s (freeze_with s after) /\
  frozen (freeze_with s after) = true.
Proof.
  intros Hfree Hstep. split; [eapply erase_error; eauto|reflexivity].
Qed.

Theorem frozen_step_has_no_flash_or_allocation_effect g boss_ok data_len page
    sector s s' :
  frozen s = true ->
  normal_step g boss_ok data_len page sector s s' ->
  frozen s' = true /\ image s' = image s /\
  held s' = held s /\ acks s' = acks s.
Proof.
  intros Hf Hstep. inversion Hstep; subst; simpl in *;
    try congruence; repeat split; try exact Hf; reflexivity.
Qed.

Theorem frozen_scope_close_keeps_reservations s :
  frozen s = true ->
  scope_depth (close_scope s) = Nat.pred (scope_depth s) /\
  held (close_scope s) = held s /\
  image (close_scope s) = image s.
Proof. intro Hf. repeat split; reflexivity. Qed.

Theorem frozen_finite_trace_cannot_ack g boss_ok data_len page sector s s' :
  frozen s = true ->
  clos_refl_trans witness (normal_step g boss_ok data_len page sector) s s' ->
  frozen s' = true /\ image s' = image s /\
  held s' = held s /\ acks s' = acks s.
Proof.
  intros Hf Htrace. induction Htrace.
  - exact (frozen_step_has_no_flash_or_allocation_effect _ _ _ _ _ _ _
      Hf H).
  - repeat split; try exact Hf; reflexivity.
  - destruct (IHHtrace1 Hf) as [Hmid [Hflash [Hheld Hacks]]].
    destruct (IHHtrace2 Hmid) as [Hend [Hflash' [Hheld' Hacks']]].
    repeat split; try exact Hend; congruence.
Qed.

Theorem reset_requires_recovery_before_ack s :
  boot_ready (reset_to_boot s (image s)) = false /\
  frozen (reset_to_boot s (image s)) = false /\
  pending_ack (reset_to_boot s (image s)) = None /\
  image (reset_to_boot s (image s)) = image s /\
  acks (reset_to_boot s (image s)) = acks s.
Proof. repeat split; reflexivity. Qed.

Theorem only_recovery_sets_boot_ready g boss_ok data_len page sector s s' :
  normal_step g boss_ok data_len page sector s s' ->
  boot_ready s = false -> boot_ready s' = true ->
  exists a, recovered boss_ok data_len page sector s a.
Proof.
  intros Hstep Hpending Hready.
  inversion Hstep; subst; simpl in *; try congruence.
  eauto.
Qed.

Theorem boot_pending_step_cannot_ack g boss_ok data_len page sector s s' :
  normal_step g boss_ok data_len page sector s s' ->
  boot_ready s = false -> acks s' = acks s.
Proof.
  intros Hstep Hpending.
  inversion Hstep; subst; simpl in *; try congruence; reflexivity.
Qed.

Definition waiting_step g boss_ok data_len page sector s s' :=
  normal_step g boss_ok data_len page sector s s' /\
  boot_ready s = false /\ boot_ready s' = false.

Theorem repeated_boot_interruptions_cannot_ack g boss_ok data_len page sector
    s s' :
  clos_refl_trans witness (waiting_step g boss_ok data_len page sector) s s' ->
  acks s' = acks s.
Proof.
  intro Htrace. induction Htrace.
  - destruct H as [Hstep [Hpending _]].
    eapply boot_pending_step_cannot_ack; eauto.
  - reflexivity.
  - congruence.
Qed.

Definition stale_before_failure : witness :=
  Witness stale_after_error_flash false true None [stale_A] [8;9] 1.
Definition stale_after_failure :=
  freeze_with stale_before_failure stale_after_error_flash.

Theorem stale_secondary_failure_freezes :
  normal_step stale_geometry stale_boss_ok 704%N 64%N stale_sector
    stale_before_failure stale_after_failure.
Proof.
  unfold stale_after_failure, stale_before_failure.
  eapply erase_error with (addr:=stale_sector); [reflexivity|].
  apply stale_secondary_erase_may_fail_without_effect.
  exact stale_after_error_valid.
Qed.

Theorem old_D_after_error_is_excluded s :
  clos_refl_trans witness
    (normal_step stale_geometry stale_boss_ok 704%N 64%N stale_sector)
    stale_after_failure s ->
  image s = stale_after_error_flash /\
  acks s = [stale_A] /\
  held s = [8;9] /\
  frozen s = true.
Proof.
  intro Htrace.
  assert (Hfrozen : frozen stale_after_failure = true) by reflexivity.
  pose proof (frozen_finite_trace_cannot_ack _ _ _ _ _ _ _
    Hfrozen Htrace) as [Hf [Hflash [Hheld Hacks]]].
  repeat split; simpl in *; try exact Hf; congruence.
Qed.
