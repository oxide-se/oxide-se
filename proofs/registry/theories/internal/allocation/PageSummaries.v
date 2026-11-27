From Coq Require Import Arith Bool Lia List.
From OxideSE.Registry Require Import PageOwnership RetentionCoverage ScopeOwnership.

Definition set_summary (bits : nat -> bool) d :=
  fun k => if k =? d then true else bits k.
Definition close_summary (bits : nat -> bool) d accept :=
  fun k => if accept && (k =? d-1) then true
           else if k =? d then false else bits k.

Theorem reserve_summary_sound page r depth t bits :
  summary_sound bits t ->
  summary_sound (set_summary bits depth) (reserve_extent page r depth t).
Proof.
  intros H d p D O. unfold reserve_extent in O. unfold set_summary.
  destruct (touches page r p) eqn:E; simpl in O.
  - inversion O; subst. rewrite Nat.eqb_refl; reflexivity.
  - destruct (d =? depth); [reflexivity|eapply H; eauto].
Qed.
Theorem rehome_summary_sound page r depth t bits :
  summary_sound bits t ->
  summary_sound (set_summary bits depth) (rehome_extent page r depth t).
Proof.
  intros H d p D O. unfold rehome_extent in O. unfold set_summary.
  destruct (touches page r p) eqn:E; simpl in O.
  - inversion O; subst. rewrite Nat.eqb_refl; reflexivity.
  - destruct (d =? depth); [reflexivity|eapply H; eauto].
Qed.
Theorem release_summary_sound page r t bits :
  summary_sound bits t -> summary_sound bits (release_extent page r t).
Proof.
  intros H d p D O. unfold release_extent in O.
  destruct (touches page r p); simpl in O; [discriminate|eapply H; eauto].
Qed.
Theorem close_summary_sound depth accept t bits :
  0 < depth -> summary_sound bits t ->
  summary_sound (close_summary bits depth accept) (finish_table depth accept t).
Proof.
  intros L H d p D O. unfold finish_table in O. unfold close_summary.
  destruct (owner (t p) =? S depth) eqn:E.
  - destruct accept; simpl in O; [|discriminate].
    assert (K : d = depth - 1) by lia. rewrite K, Nat.eqb_refl. reflexivity.
  - destruct (accept && (d =? depth-1)); [reflexivity|].
    destruct (d =? depth) eqn:K.
    + apply Nat.eqb_eq in K; subst. apply Nat.eqb_neq in E. contradiction.
    + eapply H; eauto.
Qed.
Theorem collect_summary_sound page ranges t :
  summary_sound (fun _ => false) (collect_table page ranges t).
Proof.
  intros d p D O. unfold collect_table in O.
  destruct (marked page ranges p); simpl in O; lia.
Qed.

(* collection_needed is a conservative dirty flag. Its useful negative
   observation is that the table was last installed by a complete collection
   and no allocation/reference edit has happened since. It is not a claim
   that no scoped owner exists: rehome does not set this flag in Rust. *)
Record summary_witness := {
  summary_table : page_table;
  scope_bits : nat -> bool;
  collection_flag : bool
}.
Inductive summary_step page : summary_witness -> summary_witness -> Prop :=
| summary_reserve t bits dirty r depth :
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness (reserve_extent page r depth t) (set_summary bits depth) true)
| summary_rehome t bits dirty r depth :
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness (rehome_extent page r depth t) (set_summary bits depth) dirty)
| summary_release t bits dirty r :
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness (release_extent page r t) bits dirty)
| summary_close t bits dirty depth accept : 0 < depth ->
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness (finish_table depth accept t) (close_summary bits depth accept) dirty)
| summary_collect t bits dirty ranges :
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness (collect_table page ranges t) (fun _ => false) false)
| summary_changed t bits dirty :
    summary_step page (Build_summary_witness t bits dirty)
      (Build_summary_witness t bits true).
Theorem summary_step_sound page s s' :
  summary_sound (scope_bits s) (summary_table s) -> summary_step page s s' ->
  summary_sound (scope_bits s') (summary_table s').
Proof.
  intros I S. destruct S; simpl in *;
    eauto using reserve_summary_sound, rehome_summary_sound, release_summary_sound,
      close_summary_sound, collect_summary_sound.
Qed.
Inductive summary_trace page : summary_witness -> summary_witness -> Prop :=
| summary_refl s : summary_trace page s s
| summary_cons s m last : summary_step page s m -> summary_trace page m last -> summary_trace page s last.
Theorem finite_summary_trace_sound page s s' :
  summary_sound (scope_bits s) (summary_table s) -> summary_trace page s s' ->
  summary_sound (scope_bits s') (summary_table s').
Proof.
  intros I T. induction T; [exact I|]. apply IHT. eapply summary_step_sound; eauto.
Qed.

(* pages.rs skips both the scan and summary writes when the closing bit is
   absent. Keep that branch exact, including conservative parent bits. *)
Definition finish_summary (bits : nat -> bool) depth accept :=
  if bits depth then close_summary bits depth accept else bits.
Theorem finish_summary_sound depth accept t bits :
  0 < depth -> summary_sound bits t ->
  summary_sound (finish_summary bits depth accept) (finish_table depth accept t).
Proof.
  intros D H. unfold finish_summary. destruct (bits depth) eqn:B.
  - apply close_summary_sound; assumption.
  - intros d p L O. unfold finish_table in O.
    destruct (owner (t p) =? S depth) eqn:E.
    + apply Nat.eqb_eq in E. specialize (H depth p D E). congruence.
    + eapply H; eauto.
Qed.
