From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* A pure fragment of snapshots.rs. Roots are optional because a new scope may
   share the current image until the first change. No flash call is modeled by
   begin or by the list update itself. *)
Definition max_depth := 6.
Definition roots := list (option nat).
Definition begin_scope (current : option nat) (rs : roots) : option roots :=
  if length rs <? max_depth then Some (rs ++ [current]) else None.
Definition resolve_root (saved : nat) (r : option nat) : option nat :=
  match r with None => Some saved | Some old => Some old end.
Definition before_change (saved : nat) (rs : roots) : roots :=
  map (resolve_root saved) rs.
Fixpoint first_unresolved (rs : roots) : nat :=
  match rs with
  | [] => 0
  | None :: _ => 0
  | Some _ :: tail => S (first_unresolved tail)
  end.
Definition snapshot_owner (rs : roots) : nat :=
  Nat.min (first_unresolved rs) (length rs).

Lemma begin_scope_length current rs next :
  begin_scope current rs = Some next -> length next = S (length rs) /\ length rs < max_depth.
Proof.
  unfold begin_scope. destruct (length rs <? max_depth) eqn:H; [|discriminate].
  intros E; inversion E; subst. rewrite length_app; simpl.
  apply Nat.ltb_lt in H. split; lia.
Qed.
Lemma seventh_scope_rejected current rs :
  length rs = max_depth -> begin_scope current rs = None.
Proof. intros H; unfold begin_scope; rewrite H; reflexivity. Qed.
Lemma before_change_length saved rs :
  length (before_change saved rs) = length rs.
Proof. apply length_map. Qed.
Lemma before_change_resolves saved rs i :
  nth_error rs i = Some None ->
  nth_error (before_change saved rs) i = Some (Some saved).
Proof.
  revert i. induction rs as [|r tail IH]; intros [|i] H; simpl in *;
    try discriminate.
  - inversion H; subst. reflexivity.
  - apply IH. exact H.
Qed.
Lemma before_change_keeps_materialized saved rs i old :
  nth_error rs i = Some (Some old) ->
  nth_error (before_change saved rs) i = Some (Some old).
Proof.
  revert i. induction rs as [|r tail IH]; intros [|i] H; simpl in *;
    try discriminate.
  - inversion H; subst. reflexivity.
  - apply IH. exact H.
Qed.
Lemma resolved_owner_is_depth saved rs :
  snapshot_owner (before_change saved rs) = length rs.
Proof.
  unfold snapshot_owner, before_change.
  induction rs as [|[old|] tail IH]; simpl; rewrite ?IH; lia.
Qed.

Example six_scopes_share_first_prestate :
  before_change 42 (repeat None max_depth) = repeat (Some 42) max_depth /\
  snapshot_owner (repeat None max_depth) = 0 /\
  begin_scope None (repeat None max_depth) = None.
Proof. vm_compute. auto. Qed.
Example accepted_child_still_has_parent_prestate :
  before_change 42 [None; None] = [Some 42; Some 42] /\
  hd None (before_change 42 [None; None]) = Some 42.
Proof. vm_compute. auto. Qed.
