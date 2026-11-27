From Coq Require Import List Arith Lia.
From OxideSE.Registry Require Import PageOwnership RetentionCoverage ScopeOwnership.
Import ListNotations.

(* Immutable decoded views of root identifiers, for one lifetime of the blocks.
   The agreement premise is a format/image relation, not a lifetime promise. *)
Section Roots.
Variable view : nat -> root_view.
Definition optional_root (id : option nat) : list extent :=
  match id with None => [] | Some r => root_extents (view r) end.
Definition optional_boss (id : option nat) : list extent :=
  match id with None => [] | Some r => [boss_extent (view r)] end.
Definition current_agrees (current : option nat) (entries : list extent) :=
  forall r, current = Some r -> entries = object_extents (view r).
Definition collect_guard (durable current : option nat) :=
  durable = None \/ durable = current.
Definition collect_ranges marker current entries load :=
  marker :: optional_boss current ++ entries ++ load.
Definition live_ranges marker durable current snapshots entries load :=
  marker :: optional_root durable ++ optional_root current ++
    flat_map (fun r => root_extents (view r)) snapshots ++ entries ++ load.

Theorem final_collection_enumerates_surviving_roots marker durable current entries load :
  collect_guard durable current -> current_agrees current entries ->
  forall r, In r (live_ranges marker durable current [] entries load) ->
    In r (collect_ranges marker current entries load).
Proof.
  intros G A r I. unfold collect_ranges, live_ranges in *; simpl in I.
  destruct G as [G|G]; rewrite G in *; destruct current as [id|]; simpl in *;
    try specialize (A id eq_refl); subst;
    unfold root_extents in *; simpl in *;
    repeat rewrite in_app_iff in *; try tauto.
  simpl in I. repeat rewrite in_app_iff in I. tauto.
Qed.

Theorem final_collection_covers_all_survivors page marker durable current entries load t :
  collect_guard durable current -> current_agrees current entries ->
  protected (needed page (live_ranges marker durable current [] entries load))
    (collect_table page (collect_ranges marker current entries load) t).
Proof.
  intros G A p [r [I T]]. apply collection_establishes_coverage.
  exists r. split; [eapply final_collection_enumerates_surviving_roots; eauto|exact T].
Qed.
Theorem final_collection_release_is_safe page marker durable current entries load t p :
  collect_guard durable current -> current_agrees current entries ->
  owner (collect_table page (collect_ranges marker current entries load) t p) = 0 ->
  ~ needed page (live_ranges marker durable current [] entries load) p.
Proof.
  intros G A F N. exact (final_collection_covers_all_survivors page marker durable current entries load t G A p N F).
Qed.
End Roots.
