From Coq Require Import List Arith Bool Lia.
From OxideSE.Registry Require Import FlashSpec PageOwnership RetentionCoverage DeferredSnapshots.
Import ListNotations.

(* pages.rs::finish_scope, before the conservative owned_scopes shortcut.
   Authentication is independent of ownership. *)
Definition finish_table (depth : nat) (accept : bool) (t : page_table) : page_table :=
  fun p => if owner (t p) =? S depth
           then if accept then {| owner := depth; validated := validated (t p) |}
                else free_cell
           else t p.
Definition bounded page ranges limit t :=
  forall p, needed page ranges p -> 0 < owner (t p) <= limit.
Definition stack_bounded page (views : list (list extent)) t :=
  forall i v, nth_error views i = Some v -> bounded page v (S i) t.

Lemma bounded_protected page ranges n t :
  bounded page ranges n t -> protected (needed page ranges) t.
Proof. intros H p N. specialize (H p N); lia. Qed.
Lemma bounded_weaken page ranges n m t :
  n <= m -> bounded page ranges n t -> bounded page ranges m t.
Proof. intros L H p N. specialize (H p N); lia. Qed.
Lemma finish_ancestor_unchanged depth accept t p :
  owner (t p) <= depth -> finish_table depth accept t p = t p.
Proof.
  intros B. unfold finish_table. destruct (owner (t p) =? S depth) eqn:E;
    [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.
Lemma finish_preserves_ancestor page ranges n depth accept t :
  n <= depth -> bounded page ranges n t ->
  bounded page ranges n (finish_table depth accept t).
Proof.
  intros L H p N. specialize (H p N).
  rewrite finish_ancestor_unchanged; [exact H|lia].
Qed.
Lemma accept_rehomes_current page ranges depth t :
  0 < depth -> bounded page ranges (S depth) t ->
  bounded page ranges depth (finish_table depth true t).
Proof.
  intros D H p N. specialize (H p N). unfold finish_table.
  destruct (owner (t p) =? S depth) eqn:E; simpl; [lia|].
  apply Nat.eqb_neq in E; lia.
Qed.
Lemma stack_push page views current t :
  stack_bounded page views t -> bounded page current (S (length views)) t ->
  stack_bounded page (views ++ [current]) t.
Proof.
  intros S C i v E. unfold stack_bounded in S.
  destruct (Nat.lt_ge_cases i (length views)) as [L|L].
  - rewrite nth_error_app1 in E by exact L. eauto.
  - rewrite nth_error_app2 in E by exact L.
    destruct (i - length views) eqn:K; simpl in E; [|destruct n; discriminate].
    inversion E; subst. replace i with (length views) by lia. exact C.
Qed.

(* Pop the last boundary only. Its prestate belongs at most to owner depth,
   whereas rollback releases owner depth+1. This derives the non-release
   property, rather than assuming the released pages have no surviving roots. *)
Theorem rollback_restores_prestate page views saved t :
  stack_bounded page (views ++ [saved]) t ->
  bounded page saved (S (length views))
    (finish_table (S (length views)) false t).
Proof.
  intros H. apply finish_preserves_ancestor; [lia|].
  apply (H (length views)). rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag; reflexivity.
Qed.
Theorem close_preserves_remaining_boundaries page views saved t accept :
  stack_bounded page (views ++ [saved]) t ->
  stack_bounded page views (finish_table (S (length views)) accept t).
Proof.
  intros H i v E. apply finish_preserves_ancestor.
  - apply nth_error_Some in E || idtac.
    assert (i < length views).
    { apply nth_error_Some. rewrite E; discriminate. } lia.
  - apply (H i). rewrite nth_error_app1; [exact E|].
    apply nth_error_Some. rewrite E; discriminate.
Qed.
Theorem accept_child_preserves_parent_rollback page views parent child t :
  stack_bounded page (views ++ [parent; child]) t ->
  bounded page parent (S (length views))
    (finish_table (S (length views)) false
      (finish_table (length (views ++ [parent; child])) true t)).
Proof.
  intros HS. apply rollback_restores_prestate.
  replace (views ++ [parent; child]) with ((views ++ [parent]) ++ [child]) in HS
    by (rewrite <- app_assoc; reflexivity).
  pose proof (close_preserves_remaining_boundaries page (views ++ [parent]) child t true HS) as H.
  rewrite !length_app in *; simpl in *.
  replace (length views + 2) with (S (length views + 1)) by lia.
  exact H.
Qed.

(* Reserve is a two-pass check in Rust: no owner is changed on rejection. *)
Definition reserve_extent page r depth (t : page_table) : page_table :=
  fun p => if touches page r p then {| owner := S depth; validated := false |} else t p.
Definition rehome_extent page r depth (t : page_table) : page_table :=
  fun p => if touches page r p then {| owner := S depth; validated := validated (t p) |} else t p.
Lemma reserve_preserves_bounds page ranges r depth n t :
  free_range page t r -> bounded page ranges n t ->
  bounded page ranges n (reserve_extent page r depth t).
Proof.
  intros F H p N. specialize (H p N). unfold reserve_extent.
  destruct (touches page r p) eqn:E; [specialize (F p E); lia|exact H].
Qed.
Lemma reservation_has_current_owner page r depth t :
  bounded page [r] (S depth) (reserve_extent page r depth t).
Proof.
  intros p [v [[V|[]] E]]. subst v. unfold reserve_extent. rewrite E; simpl; lia.
Qed.
Lemma lower_owner_preserves_bounds page ranges r depth n t :
  bounded page ranges n t ->
  (forall p, touches page r p = true -> S depth <= owner (t p)) ->
  bounded page ranges n (rehome_extent page r depth t).
Proof.
  intros H L p N. specialize (H p N). unfold rehome_extent.
  destruct (touches page r p) eqn:E; [specialize (L p E); simpl; lia|exact H].
Qed.

(* first_unresolved in DeferredSnapshots is the Rust zero-based index. *)
Lemma first_unresolved_le_none rs i :
  nth_error rs i = Some None -> first_unresolved rs <= i.
Proof.
  revert i. induction rs as [|[r|] rs IH]; intros [|i] E; simpl in *;
    try discriminate; try lia. apply IH in E; lia.
Qed.
Theorem materialized_shared_boss_survives_each_rollback page rs i r t :
  nth_error rs i = Some None ->
  bounded page [r] (S i) (rehome_extent page r (snapshot_owner rs) t).
Proof.
  intros E p [v [[V|[]] T]]. subst v.
  unfold rehome_extent. rewrite T; simpl.
  pose proof (first_unresolved_le_none rs i E).
  unfold snapshot_owner. split; [lia|].
  pose proof (Nat.le_min_l (first_unresolved rs) (length rs)); lia.
Qed.

(* Summary bits only skip a scan when there are no corresponding owners. *)
Definition summary_sound (bits : nat -> bool) (t : page_table) :=
  forall d p, 0 < d -> owner (t p) = S d -> bits d = true.
Theorem absent_summary_scan_is_identity bits t depth accept :
  0 < depth -> summary_sound bits t -> bits depth = false ->
  forall p, finish_table depth accept t p = t p.
Proof.
  intros D H B p. unfold finish_table. destruct (owner (t p) =? S depth) eqn:E;
    [apply Nat.eqb_eq in E; specialize (H depth p D E); congruence|reflexivity].
Qed.

Example child_accept_parent_rollback_example :
  let t := fun p => {| owner := if p =? 1 then 1 else if p =? 2 then 2 else 3;
                       validated := false |} in
  owner (finish_table 1 false (finish_table 2 true t) 1) = 1 /\
  owner (finish_table 1 false (finish_table 2 true t) 2) = 0 /\
  owner (finish_table 1 false (finish_table 2 true t) 3) = 0.
Proof. vm_compute; auto. Qed.

Lemma bounded_union page xs ys n t :
  bounded page xs n t -> bounded page ys n t -> bounded page (xs ++ ys) n t.
Proof.
  intros X Y p [r [I T]]. apply in_app_or in I. destruct I as [I|I];
    [apply X|apply Y]; exists r; auto.
Qed.
Lemma bounded_subset page xs ys n t :
  (forall r, In r xs -> In r ys) -> bounded page ys n t -> bounded page xs n t.
Proof. intros S H p [r [I T]]. apply H. exists r; auto. Qed.

(* A newly reserved range cannot alias any already necessary extent. The
   condition for releasing an unattached allocation is derived at reservation
   time, then preserved while it remains unattached. *)
Definition apart page xs r := forall p, needed page xs p -> touches page r p = false.
Definition release_extent page r (t : page_table) : page_table :=
  fun p => if touches page r p then free_cell else t p.
Lemma fresh_reservation_apart page xs n t r :
  bounded page xs n t -> free_range page t r -> apart page xs r.
Proof.
  intros B F p N. destruct (touches page r p) eqn:E; [|reflexivity].
  specialize (B p N); specialize (F p E); lia.
Qed.
Lemma release_unattached_preserves_bounds page xs n t r :
  bounded page xs n t -> apart page xs r ->
  bounded page xs n (release_extent page r t).
Proof.
  intros B A p N. unfold release_extent. rewrite (A p N). apply B; exact N.
Qed.

(* An ownership spine records physical dependencies, not logical object values.
   saved views are ghost observations of each rollback prestate. Materializing
   a BOSS is dealt with separately below; ordinary edits never free old pages. *)
Record scope_state := {
  current_ranges : list extent;
  saved_ranges : list (list extent);
  base_ranges : list extent;
  scope_pages : page_table
}.
Definition scope_invariant page s :=
  length (saved_ranges s) <= max_depth /\
  bounded page (current_ranges s) (S (length (saved_ranges s))) (scope_pages s) /\
  stack_bounded page (saved_ranges s) (scope_pages s) /\
  bounded page (base_ranges s) 1 (scope_pages s).

Inductive scope_step page : scope_state -> scope_state -> Prop :=
| begin_step cur views base t : length views < max_depth ->
    scope_step page (Build_scope_state cur views base t)
      (Build_scope_state cur (views ++ [cur]) base t)
| reserve_attach_step cur views base t r : free_range page t r ->
    scope_step page (Build_scope_state cur views base t)
      (Build_scope_state (r :: cur) views base (reserve_extent page r (length views) t))
| edit_step cur next views base t :
    (forall r, In r next -> In r cur) ->
    scope_step page (Build_scope_state cur views base t)
      (Build_scope_state next views base t)
| accept_step cur views saved base t :
    scope_step page (Build_scope_state cur (views ++ [saved]) base t)
      (Build_scope_state cur views base (finish_table (S (length views)) true t))
| rollback_step cur views saved base t :
    scope_step page (Build_scope_state cur (views ++ [saved]) base t)
      (Build_scope_state saved views base (finish_table (S (length views)) false t)).

Theorem scope_step_inductive page s s' :
  scope_invariant page s -> scope_step page s s' -> scope_invariant page s'.
Proof.
  intros INV STEP. destruct STEP; destruct INV as [D [C [B A]]]; simpl in *.
  - unfold scope_invariant; simpl. split; [rewrite length_app; simpl; lia|].
    split; [|split].
    + eapply bounded_weaken; [|exact C]. rewrite length_app; simpl; lia.
    + apply stack_push; assumption.
    + exact A.
  - unfold scope_invariant; simpl. split; [exact D|]. split; [|split].
    + change (bounded page ([r] ++ cur) (S (length views))
        (reserve_extent page r (length views) t)).
      apply bounded_union; [apply reservation_has_current_owner|].
      apply reserve_preserves_bounds; assumption.
    + intros i v E. apply reserve_preserves_bounds; [assumption|eapply B; eauto].
    + apply reserve_preserves_bounds; assumption.
  - unfold scope_invariant; simpl. split; [exact D|]. split; [|split; assumption].
    eapply bounded_subset; eauto.
  - rewrite length_app in *; simpl in *.
    unfold scope_invariant; simpl. split; [lia|]. split; [|split].
    + apply accept_rehomes_current; [lia|].
      replace (S (S (length views))) with (S (length views + 1)) by lia. exact C.
    + eapply close_preserves_remaining_boundaries; exact B.
    + apply finish_preserves_ancestor; [lia|exact A].
  - rewrite length_app in *; simpl in *.
    unfold scope_invariant; simpl. split; [lia|]. split; [|split].
    + eapply rollback_restores_prestate; exact B.
    + eapply close_preserves_remaining_boundaries; exact B.
    + apply finish_preserves_ancestor; [lia|exact A].
Qed.
Inductive scope_trace page : scope_state -> scope_state -> Prop :=
| scopes_refl s : scope_trace page s s
| scopes_cons s middle last : scope_step page s middle ->
    scope_trace page middle last -> scope_trace page s last.
Theorem finite_scope_trace_inductive page s s' :
  scope_invariant page s -> scope_trace page s s' -> scope_invariant page s'.
Proof. intros I T. induction T; [exact I|]. apply IHT. eapply scope_step_inductive; eauto. Qed.

Definition surviving_ranges s :=
  current_ranges s ++ flat_map (fun x => x) (saved_ranges s) ++ base_ranges s.
Theorem scope_invariant_covers_survivors page s :
  scope_invariant page s -> protected (needed page (surviving_ranges s)) (scope_pages s).
Proof.
  intros [_ [C [B A]]] p [r [I T]]. unfold surviving_ranges in I.
  apply in_app_or in I; destruct I as [I|I].
  - apply (bounded_protected _ _ _ _ C p). exists r; auto.
  - apply in_app_or in I; destruct I as [I|I].
    + apply in_flat_map in I. destruct I as [v [V I]].
      apply In_nth_error in V. destruct V as [i E].
      apply (bounded_protected _ _ _ _ (B i v E) p). exists r; auto.
    + apply (bounded_protected _ _ _ _ A p). exists r; auto.
Qed.
Theorem reachable_scope_erase_preserves g page start finish f f' a result :
  page > 0 -> scope_invariant page start -> scope_trace page start finish ->
  free_range page (scope_pages finish) {| offset := a; span := sector_size g |} ->
  erase_step g f a result f' -> unchanged (surviving_ranges finish) f f'.
Proof.
  intros. eapply erase_preserves_covered_ranges; eauto.
  apply scope_invariant_covers_survivors.
  eapply finite_scope_trace_inductive; eauto.
Qed.

Lemma repeated_view_nth A (x : A) n i y :
  nth_error (repeat x n) i = Some y -> y = x /\ i < n.
Proof.
  revert i. induction n as [|n IH]; intros [|i] E; simpl in E; try discriminate.
  - inversion E; subst. split; [reflexivity|lia].
  - apply IH in E; destruct E as [Y L]. split; [exact Y|lia].
Qed.
Lemma first_deferred_bound page prefix cur count t :
  count > 0 -> stack_bounded page (prefix ++ repeat cur count) t ->
  bounded page cur (S (length prefix)) t.
Proof.
  intros P B. apply (B (length prefix)). rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag. destruct count; [lia|reflexivity].
Qed.
Theorem shared_snapshot_stack_bound page prefix cur count t r :
  count > 0 -> stack_bounded page (prefix ++ repeat cur count) t ->
  free_range page t r ->
  stack_bounded page (prefix ++ repeat (r :: cur) count)
    (reserve_extent page r (length prefix) t).
Proof.
  intros P B F i v E.
  destruct (Nat.lt_ge_cases i (length prefix)) as [L|L].
  - rewrite nth_error_app1 in E by exact L.
    apply reserve_preserves_bounds; [exact F|].
    apply (B i). rewrite nth_error_app1 by exact L; exact E.
  - rewrite nth_error_app2 in E by exact L.
    apply repeated_view_nth in E. destruct E as [-> I].
    change (bounded page ([r] ++ cur) (S i) (reserve_extent page r (length prefix) t)).
    apply bounded_union.
    + eapply bounded_weaken; [|apply reservation_has_current_owner]; lia.
    + apply reserve_preserves_bounds; [exact F|].
      eapply bounded_weaken; [|eapply first_deferred_bound; eauto]; lia.
Qed.
Definition materialized_state page cur prefix count base t r :=
  Build_scope_state (r :: cur) (prefix ++ repeat (r :: cur) count) base
    (reserve_extent page r (length prefix) t).

Theorem shared_snapshot_inductive page cur prefix count base t r :
  count > 0 ->
  scope_invariant page (Build_scope_state cur (prefix ++ repeat cur count) base t) ->
  free_range page t r ->
  scope_invariant page (materialized_state page cur prefix count base t r).
Proof.
  intros P [D [C [B A]]] F. unfold materialized_state, scope_invariant; simpl in *.
  split.
  - rewrite !length_app, !repeat_length in *; exact D.
  - split; [|split].
    + change (bounded page ([r] ++ cur) (S (length (prefix ++ repeat (r :: cur) count)))
        (reserve_extent page r (length prefix) t)).
      apply bounded_union.
      * eapply bounded_weaken; [|apply reservation_has_current_owner].
        rewrite length_app, repeat_length; lia.
      * apply reserve_preserves_bounds; [exact F|].
        rewrite !length_app, !repeat_length in *; exact C.
    + apply shared_snapshot_stack_bound; assumption.
    + apply reserve_preserves_bounds; assumption.
Qed.

Lemma reserve_then_rehome_is_direct page r depth lifetime t p :
  rehome_extent page r lifetime (reserve_extent page r depth t) p =
  reserve_extent page r lifetime t p.
Proof. unfold rehome_extent, reserve_extent. destruct (touches page r p); reflexivity. Qed.

(* Logical graph at normal external close: no rollback boundary remains.
   base is marker / pending LOAD / durable closure. The concrete collect guard
   must identify durable with current before using only the latter's entries. *)
Theorem external_close_enumeration_complete cur base t :
  surviving_ranges (Build_scope_state cur [] base t) = cur ++ base.
Proof. reflexivity. Qed.
Theorem external_collect_inductive page cur base t :
  scope_invariant page (Build_scope_state cur [] base
    (collect_table page (cur ++ base) t)).
Proof.
  unfold scope_invariant; simpl. split; [unfold max_depth; lia|].
  assert (ALL : bounded page (cur ++ base) 1 (collect_table page (cur ++ base) t)).
  { intros p N. apply marked_spec in N. unfold collect_table. rewrite N; simpl; lia. }
  split; [|split].
  - eapply bounded_subset; [|exact ALL]. intros; apply in_or_app; auto.
  - intros [|i] v E; discriminate.
  - eapply bounded_subset; [|exact ALL]. intros; apply in_or_app; auto.
Qed.

(* Frozen cleanup keeps the table, while dependency observers may be dropped
   from RAM. held is a ghost union taken before unwinding, including a candidate
   that the journal could already have published. *)
Record frozen_state := {
  frozen_current : list extent;
  frozen_saved : list (list extent);
  frozen_load : list extent;
  held_ranges : list extent;
  frozen_pages : page_table
}.
Definition frozen_invariant page s :=
  protected (needed page (held_ranges s)) (frozen_pages s).
Inductive frozen_cleanup : frozen_state -> frozen_state -> Prop :=
| close_frozen cur views saved load held t :
    frozen_cleanup (Build_frozen_state cur (views ++ [saved]) load held t)
      (Build_frozen_state saved views load held t)
| accept_frozen cur views saved load held t :
    frozen_cleanup (Build_frozen_state cur (views ++ [saved]) load held t)
      (Build_frozen_state cur views load held t)
| abandon_load_frozen cur views load held t :
    frozen_cleanup (Build_frozen_state cur views load held t)
      (Build_frozen_state cur views [] held t)
| begin_frozen cur views load held t : length views < max_depth ->
    frozen_cleanup (Build_frozen_state cur views load held t)
      (Build_frozen_state cur (views ++ [cur]) load held t)
| rejected_or_skipped_frozen s : frozen_cleanup s s.
Theorem frozen_cleanup_preserves_held page s s' :
  frozen_invariant page s -> frozen_cleanup s s' -> frozen_invariant page s'.
Proof. intros I H. destruct H; exact I. Qed.
Definition freeze_scope s := Build_frozen_state
  (current_ranges s) (saved_ranges s) [] (surviving_ranges s) (scope_pages s).
Theorem error_freeze_protects_possible_current_authority page s :
  scope_invariant page s -> frozen_invariant page (freeze_scope s).
Proof. apply scope_invariant_covers_survivors. Qed.

(* A failed preparation has reserved its destination but has not attached it.
   Its body may be partial or physically complete: coverage is identical. *)
Definition freeze_preparation page s r := Build_frozen_state
  (current_ranges s) (saved_ranges s) [] (r :: surviving_ranges s)
  (reserve_extent page r (length (saved_ranges s)) (scope_pages s)).
Theorem failed_preparation_freeze_covers_reservation page s r :
  scope_invariant page s -> free_range page (scope_pages s) r ->
  frozen_invariant page (freeze_preparation page s r).
Proof.
  intros INV F p [v [[V|I] T]].
  - subst v. unfold freeze_preparation; simpl. unfold reserve_extent. rewrite T; simpl; lia.
  - unfold freeze_preparation; simpl. unfold reserve_extent.
    destruct (touches page r p) eqn:E; simpl; [lia|].
    apply (scope_invariant_covers_survivors page s INV p). exists v; auto.
Qed.

Inductive retention_step page : scope_state -> scope_state -> Prop :=
| ordinary_scope s s' : scope_step page s s' -> retention_step page s s'
| save_shared cur prefix count base t r :
    count > 0 -> free_range page t r ->
    retention_step page (Build_scope_state cur (prefix ++ repeat cur count) base t)
      (materialized_state page cur prefix count base t r)
| collect_external cur base t :
    retention_step page (Build_scope_state cur [] base t)
      (Build_scope_state cur [] base (collect_table page (cur ++ base) t))
| reject_without_change s : retention_step page s s.
Theorem retention_step_inductive page s s' :
  scope_invariant page s -> retention_step page s s' -> scope_invariant page s'.
Proof.
  intros I S. destruct S.
  - eapply scope_step_inductive; eauto.
  - eapply shared_snapshot_inductive; eauto.
  - apply external_collect_inductive.
  - exact I.
Qed.
Inductive retention_trace page : scope_state -> scope_state -> Prop :=
| retention_refl s : retention_trace page s s
| retention_cons s middle last : retention_step page s middle ->
    retention_trace page middle last -> retention_trace page s last.
Theorem finite_retention_trace_inductive page s s' :
  scope_invariant page s -> retention_trace page s s' -> scope_invariant page s'.
Proof.
  intros I T. induction T; [exact I|]. apply IHT. eapply retention_step_inductive; eauto.
Qed.
Theorem reachable_retention_erase_preserves g page start finish f f' a result :
  page > 0 -> scope_invariant page start -> retention_trace page start finish ->
  free_range page (scope_pages finish) {| offset := a; span := sector_size g |} ->
  erase_step g f a result f' -> unchanged (surviving_ranges finish) f f'.
Proof.
  intros. eapply erase_preserves_covered_ranges; eauto.
  apply scope_invariant_covers_survivors.
  eapply finite_retention_trace_inductive; eauto.
Qed.

Inductive frozen_cleanup_trace : frozen_state -> frozen_state -> Prop :=
| frozen_refl s : frozen_cleanup_trace s s
| frozen_cons s middle last : frozen_cleanup s middle ->
    frozen_cleanup_trace middle last -> frozen_cleanup_trace s last.
Theorem finite_frozen_cleanup_keeps_possible_authority page s s' :
  frozen_invariant page s -> frozen_cleanup_trace s s' -> frozen_invariant page s'.
Proof.
  intros I T. induction T; [exact I|]. apply IHT.
  eapply frozen_cleanup_preserves_held; eauto.
Qed.
