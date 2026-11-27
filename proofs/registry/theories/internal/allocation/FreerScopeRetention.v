From Stdlib Require Import List Arith Lia.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import PageOwnership RetentionCoverage ScopeOwnership
  FlashSpec FreerFlash FreerRetention.
Import ListNotations.

Inductive ScopePagesAPI : interface :=
| FinishPages : nat -> bool -> ScopePagesAPI unit.
Definition scope_pages_caller (t : page_table) (A : Type) (e : ScopePagesAPI A) :=
  match e with FinishPages d _ => 1 <= d <= 6 end.
Definition scope_pages_callee (t : page_table) (A : Type)
    (e : ScopePagesAPI A) (reply : A) : Prop := True.
Definition scope_pages_update (t : page_table) (A : Type)
    (e : ScopePagesAPI A) (reply : A) : page_table :=
  match e with FinishPages d accept => finish_table d accept t end.
Definition scope_pages_contract : contract ScopePagesAPI page_table :=
  make_contract scope_pages_update scope_pages_caller scope_pages_callee.
Definition close_pages d accept : impure ScopePagesAPI unit :=
  request_then (FinishPages d accept) (fun _ => local tt).
Theorem close_pages_post d accept t t' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure ScopePagesAPI)
    scope_pages_contract (close_pages d accept)) t tt t' ->
  t' = finish_table d accept t.
Proof.
  intro H. unfold close_pages in H. unroll_post H.
  destruct H0 as [middle [Hfinish Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure ScopePagesAPI)
    scope_pages_contract (local tt)) middle tt t') in Hlocal.
  unroll_post Hlocal. subst. reflexivity.
Qed.
Theorem close_pages_caller_from_invariant page cur views saved base t accept :
  scope_invariant page (Build_scope_state cur (views ++ [saved]) base t) ->
  scope_pages_caller t _ (FinishPages (S (length views)) accept).
Proof.
  intros [D _]. unfold scope_pages_caller. simpl in D.
  rewrite length_app in D; simpl in D. unfold DeferredSnapshots.max_depth in D; lia.
Qed.
Theorem composed_rollback_preserves_prestate page views saved t t' :
  stack_bounded page (views ++ [saved]) t ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure ScopePagesAPI)
    scope_pages_contract (close_pages (S (length views)) false)) t tt t' ->
  bounded page saved (S (length views)) t'.
Proof. intros B H. apply close_pages_post in H. subst. apply rollback_restores_prestate; exact B. Qed.
Theorem composed_reachable_scope_erase g page start finish f f' a result :
  page > 0 -> scope_invariant page start -> retention_trace page start finish ->
  free_range page (scope_pages finish) {| offset := a; span := sector_size g |} ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (erase_reserved_sector a)) f result f' ->
  unchanged (surviving_ranges finish) f f'.
Proof.
  intros P I T F H. apply erase_reserved_sector_post in H.
  eapply reachable_retention_erase_preserves; eauto. exact (proj1 H).
Qed.
