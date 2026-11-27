From Coq Require Import List Arith Bool NArith Lia.
From OxideSE.Registry Require Import FlashSpec PageOwnership RetentionCoverage ScopeOwnership PageSummaries CollectionRoots DeferredRootMachine DeferredSnapshots CompactUpdates CompactImage.
Import ListNotations.

(* The preparation/publication interval consumes an established scope witness.
   Ancestors are observed from that witness, not an arbitrary held-page oracle.
   Writable rollback and collection are deliberately not edges here yet. *)
Inductive preparation_kind := ObjectPreparation | LoadPreparation | BossPreparation.
Inductive preparation_phase := Reserved | Written | Detached.
Record preparation := {
  prep_kind : preparation_kind;
  prep_range : extent;
  prep_phase : preparation_phase
}.
(* There is one table and one dependency stack. ScopeOwnership and
   PageSummaries observe them; neither stores a second mutable copy. *)
Record protection_state := ObservedProtectionState {
  protection_current : list extent;
  protection_saved : list (list extent);
  protection_base : list extent;
  attached_ranges : list extent;
  pending_preparation : option preparation;
  physical_authority : list extent;
  acknowledged_authority : list extent;
  protection_frozen : bool;
  protection_table : page_table;
  protection_bits : nat -> bool;
  protection_dirty : bool;
  (* Knowledge of the current Image scalar, not the persistence-runtime counter.
     Legacy state constructors intentionally forget this observation. *)
  protection_image_generation : option N
}.
Definition ProtectionState current saved base attached pending authority ack frozen table bits dirty :=
  ObservedProtectionState current saved base attached pending authority ack frozen table bits dirty None.
Definition image_generation_observe value s :=
  ObservedProtectionState (protection_current s) (protection_saved s) (protection_base s)
    (attached_ranges s) (pending_preparation s) (physical_authority s)
    (acknowledged_authority s) (protection_frozen s) (protection_table s)
    (protection_bits s) (protection_dirty s) value.
Definition image_generation_set next s := image_generation_observe (Some next) s.

Definition context_scopes s := Build_scope_state
  (protection_current s) (protection_saved s) (protection_base s) (protection_table s).
Definition summary_view s := Build_summary_witness
  (protection_table s) (protection_bits s) (protection_dirty s).
Definition Build_protection_state c extra pending authority ack frozen t bits dirty :=
  ProtectionState (current_ranges c) (saved_ranges c) (base_ranges c)
    extra pending authority ack frozen t bits dirty.
Lemma scope_table_is_shared s : scope_pages (context_scopes s) = protection_table s.
Proof. reflexivity. Qed.
Lemma summary_table_is_shared s : summary_table (summary_view s) = protection_table s.
Proof. reflexivity. Qed.
Definition context_ranges s := surviving_ranges (context_scopes s).
Definition pending_ranges s :=
  match pending_preparation s with None => [] | Some p => [prep_range p] end.
Definition required_ranges s := context_ranges s ++ attached_ranges s ++
  physical_authority s ++ acknowledged_authority s ++ pending_ranges s.
Definition protected_roots s := context_ranges s ++ attached_ranges s ++
  physical_authority s ++ acknowledged_authority s.
Definition preparation_invariant page s :=
  protected (needed page (required_ranges s)) (protection_table s) /\
  match pending_preparation s with
  | None => True
  | Some p => apart page (protected_roots s) (prep_range p)
  end.
Definition change_preparation s pending frozen t bits dirty :=
  Build_protection_state (context_scopes s) (attached_ranges s) pending
    (physical_authority s) (acknowledged_authority s) frozen t bits dirty.
Definition set_phase p phase := Build_preparation (prep_kind p) (prep_range p) phase.
Definition publication_candidate s := context_ranges s ++ attached_ranges s.

(* Projection of the current dependency view including already consumed
   tokens. There is still exactly one physical ownership table. *)
Definition data_scope s := Build_scope_state
  (protection_current s ++ attached_ranges s) (protection_saved s)
  (protection_base s) (protection_table s).
Definition data_ownership page s :=
  scope_invariant page (data_scope s) /\
  bounded page (physical_authority s ++ acknowledged_authority s) 1 (protection_table s) /\
  match pending_preparation s with
  | None => True
  | Some p => bounded page [prep_range p] (S (length (protection_saved s))) (protection_table s)
  end.

Inductive preparation_step page : protection_state -> protection_state -> Prop :=
| reserve_preparation s kind r :
    protection_frozen s = false -> pending_preparation s = None ->
    free_range page (protection_table s) r ->
    preparation_step page s
      (change_preparation s (Some (Build_preparation kind r Reserved)) false
        (reserve_extent page r (length (saved_ranges (context_scopes s))) (protection_table s))
        (set_summary (protection_bits s) (length (saved_ranges (context_scopes s)))) true)
| retain_load_reservation s p :
    protection_frozen s = false -> pending_preparation s = Some p ->
    prep_kind p = LoadPreparation -> prep_phase p = Reserved ->
    preparation_step page s
      (change_preparation s (Some p) false
        (rehome_extent page (prep_range p) 0 (protection_table s))
        (set_summary (protection_bits s) 0) (protection_dirty s))
| physical_preparation_complete s p :
    protection_frozen s = false -> pending_preparation s = Some p ->
    preparation_step page s
      (change_preparation s (Some (set_phase p Written)) false (protection_table s) (protection_bits s) (protection_dirty s))
| withdraw_load_context s p :
    protection_frozen s = false -> pending_preparation s = Some p ->
    prep_kind p = LoadPreparation -> prep_phase p = Written ->
    preparation_step page s
      (change_preparation s (Some (set_phase p Detached)) false (protection_table s) (protection_bits s) (protection_dirty s))
| attach_preparation s p :
    protection_frozen s = false -> pending_preparation s = Some p ->
    (prep_phase p = Written \/ prep_phase p = Detached) ->
    preparation_step page s
      (Build_protection_state (context_scopes s) (prep_range p :: attached_ranges s) None
        (physical_authority s) (acknowledged_authority s) false (protection_table s) (protection_bits s) true)
| abandon_preparation s p :
    protection_frozen s = false -> pending_preparation s = Some p ->
    preparation_step page s
      (change_preparation s None false (release_extent page (prep_range p) (protection_table s)) (protection_bits s) (protection_dirty s))
| load_error_without_freeze s p :
    protection_frozen s = false -> pending_preparation s = Some p -> prep_kind p = LoadPreparation ->
    preparation_step page s s
| returned_uncertain_error s :
    preparation_step page s (change_preparation s (pending_preparation s) true (protection_table s) (protection_bits s) (protection_dirty s))
| publish_complete s :
    protection_frozen s = false ->
    preparation_step page s
      (Build_protection_state (context_scopes s) (attached_ranges s) (pending_preparation s)
        (publication_candidate s) (acknowledged_authority s) false (protection_table s) (protection_bits s) (protection_dirty s))
| acknowledge_publication s :
    protection_frozen s = false ->
    preparation_step page s
      (Build_protection_state (context_scopes s) (attached_ranges s) (pending_preparation s)
        (physical_authority s) (physical_authority s) false (protection_table s) (protection_bits s) (protection_dirty s))
| abandon_frozen_context s :
    protection_frozen s = true ->
    preparation_step page s (change_preparation s None true (protection_table s) (protection_bits s) (protection_dirty s))
| writable_begin_context cur views base extra pending authority ack t bits dirty observed :
    length views < 6 ->
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur views base t) extra pending authority ack false t bits dirty))
      (Build_protection_state (Build_scope_state (cur ++ extra) (views ++ [cur ++ extra]) base t)
        [] pending authority ack false t bits dirty)
| writable_accept_context cur views saved base extra pending authority ack t bits dirty observed :
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t) extra pending authority ack false t bits dirty))
      (Build_protection_state (Build_scope_state cur views base t) extra pending authority ack false
        (finish_table (S (length views)) true t)
        (finish_summary bits (S (length views)) true) dirty)
| frozen_rollback_context cur views saved base extra pending authority ack t bits dirty observed :
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t) extra pending authority ack true t bits dirty))
      (Build_protection_state (Build_scope_state saved views base t) extra pending authority ack true t bits dirty)
| frozen_accept_context cur views saved base extra pending authority ack t bits dirty observed :
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t) extra pending authority ack true t bits dirty))
      (Build_protection_state (Build_scope_state cur views base t) extra pending authority ack true t bits dirty)
| frozen_begin_context cur views base extra pending authority ack t bits dirty observed :
    length views < 6 ->
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur views base t) extra pending authority ack true t bits dirty))
      (Build_protection_state (Build_scope_state cur (views ++ [cur]) base t) extra pending authority ack true t bits dirty)
| writable_rollback_data cur views saved base extra authority ack t bits dirty observed :
    scope_invariant page (Build_scope_state (cur ++ extra) (views ++ [saved]) base t) ->
    bounded page (authority ++ ack) 1 t ->
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
        extra None authority ack false t bits dirty))
      (Build_protection_state (Build_scope_state saved views base t)
        [] None authority ack false (finish_table (S (length views)) false t)
        (finish_summary bits (S (length views)) false) dirty)
| frozen_rollback_data cur views saved base extra authority ack t bits dirty observed :
    preparation_step page
      (image_generation_observe observed (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
        extra None authority ack true t bits dirty))
      (Build_protection_state (Build_scope_state saved views base t)
        [] None authority ack true t bits dirty)
| writable_collect_data view marker durable current entries cur extra t bits observed :
    collect_guard durable current -> current_agrees view current entries ->
    cur ++ extra = collect_ranges view marker current entries [] ->
    preparation_step page
      (image_generation_observe observed (Build_protection_state
        (Build_scope_state cur [] (optional_root view durable) t)
        extra None (optional_root view durable) (optional_root view durable) false t bits true))
      (Build_protection_state
        (Build_scope_state cur [] (optional_root view durable) t)
        extra None (optional_root view durable) (optional_root view durable) false
        (collect_table page (collect_ranges view marker current entries []) t)
        (fun _ => false) false)
| reject_or_skip s : preparation_step page s s.

(* Historical preparation steps either keep known metadata on an identity
   step or forget it. They never manufacture a known Image generation. *)
Lemma preparation_generation_not_invented page s final :
 preparation_step page s final ->
 protection_image_generation final=None \/
 protection_image_generation final=protection_image_generation s.
Proof.
 intro RUN;destruct RUN;first [left;reflexivity | right;reflexivity].
Qed.

Lemma needed_membership page xs ys :
  (forall r, In r xs -> In r ys) -> forall p, needed page xs p -> needed page ys p.
Proof. intros I p [r [R T]]. exists r; auto. Qed.
Lemma roots_in_required s r : In r (protected_roots s) -> In r (required_ranges s).
Proof.
  unfold protected_roots, required_ranges. repeat rewrite in_app_iff. tauto.
Qed.
Lemma protected_subset page xs ys t :
  (forall r, In r xs -> In r ys) -> protected (needed page ys) t -> protected (needed page xs) t.
Proof. intros I P p N. apply P. eapply needed_membership; eauto. Qed.

Lemma context_subset_preserves page c c' extra pending authority ack frozen t bits dirty :
  (forall r, In r (surviving_ranges c') -> In r (surviving_ranges c)) ->
  preparation_invariant page (Build_protection_state c extra pending authority ack frozen t bits dirty) ->
  preparation_invariant page (Build_protection_state c' extra pending authority ack frozen t bits dirty).
Proof.
  intros SUB [C A]. split.
  - eapply protected_subset; [|exact C].
    intros r I. unfold required_ranges, context_ranges in *; simpl in *.
    repeat rewrite in_app_iff in *; intuition.
  - destruct pending as [p|]; simpl in *; [|exact I].
    intros q N. apply A. eapply needed_membership; [|exact N].
    intros r I. unfold protected_roots, context_ranges in *; simpl in *.
    repeat rewrite in_app_iff in *; intuition.
Qed.

Lemma accepting_table_keeps_protection page ranges depth t :
  depth > 0 -> protected (needed page ranges) t ->
  protected (needed page ranges) (finish_table depth true t).
Proof.
  intros D P p N. unfold finish_table.
  destruct (owner (t p) =? S depth); simpl; [lia|apply P; exact N].
Qed.

Lemma data_collection_membership view marker durable current entries cur extra r :
  collect_guard durable current -> current_agrees view current entries ->
  cur ++ extra = collect_ranges view marker current entries [] ->
  (In r cur \/ In r extra \/ In r (optional_root view durable)) ->
  In r (collect_ranges view marker current entries []).
Proof.
  intros G A E [R|[R|R]].
  - rewrite <- E. apply in_or_app; auto.
  - rewrite <- E. apply in_or_app; auto.
  - apply (final_collection_enumerates_surviving_roots view marker durable current entries [] G A).
    unfold live_ranges; simpl. right. apply in_or_app; auto.
Qed.

Theorem preparation_step_inductive page s s' :
  preparation_invariant page s -> preparation_step page s s' -> preparation_invariant page s'.
Proof.
  intros [C A] S. destruct S.
  - unfold preparation_invariant; simpl. split.
    + intros p [v [I T]]. unfold required_ranges, change_preparation in I; simpl in I.
      repeat rewrite in_app_iff in I. simpl in I.
      unfold reserve_extent. destruct (touches page r p) eqn:E; simpl; [lia|].
      apply C. exists v. split; [|exact T].
      unfold required_ranges, pending_ranges. rewrite H0. simpl.
      repeat rewrite in_app_iff. destruct I as [I|[I|[I|[I|[I|I]]]]]; auto; try contradiction.
      subst v; congruence.
    + intros p N. destruct (touches page r p) eqn:E; [|reflexivity].
      exfalso. apply (C p).
      * eapply needed_membership; [apply roots_in_required|exact N].
      * apply H1; exact E.
  - split.
    + intros q N. unfold change_preparation; simpl. unfold rehome_extent.
      destruct (touches page (prep_range p) q); simpl; [lia|].
      apply C. unfold required_ranges, context_ranges, pending_ranges, change_preparation in *;
        simpl in *; rewrite H0; exact N.
    + unfold protected_roots, context_ranges, change_preparation; simpl.
      rewrite H0 in A. exact A.
  - unfold preparation_invariant, required_ranges, protected_roots, context_ranges,
      pending_ranges, change_preparation, set_phase in *; simpl in *.
    rewrite H0 in *; exact (conj C A).
  - unfold preparation_invariant, required_ranges, protected_roots, context_ranges,
      pending_ranges, change_preparation, set_phase in *; simpl in *.
    rewrite H0 in *; exact (conj C A).
  - split; [|exact I].
    intros q [v [V T]]. apply C. exists v. split; [|exact T].
    unfold required_ranges, context_ranges, pending_ranges in *; simpl in *.
    rewrite H0. simpl. repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; simpl in *; tauto.
  - split; [|exact I]. intros q N. unfold change_preparation; simpl.
    unfold release_extent. assert (Nroot : needed page (protected_roots s) q).
    { destruct N as [v [V T]]. exists v. split; [|exact T].
      unfold required_ranges, protected_roots, context_ranges, pending_ranges, change_preparation in *;
        simpl in *; repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; simpl in *; tauto. }
    rewrite H0 in A. rewrite (A q Nroot). apply C.
    eapply needed_membership; [apply roots_in_required|exact Nroot].
  - split; assumption.
  - unfold preparation_invariant, required_ranges, protected_roots, context_ranges,
      pending_ranges, change_preparation in *; simpl in *; exact (conj C A).
  - split.
    + intros q [v [V T]]. apply C. exists v. split; [|exact T].
      unfold required_ranges, context_ranges, publication_candidate, pending_ranges in *; simpl in *.
      repeat rewrite in_app_iff in *; tauto.
    + destruct (pending_preparation s) as [p|] eqn:E; simpl in *; [|exact I].
      intros q N. apply A. eapply needed_membership; [|exact N].
      intros r R. unfold protected_roots, context_ranges, publication_candidate in *; simpl in *.
      repeat rewrite in_app_iff in *; tauto.
  - split.
    + intros q [v [V T]]. apply C. exists v. split; [|exact T].
      unfold required_ranges, context_ranges, pending_ranges in *; simpl in *.
      repeat rewrite in_app_iff in *; tauto.
    + destruct (pending_preparation s) as [p|] eqn:E; simpl in *; [|exact I].
      intros q N. apply A. eapply needed_membership; [|exact N].
      intros r R. unfold protected_roots, context_ranges in *; simpl in *.
      repeat rewrite in_app_iff in *; tauto.
  - split; [|exact I]. eapply protected_subset; [|exact C].
    intros r R. unfold required_ranges, context_ranges, pending_ranges, change_preparation in *;
      simpl in *; repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; simpl in *; tauto.
  - split.
    + eapply protected_subset; [|exact C].
      intros r R. unfold required_ranges, context_ranges, surviving_ranges in *; simpl in *.
      rewrite flat_map_app in R; simpl in R.
      repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; tauto.
    + destruct pending as [p|]; simpl in *; [|exact I].
      intros q N. apply A. eapply needed_membership; [|exact N].
      intros r R. unfold protected_roots, context_ranges, surviving_ranges in *; simpl in *.
      rewrite flat_map_app in R; simpl in R.
      repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; tauto.
  - assert (MID : preparation_invariant page
        (Build_protection_state (Build_scope_state cur views base t) extra pending authority ack false t bits dirty)).
    { eapply context_subset_preserves; [|exact (conj C A)].
      intros r R. unfold surviving_ranges in *; simpl in *.
      rewrite flat_map_app; simpl. repeat rewrite in_app_iff in *; tauto. }
    destruct MID as [MC MA]. split; [|exact MA].
    apply accepting_table_keeps_protection; [lia|exact MC].
  - eapply context_subset_preserves; [|exact (conj C A)].
    intros r I. unfold surviving_ranges in *; simpl in *.
    rewrite flat_map_app; simpl. repeat rewrite in_app_iff in *; simpl in *; tauto.
  - eapply context_subset_preserves; [|exact (conj C A)].
    intros r I. unfold surviving_ranges in *; simpl in *.
    rewrite flat_map_app; simpl. repeat rewrite in_app_iff in *; simpl in *; tauto.
  - eapply context_subset_preserves; [|exact (conj C A)].
    intros r I. unfold surviving_ranges in *; simpl in *.
    rewrite flat_map_app in I; simpl in I. repeat rewrite in_app_iff in *; simpl in *; tauto.
  - split; [|exact I].
    pose proof (scope_step_inductive page _ _ H
      (rollback_step page (cur ++ extra) views saved base t)) as R.
    pose proof (scope_invariant_covers_survivors page _ R) as COVER.
    pose proof (finish_preserves_ancestor page (authority ++ ack) 1
      (S (length views)) false t ltac:(lia) H0) as AUTH.
    intros q [r [MEM TOUCH]]. unfold required_ranges, context_ranges,
      pending_ranges, surviving_ranges in MEM; simpl in MEM.
    repeat rewrite in_app_iff in MEM; simpl in MEM.
    destruct MEM as [M|[M|[M|[]]]].
    + apply COVER. exists r. split; [unfold surviving_ranges; simpl; repeat rewrite in_app_iff; exact M|exact TOUCH].
    + apply (bounded_protected _ _ _ _ AUTH). exists r. split; [apply in_or_app; auto|exact TOUCH].
    + apply (bounded_protected _ _ _ _ AUTH). exists r. split; [apply in_or_app; auto|exact TOUCH].
  - split; [|exact I]. eapply protected_subset; [|exact C].
    intros r R. unfold required_ranges, context_ranges, pending_ranges, surviving_ranges in *;
      simpl in *; rewrite flat_map_app; simpl.
    repeat rewrite in_app_iff in *; simpl in *; tauto.
  - split; [|exact I]. intros q [r [R T]].
    apply collection_establishes_coverage. exists r. split; [|exact T].
    eapply data_collection_membership; eauto.
    unfold required_ranges, context_ranges, pending_ranges, surviving_ranges in R;
      simpl in R; repeat rewrite in_app_iff in R; simpl in R;
      repeat rewrite in_app_iff in R; tauto.
  - split; assumption.
Qed.

Inductive preparation_trace page : protection_state -> protection_state -> Prop :=
| prep_refl s : preparation_trace page s s
| prep_cons s m last : preparation_step page s m -> preparation_trace page m last -> preparation_trace page s last.
Theorem finite_preparation_trace_protects page s s' :
  preparation_invariant page s -> preparation_trace page s s' -> preparation_invariant page s'.
Proof.
  intros I T. induction T; [exact I|]. apply IHT. eapply preparation_step_inductive; eauto.
Qed.

Definition enter_preparation (s : scope_state) bits dirty :=
  Build_protection_state s [] None (base_ranges s) (base_ranges s) false (scope_pages s) bits dirty.
Theorem enter_preparation_invariant page s bits dirty :
  scope_invariant page s -> preparation_invariant page (enter_preparation s bits dirty).
Proof.
  intros I. split; [|exact Logic.I].
  eapply protected_subset; [|apply scope_invariant_covers_survivors; exact I].
  intros r R. unfold enter_preparation, required_ranges, context_ranges,
    pending_ranges, surviving_ranges in *; simpl in *.
  repeat rewrite in_app_iff in *; simpl in *; tauto.
Qed.
Theorem reachable_preparation_erase_preserves g page initial bits dirty final f f' a outcome :
  page > 0 -> scope_invariant page initial ->
  preparation_trace page (enter_preparation initial bits dirty) final ->
  free_range page (protection_table final) {| offset := a; span := sector_size g |} ->
  erase_step g f a outcome f' -> unchanged (required_ranges final) f f'.
Proof.
  intros P I T F E. eapply erase_preserves_covered_ranges; eauto.
  exact (proj1 (finite_preparation_trace_protects page _ _ (enter_preparation_invariant page initial bits dirty I) T)).
Qed.

Theorem frozen_preparation_step_keeps_storage page s s' :
  protection_frozen s = true -> preparation_step page s s' ->
  protection_frozen s' = true /\ protection_table s' = protection_table s /\
  physical_authority s' = physical_authority s.
Proof.
  intros F S. destruct S; simpl in *; try congruence;
    repeat split; assumption || reflexivity.
Qed.
Theorem frozen_preparation_trace_keeps_storage page s s' :
  protection_frozen s = true -> preparation_trace page s s' ->
  protection_frozen s' = true /\ protection_table s' = protection_table s /\
  physical_authority s' = physical_authority s.
Proof.
  intros F T. induction T; [repeat split; auto|].
  destruct (frozen_preparation_step_keeps_storage page _ _ F H) as [FM [TM AM]].
  destruct (IHT FM) as [FL [TL AL]]. repeat split; congruence.
Qed.

(* Physical commands on an in-flight reservation may damage that incomplete
   block. They do not damage any attached/recoverable root, for any outcome. *)
Theorem preparation_program_preserves_roots g page s p a data result f f' :
  page > 0 -> preparation_invariant page s -> pending_preparation s = Some p ->
  (forall q, touches page {| offset := a; span := length data |} q = true ->
     touches page (prep_range p) q = true) ->
  program_step g f a data result f' -> unchanged (protected_roots s) f f'.
Proof.
  intros P [_ A] E INS STEP live b I B.
  apply (program_locality _ _ _ _ _ _ STEP).
  destruct (Nat.lt_ge_cases b a); [auto|].
  right. destruct (Nat.le_gt_cases (a + length data) b); [assumption|].
  exfalso. rewrite E in A.
  assert (N : needed page (protected_roots s) (b / page)).
  { exists live. split; [exact I|eapply byte_page_touched; eauto]. }
  pose proof (A _ N) as OUT. assert (IN : touches page (prep_range p) (b / page) = true).
  { apply INS. apply byte_page_touched; [exact P|]. unfold contains; simpl; lia. }
  congruence.
Qed.

(* The summary is observed from the same transition as reservation/cleanup.
   There is no separately supplied summary trace. *)
Theorem preparation_step_summary_sound page s s' :
  summary_sound (protection_bits s) (protection_table s) ->
  preparation_step page s s' ->
  summary_sound (protection_bits s') (protection_table s').
Proof.
  intros I S. destruct S; simpl in *;
    eauto using reserve_summary_sound, rehome_summary_sound,
      release_summary_sound, close_summary_sound, collect_summary_sound.
  all: apply finish_summary_sound; [lia|exact I].
Qed.
Definition protection_invariant page s :=
  preparation_invariant page s /\
  summary_sound (protection_bits s) (protection_table s).
Theorem protection_step_inductive page s s' :
  protection_invariant page s -> preparation_step page s s' ->
  protection_invariant page s'.
Proof.
  intros [P B] S. split.
  - eapply preparation_step_inductive; eauto.
  - eapply preparation_step_summary_sound; eauto.
Qed.
Theorem finite_protection_trace page s s' :
  protection_invariant page s -> preparation_trace page s s' ->
  protection_invariant page s'.
Proof.
  intros I T. induction T; [exact I|]. apply IHT.
  eapply protection_step_inductive; eauto.
Qed.
Definition enter_with_summaries (s : scope_state) bits dirty :=
  Build_protection_state s [] None (base_ranges s) (base_ranges s) false
    (scope_pages s) bits dirty.
Theorem enter_with_summaries_invariant page s bits dirty :
  scope_invariant page s -> summary_sound bits (scope_pages s) ->
  protection_invariant page (enter_with_summaries s bits dirty).
Proof.
  intros I B. split; [|exact B]. split; [|exact Logic.I].
  eapply protected_subset; [|apply scope_invariant_covers_survivors; exact I].
  intros r R. unfold enter_with_summaries, required_ranges, context_ranges,
    pending_ranges, surviving_ranges in *; simpl in *.
  repeat rewrite in_app_iff in *; simpl in *; tauto.
Qed.
Theorem reachable_absent_summary_scan_identity page s s' depth accept :
  protection_invariant page s -> preparation_trace page s s' ->
  0 < depth -> protection_bits s' depth = false ->
  forall p, finish_table depth accept (protection_table s') p = protection_table s' p.
Proof.
  intros I T D B p.
  pose proof (proj2 (finite_protection_trace page s s' I T)) as SOUND.
  unfold finish_table. destruct (owner (protection_table s' p) =? S depth) eqn:E;
    [|reflexivity].
  apply Nat.eqb_eq in E. specialize (SOUND depth p D E). congruence.
Qed.

(* Data-token ownership facts. These establish the rollback caller obligations;
   they are not preservation assumptions in the flash or token callee. *)
Lemma data_scope_table_shared s : scope_pages (data_scope s) = protection_table s.
Proof. reflexivity. Qed.
Lemma data_roots_membership s r :
  In r (surviving_ranges (data_scope s)) \/
  In r (physical_authority s ++ acknowledged_authority s) ->
  In r (protected_roots s).
Proof.
  unfold data_scope, protected_roots, context_ranges, context_scopes, surviving_ranges;
    simpl; repeat rewrite in_app_iff; tauto.
Qed.
Lemma data_reserve_ownership page s kind r :
  data_ownership page s -> free_range page (protection_table s) r ->
  data_ownership page
    (change_preparation s (Some (Build_preparation kind r Reserved)) false
      (reserve_extent page r (length (protection_saved s)) (protection_table s))
      (set_summary (protection_bits s) (length (protection_saved s))) true).
Proof.
  intros [[D [C [STACK BASE]]] [AUTH P]] FREE.
  unfold data_ownership, data_scope, change_preparation, Build_protection_state, context_scopes;
    simpl. split; [|split].
  - unfold scope_invariant; simpl. split; [exact D|]. split; [|split].
    + apply reserve_preserves_bounds; assumption.
    + intros i v E. apply reserve_preserves_bounds; [exact FREE|eapply STACK; eauto].
    + apply reserve_preserves_bounds; assumption.
  - apply reserve_preserves_bounds; assumption.
  - apply reservation_has_current_owner.
Qed.
Lemma data_phase_ownership page s p phase :
  data_ownership page s -> pending_preparation s = Some p ->
  data_ownership page (change_preparation s (Some (set_phase p phase)) false
    (protection_table s) (protection_bits s) (protection_dirty s)).
Proof.
  unfold data_ownership, data_scope, change_preparation, Build_protection_state, context_scopes;
    simpl. intros [C [A P]] E. rewrite E in P. exact (conj C (conj A P)).
Qed.
Lemma data_attach_ownership page s p :
  data_ownership page s -> pending_preparation s = Some p ->
  data_ownership page (Build_protection_state (context_scopes s)
    (prep_range p :: attached_ranges s) None (physical_authority s)
    (acknowledged_authority s) false (protection_table s) (protection_bits s) true).
Proof.
  intros [[D [C [STACK BASE]]] [AUTH P]] E. rewrite E in P.
  unfold data_ownership, data_scope; simpl. split; [|split; auto].
  unfold scope_invariant; simpl. split; [exact D|]. split; [|split; assumption].
  intros q [r [R T]]. repeat rewrite in_app_iff in R; simpl in R.
  destruct R as [R|[R|R]].
  - apply C. exists r. split; [apply in_or_app; auto|exact T].
  - subst r. apply P. exists (prep_range p). split; [simpl; auto|exact T].
  - apply C. exists r. split; [apply in_or_app; auto|exact T].
Qed.
Lemma data_abandon_ownership page s p :
  preparation_invariant page s -> data_ownership page s ->
  pending_preparation s = Some p ->
  data_ownership page (change_preparation s None false
    (release_extent page (prep_range p) (protection_table s))
    (protection_bits s) (protection_dirty s)).
Proof.
  intros [_ APART] [[D [C [STACK BASE]]] [AUTH P]] E. rewrite E in APART.
  assert (UNCHANGED : forall q, needed page (protected_roots s) q ->
    release_extent page (prep_range p) (protection_table s) q = protection_table s q).
  { intros q N. unfold release_extent. rewrite (APART q N). reflexivity. }
  unfold data_ownership, data_scope, change_preparation, Build_protection_state, context_scopes;
    simpl. split; [|split; [|exact I]].
  - unfold scope_invariant; simpl. split; [exact D|]. split; [|split].
    + intros q [r [R T]]. rewrite UNCHANGED.
      * apply C. exists r; auto.
      * exists r. split; [apply data_roots_membership; left; unfold surviving_ranges, data_scope; simpl; repeat rewrite in_app_iff in *; tauto|exact T].
    + intros i v E' q [r [R T]]. rewrite UNCHANGED.
      * apply (STACK i v E'). exists r; auto.
      * exists r. split; [|exact T]. apply data_roots_membership; left.
        unfold surviving_ranges, data_scope; simpl. apply in_or_app; right. apply in_or_app; left.
        apply in_flat_map. exists v. split; [eapply nth_error_In; exact E'|exact R].
    + intros q [r [R T]]. rewrite UNCHANGED.
      * apply BASE. exists r; auto.
      * exists r. split; [apply data_roots_membership; left; unfold surviving_ranges, data_scope; simpl; repeat rewrite in_app_iff; auto|exact T].
  - intros q [r [R T]]. rewrite UNCHANGED.
    + apply AUTH. exists r; auto.
    + exists r. split; [apply data_roots_membership; auto|exact T].
Qed.

Lemma data_begin_ownership page cur views base extra authority ack t bits dirty :
  length views < 6 ->
  data_ownership page (Build_protection_state (Build_scope_state cur views base t)
    extra None authority ack false t bits dirty) ->
  data_ownership page (Build_protection_state
    (Build_scope_state (cur ++ extra) (views ++ [cur ++ extra]) base t)
    [] None authority ack false t bits dirty).
Proof.
  intros D [S [A _]]. split; [|split; [exact A|exact I]].
  unfold data_scope in *; simpl in *. rewrite app_nil_r.
  eapply scope_step_inductive; [exact S|]. apply begin_step; exact D.
Qed.
Lemma data_accept_ownership page cur views saved base extra authority ack t bits dirty :
  data_ownership page (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
    extra None authority ack false t bits dirty) ->
  data_ownership page (Build_protection_state (Build_scope_state cur views base t)
    extra None authority ack false (finish_table (S (length views)) true t)
    (finish_summary bits (S (length views)) true) dirty).
Proof.
  intros [S [A _]]. split; [|split; [|exact I]].
  - eapply scope_step_inductive; [exact S|]. apply accept_step.
  - apply finish_preserves_ancestor; [lia|exact A].
Qed.
Lemma data_rollback_ownership page cur views saved base extra authority ack t bits dirty :
  data_ownership page (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
    extra None authority ack false t bits dirty) ->
  data_ownership page (Build_protection_state (Build_scope_state saved views base t)
    [] None authority ack false (finish_table (S (length views)) false t)
    (finish_summary bits (S (length views)) false) dirty).
Proof.
  intros [S [A _]]. split; [|split; [|exact I]].
  - unfold data_scope in *; simpl in *. rewrite app_nil_r.
    eapply scope_step_inductive; [exact S|]. apply rollback_step.
  - apply finish_preserves_ancestor; [lia|exact A].
Qed.
Theorem data_rollback_caller_derived page cur views saved base extra authority ack t bits dirty :
  data_ownership page (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
    extra None authority ack false t bits dirty) ->
  preparation_step page
    (Build_protection_state (Build_scope_state cur (views ++ [saved]) base t)
      extra None authority ack false t bits dirty)
    (Build_protection_state (Build_scope_state saved views base t)
      [] None authority ack false (finish_table (S (length views)) false t)
      (finish_summary bits (S (length views)) false) dirty).
Proof. intros [S [A _]]. apply writable_rollback_data; assumption. Qed.

(* Instructions interpreted on protection_state itself. They are also the
   services of the FreerDPS Data interface; there is no second registry state. *)
Inductive data_command :=
| DataReserve (r : extent)
| DataWritten
| DataAttach
| DataDrop
| DataBegin
| DataClose (views : list (list extent)) (saved : list extent) (accept : bool)
| DataFreeze
| DataUnchanged.
Definition data_next cmd s :=
  let t := protection_table s in
  let bits := protection_bits s in let dirty := protection_dirty s in
  match cmd with
  | DataReserve r => change_preparation s (Some (Build_preparation ObjectPreparation r Reserved)) false
      (reserve_extent 256 r (length (protection_saved s)) t)
      (set_summary bits (length (protection_saved s))) true
  | DataWritten => match pending_preparation s with
      | Some p => change_preparation s (Some (set_phase p Written)) false t bits dirty
      | None => s end
  | DataAttach => match pending_preparation s with
      | Some p => Build_protection_state (context_scopes s) (prep_range p :: attached_ranges s)
          None (physical_authority s) (acknowledged_authority s) false t bits true
      | None => s end
  | DataDrop => change_preparation s None (protection_frozen s)
      (if protection_frozen s then t else match pending_preparation s with
       | Some p => release_extent 256 (prep_range p) t | None => t end) bits dirty
  | DataBegin => Build_protection_state
      (Build_scope_state (protection_current s ++ attached_ranges s)
        (protection_saved s ++ [protection_current s ++ attached_ranges s]) (protection_base s) t)
      [] None (physical_authority s) (acknowledged_authority s) false t bits dirty
  | DataClose views saved accept =>
      Build_protection_state (Build_scope_state
        (if accept then protection_current s else saved) views (protection_base s) t)
        (if accept then attached_ranges s else []) None
        (physical_authority s) (acknowledged_authority s) (protection_frozen s)
        (if protection_frozen s then t else finish_table (S (length views)) accept t)
        (if protection_frozen s then bits else finish_summary bits (S (length views)) accept) dirty
  | DataFreeze => change_preparation s (pending_preparation s) true t bits dirty
  | DataUnchanged => s
  end.
Definition data_caller cmd s :=
  match cmd with
  | DataReserve r => protection_frozen s = false /\ pending_preparation s = None /\
      free_range 256 (protection_table s) r
  | DataWritten | DataAttach => protection_frozen s = false /\
      exists p, pending_preparation s = Some p /\ prep_kind p = ObjectPreparation /\
        (cmd = DataAttach -> prep_phase p = Written)
  | DataDrop => exists p, pending_preparation s = Some p
  | DataBegin => protection_frozen s = false /\ pending_preparation s = None /\
      length (protection_saved s) < 6
  | DataClose views saved _ => pending_preparation s = None /\
      protection_saved s = views ++ [saved]
  | DataFreeze | DataUnchanged => True
  end.
Definition data_invariant s := protection_invariant 256 s /\
  (protection_frozen s = false -> data_ownership 256 s).
Lemma data_command_refines_step cmd s :
  data_invariant s -> data_caller cmd s -> preparation_step 256 s (data_next cmd s).
Proof.
  intros [I OWN] CALL. destruct cmd; simpl in CALL; unfold data_next.
  - destruct CALL as [F [P R]]. apply reserve_preparation; assumption.
  - destruct CALL as [F [p [P [K W]]]]. rewrite P. apply physical_preparation_complete; assumption.
  - destruct CALL as [F [p [P [K W]]]]. rewrite P. apply attach_preparation; auto.
  - destruct CALL as [p P]. destruct (protection_frozen s) eqn:F.
    + apply abandon_frozen_context; exact F.
    + rewrite P. apply abandon_preparation; assumption.
  - destruct CALL as [F [P D]]. destruct s; simpl in *; subst.
    apply writable_begin_context; exact D.
  - destruct CALL as [P E]. destruct (protection_frozen s) eqn:F.
    + destruct s; simpl in *; subst. destruct accept;
        [apply frozen_accept_context|apply frozen_rollback_data].
    + specialize (OWN eq_refl). destruct s; simpl in *; subst. destruct accept.
      * apply writable_accept_context.
      * destruct OWN as [SC [AUTH _]]. apply writable_rollback_data; assumption.
  - apply returned_uncertain_error.
  - apply reject_or_skip.
Qed.
Lemma data_command_generation_not_invented cmd s :
 data_invariant s -> data_caller cmd s ->
 protection_image_generation (data_next cmd s)=None \/
 protection_image_generation (data_next cmd s)=protection_image_generation s.
Proof.
 intros INV CALL;apply preparation_generation_not_invented with (page:=256).
 apply data_command_refines_step;assumption.
Qed.

Theorem data_command_preserves cmd s :
  data_invariant s -> data_caller cmd s -> data_invariant (data_next cmd s).
Proof.
  intros INV CALL. pose proof (data_command_refines_step cmd s INV CALL) as STEP.
  destruct INV as [I OWN]. split.
  - eapply protection_step_inductive; eauto.
  - destruct cmd; simpl in CALL; unfold data_next; simpl.
    + intros _. apply data_reserve_ownership; [apply OWN; tauto|tauto].
    + destruct CALL as [F [p [P [K W]]]]. rewrite P. intros _.
      apply data_phase_ownership; [apply OWN; exact F|exact P].
    + destruct CALL as [F [p [P [K W]]]]. rewrite P. intros _.
      apply data_attach_ownership; [apply OWN; exact F|exact P].
    + destruct CALL as [p P]. destruct (protection_frozen s) eqn:F; [discriminate|].
      rewrite P. intros _. apply data_abandon_ownership; [exact (proj1 I)|apply OWN; reflexivity|exact P].
    + destruct CALL as [F [P D]]. specialize (OWN F). destruct s; simpl in *; subst.
      intros _. apply data_begin_ownership; assumption.
    + destruct CALL as [P E]. destruct (protection_frozen s) eqn:F; [discriminate|].
      specialize (OWN eq_refl). destruct s; simpl in *; subst.
      destruct accept; intros _; [eapply data_accept_ownership|eapply data_rollback_ownership]; exact OWN.
    + discriminate.
    + exact OWN.
Qed.
Theorem data_commands_do_not_publish cmd s :
  physical_authority (data_next cmd s) = physical_authority s /\
  acknowledged_authority (data_next cmd s) = acknowledged_authority s.
Proof.
  destruct cmd; unfold data_next;
    try destruct (pending_preparation s); simpl; auto.
Qed.
Theorem data_token_consumed_before_close views saved accept s :
  data_caller (DataClose views saved accept) s -> pending_preparation s = None.
Proof. simpl; tauto. Qed.
Theorem data_drop_does_not_release_survivor s p q :
  data_invariant s -> pending_preparation s = Some p ->
  needed 256 (protected_roots s) q ->
  protection_table (data_next DataDrop s) q = protection_table s q.
Proof.
  intros [[[_ APART] _] _] P N. rewrite P in APART.
  unfold data_next, change_preparation; simpl.
  destruct (protection_frozen s); [reflexivity|]. rewrite P.
  unfold release_extent. rewrite (APART q N); reflexivity.
Qed.

Fixpoint execute_data (commands : list data_command) s :=
  match commands with [] => s | c :: tail => execute_data tail (data_next c s) end.
Fixpoint data_calls (commands : list data_command) s : Prop :=
  match commands with [] => True | c :: tail => data_caller c s /\ data_calls tail (data_next c s) end.
Theorem data_execution_preserves commands s :
  data_invariant s -> data_calls commands s -> data_invariant (execute_data commands s).
Proof.
  revert s. induction commands as [|c tail IH]; intros s I CALL; simpl in *; [exact I|].
  destruct CALL as [C T]. apply IH; [eapply data_command_preserves; eauto|exact T].
Qed.
Theorem data_execution_refines commands s :
  data_invariant s -> data_calls commands s ->
  preparation_trace 256 s (execute_data commands s).
Proof.
  revert s. induction commands as [|c tail IH]; intros s I CALL; simpl in *; [constructor|].
  destruct CALL as [C T]. econstructor.
  - exact (data_command_refines_step c s I C).
  - apply IH; [eapply data_command_preserves; eauto|exact T].
Qed.
Theorem data_execution_no_publication commands s :
  physical_authority (execute_data commands s) = physical_authority s /\
  acknowledged_authority (execute_data commands s) = acknowledged_authority s.
Proof.
  revert s. induction commands as [|c tail IH]; intros s; simpl; [auto|].
  destruct (IH (data_next c s)), (data_commands_do_not_publish c s). split; congruence.
Qed.
Definition successful_data_member r := [DataReserve r; DataWritten; DataAttach].
Definition failed_data_member r (completed uncertain : bool) :=
  [DataReserve r] ++ (if completed then [DataWritten] else []) ++
  (if uncertain then [DataFreeze] else []) ++ [DataDrop].
Theorem successful_data_member_consumes_token r s :
  pending_preparation (execute_data (successful_data_member r) s) = None.
Proof. reflexivity. Qed.
Theorem failed_data_member_consumes_token r completed uncertain s :
  pending_preparation (execute_data (failed_data_member r completed uncertain) s) = None.
Proof. destruct completed, uncertain; reflexivity. Qed.
Theorem unchanged_data_preserves_dirty_and_table s :
  execute_data [DataUnchanged] s = s.
Proof. reflexivity. Qed.
Theorem completed_token_has_scope_bound s p :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = Some p ->
  bounded 256 [prep_range p] (S (length (protection_saved s))) (protection_table s).
Proof. intros [_ H] F P. specialize (H F). destruct H as [_ [_ B]]. rewrite P in B; exact B. Qed.
Theorem data_execution_erase_preserves g initial commands f f' a outcome :
  data_invariant initial -> data_calls commands initial ->
  free_range 256 (protection_table (execute_data commands initial))
    {| offset := a; span := sector_size g |} ->
  erase_step g f a outcome f' ->
  unchanged (required_ranges (execute_data commands initial)) f f'.
Proof.
  intros I C F E. eapply erase_preserves_covered_ranges with (page:=256); eauto; [lia|].
  exact (proj1 (proj1 (proj1 (data_execution_preserves commands initial I C)))).
Qed.
Theorem data_entry_invariant initial bits dirty :
  scope_invariant 256 initial -> summary_sound bits (scope_pages initial) ->
  data_invariant (enter_with_summaries initial bits dirty).
Proof.
  intros S B. split; [apply enter_with_summaries_invariant; assumption|]. intros _.
  split.
  - unfold data_scope, enter_with_summaries; simpl. rewrite app_nil_r.
    destruct initial; exact S.
  - split; [|exact I]. apply bounded_union; exact (proj2 (proj2 (proj2 S))).
Qed.

(* A has been consumed by the image; B is rejected before reserving a block.
   Drop is unnecessary for B, and local rollback removes A's staged reference. *)
Definition data_B_rejected_path a s :=
  DataBegin :: successful_data_member a ++
    [DataClose (protection_saved s) (protection_current s ++ attached_ranges s) false].
Theorem data_B_rejected_callers a s :
  protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  data_calls (data_B_rejected_path a s) s.
Proof.
  intros F P D FREE. unfold data_B_rejected_path, successful_data_member.
  cbn [data_calls data_caller data_next change_preparation Build_protection_state ProtectionState context_scopes].
  repeat split; try assumption; try reflexivity;
    try (eexists; repeat split; reflexivity || (intros; discriminate)).
Qed.
Theorem data_B_rejected_restores_pair a s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  let final := execute_data (data_B_rejected_path a s) s in
  data_invariant final /\ pending_preparation final = None /\
  protection_current final = protection_current s ++ attached_ranges s /\
  attached_ranges final = [] /\ protection_saved final = protection_saved s /\
  physical_authority final = physical_authority s /\
  acknowledged_authority final = acknowledged_authority s.
Proof.
  intros I F P D FREE; cbn zeta. split.
  - apply data_execution_preserves; [exact I|apply data_B_rejected_callers; assumption].
  - repeat split; reflexivity.
Qed.
Definition data_B_failed_path a b completed uncertain s :=
  DataBegin :: successful_data_member a ++ failed_data_member b completed uncertain ++
    [DataClose (protection_saved s) (protection_current s ++ attached_ranges s) false].
Theorem data_B_failed_callers a b completed uncertain s :
  protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  free_range 256
    (reserve_extent 256 a (S (length (protection_saved s))) (protection_table s)) b ->
  data_calls (data_B_failed_path a b completed uncertain s) s.
Proof.
  intros F P D FREE_A FREE_B. destruct completed, uncertain;
    unfold data_B_failed_path, successful_data_member, failed_data_member;
    cbn [app data_calls data_caller data_next change_preparation Build_protection_state ProtectionState context_scopes
      protection_saved protection_current protection_base attached_ranges pending_preparation
      physical_authority acknowledged_authority protection_frozen protection_table protection_bits protection_dirty];
    rewrite ?length_app; simpl;
    replace (length (protection_saved s) + 1) with (S (length (protection_saved s))) by lia;
    repeat split; try assumption; try reflexivity;
    try (eexists; repeat split; reflexivity || (intros; discriminate)).
  all: rewrite length_app; simpl;
    replace (length (protection_saved s) + 1) with (S (length (protection_saved s))) by lia;
    exact FREE_B.
Qed.
Theorem data_B_failed_preserves a b completed uncertain s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  free_range 256
    (reserve_extent 256 a (S (length (protection_saved s))) (protection_table s)) b ->
  data_invariant (execute_data (data_B_failed_path a b completed uncertain s) s).
Proof.
  intros I F P D A B. apply data_execution_preserves; [exact I|].
  apply data_B_failed_callers; assumption.
Qed.

Lemma execute_data_app first rest s :
  execute_data (first ++ rest) s = execute_data rest (execute_data first s).
Proof. revert s; induction first; intros s; simpl; auto. Qed.
Lemma data_calls_app first rest s :
  data_calls (first ++ rest) s <-> data_calls first s /\ data_calls rest (execute_data first s).
Proof. revert s; induction first; intros s; simpl; [tauto|rewrite IHfirst; tauto]. Qed.
Lemma successful_data_member_callers r s :
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> data_calls (successful_data_member r) s.
Proof.
  intros F P FREE. unfold successful_data_member.
  cbn [data_calls data_caller]. split; [auto|]. split.
  - split; [reflexivity|]. exists (Build_preparation ObjectPreparation r Reserved).
    repeat split; try reflexivity; intros; discriminate.
  - split; [|exact I]. split; [reflexivity|].
    exists (Build_preparation ObjectPreparation r Written). repeat split; reflexivity.
Qed.

Definition data_success_path a b s :=
  DataBegin :: successful_data_member a ++ successful_data_member b ++
    [DataClose (protection_saved s) (protection_current s ++ attached_ranges s) true].
Theorem data_success_callers a b s :
  protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (S (length (protection_saved s))) (protection_table s)) b ->
  data_calls (data_success_path a b s) s.
Proof.
  intros F P D FREE_A FREE_B. unfold data_success_path.
  change (data_caller DataBegin s /\ data_calls
    (successful_data_member a ++ successful_data_member b ++
     [DataClose (protection_saved s) (protection_current s ++ attached_ranges s) true])
    (data_next DataBegin s)). split; [simpl; auto|].
  apply data_calls_app. split.
  - apply successful_data_member_callers; auto.
  - apply data_calls_app. split.
    + apply successful_data_member_callers; try reflexivity.
      change (free_range 256 (reserve_extent 256 a
        (length (protection_saved s ++ [protection_current s ++ attached_ranges s]))
        (protection_table s)) b).
      rewrite length_app; simpl.
      replace (length (protection_saved s) + 1) with (S (length (protection_saved s))) by lia.
      exact FREE_B.
    + split; [|exact I]. repeat split; reflexivity.
Qed.
Theorem data_success_preserves a b s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (S (length (protection_saved s))) (protection_table s)) b ->
  data_invariant (execute_data (data_success_path a b s) s).
Proof.
  intros I F P D A B. apply data_execution_preserves; [exact I|apply data_success_callers; assumption].
Qed.
Definition data_parent_rollback_path a b s :=
  let old := protection_current s ++ attached_ranges s in
  DataBegin :: DataBegin :: successful_data_member a ++ successful_data_member b ++
  [DataClose (protection_saved s ++ [old]) (old ++ []) true;
   DataClose (protection_saved s) old false].
Theorem data_parent_rollback_callers a b s :
  protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 5 -> free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (S (S (length (protection_saved s)))) (protection_table s)) b ->
  data_calls (data_parent_rollback_path a b s) s.
Proof.
  intros F P D FREE_A FREE_B. unfold data_parent_rollback_path.
  change (data_caller DataBegin s /\ data_caller DataBegin (data_next DataBegin s) /\
    data_calls (successful_data_member a ++ successful_data_member b ++
      [DataClose (protection_saved s ++ [protection_current s ++ attached_ranges s])
        ((protection_current s ++ attached_ranges s) ++ []) true;
       DataClose (protection_saved s) (protection_current s ++ attached_ranges s) false])
      (data_next DataBegin (data_next DataBegin s))).
  split; [simpl; repeat split; auto; lia|]. split.
  - repeat split; try reflexivity. change (length (protection_saved s ++ [protection_current s ++ attached_ranges s]) < 6).
    rewrite length_app; simpl; lia.
  - apply data_calls_app. split.
    + apply successful_data_member_callers; auto.
    + apply data_calls_app. split.
      * apply successful_data_member_callers; try reflexivity.
        change (free_range 256 (reserve_extent 256 a
          (length ((protection_saved s ++ [protection_current s ++ attached_ranges s]) ++
            [(protection_current s ++ attached_ranges s) ++ []])) (protection_table s)) b).
        rewrite !length_app; simpl.
        replace (length (protection_saved s) + 1 + 1) with (S (S (length (protection_saved s)))) by lia.
        exact FREE_B.
      * split; [repeat split; reflexivity|]. split; [repeat split; reflexivity|exact I].
Qed.
Theorem data_accepted_child_parent_rollback a b s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 5 -> free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (S (S (length (protection_saved s)))) (protection_table s)) b ->
  let final := execute_data (data_parent_rollback_path a b s) s in
  data_invariant final /\ protection_current final = protection_current s ++ attached_ranges s /\
  attached_ranges final = [] /\ pending_preparation final = None.
Proof.
  intros I F P D A B; cbn zeta. split.
  - apply data_execution_preserves; [exact I|apply data_parent_rollback_callers; assumption].
  - repeat split; reflexivity.
Qed.

Lemma collect_subset_bound page ranges xs t :
  (forall r, In r xs -> In r ranges) -> bounded page xs 1 (collect_table page ranges t).
Proof.
  intros SUB q [r [R T]]. unfold collect_table.
  assert (M : marked page ranges q = true).
  { apply marked_spec. exists r; auto. }
  rewrite M; simpl; lia.
Qed.
Theorem data_collection_preserves view marker durable current entries cur extra t bits :
  let s := Build_protection_state (Build_scope_state cur [] (optional_root view durable) t)
    extra None (optional_root view durable) (optional_root view durable) false t bits true in
  let final := Build_protection_state (Build_scope_state cur [] (optional_root view durable) t)
    extra None (optional_root view durable) (optional_root view durable) false
      (collect_table 256 (collect_ranges view marker current entries []) t) (fun _ => false) false in
  data_invariant s -> collect_guard durable current -> current_agrees view current entries ->
  cur ++ extra = collect_ranges view marker current entries [] -> data_invariant final.
Proof.
  cbn zeta. intros [INV OWN] GUARD AGREE EQ. split.
  - eapply protection_step_inductive; [exact INV|]. apply writable_collect_data; assumption.
  - intros _. split; [|split; [|exact I]].
    + unfold scope_invariant, data_scope; simpl. split; [change (0 <= 6); lia|].
      split; [|split].
      * apply collect_subset_bound. intros r R. rewrite EQ in R; exact R.
      * intros i v E. destruct i; discriminate.
      * apply collect_subset_bound. intros r R. eapply data_collection_membership; eauto.
    + apply collect_subset_bound. intros r R. eapply data_collection_membership; eauto.
      apply in_app_or in R; tauto.
Qed.

Definition data_A_failed_path a completed uncertain s :=
  DataBegin :: failed_data_member a completed uncertain ++
    [DataClose (protection_saved s) (protection_current s ++ attached_ranges s) false].
Theorem data_A_failed_callers a completed uncertain s :
  protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  data_calls (data_A_failed_path a completed uncertain s) s.
Proof.
  intros F P D FREE. destruct completed, uncertain;
    unfold data_A_failed_path, failed_data_member;
    cbn [app data_calls data_caller data_next change_preparation Build_protection_state ProtectionState context_scopes];
    repeat split; try assumption; try reflexivity;
    try (eexists; repeat split; reflexivity || (intros; discriminate)).
Qed.
Theorem data_A_failed_preserves a completed uncertain s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  length (protection_saved s) < 6 -> free_range 256 (protection_table s) a ->
  data_invariant (execute_data (data_A_failed_path a completed uncertain s) s).
Proof.
  intros I F P D A. apply data_execution_preserves; [exact I|apply data_A_failed_callers; assumption].
Qed.


(* Snapshot observations are related to the existing dependency stack. They
   contain no second page table and are not an independently executing machine.
   [decoded] is an encoding specification on logical root names, not a claim
   that physical offsets have immutable contents. *)
Definition snapshot_dependencies (boss : nat -> extent)
    (b : option nat * list extent) : list extent :=
  match fst b with None => snd b | Some id => boss id :: snd b end.
Definition snapshot_correspondence boss decoded image current frames s :=
  roots_invariant decoded image current frames /\
  protection_current s ++ attached_ranges s =
    snapshot_dependencies boss (current, image) /\
  protection_saved s = map (snapshot_dependencies boss) frames.

Theorem snapshot_suffix_from_correspondence boss decoded image current frames s :
  snapshot_correspondence boss decoded image current frames s ->
  exists prefix count,
    all_saved prefix /\ frames = prefix ++ repeat (None,image) count /\
    protection_saved s = map (snapshot_dependencies boss) prefix ++ repeat image count.
Proof.
  intros [R [C S]]. destruct (deferred_suffix_derived decoded image current frames R)
    as [prefix [count [P E]]]. exists prefix, count. repeat split; auto.
  rewrite S, E, map_app, map_repeat. reflexivity.
Qed.

Lemma saved_prefix_owner prefix image count :
  all_saved prefix -> count > 0 ->
  snapshot_owner (map (@fst (option nat) (list extent))
    (prefix ++ repeat (None,image) count)) = length prefix.
Proof.
  intros P N. unfold snapshot_owner. rewrite map_app, map_repeat, length_app,
    !length_map, repeat_length.
  assert (E : first_unresolved
      (map (@fst (option nat) (list extent)) prefix ++ repeat None count) = length prefix).
  { induction P as [|[[id|] v] tail H P IH]; simpl in *.
    - destruct count; [lia|reflexivity].
    - f_equal; exact IH.
    - destruct H as [id H]; discriminate. }
  cbn [fst]. transitivity (Nat.min (length prefix) (length prefix + count)).
  - f_equal. exact E.
  - apply Nat.min_l; lia.
Qed.

(* Rehome and root installation are separate RAM steps after a successful
   physical write. Detached here means written and rehomed, not a LOAD token. *)
Definition snapshot_rehome lifetime s :=
  match pending_preparation s with
  | None => s
  | Some p => change_preparation s (Some (set_phase p Detached))
      (protection_frozen s)
      (rehome_extent 256 (prep_range p) lifetime (protection_table s))
      (set_summary (protection_bits s) lifetime) (protection_dirty s)
  end.
Definition snapshot_install prefix count r s :=
  let image := protection_current s ++ attached_ranges s in
  Build_protection_state
    (Build_scope_state (r :: image) (prefix ++ repeat (r :: image) count)
      (protection_base s) (protection_table s)) [] None
    (physical_authority s) (acknowledged_authority s)
    (protection_frozen s) (protection_table s) (protection_bits s) (protection_dirty s).

Lemma apart_rehome_unchanged page xs r lifetime t :
  apart page xs r -> forall q, needed page xs q ->
  rehome_extent page r lifetime t q = t q.
Proof. intros A q N. unfold rehome_extent; rewrite (A q N); reflexivity. Qed.

Theorem snapshot_rehome_preserves s p lifetime :
  data_invariant s -> protection_frozen s = false ->
  pending_preparation s = Some p -> lifetime <= length (protection_saved s) ->
  data_invariant (snapshot_rehome lifetime s).
Proof.
  intros [[ [C AP] SUM] OWN] F P L. rewrite P in AP.
  specialize (OWN F). destruct OWN as [[D [CUR [STACK BASE]]] [AUTH PEND]].
  unfold snapshot_rehome; rewrite P.
  split.
  - split; [split|].
    + intros q [r [R T]]. unfold required_ranges, context_ranges,
        surviving_ranges, change_preparation, Build_protection_state, context_scopes in R;
        simpl in R. repeat rewrite in_app_iff in R; simpl in R.
      unfold change_preparation; simpl. unfold rehome_extent.
      destruct (touches 256 (prep_range p) q) eqn:E; simpl; [lia|].
      apply C. exists r. split; [|exact T].
      unfold required_ranges, context_ranges, surviving_ranges; simpl.
      unfold pending_ranges. rewrite P. simpl. repeat rewrite in_app_iff; simpl. tauto.
    + simpl. exact AP.
    + apply rehome_summary_sound; exact SUM.
  - intros _. unfold data_ownership, data_scope; simpl.
    assert (OLD : forall xs n, (forall r, In r xs -> In r (protected_roots s)) ->
      bounded 256 xs n (protection_table s) ->
      bounded 256 xs n (rehome_extent 256 (prep_range p) lifetime (protection_table s))).
    { intros xs n SUB B q N. rewrite (apart_rehome_unchanged _ _ _ _ _ AP).
      - apply B; exact N.
      - eapply needed_membership; eauto. }
    assert (MEM : forall r, In r (protected_roots s) <->
      In r (protection_current s) \/ In r (attached_ranges s) \/
      In r (flat_map (fun x => x) (protection_saved s)) \/
      In r (protection_base s) \/ In r (physical_authority s) \/
      In r (acknowledged_authority s)).
    { intro r. unfold protected_roots, context_ranges, surviving_ranges; simpl.
      repeat rewrite in_app_iff. tauto. }
    split; [|split].
    + unfold scope_invariant; simpl. split; [exact D|]. split; [|split].
      * apply OLD; [intros r R; apply MEM; apply in_app_or in R; tauto|exact CUR].
      * intros i v E. apply OLD; [|eapply STACK; eauto].
        intros r R. apply MEM. right; right; left. apply in_flat_map.
        exists v; split; [eapply nth_error_In; eauto|exact R].
      * apply OLD; [intros r R; apply MEM; tauto|exact BASE].
    + apply OLD; [intros r R; apply MEM; apply in_app_or in R; tauto|exact AUTH].
    + intros q [r [[E|[]] T]]. subst r. unfold rehome_extent. rewrite T; simpl; lia.
Qed.

Lemma ownership_without_token_covers s :
  data_ownership 256 s -> pending_preparation s = None ->
  preparation_invariant 256 s.
Proof.
  intros [[D [CUR [STACK BASE]]] [AUTH P]] NONE. split; [|rewrite NONE; exact I].
  intros q [r [R T]]. unfold required_ranges, context_ranges, surviving_ranges in R;
    simpl in R. unfold pending_ranges in R; rewrite NONE in R.
  repeat rewrite in_app_iff in R; simpl in R.
  assert (GET : forall xs n, In r xs -> bounded 256 xs n (protection_table s) ->
      owner (protection_table s q) <> 0).
  { intros xs n IN B. assert (N : needed 256 xs q) by (exists r; auto).
    specialize (B q N); lia. }
  destruct R as [[R|[R|R]]|[R|[R|[R|[]]]]].
  - eapply GET; [apply in_or_app; left; exact R|exact CUR].
  - apply in_flat_map in R. destruct R as [v [V R]].
    apply In_nth_error in V. destruct V as [i E]. eapply GET; [exact R|eapply STACK; eauto].
  - eapply GET; eauto.
  - eapply GET; [apply in_or_app; right; exact R|exact CUR].
  - eapply GET; [apply in_or_app; left; exact R|exact AUTH].
  - eapply GET; [apply in_or_app; right; exact R|exact AUTH].
Qed.

Theorem snapshot_install_preserves s p prefix count :
  data_invariant s -> protection_frozen s = false ->
  pending_preparation s = Some p -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  bounded 256 [prep_range p] (S (length prefix)) (protection_table s) ->
  data_invariant (snapshot_install prefix count (prep_range p) s).
Proof.
  intros [INV OWN] F P N SHAPE BOSS. specialize (OWN F).
  destruct OWN as [[D [CUR [STACK BASE]]] [AUTH PEND]].
  cbn [data_scope current_ranges saved_ranges base_ranges scope_pages] in D, CUR, STACK, BASE.
  assert (OWN : data_ownership 256 (snapshot_install prefix count (prep_range p) s)).
  { unfold data_ownership, data_scope, snapshot_install; simpl. rewrite app_nil_r.
    split; [|split; auto]. unfold scope_invariant; simpl.
    split; [rewrite SHAPE, length_app, repeat_length in D;
      rewrite length_app, repeat_length; exact D|]. split; [|split; [|exact BASE]].
    - change (bounded 256 ([prep_range p] ++ (protection_current s ++ attached_ranges s))
        (S (length (prefix ++ repeat (prep_range p :: (protection_current s ++ attached_ranges s)) count)))
        (protection_table s)).
      apply bounded_union.
      + eapply bounded_weaken; [|exact BOSS]. rewrite length_app, repeat_length; lia.
      + rewrite SHAPE, length_app, repeat_length in CUR.
        rewrite length_app, repeat_length. exact CUR.
    - intros i v E. destruct (Nat.lt_ge_cases i (length prefix)) as [L|L].
      + rewrite nth_error_app1 in E by exact L. apply (STACK i).
        rewrite SHAPE, nth_error_app1 by exact L; exact E.
      + rewrite nth_error_app2 in E by exact L. apply repeated_view_nth in E.
        destruct E as [-> K]. change (bounded 256
          ([prep_range p] ++ (protection_current s ++ attached_ranges s))
          (S i) (protection_table s)). apply bounded_union.
        * eapply bounded_weaken; [|exact BOSS]; lia.
        * eapply bounded_weaken; [|eapply first_deferred_bound; [exact N|rewrite <- SHAPE; exact STACK]]; lia. }
  split; [split|].
  - apply ownership_without_token_covers; [exact OWN|reflexivity].
  - exact (proj2 INV).
  - intros _; exact OWN.
Qed.

Theorem snapshot_rehome_install_preserves s p prefix count :
  data_invariant s -> protection_frozen s = false ->
  pending_preparation s = Some p -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  data_invariant (snapshot_install prefix count (prep_range p)
    (snapshot_rehome (length prefix) s)).
Proof.
  intros INV F P N SHAPE.
  assert (L : length prefix <= length (protection_saved s)).
  { rewrite SHAPE, length_app, repeat_length; lia. }
  pose proof (snapshot_rehome_preserves s p (length prefix) INV F P L) as RH.
  eapply snapshot_install_preserves with (p:=set_phase p Detached); [exact RH| | |exact N| |].
  - unfold snapshot_rehome; rewrite P; exact F.
  - unfold snapshot_rehome; rewrite P; reflexivity.
  - unfold snapshot_rehome; rewrite P; exact SHAPE.
  - unfold snapshot_rehome; rewrite P; simpl. intros q [r [[E|[]] T]].
    subst r. unfold rehome_extent; rewrite T; simpl; lia.
Qed.

Lemma saved_prefix_resolve id (fs : list (option nat * list extent)) : all_saved fs -> map (resolve id) fs = fs.
Proof.
  intros H. induction H as [|[[r|] v] tail H T IH]; simpl; auto.
  - f_equal; exact IH.
  - destruct H as [r H]; discriminate.
Qed.

Theorem snapshot_install_correspondence boss decoded image frames s id prefix count p :
  snapshot_correspondence boss decoded image None frames s ->
  all_saved prefix -> frames = prefix ++ repeat (None,image) count ->
  decoded id = Some image -> boss id = prep_range p ->
  pending_preparation s = Some p ->
  snapshot_correspondence boss decoded image (Some id) (map (resolve id) frames)
    (snapshot_install (map (snapshot_dependencies boss) prefix) count (prep_range p)
      (snapshot_rehome (length prefix) s)).
Proof.
  intros [ROOT [CUR STACK]] SAVED SHAPE ENC RANGE P.
  split.
  - eapply root_step_inductive; [exact ROOT|apply root_save; exact ENC].
  - unfold snapshot_install, snapshot_rehome; rewrite P; simpl.
    unfold snapshot_dependencies in CUR; simpl in CUR.
    split.
    + rewrite app_nil_r, CUR. unfold snapshot_dependencies; simpl. rewrite RANGE; reflexivity.
    + rewrite SHAPE, !map_app, !map_repeat, saved_prefix_resolve by exact SAVED.
      rewrite CUR. unfold snapshot_dependencies; simpl. rewrite RANGE; reflexivity.
Qed.

(* The None guard is read from the concrete stack. Its shared suffix and
   owner's bound are conclusions of correspondence, not caller assumptions. *)
Theorem snapshot_barrier_shape boss decoded image current frames s :
  snapshot_correspondence boss decoded image current frames s ->
  (exists b, In b frames /\ fst b = None) ->
  current = None /\ exists prefix count,
    count > 0 /\ all_saved prefix /\ frames = prefix ++ repeat (None,image) count /\
    protection_saved s = map (snapshot_dependencies boss) prefix ++
      repeat (protection_current s ++ attached_ranges s) count /\
    snapshot_owner (map (@fst (option nat) (list extent)) frames) = length prefix.
Proof.
  intros COR [b [IN NONE]]. destruct COR as [ROOT [CUR STACK]].
  destruct ROOT as [D [O [C AGREES]]].
  pose proof (proj1 (Forall_forall _ _) AGREES b IN) as B.
  cbn beta in B. rewrite NONE in B. destruct B as [VIEW CURRENT]. split; [exact CURRENT|].
  destruct (snapshot_suffix_from_correspondence boss decoded image current frames s
    ltac:(repeat split; assumption)) as [prefix [count [SAVED [SHAPE DEPS]]]].
  assert (POS : count > 0).
  { destruct count; [|lia]. simpl in SHAPE. rewrite app_nil_r in SHAPE.
    subst frames. pose proof (proj1 (Forall_forall _ _) SAVED b IN) as [r E]. congruence. }
  exists prefix, count. repeat split; auto.
  - rewrite CURRENT in CUR. simpl in CUR. rewrite CUR; exact DEPS.
  - rewrite SHAPE. apply saved_prefix_owner; assumption.
Qed.

Definition snapshot_reserve r s := change_preparation s
  (Some (Build_preparation BossPreparation r Reserved)) false
  (reserve_extent 256 r (length (protection_saved s)) (protection_table s))
  (set_summary (protection_bits s) (length (protection_saved s))) true.
Definition snapshot_written s :=
  match pending_preparation s with
  | Some p => change_preparation s (Some (set_phase p Written)) false
      (protection_table s) (protection_bits s) (protection_dirty s)
  | None => s
  end.
Lemma snapshot_reserve_preserves s r :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> data_invariant (snapshot_reserve r s).
Proof.
  intros [I OWN] F P FREE. split.
  - eapply protection_step_inductive; [exact I|]. apply reserve_preparation; assumption.
  - intros _. apply data_reserve_ownership; [apply OWN; exact F|exact FREE].
Qed.
Lemma snapshot_written_preserves s p :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = Some p ->
  data_invariant (snapshot_written s).
Proof.
  intros [I OWN] F P. unfold snapshot_written; rewrite P. split.
  - eapply protection_step_inductive; [exact I|]. apply physical_preparation_complete; assumption.
  - intros _. apply data_phase_ownership; [apply OWN; exact F|exact P].
Qed.

(* Before-return errors do not run the installation continuation. The bool
   denotes the actual freeze policy, not all errors indiscriminately. *)
Definition snapshot_error (frozen : bool) s :=
  data_next DataDrop (if frozen then data_next DataFreeze s else s).
Theorem snapshot_error_preserves s p frozen :
  data_invariant s -> pending_preparation s = Some p ->
  data_invariant (snapshot_error frozen s) /\
  protection_saved (snapshot_error frozen s) = protection_saved s /\
  protection_current (snapshot_error frozen s) = protection_current s /\
  attached_ranges (snapshot_error frozen s) = attached_ranges s.
Proof.
  intros INV P. split.
  - unfold snapshot_error. apply data_command_preserves.
    + destruct frozen; [apply data_command_preserves; [exact INV|exact I]|exact INV].
    + destruct frozen; simpl; exists p; exact P.
  - unfold snapshot_error, data_next. destruct frozen; simpl; rewrite ?P;
      simpl; repeat split; reflexivity.
Qed.
Theorem snapshot_error_frozen_keeps_pages s :
  protection_table (snapshot_error true s) = protection_table s.
Proof. reflexivity. Qed.

(* Success is a composition of four updates, each over the same table.
   [snapshot_written] only follows success of the lower writer: Reset has no
   continuation and never justifies that step. *)
Definition snapshot_success prefix count r s :=
  snapshot_install prefix count r
    (snapshot_rehome (length prefix) (snapshot_written (snapshot_reserve r s))).
Theorem snapshot_success_preserves s prefix count r :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  data_invariant (snapshot_success prefix count r s).
Proof.
  intros INV F P FREE N SHAPE.
  pose proof (snapshot_reserve_preserves s r INV F P FREE) as RES.
  pose proof (snapshot_written_preserves (snapshot_reserve r s)
    (Build_preparation BossPreparation r Reserved) RES eq_refl eq_refl) as WR.
  unfold snapshot_success. eapply snapshot_rehome_install_preserves
    with (p:=Build_preparation BossPreparation r Written); eauto.
Qed.

Theorem snapshot_then_data_preserves s prefix count r commands :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  data_calls commands (snapshot_success prefix count r s) ->
  data_invariant (execute_data commands (snapshot_success prefix count r s)).
Proof.
  intros. apply data_execution_preserves; [eapply snapshot_success_preserves; eauto|assumption].
Qed.
Theorem snapshot_success_does_not_publish s prefix count r :
  physical_authority (snapshot_success prefix count r s) = physical_authority s /\
  acknowledged_authority (snapshot_success prefix count r s) = acknowledged_authority s.
Proof. split; reflexivity. Qed.

(* Admission for the RAM install. The owner equality is supplied by the
   immediately preceding rehome, never by an invariant in a callee contract. *)
Definition snapshot_install_caller prefix count s :=
  protection_frozen s = false /\ exists p,
    pending_preparation s = Some p /\ prep_kind p = BossPreparation /\
    prep_phase p = Detached /\ count > 0 /\
    protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count /\
    (forall q, touches 256 (prep_range p) q = true ->
      owner (protection_table s q) = S (length prefix)).
Lemma snapshot_install_caller_derived prefix count s p :
  protection_frozen s = false -> pending_preparation s = Some p ->
  prep_kind p = BossPreparation -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  snapshot_install_caller prefix count (snapshot_rehome (length prefix) s).
Proof.
  intros F P K N SHAPE. unfold snapshot_install_caller, snapshot_rehome; rewrite P; simpl.
  split; [exact F|]. exists (set_phase p Detached). repeat split; auto.
  intros q T. simpl in T. unfold rehome_extent; rewrite T; reflexivity.
Qed.
Definition snapshot_install_pending prefix count s :=
  match pending_preparation s with
  | Some p => snapshot_install prefix count (prep_range p) s
  | None => s
  end.
Theorem snapshot_install_pending_preserves prefix count s :
  data_invariant s -> snapshot_install_caller prefix count s ->
  data_invariant (snapshot_install_pending prefix count s).
Proof.
  intros INV [F [p [P [K [W [N [SHAPE OWNER]]]]]]].
  unfold snapshot_install_pending; rewrite P. eapply snapshot_install_preserves; eauto.
  intros q [r [[E|[]] T]]. subst r. rewrite (OWNER q T); lia.
Qed.

(* A barrier is skipped once every active boundary is materialized. Merely
   preparing, dropping or attaching Data never introduces a new None boundary.
   No new scope is allowed by the actual synchronous prepare/attach body. *)
Theorem snapshot_resolved_barrier_has_no_work id frames :
  ~ exists b, In b (map (@resolve (list extent) id) frames) /\ fst b = None.
Proof.
  intros [b [IN NONE]]. pose proof (resolved_all_saved id frames) as H.
  destruct (proj1 (Forall_forall _ _) H b IN) as [r E]. congruence.
Qed.
Theorem snapshot_unchanged_no_work s :
  data_next DataUnchanged s = s /\ protection_dirty (data_next DataUnchanged s) = protection_dirty s.
Proof. split; reflexivity. Qed.

(* Once installation has returned, the same data_invariant discharges the
   existing local Data caller proofs. In particular no independent table or
   assumed release separation is passed to these continuations. *)
Theorem snapshot_success_then_B_failure s prefix count r a b completed uncertain :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  let ready := snapshot_success prefix count r s in
  length (protection_saved ready) < 6 -> free_range 256 (protection_table ready) a ->
  free_range 256 (reserve_extent 256 a (S (length (protection_saved ready))) (protection_table ready)) b ->
  data_invariant (execute_data (data_B_failed_path a b completed uncertain ready) ready).
Proof.
  intros INV F P FREE N SHAPE ready DEP A B.
  apply data_B_failed_preserves; try assumption; try reflexivity.
  eapply snapshot_success_preserves; eauto.
Qed.

Theorem snapshot_barrier_composed boss decoded image current frames s id :
  data_invariant s -> snapshot_correspondence boss decoded image current frames s ->
  (exists b, In b frames /\ fst b = None) ->
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) (boss id) -> decoded id = Some image ->
  exists prefix count,
    count > 0 /\
    snapshot_owner (map (@fst (option nat) (list extent)) frames) = length prefix /\
    let final := snapshot_success (map (snapshot_dependencies boss) prefix) count (boss id) s in
    data_invariant final /\
    snapshot_correspondence boss decoded image (Some id) (map (resolve id) frames) final.
Proof.
  intros INV COR NEED F P FREE ENC.
  destruct (snapshot_barrier_shape boss decoded image current frames s COR NEED)
    as [CURRENT [prefix [count [POS [SAVED [SHAPE [DEPS OWNER]]]]]]].
  subst current. exists prefix, count. split; [exact POS|]. split; [exact OWNER|].
  cbn zeta. split.
  - apply snapshot_success_preserves; assumption.
  - unfold snapshot_success. rewrite length_map.
    eapply snapshot_install_correspondence with
      (p:=Build_preparation BossPreparation (boss id) Written); try reflexivity; try assumption.
Qed.

(* Frames are observations of the unique saved-dependency stack. These local
   token instructions do not change it. The ensuing close removes its last
   element; it does not free a surviving parent's prestate. *)
Definition data_body_command c : Prop :=
  match c with DataBegin | DataClose _ _ _ => False | _ => True end.
Theorem data_body_keeps_saved_projection boss frames c s :
  data_body_command c ->
  protection_saved s = map (snapshot_dependencies boss) frames ->
  protection_saved (data_next c s) = map (snapshot_dependencies boss) frames.
Proof.
  intros BODY E. destruct c; simpl in BODY; try contradiction;
    unfold data_next; try destruct (pending_preparation s); exact E.
Qed.

Definition after_barrier_B_failed a b completed uncertain views old :=
  successful_data_member a ++ failed_data_member b completed uncertain ++
    [DataClose views old false].
Theorem after_barrier_B_failed_callers a b completed uncertain views old s :
  protection_frozen s = false -> pending_preparation s = None ->
  protection_saved s = views ++ [old] -> free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (length (protection_saved s)) (protection_table s)) b ->
  data_calls (after_barrier_B_failed a b completed uncertain views old) s.
Proof.
  intros F P STACK A B. destruct completed, uncertain;
    unfold after_barrier_B_failed, successful_data_member, failed_data_member;
    cbn [app data_calls data_caller data_next change_preparation Build_protection_state ProtectionState context_scopes
      protection_saved protection_current protection_base attached_ranges pending_preparation
      physical_authority acknowledged_authority protection_frozen protection_table protection_bits protection_dirty];
    repeat split; try assumption; try reflexivity;
    try (eexists; repeat split; reflexivity || (intros; discriminate)).
Qed.
Theorem snapshot_A_attached_B_failed s prefix r a b completed uncertain :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  protection_saved s = prefix ++ [protection_current s ++ attached_ranges s] ->
  free_range 256 (protection_table s) r ->
  let ready := snapshot_success prefix 1 r s in
  free_range 256 (protection_table ready) a ->
  free_range 256 (reserve_extent 256 a (length (protection_saved ready)) (protection_table ready)) b ->
  let old := r :: (protection_current s ++ attached_ranges s) in
  let final := execute_data (after_barrier_B_failed a b completed uncertain prefix old) ready in
  data_invariant final /\ protection_current final = old /\ attached_ranges final = [].
Proof.
  intros INV F P STACK FREE ready A B old final.
  assert (READY : data_invariant ready).
  { apply snapshot_success_preserves; try assumption; simpl; auto. }
  split.
  - apply data_execution_preserves; [exact READY|].
    apply after_barrier_B_failed_callers; try assumption; reflexivity.
  - subst final. destruct completed, uncertain; split; reflexivity.
Qed.

Definition after_barrier_accept_child_rollback_parent a b prefix old :=
  successful_data_member a ++ successful_data_member b ++
    [DataClose (prefix ++ [old]) old true; DataClose prefix old false].
Theorem after_barrier_accept_child_rollback_parent_callers a b prefix old s :
  protection_frozen s = false -> pending_preparation s = None ->
  protection_saved s = (prefix ++ [old]) ++ [old] ->
  free_range 256 (protection_table s) a ->
  free_range 256 (reserve_extent 256 a (length (protection_saved s)) (protection_table s)) b ->
  data_calls (after_barrier_accept_child_rollback_parent a b prefix old) s.
Proof.
  intros F P STACK A B. unfold after_barrier_accept_child_rollback_parent.
  apply data_calls_app; split; [apply successful_data_member_callers; assumption|].
  apply data_calls_app; split.
  - apply successful_data_member_callers; try reflexivity; exact B.
  - split; [split; [reflexivity|exact STACK]|]. split; [repeat split; reflexivity|exact I].
Qed.
Theorem snapshot_shared_child_accept_parent_rollback s prefix r a b :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) 2 ->
  free_range 256 (protection_table s) r ->
  let ready := snapshot_success prefix 2 r s in
  free_range 256 (protection_table ready) a ->
  free_range 256 (reserve_extent 256 a (length (protection_saved ready)) (protection_table ready)) b ->
  let old := r :: (protection_current s ++ attached_ranges s) in
  let final := execute_data (after_barrier_accept_child_rollback_parent a b prefix old) ready in
  data_invariant final /\ protection_current final = old /\
  protected (needed 256 [r]) (protection_table final).
Proof.
  intros INV F P STACK FREE ready A B old final.
  assert (READY : data_invariant ready).
  { apply snapshot_success_preserves; try assumption; lia. }
  assert (FINAL : data_invariant final).
  { apply data_execution_preserves; [exact READY|].
    apply after_barrier_accept_child_rollback_parent_callers; try assumption; try reflexivity.
    unfold ready, snapshot_success, snapshot_install; simpl. rewrite <- app_assoc; reflexivity. }
  split; [exact FINAL|]. split; [reflexivity|].
  eapply protected_subset; [|exact (proj1 (proj1 (proj1 FINAL)))].
  intros x [E|[]]. subst x. unfold required_ranges, context_ranges, surviving_ranges;
    simpl. repeat rewrite in_app_iff. tauto.
Qed.

Theorem snapshot_entry_correspondence boss decoded image base t bits dirty :
  snapshot_correspondence boss decoded image None []
    (enter_with_summaries (Build_scope_state image [] base t) bits dirty).
Proof.
  unfold snapshot_correspondence. split.
  - unfold roots_invariant, agrees; simpl. split; [lia|].
    split; [exact I|]. split; [intros r E; discriminate|constructor].
  - split; [simpl; rewrite app_nil_r; reflexivity|reflexivity].
Qed.
Theorem snapshot_begin_correspondence boss decoded image current frames s :
  snapshot_correspondence boss decoded image current frames s ->
  data_caller DataBegin s ->
  snapshot_correspondence boss decoded image current (frames ++ [(current,image)])
    (data_next DataBegin s).
Proof.
  intros [ROOT [CUR STACK]] [F [P DEP]]. split.
  - eapply root_step_inductive; [exact ROOT|]. apply root_begin.
    rewrite STACK, length_map in DEP; exact DEP.
  - split.
    + change ((protection_current s ++ attached_ranges s) ++ [] =
        snapshot_dependencies boss (current,image)). rewrite app_nil_r; exact CUR.
    + change (protection_saved s ++ [protection_current s ++ attached_ranges s] =
        map (snapshot_dependencies boss) (frames ++ [(current,image)])).
      rewrite map_app; simpl. rewrite STACK, CUR; reflexivity.
Qed.
Theorem snapshot_body_saved_roots_do_not_need_save boss frames c s :
  all_saved frames -> data_body_command c ->
  protection_saved s = map (snapshot_dependencies boss) frames ->
  protection_saved (data_next c s) = map (snapshot_dependencies boss) frames /\
  ~ (exists b, In b frames /\ fst b = None).
Proof.
  intros SAVED BODY E. split; [apply data_body_keeps_saved_projection; assumption|].
  intros [b [IN NONE]]. destruct (proj1 (Forall_forall _ _) SAVED b IN) as [r R]. congruence.
Qed.

Theorem snapshot_error_keeps_correspondence boss decoded image current frames s p frozen :
  snapshot_correspondence boss decoded image current frames s ->
  data_invariant s -> pending_preparation s = Some p ->
  snapshot_correspondence boss decoded image current frames (snapshot_error frozen s).
Proof.
  intros [ROOT [CUR STACK]] INV P.
  destruct (snapshot_error_preserves s p frozen INV P) as [_ [S [C A]]].
  split; [exact ROOT|]. rewrite S, C, A; auto.
Qed.
Theorem snapshot_reservation_program_locality g s r a bytes outcome f f' :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r ->
  (forall q, touches 256 {| offset := a; span := length bytes |} q = true ->
    touches 256 r q = true) ->
  program_step g f a bytes outcome f' -> unchanged (protected_roots s) f f'.
Proof.
  intros INV F P FREE INS STEP.
  pose proof (snapshot_reserve_preserves s r INV F P FREE) as RES.
  eapply preparation_program_preserves_roots with
    (s:=snapshot_reserve r s) (p:=Build_preparation BossPreparation r Reserved)
    (page:=256) (a:=a) (data:=bytes) (result:=outcome).
  - lia.
  - exact (proj1 (proj1 RES)).
  - reflexivity.
  - exact INS.
  - exact STEP.
Qed.

(* The post-write rehome/Address::new `?` exits in write_snapshot do not use
   release_unattached. Forget the local handle while retaining the allocation;
   subsequent scope cleanup is still governed by the ordinary Data invariant. *)
Definition snapshot_retain_error s := change_preparation s None
  (protection_frozen s) (protection_table s) (protection_bits s) (protection_dirty s).
Theorem snapshot_retain_error_preserves s :
  data_invariant s -> data_invariant (snapshot_retain_error s).
Proof.
  intros [[ [C AP] SUM] OWN]. split.
  - split; [split|exact SUM]; [|exact I].
    eapply protected_subset; [|exact C]. intros r R.
    unfold snapshot_retain_error, required_ranges, context_ranges,
      surviving_ranges, change_preparation, Build_protection_state, context_scopes,
      pending_ranges in R; simpl in R.
    unfold required_ranges, context_ranges, surviving_ranges; simpl.
    repeat rewrite in_app_iff in *; simpl in R; tauto.
  - intros F. specialize (OWN F). destruct OWN as [S [A P]].
    split; [exact S|split; [exact A|exact I]].
Qed.
Theorem snapshot_retain_error_keeps_correspondence boss decoded image current frames s :
  snapshot_correspondence boss decoded image current frames s ->
  snapshot_correspondence boss decoded image current frames (snapshot_retain_error s).
Proof. intros H; exact H. Qed.
Theorem snapshot_retain_error_keeps_table s :
  protection_table (snapshot_retain_error s) = protection_table s /\
  protection_frozen (snapshot_retain_error s) = protection_frozen s /\
  pending_preparation (snapshot_retain_error s) = None.
Proof. repeat split; reflexivity. Qed.

(* Exact current dependencies replace the previous conservative staging view.
   Removing a dependency never clears a page cell. Saved/base/authority views
   remain independent roots and may still reference the same physical extent. *)
Definition replace_current_dependencies next s :=
  Build_protection_state
    (Build_scope_state next (protection_saved s) (protection_base s) (protection_table s))
    [] None (physical_authority s) (acknowledged_authority s)
    (protection_frozen s) (protection_table s) (protection_bits s) true.
Theorem replace_current_dependencies_preserves s next :
  data_invariant s -> pending_preparation s = None ->
  (forall r, In r next -> In r (protection_current s ++ attached_ranges s)) ->
  data_invariant (replace_current_dependencies next s).
Proof.
  intros [[[C AP] SUM] OWN] P SUB. split.
  - split; [split; [|exact I]|exact SUM].
    eapply protected_subset; [|exact C]. intros r R.
    unfold required_ranges, context_ranges, surviving_ranges,
      replace_current_dependencies, Build_protection_state, context_scopes, pending_ranges in R;
      simpl in R.
    unfold required_ranges, context_ranges, surviving_ranges; simpl.
    repeat rewrite in_app_iff in *; simpl in R.
    assert (S : In r next -> In r (protection_current s) \/ In r (attached_ranges s)).
    { intros H. apply in_app_or; apply SUB; exact H. } tauto.
  - intros F. destruct (OWN F) as [[D [CUR [STACK BASE]]] [AUTH _]].
    unfold data_ownership, data_scope, replace_current_dependencies; simpl; rewrite app_nil_r.
    split; [|split; auto]. unfold scope_invariant; simpl.
    split; [exact D|]. split; [|split; assumption].
    eapply bounded_subset; [exact SUB|exact CUR].
Qed.
Definition image_current_correspondence ranges image root s :=
  protection_current s ++ attached_ranges s = root ++ image_dependencies ranges image.
Definition exact_attach ranges image index entry s :=
  replace_current_dependencies (image_dependencies ranges (image_replace image index (Some entry)))
    (data_next DataAttach s).
Theorem exact_attach_preserves ranges image root index entry s p :
  data_invariant s -> data_caller DataAttach s -> pending_preparation s = Some p ->
  image_current_correspondence ranges image root s -> ranges entry = [prep_range p] ->
  data_invariant (exact_attach ranges image index entry s) /\
  image_current_correspondence ranges (image_replace image index (Some entry)) []
    (exact_attach ranges image index entry s).
Proof.
  intros INV CALL P COR RANGE. split; [|unfold image_current_correspondence, exact_attach,
    replace_current_dependencies; simpl; rewrite app_nil_r; reflexivity].
  unfold exact_attach. apply replace_current_dependencies_preserves.
  - apply data_command_preserves; assumption.
  - unfold data_next; rewrite P; reflexivity.
  - intros r R. apply dependencies_replace_subset in R. destruct R as [R|R].
    + simpl in R; rewrite RANGE in R. destruct R as [E|[]]; subst r.
      unfold data_next; rewrite P; simpl. apply in_or_app; right; simpl; auto.
    + assert (OLD : In r (protection_current s ++ attached_ranges s)).
      { unfold image_current_correspondence in COR. rewrite COR. apply in_or_app; auto. }
      unfold data_next; rewrite P; simpl. apply in_app_or in OLD.
      apply in_or_app; simpl; tauto.
Qed.
Theorem exact_attach_observers ranges image index entry s p :
  pending_preparation s = Some p ->
  protection_saved (exact_attach ranges image index entry s) = protection_saved s /\
  protection_table (exact_attach ranges image index entry s) = protection_table s /\
  protection_bits (exact_attach ranges image index entry s) = protection_bits s /\
  protection_dirty (exact_attach ranges image index entry s) = true /\
  physical_authority (exact_attach ranges image index entry s) = physical_authority s /\
  acknowledged_authority (exact_attach ranges image index entry s) = acknowledged_authority s.
Proof. intros P. unfold exact_attach, data_next; rewrite P; repeat split; reflexivity. Qed.
Definition exact_delete ranges image index s :=
  replace_current_dependencies (image_dependencies ranges (image_replace image index None)) s.
Theorem exact_delete_preserves ranges image root index s :
  data_invariant s -> pending_preparation s = None ->
  image_current_correspondence ranges image root s ->
  data_invariant (exact_delete ranges image index s) /\
  image_current_correspondence ranges (image_replace image index None) []
    (exact_delete ranges image index s) /\
  protection_table (exact_delete ranges image index s) = protection_table s.
Proof.
  intros INV P COR. split.
  - apply replace_current_dependencies_preserves; auto.
    intros r R. apply dependencies_replace_subset in R. destruct R as [R|R]; [contradiction|].
    unfold image_current_correspondence in COR; rewrite COR. apply in_or_app; auto.
  - split; [unfold image_current_correspondence, exact_delete,
      replace_current_dependencies; simpl; rewrite app_nil_r; reflexivity|reflexivity].
Qed.
Theorem exact_rollback_correspondence ranges old_image old_root views s :
  data_invariant s -> pending_preparation s = None ->
  protection_saved s = views ++ [old_root ++ image_dependencies ranges old_image] ->
  let final := data_next (DataClose views (old_root ++ image_dependencies ranges old_image) false) s in
  data_invariant final /\ image_current_correspondence ranges old_image old_root final.
Proof.
  intros INV P STACK; cbn zeta. split.
  - apply data_command_preserves; [exact INV|split; assumption].
  - unfold image_current_correspondence; simpl; rewrite app_nil_r; reflexivity.
Qed.
Theorem exact_current_enumeration ranges image s :
  image_current_correspondence ranges image [] s ->
  forall r, In r (protection_current s ++ attached_ranges s) <->
    exists i e, nth_error image i = Some (Some e) /\ In r (ranges e).
Proof. intros COR r; rewrite COR. simpl. apply dependencies_occurrence. Qed.

Definition exact_member ranges image index entry r s :=
  exact_attach ranges image index entry (execute_data [DataReserve r; DataWritten] s).
Theorem exact_member_preserves ranges image root index entry r s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> ranges entry = [r] ->
  image_current_correspondence ranges image root s ->
  data_invariant (exact_member ranges image index entry r s) /\
  image_current_correspondence ranges (image_replace image index (Some entry)) []
    (exact_member ranges image index entry r s).
Proof.
  intros INV F P FREE RANGE COR. unfold exact_member.
  apply exact_attach_preserves with (root:=root) (p:=Build_preparation ObjectPreparation r Written).
  - apply data_execution_preserves; [exact INV|].
    split; [simpl; auto|]. split; [|exact I]. split; [reflexivity|].
    exists (Build_preparation ObjectPreparation r Reserved); repeat split; try reflexivity; intros; discriminate.
  - split; [reflexivity|]. exists (Build_preparation ObjectPreparation r Written); repeat split; reflexivity.
  - reflexivity.
  - exact COR.
  - exact RANGE.
Qed.
Theorem exact_pair_preserves ranges image root ia ib a b ra rb s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  image_current_correspondence ranges image root s ->
  ranges a = [ra] -> ranges b = [rb] -> free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  let after_a := exact_member ranges image ia a ra s in
  let image_a := image_replace image ia (Some a) in
  let final := exact_member ranges image_a ib b rb after_a in
  data_invariant final /\
  image_current_correspondence ranges (image_replace image_a ib (Some b)) [] final.
Proof.
  intros INV F P COR A B FA FB; cbn zeta.
  destruct (exact_member_preserves ranges image root ia a ra s INV F P FA A COR) as [IA CA].
  apply exact_member_preserves with (root:=[]); try reflexivity; assumption.
Qed.
Theorem exact_pair_rollback ranges image root ia ib a b ra rb s views old_root old_image :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  image_current_correspondence ranges image root s ->
  protection_saved s = views ++ [old_root ++ image_dependencies ranges old_image] ->
  ranges a = [ra] -> ranges b = [rb] -> free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  let after_a := exact_member ranges image ia a ra s in
  let final := exact_member ranges (image_replace image ia (Some a)) ib b rb after_a in
  let restored := data_next (DataClose views (old_root ++ image_dependencies ranges old_image) false) final in
  data_invariant restored /\ image_current_correspondence ranges old_image old_root restored.
Proof.
  intros INV F P COR STACK A B FA FB; cbn zeta.
  apply exact_rollback_correspondence; try reflexivity; try exact STACK.
  exact (proj1 (exact_pair_preserves ranges image root ia ib a b ra rb s INV F P COR A B FA FB)).
Qed.
Theorem exact_A_then_B_failure ranges image root ia a ra rb s views old_root old_image completed frozen :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  image_current_correspondence ranges image root s ->
  protection_saved s = views ++ [old_root ++ image_dependencies ranges old_image] ->
  ranges a = [ra] -> free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  let after_a := exact_member ranges image ia a ra s in
  let failed := execute_data (failed_data_member rb completed frozen) after_a in
  let restored := data_next (DataClose views (old_root ++ image_dependencies ranges old_image) false) failed in
  data_invariant restored /\ image_current_correspondence ranges old_image old_root restored.
Proof.
  intros INV F P COR STACK A FA FB; cbn zeta.
  destruct (exact_member_preserves ranges image root ia a ra s INV F P FA A COR) as [IA CA].
  apply exact_rollback_correspondence.
  - apply data_execution_preserves; [exact IA|].
    destruct completed, frozen; unfold failed_data_member;
      cbn [data_calls data_caller data_next execute_data app exact_member exact_attach
        replace_current_dependencies change_preparation Build_protection_state ProtectionState context_scopes
        protection_saved protection_current protection_base attached_ranges pending_preparation
        physical_authority acknowledged_authority protection_frozen protection_table protection_bits protection_dirty];
      repeat split; try reflexivity; try exact FB;
      try (eexists; repeat split; try reflexivity; intros; discriminate).
  - apply failed_data_member_consumes_token.
  - destruct completed, frozen; exact STACK.
Qed.
Theorem exact_pair_accept_child_rollback_parent ranges image root ia ib a b ra rb s views parent child :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  image_current_correspondence ranges image root s ->
  protection_saved s = (views ++ [parent]) ++ [child] ->
  ranges a = [ra] -> ranges b = [rb] -> free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  let after_a := exact_member ranges image ia a ra s in
  let final := exact_member ranges (image_replace image ia (Some a)) ib b rb after_a in
  let accepted := data_next (DataClose (views ++ [parent]) child true) final in
  let restored := data_next (DataClose views parent false) accepted in
  data_invariant restored /\ protection_current restored = parent /\ attached_ranges restored = [].
Proof.
  intros INV F P COR STACK A B FA FB; cbn zeta. split.
  - apply data_command_preserves.
    + apply data_command_preserves.
      * exact (proj1 (exact_pair_preserves ranges image root ia ib a b ra rb s INV F P COR A B FA FB)).
      * split; [reflexivity|exact STACK].
    + split; reflexivity.
  - split; reflexivity.
Qed.
Theorem snapshot_installs_exact_image_view ranges image prefix count r s :
  image_current_correspondence ranges image [] s ->
  image_current_correspondence ranges image [r] (snapshot_success prefix count r s).
Proof.
  unfold image_current_correspondence, snapshot_success, snapshot_install; simpl.
  intros E. rewrite app_nil_r, E; reflexivity.
Qed.
Theorem exact_attach_preserves_saved_projection boss frames ranges image index entry s p :
  pending_preparation s = Some p ->
  protection_saved s = map (snapshot_dependencies boss) frames ->
  protection_saved (exact_attach ranges image index entry s) = map (snapshot_dependencies boss) frames.
Proof. intros P E. rewrite (proj1 (exact_attach_observers ranges image index entry s p P)); exact E. Qed.

Record exact_edit := ExactEdit {
  edit_index : nat; edit_entry : compact_entry; edit_reservation : extent
}.
Fixpoint edited_image commands image :=
  match commands with [] => image | c::tail =>
    edited_image tail (image_replace image (edit_index c) (Some (edit_entry c))) end.
Fixpoint execute_exact commands ranges image s :=
  match commands with [] => s | c::tail =>
    execute_exact tail ranges (image_replace image (edit_index c) (Some (edit_entry c)))
      (exact_member ranges image (edit_index c) (edit_entry c) (edit_reservation c) s) end.
Fixpoint exact_calls kind ranges commands image s : Prop :=
  match commands with [] => True | c::tail =>
    protection_frozen s = false /\ pending_preparation s = None /\
    free_range 256 (protection_table s) (edit_reservation c) /\
    ranges (edit_entry c) = [edit_reservation c] /\
    data_slot_for kind image (entry_key kind (edit_entry c)) = Some (edit_index c) /\
    exact_calls kind ranges tail (image_replace image (edit_index c) (Some (edit_entry c)))
      (exact_member ranges image (edit_index c) (edit_entry c) (edit_reservation c) s)
  end.
Theorem finite_exact_edits_preserve kind ranges commands image root s :
  data_invariant s -> image_current_correspondence ranges image root s -> image_unique kind image ->
  exact_calls kind ranges commands image s ->
  data_invariant (execute_exact commands ranges image s) /\
  image_current_correspondence ranges (edited_image commands image)
    (match commands with [] => root | _ => [] end) (execute_exact commands ranges image s) /\
  image_unique kind (edited_image commands image).
Proof.
  revert image root s. induction commands as [|c tail IH]; intros image root s INV COR U CALLS; simpl in *.
  - auto.
  - destruct CALLS as [F [P [FREE [RANGE [SEL REST]]]]].
    destruct (exact_member_preserves ranges image root (edit_index c) (edit_entry c)
      (edit_reservation c) s INV F P FREE RANGE COR) as [INV' COR'].
    pose proof (proj1 (proj2 (selected_insert_exact kind image (edit_entry c) (edit_index c) U SEL))) as U'.
    specialize (IH _ [] _ INV' COR' U' REST). destruct tail; exact IH.
Qed.
Theorem exact_pair_keeps_allocations ranges image ia ib a b ra rb s :
  let final := exact_member ranges (image_replace image ia (Some a)) ib b rb
    (exact_member ranges image ia a ra s) in
  protection_table final =
    reserve_extent 256 rb (length (protection_saved s))
      (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) /\
  protection_dirty final = true /\ physical_authority final = physical_authority s /\
  acknowledged_authority final = acknowledged_authority s.
Proof. repeat split; reflexivity. Qed.

(* The early identical-entry branch cannot consume a genuinely fresh nonempty
   Data allocation that already occurs in the current image. This follows from
   reservation separation, not an assumption that all addresses are distinct. *)
Theorem fresh_data_entry_not_already_attached ranges image root s p entry i :
  data_invariant s -> pending_preparation s = Some p ->
  image_current_correspondence ranges image root s -> ranges entry = [prep_range p] ->
  span (prep_range p) > 0 -> nth_error image i <> Some (Some entry).
Proof.
  intros [[[C AP] SUM] OWN] P COR RANGE POS E. rewrite P in AP.
  assert (TOUCH : touches 256 (prep_range p) (offset (prep_range p) / 256) = true).
  { apply byte_page_touched; [lia|unfold contains; lia]. }
  assert (IN : In (prep_range p) (image_dependencies ranges image)).
  { apply dependencies_occurrence. exists i,entry; split; [exact E|rewrite RANGE; simpl; auto]. }
  assert (CURRENT : In (prep_range p) (protection_current s ++ attached_ranges s)).
  { rewrite COR. apply in_or_app; auto. }
  assert (ROOT : needed 256 (protected_roots s) (offset (prep_range p) / 256)).
  { exists (prep_range p); split; [|exact TOUCH].
    unfold protected_roots, context_ranges, surviving_ranges; simpl.
    apply in_app_or in CURRENT. repeat rewrite in_app_iff; tauto. }
  specialize (AP _ ROOT); congruence.
Qed.

Theorem exact_two_callers kind ranges image ia ib a b ra rb s :
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  ranges a = [ra] -> ranges b = [rb] ->
  data_slot_for kind image (entry_key kind a) = Some ia ->
  data_slot_for kind (image_replace image ia (Some a)) (entry_key kind b) = Some ib ->
  exact_calls kind ranges [ExactEdit ia a ra; ExactEdit ib b rb] image s.
Proof. intros F P FA FB A B SA SB. repeat split; try assumption; reflexivity. Qed.
Theorem exact_repeated_identity_pair kind ranges image root i a b ra rb s :
  data_invariant s -> image_current_correspondence ranges image root s -> image_unique kind image ->
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) ra ->
  free_range 256 (reserve_extent 256 ra (length (protection_saved s)) (protection_table s)) rb ->
  ranges a = [ra] -> ranges b = [rb] -> entry_key kind a = entry_key kind b ->
  data_slot_for kind image (entry_key kind a) = Some i ->
  let final := execute_exact [ExactEdit i a ra; ExactEdit i b rb] ranges image s in
  data_invariant final /\ image_current_correspondence ranges (image_replace image i (Some b)) [] final /\
  image_unique kind (image_replace image i (Some b)).
Proof.
  intros INV COR U F P FA FB A B KEY SEL; cbn zeta.
  assert (SECOND : data_slot_for kind (image_replace image i (Some a)) (entry_key kind b) = Some i).
  { rewrite <- KEY. apply repeated_identity_uses_same_slot.
    eapply data_slot_for_admissible; eauto. }
  pose proof (exact_two_callers kind ranges image i i a b ra rb s F P FA FB A B SEL SECOND) as CALLS.
  pose proof (finite_exact_edits_preserve kind ranges [ExactEdit i a ra; ExactEdit i b rb]
    image root s INV COR U CALLS) as FINAL.
  cbn [edited_image] in FINAL. rewrite image_replace_shadow in FINAL; exact FINAL.
Qed.
Theorem exact_rejection_preserves_current ranges image root s p :
  data_invariant s -> pending_preparation s = Some p ->
  image_current_correspondence ranges image root s ->
  data_invariant (data_next DataDrop s) /\ image_current_correspondence ranges image root (data_next DataDrop s).
Proof.
  intros INV P COR. split.
  - apply data_command_preserves; [exact INV|exists p; exact P].
  - unfold image_current_correspondence, data_next; rewrite P; exact COR.
Qed.
Theorem exact_empty_cycle_unchanged ranges image s : execute_exact [] ranges image s = s.
Proof. reflexivity. Qed.

Theorem exact_edits_keep_saved commands ranges image s :
  protection_saved (execute_exact commands ranges image s) = protection_saved s.
Proof.
  revert image s. induction commands as [|c tail IH]; intros image s; simpl; [reflexivity|].
  rewrite IH; reflexivity.
Qed.
Theorem snapshot_then_exact_edits kind ranges image prefix count boss commands s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  image_current_correspondence ranges image [] s -> image_unique kind image ->
  free_range 256 (protection_table s) boss -> count > 0 ->
  protection_saved s = prefix ++ repeat (protection_current s ++ attached_ranges s) count ->
  exact_calls kind ranges commands image (snapshot_success prefix count boss s) ->
  let ready := snapshot_success prefix count boss s in
  let final := execute_exact commands ranges image ready in
  data_invariant final /\
  image_current_correspondence ranges (edited_image commands image)
    (match commands with [] => [boss] | _ => [] end) final /\
  image_unique kind (edited_image commands image) /\
  protection_saved final = protection_saved ready.
Proof.
  intros INV F P COR U FREE POS SHAPE CALLS; cbn zeta.
  pose proof (snapshot_success_preserves s prefix count boss INV F P FREE POS SHAPE) as READY.
  pose proof (snapshot_installs_exact_image_view ranges image prefix count boss s COR) as VIEW.
  destruct (finite_exact_edits_preserve kind ranges commands image [boss]
    (snapshot_success prefix count boss s) READY VIEW U CALLS) as [I [C UN]].
  split; [exact I|]. split; [exact C|]. split; [exact UN|apply exact_edits_keep_saved].
Qed.

(* Collection installs a scratch mask only after all range resolutions succeed.
   These observations refer to the existing state/table, not another machine.
   The relation is a boundary obligation; its establishment by publication and
   detached LOAD control flow is NOT claimed by the lemmas below. *)
Definition collection_enabled initialized durable current s :=
  Nat.eqb (length (protection_saved s)) 0 &&
  negb (protection_frozen s) && initialized && protection_dirty s &&
  match durable with None => true | Some d =>
    match current with None => false | Some c => Nat.eqb d c end end.

Lemma collection_enabled_spec initialized durable current s :
  collection_enabled initialized durable current s = true <->
  protection_saved s = [] /\ protection_frozen s = false /\
  initialized = true /\ protection_dirty s = true /\ collect_guard durable current.
Proof.
  unfold collection_enabled, collect_guard. rewrite !andb_true_iff.
  rewrite Nat.eqb_eq, negb_true_iff, length_zero_iff_nil.
  destruct durable as [d|], current as [c|]; simpl;
    try rewrite Nat.eqb_eq; intuition congruence.
Qed.

Definition install_collection page ranges s :=
  ProtectionState (protection_current s) (protection_saved s) (protection_base s)
    (attached_ranges s) (pending_preparation s) (physical_authority s)
    (acknowledged_authority s) (protection_frozen s)
    (collect_table page ranges (protection_table s)) (fun _ => false) false.

(* None is a range/mark failure, not Reset. No flash command is executed here. *)
Definition collection_return page initialized durable current resolved s :=
  if collection_enabled initialized durable current s then
    match resolved with None => s | Some ranges => install_collection page ranges s end
  else s.

Lemma failed_collection_keeps_state page initialized durable current s :
  collection_return page initialized durable current None s = s.
Proof. unfold collection_return; destruct (collection_enabled initialized durable current s); reflexivity. Qed.
Lemma skipped_collection_keeps_state page initialized durable current resolved s :
  collection_enabled initialized durable current s = false ->
  collection_return page initialized durable current resolved s = s.
Proof. intros H; unfold collection_return; rewrite H; reflexivity. Qed.
Lemma frozen_collection_keeps_state page initialized durable current resolved s :
  protection_frozen s = true ->
  collection_return page initialized durable current resolved s = s.
Proof.
  intros F. apply skipped_collection_keeps_state. unfold collection_enabled.
  rewrite F. simpl. rewrite andb_false_r. reflexivity.
Qed.

Definition collection_boundary view marker durable current entries load s :=
  protection_current s ++ attached_ranges s = optional_boss view current ++ entries /\
  protection_base s = marker :: optional_root view durable /\
  physical_authority s = optional_root view durable /\
  acknowledged_authority s = optional_root view durable /\
  pending_ranges s = load /\ current_agrees view current entries.

Lemma boundary_ranges_enumerated view marker durable current entries load s :
  collection_boundary view marker durable current entries load s ->
  protection_saved s = [] -> collect_guard durable current ->
  forall r, In r (required_ranges s) ->
    In r (collect_ranges view marker current entries load).
Proof.
  intros [C [B [P [A [L E]]]]] S G r R.
  assert (ROOT : forall x, In x (optional_root view durable) ->
    In x (collect_ranges view marker current entries load)).
  { intros x X. eapply final_collection_enumerates_surviving_roots; eauto.
    unfold live_ranges; simpl. right. apply in_or_app; auto. }
  unfold required_ranges, context_ranges, surviving_ranges, context_scopes in R; simpl in R.
  rewrite S, B, P, A in R. simpl in R. rewrite L in R.
  assert (CUR : forall x, In x (protection_current s) \/ In x (attached_ranges s) ->
    In x (collect_ranges view marker current entries load)).
  { intros x X. assert (Y : In x (protection_current s ++ attached_ranges s))
      by (apply in_or_app; tauto).
    rewrite C in Y. unfold collect_ranges. right.
    repeat rewrite in_app_iff in *; tauto. }
  unfold collect_ranges. simpl.
  repeat rewrite in_app_iff in R. simpl in R.
  specialize (ROOT r). specialize (CUR r).
  unfold collect_ranges in ROOT, CUR. simpl in ROOT, CUR.
  repeat rewrite in_app_iff in *; intuition eauto.
Qed.

Lemma install_collection_required page ranges s :
  required_ranges (install_collection page ranges s) = required_ranges s.
Proof. reflexivity. Qed.
Lemma install_collection_boundary page ranges view marker durable current entries load s :
  collection_boundary view marker durable current entries load s ->
  collection_boundary view marker durable current entries load (install_collection page ranges s).
Proof. exact (fun H => H). Qed.

Theorem collection_return_preserves page initialized view marker durable current entries load resolved s :
  protection_invariant page s ->
  collection_boundary view marker durable current entries load s ->
  (forall ranges, resolved = Some ranges -> ranges = collect_ranges view marker current entries load) ->
  protection_invariant page (collection_return page initialized durable current resolved s).
Proof.
  intros [[C SEP] BITS] REL RES. unfold collection_return.
  destruct (collection_enabled initialized durable current s) eqn:G;
    [|repeat split; assumption].
  destruct resolved as [ranges|]; [|repeat split; assumption].
  specialize (RES ranges eq_refl). subst ranges.
  apply collection_enabled_spec in G. destruct G as [S [F [I [D GUARD]]]].
  split; [split|apply collect_summary_sound].
  - rewrite install_collection_required. apply protected_subset with
      (ys := collect_ranges view marker current entries load).
    + eapply boundary_ranges_enumerated; eauto.
    + apply collection_establishes_coverage.
  - exact SEP.
Qed.

Theorem collected_free_excludes_survivor page view marker durable current entries load s p :
  collection_boundary view marker durable current entries load s ->
  protection_saved s = [] -> collect_guard durable current ->
  owner (collect_table page (collect_ranges view marker current entries load) (protection_table s) p) = 0 ->
  ~ needed page (required_ranges s) p.
Proof.
  intros B S G F N. apply (collection_free_implies_no_listed_reference _ _ _ _ F).
  eapply needed_membership; [eapply boundary_ranges_enumerated; eauto|exact N].
Qed.

Theorem collection_then_erase g page initialized view marker durable current entries load resolved s f f' a outcome :
  page > 0 -> protection_invariant page s ->
  collection_boundary view marker durable current entries load s ->
  (forall ranges, resolved = Some ranges -> ranges = collect_ranges view marker current entries load) ->
  free_range page (protection_table (collection_return page initialized durable current resolved s))
    {| offset := a; span := sector_size g |} ->
  erase_step g f a outcome f' -> unchanged (required_ranges s) f f'.
Proof.
  intros P I B R F E.
  pose proof (collection_return_preserves page initialized view marker durable current entries load resolved s I B R) as [[C _] _].
  assert (Q : required_ranges (collection_return page initialized durable current resolved s) = required_ranges s).
  { unfold collection_return. destruct (collection_enabled initialized durable current s);
      [destruct resolved|]; reflexivity. }
  rewrite Q in C. eapply erase_preserves_covered_ranges; eauto.
Qed.

(* Exact attachment removes the current BOSS root; it does not change the RAM
   durable root or the authority envelopes. The consumed Data token is absent
   from the next collection enumeration. No collection is enabled merely by
   establishing this relation: the scope/root guards still apply. *)
Theorem exact_attach_collection_boundary view marker durable current entries load
    ranges image index entry s p :
  collection_boundary view marker durable current entries load s ->
  pending_preparation s = Some p ->
  collection_boundary view marker durable None
    (image_dependencies ranges (image_replace image index (Some entry))) []
    (exact_attach ranges image index entry s).
Proof.
  intros [_ [B [P [A [_ _]]]]] TOKEN.
  unfold collection_boundary, exact_attach, replace_current_dependencies, data_next.
  rewrite TOKEN. simpl. rewrite app_nil_r.
  repeat split; auto. intros r E; discriminate.
Qed.

Theorem exact_delete_collection_boundary view marker durable current entries load
    ranges image index s :
  collection_boundary view marker durable current entries load s ->
  collection_boundary view marker durable None
    (image_dependencies ranges (image_replace image index None)) []
    (exact_delete ranges image index s).
Proof.
  intros [_ [B [P [A [_ _]]]]].
  unfold collection_boundary, exact_delete, replace_current_dependencies.
  simpl. rewrite app_nil_r. repeat split; auto. intros r E; discriminate.
Qed.

Theorem changed_image_with_durable_skips_collection page initialized durable resolved s :
  collection_return page initialized (Some durable) None resolved s = s.
Proof.
  apply skipped_collection_keeps_state. unfold collection_enabled.
  apply andb_false_r.
Qed.

Theorem open_scope_skips_collection page initialized durable current resolved s :
  protection_saved s <> [] ->
  collection_return page initialized durable current resolved s = s.
Proof.
  intros S. apply skipped_collection_keeps_state.
  destruct (collection_enabled initialized durable current s) eqn:E; auto.
  apply collection_enabled_spec in E. tauto.
Qed.

(* Successful publication exit, no active or detached LOAD. These are distinct
   witness updates; no page ownership changes until external close. *)
Definition slot_publication candidate s :=
  ProtectionState (protection_current s) (protection_saved s) (protection_base s)
    (attached_ranges s) (pending_preparation s) candidate (acknowledged_authority s)
    (protection_frozen s) (protection_table s) (protection_bits s) (protection_dirty s).
Definition durable_ram_update marker candidate s :=
  ProtectionState (protection_current s) (protection_saved s) (marker :: candidate)
    (attached_ranges s) (pending_preparation s) (physical_authority s) candidate
    (protection_frozen s) (protection_table s) (protection_bits s) (protection_dirty s).
Definition successful_external_close marker candidate saved s :=
  data_next (DataClose [] saved true)
    (durable_ram_update marker candidate (slot_publication candidate s)).

Lemma candidate_current_is_required candidate s :
  protection_current s ++ attached_ranges s = candidate ->
  forall r, In r candidate -> In r (required_ranges s).
Proof.
  intros C r R. rewrite <- C in R. unfold required_ranges, context_ranges,
    surviving_ranges, context_scopes; simpl. repeat rewrite in_app_iff in *; tauto.
Qed.
Theorem slot_publication_preserves page candidate s :
  protection_invariant page s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  protection_invariant page (slot_publication candidate s).
Proof.
  intros [[C SEP] SUM] P CUR. split; [split|exact SUM].
  - eapply protected_subset; [|exact C]. intros r R.
    unfold required_ranges, context_ranges, surviving_ranges, slot_publication,
      context_scopes, pending_ranges in R; simpl in R. rewrite P in R; simpl in R.
    pose proof (candidate_current_is_required candidate s CUR r).
    unfold required_ranges, context_ranges, surviving_ranges, context_scopes,
      pending_ranges in *; simpl in *; rewrite P in H; rewrite P; simpl.
    repeat rewrite in_app_iff in *; tauto.
  - simpl; rewrite P; exact I.
Qed.

Theorem successful_close_boundary view marker id saved s :
  protection_current s ++ attached_ranges s = root_extents (view id) ->
  collection_boundary view marker (Some id) (Some id) (object_extents (view id)) []
    (successful_external_close marker (root_extents (view id)) saved s).
Proof.
  intros C. unfold collection_boundary, successful_external_close, data_next,
    durable_ram_update, slot_publication; simpl.
  repeat split; auto. intros r E. inversion E; reflexivity.
Qed.

Theorem successful_close_protects (candidate : list extent) marker saved s :
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = candidate ->
  protection_invariant 256
    (successful_external_close marker (candidate) saved s).
Proof.
  intros [PI OWN] F STACK P MARK CUR.
  specialize (OWN F). destruct OWN as [SCOPE [AUTH TOKEN]].
  destruct SCOPE as [DEPTH [CURRENT [SAVED BASE]]].
  unfold data_scope in CURRENT, BASE; simpl in CURRENT, BASE.
  rewrite STACK in CURRENT; simpl in CURRENT. rewrite CUR in CURRENT.
  pose proof (accept_rehomes_current 256 (candidate) 1
    (protection_table s) ltac:(lia) CURRENT) as NEW.
  assert (M : bounded 256 [marker] 1 (finish_table 1 true (protection_table s))).
  { apply finish_preserves_ancestor; [lia|]. eapply bounded_subset; [|exact BASE].
    intros r [E|[]]; subst; exact MARK. }
  destruct PI as [PI SUM].
  split; [split|].
  - unfold successful_external_close, data_next, durable_ram_update, slot_publication,
      required_ranges, context_ranges, surviving_ranges, context_scopes, pending_ranges;
      simpl. rewrite F; simpl.
    intros p [r [R T]].
    assert (CHOICE : In r (candidate) \/ r = marker).
    { rewrite <- CUR in R. repeat rewrite in_app_iff in R. simpl in R.
      repeat rewrite in_app_iff in R. simpl in R.
      rewrite <- CUR. repeat rewrite in_app_iff. intuition congruence. }
    destruct CHOICE as [R'|E].
    + apply (bounded_protected _ _ _ _ NEW p). exists r; auto.
    + subst r. apply (bounded_protected _ _ _ _ M p). exists marker; simpl; auto.
  - exact I.
  - unfold successful_external_close, data_next, durable_ram_update, slot_publication;
      simpl. rewrite F; simpl. apply finish_summary_sound; [lia|exact SUM].
Qed.

Theorem successful_exit_collection view marker id saved s initialized resolved :
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = root_extents (view id) ->
  (forall ranges, resolved = Some ranges ->
    ranges = collect_ranges view marker (Some id) (object_extents (view id)) []) ->
  let closed := successful_external_close marker (root_extents (view id)) saved s in
  protection_invariant 256 (collection_return 256 initialized (Some id) (Some id) resolved closed) /\
  collection_boundary view marker (Some id) (Some id) (object_extents (view id)) [] closed.
Proof.
  intros I F S P M C R; cbn zeta.
  assert (B := successful_close_boundary view marker id saved s C).
  split; [|exact B]. eapply collection_return_preserves; eauto.
  eapply successful_close_protects; eauto.
Qed.

Theorem durable_ram_update_preserves page marker candidate s :
  protection_invariant page s -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = candidate ->
  protection_invariant page (durable_ram_update marker candidate s).
Proof.
  intros [[C SEP] SUM] P M CUR. split; [split|exact SUM].
  - eapply protected_subset; [|exact C]. intros r R.
    unfold required_ranges, context_ranges, surviving_ranges, durable_ram_update,
      context_scopes, pending_ranges in R; simpl in R. rewrite P in R; simpl in R.
    unfold required_ranges, context_ranges, surviving_ranges, context_scopes,
      pending_ranges; simpl. rewrite P; simpl.
    rewrite <- CUR in R. repeat rewrite in_app_iff in *; simpl in R.
    intuition subst; auto. repeat rewrite in_app_iff in *; tauto.
  - simpl; rewrite P; exact I.
Qed.
Lemma successful_close_owner_transfer marker candidate saved s :
  protection_frozen s = false ->
  protection_table (successful_external_close marker candidate saved s) =
    finish_table 1 true (protection_table s).
Proof. intros F; unfold successful_external_close; simpl; rewrite F; reflexivity. Qed.
Lemma successful_close_collection_guard marker candidate saved s :
  protection_frozen s = false -> protection_dirty s = true ->
  forall id, collection_enabled true (Some id) (Some id)
    (successful_external_close marker candidate saved s) = true.
Proof.
  intros F D id. apply collection_enabled_spec.
  unfold successful_external_close; simpl. repeat split; auto.
  right; reflexivity.
Qed.

(* Full ownership restoration, not just coverage. Retained irrelevant pages
   need not be free, nor have owner 1. Bounds apply to the surviving needs. *)
Lemma idle_bounds_restore_data s :
  protection_invariant 256 s -> protection_saved s = [] ->
  pending_preparation s = None ->
  bounded 256 (required_ranges s) 1 (protection_table s) -> data_invariant s.
Proof.
  intros PI S P B. split; [exact PI|]. intros F.
  assert (SUB : forall xs, (forall r, In r xs -> In r (required_ranges s)) ->
    bounded 256 xs 1 (protection_table s)) by (intros; eapply bounded_subset; eauto).
  unfold data_ownership, data_scope; simpl. rewrite P, S; simpl.
  split; [|split; [|exact I]].
  - unfold scope_invariant; simpl. split; [unfold max_depth; lia|].
    split; [|split].
    + apply SUB. intros r R. unfold required_ranges, context_ranges, surviving_ranges, context_scopes;
        simpl. repeat rewrite in_app_iff in *; tauto.
    + intros i v E; destruct i; discriminate.
    + apply SUB. intros r R. unfold required_ranges, context_ranges, surviving_ranges, context_scopes;
        simpl. repeat rewrite in_app_iff; tauto.
  - apply SUB. intros r R. unfold required_ranges. repeat rewrite in_app_iff in *; tauto.
Qed.

Theorem successful_close_restores_data candidate marker saved s :
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) -> protection_current s ++ attached_ranges s = candidate ->
  data_invariant (successful_external_close marker candidate saved s).
Proof.
  intros INV F S P MARK CUR.
  apply idle_bounds_restore_data; try reflexivity.
  - eapply successful_close_protects; eauto.
  - destruct INV as [PI OWN]. specialize (OWN F).
    destruct OWN as [[_ [C [_ B]]] _]. unfold data_scope in C, B; simpl in C, B.
    rewrite S in C; simpl in C. rewrite CUR in C.
    pose proof (accept_rehomes_current 256 candidate 1 (protection_table s) ltac:(lia) C) as NEW.
    assert (M : bounded 256 [marker] 1 (finish_table 1 true (protection_table s))).
    { apply finish_preserves_ancestor; [lia|]. eapply bounded_subset; [|exact B].
      intros r [E|[]]; subst; exact MARK. }
    unfold successful_external_close, data_next, durable_ram_update, slot_publication,
      required_ranges, context_ranges, surviving_ranges, context_scopes, pending_ranges;
      simpl. rewrite F; simpl. intros p [r [R T]].
    assert (CHOICE : In r candidate \/ r = marker).
    { rewrite <- CUR in R. repeat rewrite in_app_iff in R. simpl in R.
      repeat rewrite in_app_iff in R. simpl in R.
      rewrite <- CUR. repeat rewrite in_app_iff. intuition congruence. }
    destruct CHOICE as [R'|E]; [apply NEW; exists r; auto|subst; apply M; exists marker; simpl; auto].
Qed.

Theorem idle_collection_restores_data initialized view marker durable current entries s resolved :
  data_invariant s -> protection_saved s = [] -> pending_preparation s = None ->
  collection_boundary view marker durable current entries [] s ->
  (forall ranges, resolved = Some ranges -> ranges = collect_ranges view marker current entries []) ->
  data_invariant (collection_return 256 initialized durable current resolved s).
Proof.
  intros INV S P B R. unfold collection_return.
  destruct (collection_enabled initialized durable current s) eqn:E; [|exact INV].
  destruct resolved as [ranges|]; [|exact INV]. specialize (R ranges eq_refl); subst ranges.
  apply idle_bounds_restore_data; simpl; auto.
  - pose proof (collection_return_preserves 256 initialized view marker durable current entries []
      (Some (collect_ranges view marker current entries [])) s (proj1 INV) B ltac:(intros; congruence)) as H.
    unfold collection_return in H; rewrite E in H; exact H.
  - rewrite install_collection_required. intros p N.
    assert (N' : needed 256 (collect_ranges view marker current entries []) p).
    { eapply needed_membership; [eapply boundary_ranges_enumerated; eauto|exact N].
      apply collection_enabled_spec in E; tauto. }
    apply marked_spec in N'. unfold collect_table; rewrite N'; simpl; lia.
Qed.

Definition idle_root (view : nat -> root_view) marker id s :=
  data_invariant s /\ protection_frozen s = false /\ protection_saved s = [] /\
  pending_preparation s = None /\
  protection_current s ++ attached_ranges s = root_extents (view id) /\
  protection_base s = marker :: root_extents (view id) /\
  physical_authority s = root_extents (view id) /\
  acknowledged_authority s = root_extents (view id).
Definition finish_collected view marker id saved s :=
  collection_return 256 true (Some id) (Some id)
    (Some (collect_ranges view marker (Some id) (object_extents (view id)) []))
    (successful_external_close marker (root_extents (view id)) saved s).

Theorem finish_collected_idle view marker id saved s :
  data_invariant s -> protection_frozen s = false -> protection_saved s = [saved] ->
  pending_preparation s = None -> In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = root_extents (view id) ->
  idle_root view marker id (finish_collected view marker id saved s).
Proof.
  intros I F S P M C. unfold idle_root. split.
  - eapply idle_collection_restores_data with (view:=view) (marker:=marker)
      (entries:=object_extents (view id)); try reflexivity.
    + eapply successful_close_restores_data; eauto.
    + apply successful_close_boundary; exact C.
    + intros; congruence.
  - unfold finish_collected, collection_return.
    destruct (collection_enabled true (Some id) (Some id)
      (successful_external_close marker (root_extents (view id)) saved s));
      simpl; repeat split; assumption.
Qed.

(* Final BOSS save with all rollback boundaries already materialized. Reserve
   and Written are existing snapshot services; installation only observes the
   completed candidate and does not resolve or replace any saved boundary. *)
Definition install_candidate s := match pending_preparation s with
  | None => s
  | Some p => replace_current_dependencies
      (prep_range p :: (protection_current s ++ attached_ranges s)) (data_next DataAttach s) end.
Definition materialize_candidate boss s :=
  install_candidate (snapshot_written (snapshot_reserve boss s)).
Theorem materialize_candidate_preserves boss s :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) boss -> data_invariant (materialize_candidate boss s).
Proof.
  intros I F P FREE.
  change (data_invariant (replace_current_dependencies (boss :: (protection_current s ++ attached_ranges s))
    (execute_data [DataReserve boss; DataWritten; DataAttach] s))).
  apply replace_current_dependencies_preserves; try reflexivity.
  - apply data_execution_preserves; [exact I|].
    split; [simpl; auto|]. split; [|split; [|exact Logic.I]].
    + split; [reflexivity|]. exists (Build_preparation ObjectPreparation boss Reserved).
      repeat split; try reflexivity; discriminate.
    + split; [reflexivity|]. exists (Build_preparation ObjectPreparation boss Written).
      repeat split; reflexivity.
  - intros r R. simpl. repeat rewrite in_app_iff in *; simpl in *;
    repeat rewrite in_app_iff in *; tauto.
Qed.

Definition modified_transaction ranges image index entry span s :=
  exact_member ranges image index entry span (data_next DataBegin s).
Definition data_transaction view marker new_id ranges image index entry span s :=
  let changed := modified_transaction ranges image index entry span s in
  let candidate := materialize_candidate (boss_extent (view new_id)) changed in
  finish_collected view marker new_id (protection_current s ++ attached_ranges s) candidate.

Theorem data_transaction_idle view marker old_id new_id ranges image index entry span s :
  idle_root view marker old_id s ->
  object_extents (view old_id) = image_dependencies ranges image ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges image index entry span s))
    (boss_extent (view new_id)) ->
  object_extents (view new_id) = image_dependencies ranges (image_replace image index (Some entry)) ->
  idle_root view marker new_id (data_transaction view marker new_id ranges image index entry span s).
Proof.
  intros [I [F [S [P [CUR [BASE [AUTH ACK]]]]]]] OLD RANGE FREE BFREE ENC.
  assert (BEGIN : data_invariant (data_next DataBegin s)).
  { apply data_command_preserves; [exact I|]. simpl; rewrite S; simpl; repeat split; auto; lia. }
  assert (COR : image_current_correspondence ranges image [boss_extent (view old_id)] (data_next DataBegin s)).
  { unfold image_current_correspondence; simpl. rewrite app_nil_r, CUR.
    unfold root_extents; rewrite OLD; reflexivity. }
  destruct (exact_member_preserves ranges image [boss_extent (view old_id)] index entry span
    (data_next DataBegin s) BEGIN eq_refl eq_refl FREE RANGE COR) as [MI MC].
  apply finish_collected_idle.
  - apply materialize_candidate_preserves; try reflexivity; assumption.
  - reflexivity.
  - change (protection_saved s ++ [protection_current s ++ attached_ranges s] =
      [protection_current s ++ attached_ranges s]). rewrite S; reflexivity.
  - reflexivity.
  - change (In marker (protection_base s)). rewrite BASE; simpl; auto.
  - change ((boss_extent (view new_id) ::
      (image_dependencies ranges (image_replace image index (Some entry)) ++ [])) ++ [] = root_extents (view new_id)).
    rewrite !app_nil_r. unfold root_extents. rewrite ENC; reflexivity.
Qed.

Theorem two_data_transactions_idle view marker root0 root1 root2 ranges image i a b ra rb s :
  idle_root view marker root0 s ->
  object_extents (view root0) = image_dependencies ranges image ->
  ranges a = [ra] -> ranges b = [rb] ->
  free_range 256 (protection_table (data_next DataBegin s)) ra ->
  free_range 256 (protection_table (modified_transaction ranges image i a ra s)) (boss_extent (view root1)) ->
  object_extents (view root1) = image_dependencies ranges (image_replace image i (Some a)) ->
  let first := data_transaction view marker root1 ranges image i a ra s in
  free_range 256 (protection_table (data_next DataBegin first)) rb ->
  free_range 256 (protection_table (modified_transaction ranges (image_replace image i (Some a)) i b rb first))
    (boss_extent (view root2)) ->
  object_extents (view root2) = image_dependencies ranges (image_replace image i (Some b)) ->
  idle_root view marker root2
    (data_transaction view marker root2 ranges (image_replace image i (Some a)) i b rb first).
Proof.
  intros I E0 A B FA FBA E1 first FB FBB E2.
  assert (MID : idle_root view marker root1 first).
  { apply data_transaction_idle with (old_id:=root0); assumption. }
  apply data_transaction_idle with (old_id:=root1); try assumption.
  rewrite image_replace_shadow. exact E2.
Qed.

Theorem data_transaction_collection_flags view marker id ranges image index entry span s :
  protection_dirty (data_transaction view marker id ranges image index entry span s) = false /\
  forall p, protection_bits (data_transaction view marker id ranges image index entry span s) p = false.
Proof.
  unfold data_transaction, finish_collected, collection_return.
  rewrite successful_close_collection_guard; try reflexivity. split; reflexivity.
Qed.

Theorem install_candidate_completed_preserves s p :
  data_invariant s -> protection_frozen s = false ->
  pending_preparation s = Some p -> prep_kind p = BossPreparation -> (prep_phase p = Written \/ prep_phase p = Detached) ->
  data_invariant (install_candidate s).
Proof.
  intros [PI OWN] F P KIND PHASE.
  assert (ATTACH : data_invariant (data_next DataAttach s)).
  { split.
    - eapply protection_step_inductive; [exact PI|].
      unfold data_next; rewrite P. apply attach_preparation; auto.
    - unfold data_next; rewrite P. intros _. apply data_attach_ownership with (p:=p); auto. }
  unfold install_candidate; rewrite P. apply replace_current_dependencies_preserves.
  - exact ATTACH.
  - unfold data_next; rewrite P; reflexivity.
  - intros r R. unfold data_next; rewrite P; simpl.
    repeat rewrite in_app_iff in *; simpl in *; repeat rewrite in_app_iff in *; tauto.
Qed.

Theorem install_candidate_preserves s p :
  data_invariant s -> protection_frozen s = false ->
  pending_preparation s = Some p -> prep_kind p = BossPreparation -> prep_phase p = Written ->
  data_invariant (install_candidate s).
Proof. intros; eapply install_candidate_completed_preserves; eauto. Qed.

(* Returned journal errors: the physical authority observer may change before
   durable RAM does. The selector is constrained by JournalHistory, not by this
   update. There is still only one ownership table. *)
Definition uncertain_return selected s :=
  data_next DataFreeze (slot_publication selected s).

Lemma slot_publication_subset_preserves page selected s :
  protection_invariant page s -> pending_preparation s = None ->
  (forall r, In r selected -> In r (required_ranges s)) ->
  protection_invariant page (slot_publication selected s).
Proof.
  intros [[C SEP] SUM] P SUB. split; [split|exact SUM].
  - eapply protected_subset; [|exact C]. intros r R.
    unfold required_ranges, context_ranges, surviving_ranges, slot_publication,
      context_scopes, pending_ranges in R; simpl in R. rewrite P in R; simpl in R.
    unfold required_ranges, context_ranges, surviving_ranges, context_scopes,
      pending_ranges; simpl; rewrite P; simpl.
    repeat rewrite in_app_iff in R |- *.
    destruct R as [[A|[A|A]]|[A|[A|[A|A]]]]; try tauto.
    specialize (SUB r A). unfold required_ranges, context_ranges, surviving_ranges,
      context_scopes, pending_ranges in SUB; simpl in SUB; rewrite P in SUB; simpl in SUB.
    repeat rewrite in_app_iff in SUB; tauto.
  - simpl; rewrite P; exact I.
Qed.

Theorem uncertain_return_protects candidate selected s :
  protection_invariant 256 s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  (forall r, In r selected -> In r (physical_authority s ++ candidate)) ->
  data_invariant (uncertain_return selected s) /\
  protected (needed 256 (physical_authority s ++ candidate))
    (protection_table (uncertain_return selected s)) /\
  protection_frozen (uncertain_return selected s) = true /\
  protection_table (uncertain_return selected s) = protection_table s /\
  protection_base (uncertain_return selected s) = protection_base s /\
  acknowledged_authority (uncertain_return selected s) = acknowledged_authority s.
Proof.
  intros INV P CUR SEL.
  assert (SUB : forall r, In r (physical_authority s ++ candidate) -> In r (required_ranges s)).
  { intros r R. apply in_app_iff in R. destruct R as [R|R].
    - unfold required_ranges. repeat rewrite in_app_iff; tauto.
    - eapply candidate_current_is_required; eauto. }
  split.
  - split.
    + eapply protection_step_inductive with (s := slot_publication selected s).
      * apply slot_publication_subset_preserves; [exact INV|exact P|].
        intros r R. apply SUB, SEL; exact R.
      * apply returned_uncertain_error.
    + discriminate.
  - split.
    + eapply protected_subset; [exact SUB|exact (proj1 (proj1 INV))].
    + repeat split; reflexivity.
Qed.

(* Any legal Data continuation from a frozen state consists only of RAM
   cleanup/stuttering. Reserve, Written, Attach and Begin have false callers.
   This also covers LIFO closes at successively smaller RAM depths. *)
Theorem frozen_data_cleanup candidate selected s commands :
  protection_invariant 256 s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  (forall r, In r selected -> In r (physical_authority s ++ candidate)) ->
  data_calls commands (uncertain_return selected s) ->
  let final := execute_data commands (uncertain_return selected s) in
  data_invariant final /\ protection_frozen final = true /\
  protection_table final = protection_table s /\
  physical_authority final = selected /\
  acknowledged_authority final = acknowledged_authority s /\
  protected (needed 256 (physical_authority s ++ candidate)) (protection_table final).
Proof.
  intros INV P CUR SEL CALL final.
  destruct (uncertain_return_protects candidate selected s INV P CUR SEL)
    as [I [C [F [T [B A]]]]].
  pose proof (data_execution_refines commands _ I CALL) as TRACE.
  destruct (frozen_preparation_trace_keeps_storage 256 _ _ F TRACE) as [F' [T' A']].
  destruct (data_execution_no_publication commands (uncertain_return selected s)) as [PH ACK].
  split; [apply data_execution_preserves; assumption|].
  split; [exact F'|]. split; [unfold final; rewrite T'; exact T|].
  split; [exact PH|]. split; [exact ACK|].
  unfold final. rewrite T'. exact C.
Qed.

Theorem uncertain_rollback_caller selected s views saved :
  pending_preparation s = None -> protection_saved s = views ++ [saved] ->
  data_calls [DataClose views saved false] (uncertain_return selected s).
Proof. intros P S. simpl. auto. Qed.

Theorem frozen_mutation_callers_rejected s r :
  protection_frozen s = true ->
  ~ data_caller (DataReserve r) s /\ ~ data_caller DataWritten s /\
  ~ data_caller DataAttach s /\ ~ data_caller DataBegin s.
Proof. unfold data_caller; intros F; repeat split; intros [E _]; congruence. Qed.

Theorem uncertain_error_then_rollback candidate selected s views saved :
  protection_invariant 256 s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  (forall r, In r selected -> In r (physical_authority s ++ candidate)) ->
  protection_saved s = views ++ [saved] ->
  let final := data_next (DataClose views saved false) (uncertain_return selected s) in
  data_invariant final /\ protection_current final = saved /\
  protection_saved final = views /\ protection_frozen final = true /\
  protection_table final = protection_table s /\
  protected (needed 256 (physical_authority s ++ candidate)) (protection_table final).
Proof.
  intros INV P C SEL STACK final.
  pose proof (uncertain_rollback_caller selected s views saved P STACK) as CALL.
  destruct (frozen_data_cleanup candidate selected s [DataClose views saved false]
    INV P C SEL CALL) as [I [F [T [PH [ACK COVER]]]]].
  split; [exact I|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact F|]. split; assumption.
Qed.

Theorem frozen_cleanup_collection_skips candidate selected s commands initialized durable current resolved :
  protection_invariant 256 s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  (forall r, In r selected -> In r (physical_authority s ++ candidate)) ->
  data_calls commands (uncertain_return selected s) ->
  let final := execute_data commands (uncertain_return selected s) in
  collection_return 256 initialized durable current resolved final = final.
Proof.
  intros I P C SEL CALL final. apply frozen_collection_keeps_state.
  exact (proj1 (proj2 (frozen_data_cleanup candidate selected s commands I P C SEL CALL))).
Qed.

(* Boot reconstruction consumes decoded RAM, never the pre-reset table.
   Each retain is a separate pages.rs::retain operation on the common state. *)
Definition recovered_ram marker boss entries :=
  ProtectionState (boss :: entries) [] (marker :: boss :: entries) [] None
    (boss :: entries) (boss :: entries) false (fun _ => free_cell)
    (fun _ => false) false.
Definition recovery_retain r s := change_preparation s (pending_preparation s)
  (protection_frozen s) (rehome_extent 256 r 0 (protection_table s))
  (set_summary (protection_bits s) 0) (protection_dirty s).
Fixpoint recovery_retains ranges s := match ranges with
  | [] => s | r :: tail => recovery_retains tail (recovery_retain r s) end.
Definition reconstructed marker boss entries :=
  recovery_retains (marker :: boss :: entries) (recovered_ram marker boss entries).

Lemma recovery_retains_observers ranges s :
  protection_current (recovery_retains ranges s) = protection_current s /\
  protection_saved (recovery_retains ranges s) = protection_saved s /\
  protection_base (recovery_retains ranges s) = protection_base s /\
  attached_ranges (recovery_retains ranges s) = attached_ranges s /\
  pending_preparation (recovery_retains ranges s) = pending_preparation s /\
  physical_authority (recovery_retains ranges s) = physical_authority s /\
  acknowledged_authority (recovery_retains ranges s) = acknowledged_authority s /\
  protection_frozen (recovery_retains ranges s) = protection_frozen s /\
  protection_dirty (recovery_retains ranges s) = protection_dirty s.
Proof.
  revert s; induction ranges as [|r tail IH]; intro s; [repeat split; reflexivity|].
  exact (IH (recovery_retain r s)).
Qed.
Lemma recovery_retains_cell ranges s p :
  protection_table (recovery_retains ranges s) p =
    if marked 256 ranges p then {| owner := 1; validated := validated (protection_table s p) |}
    else protection_table s p.
Proof.
  revert s; induction ranges as [|r tail IH]; intro s; simpl; [reflexivity|].
  rewrite IH. unfold recovery_retain, change_preparation, marked; simpl.
  unfold rehome_extent. destruct (touches 256 r p), (existsb _ tail); reflexivity.
Qed.
Lemma recovery_retains_summary ranges s :
  summary_sound (protection_bits s) (protection_table s) ->
  summary_sound (protection_bits (recovery_retains ranges s))
    (protection_table (recovery_retains ranges s)).
Proof.
  revert s; induction ranges as [|r tail IH]; intros s S; [exact S|].
  apply IH. apply rehome_summary_sound; exact S.
Qed.

Theorem reconstruction_establishes_idle view marker id entries :
  entries = object_extents (view id) ->
  idle_root view marker id (reconstructed marker (boss_extent (view id)) entries).
Proof.
  intro E; subst entries.
  set (s := recovered_ram marker (boss_extent (view id)) (object_extents (view id))).
  set (ranges := marker :: root_extents (view id)).
  change (idle_root view marker id (recovery_retains ranges s)).
  destruct (recovery_retains_observers ranges s)
    as [C [S [B [A [P [PH [ACK [F D]]]]]]]].
  assert (ENUM : forall r, In r (required_ranges (recovery_retains ranges s)) -> In r ranges).
  { unfold required_ranges, context_ranges, surviving_ranges, context_scopes, pending_ranges;
      cbn -[recovery_retains]; rewrite C, S, B, A, P, PH, ACK; unfold s, recovered_ram; simpl.
    unfold ranges, root_extents. intros r R. do 5 (repeat rewrite in_app_iff in R; simpl in R). tauto. }
  assert (BOUND : bounded 256 (required_ranges (recovery_retains ranges s)) 1
      (protection_table (recovery_retains ranges s))).
  { intros p N. assert (N' : needed 256 ranges p).
    { destruct N as [r [R T]]. exists r; split; [apply ENUM; exact R|exact T]. }
    apply marked_spec in N'. rewrite recovery_retains_cell, N'; simpl; lia. }
  unfold idle_root. split.
  - apply idle_bounds_restore_data.
    + split.
      * split; [apply bounded_protected with (n:=1); exact BOUND|]. rewrite P; exact I.
      * apply recovery_retains_summary. intros d p POS OWN; discriminate.
    + rewrite S; reflexivity.
    + rewrite P; reflexivity.
    + exact BOUND.
  - rewrite F, S, P, C, A, B, PH, ACK. unfold s, recovered_ram; simpl.
    rewrite app_nil_r. repeat split; reflexivity.
Qed.

Theorem reconstructed_image_correspondence (view : nat -> root_view) marker id ranges image :
  object_extents (view id) = image_dependencies ranges image ->
  image_current_correspondence ranges image [boss_extent (view id)]
    (reconstructed marker (boss_extent (view id)) (image_dependencies ranges image)).
Proof.
  intro E. unfold image_current_correspondence, reconstructed.
  destruct (recovery_retains_observers
    (marker :: boss_extent (view id) :: image_dependencies ranges image)
    (recovered_ram marker (boss_extent (view id)) (image_dependencies ranges image)))
    as [C [_ [_ [A _]]]]. rewrite C, A; simpl. rewrite app_nil_r; reflexivity.
Qed.

Theorem reconstructed_can_begin (view : nat -> root_view) marker id entries :
  entries = object_extents (view id) ->
  data_caller DataBegin (reconstructed marker (boss_extent (view id)) entries) /\
  data_invariant (data_next DataBegin (reconstructed marker (boss_extent (view id)) entries)).
Proof.
  intro E. pose proof (reconstruction_establishes_idle view marker id entries E)
    as [INV [F [S [P REST]]]].
  assert (CALL : data_caller DataBegin (reconstructed marker (boss_extent (view id)) entries)).
  { unfold data_caller; rewrite F, S, P; simpl; repeat split; auto; lia. }
  split; [exact CALL|apply data_command_preserves; assumption].
Qed.

Record recovery_decoding := RecoveryDecoding {
  recovered_boss : extent;
  recovered_image : list compact_slot
}.
Definition decoded_root_agrees (view : nat -> root_view) ranges id decoded :=
  recovered_boss decoded = boss_extent (view id) /\
  image_dependencies ranges (recovered_image decoded) = object_extents (view id).
Definition rebuild_decoded marker ranges decoded :=
  reconstructed marker (recovered_boss decoded)
    (image_dependencies ranges (recovered_image decoded)).
Theorem decoded_reconstruction_opens_transaction view marker ranges id decoded :
  decoded_root_agrees view ranges id decoded ->
  idle_root view marker id (rebuild_decoded marker ranges decoded) /\
  image_current_correspondence ranges (recovered_image decoded) [recovered_boss decoded]
    (rebuild_decoded marker ranges decoded) /\
  data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
  data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)).
Proof.
  intros [B E]. unfold rebuild_decoded; rewrite B. split.
  - apply reconstruction_establishes_idle; exact E.
  - split; [apply reconstructed_image_correspondence; symmetry; exact E|].
    apply reconstructed_can_begin; exact E.
Qed.

(* Validation cache bits are separate from ownership. Remembering the recovered
   BOSS changes no roots, scopes, reservation or owner. *)
Definition update_validation (bits : nat -> bool) s :=
  change_preparation s (pending_preparation s) (protection_frozen s)
    (fun p => {| owner := owner (protection_table s p); validated := bits p |})
    (protection_bits s) (protection_dirty s).
Theorem validation_update_preserves_data bits s :
  data_invariant s -> data_invariant (update_validation bits s).
Proof.
  unfold data_invariant, protection_invariant, preparation_invariant, protected,
    required_ranges, context_ranges, surviving_ranges, context_scopes, pending_ranges,
    protected_roots, data_ownership, scope_invariant, data_scope, bounded,
    stack_bounded, summary_view, summary_sound, update_validation, change_preparation;
    simpl. auto.
Qed.
Theorem validation_update_preserves_idle view marker id bits s :
  idle_root view marker id s -> idle_root view marker id (update_validation bits s).
Proof.
  intros [I REST]. split; [apply validation_update_preserves_data; exact I|exact REST].
Qed.
Definition remember_recovered_boss area_pages boss s :=
  update_validation (fun p => validated (protection_table s p) ||
    ((offset boss mod 256 =? 0) && (p =? offset boss / 256) &&
     (p <? area_pages) && negb (owner (protection_table s p) =? 0))) s.
Theorem remembered_recovery_can_begin view marker ranges id decoded area_pages :
  decoded_root_agrees view ranges id decoded ->
  let final := remember_recovered_boss area_pages (recovered_boss decoded)
    (rebuild_decoded marker ranges decoded) in
  idle_root view marker id final /\ data_caller DataBegin final /\
  data_invariant (data_next DataBegin final).
Proof.
  intro FORMAT; cbn zeta.
  destruct (decoded_reconstruction_opens_transaction view marker ranges id decoded FORMAT)
    as [IDLE [IMAGE [CALL BEGIN]]].
  assert (REST : idle_root view marker id
    (remember_recovered_boss area_pages (recovered_boss decoded) (rebuild_decoded marker ranges decoded))).
  { apply validation_update_preserves_idle; exact IDLE. }
  split; [exact REST|]. split; [exact CALL|]. apply data_command_preserves; [exact (proj1 REST)|exact CALL].
Qed.
