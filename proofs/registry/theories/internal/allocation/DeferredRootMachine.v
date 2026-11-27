From Coq Require Import List Arith Lia.
Import ListNotations.

Section Roots.
Context {V : Type}.
Variable decoded : nat -> option V.
Definition boundary := (option nat * V)%type.
Definition root_of (b : boundary) := fst b.
Definition all_saved fs := Forall (fun b : boundary => exists r, fst b = Some r) fs.
Fixpoint ordered (fs : list boundary) : Prop :=
  match fs with
  | [] => True
  | (Some _, _) :: tail => ordered tail
  | (None, _) :: tail => Forall (fun b => fst b = None) tail
  end.
Definition agrees image current fs :=
  (forall r, current = Some r -> decoded r = Some image) /\
  Forall (fun b : boundary => match fst b with
    | Some r => decoded r = Some (snd b)
    | None => snd b = image /\ current = None end) fs.
Definition roots_invariant image current fs :=
  length fs <= 6 /\ ordered fs /\ agrees image current fs.

Definition resolve id (b : boundary) : boundary :=
  match fst b with Some _ => b | None => (Some id, snd b) end.

Lemma ordered_prefix fs tail : ordered (fs ++ tail) -> ordered fs.
Proof.
  induction fs as [|[[r|] v] fs IH]; simpl; auto.
  intros H. apply Forall_app in H; tauto.
Qed.
Lemma ordered_append_none fs v : ordered fs -> ordered (fs ++ [(None,v)]).
Proof.
  induction fs as [|[[r|] w] fs IH]; simpl; auto.
  intros H. apply Forall_app; split; [exact H|constructor; auto].
Qed.
Lemma all_saved_ordered fs : all_saved fs -> ordered fs.
Proof.
  intros H. induction H as [|[[r|] v] fs E H IH]; simpl in *; auto.
  destruct E as [r E]; discriminate.
Qed.
Lemma current_materialized_all_saved image id fs :
  agrees image (Some id) fs -> all_saved fs.
Proof.
  intros [_ H]. induction H as [|[[r|] v] fs E H IH]; constructor; simpl in *; auto.
  - exists r; reflexivity.
  - destruct E; discriminate.
Qed.
Lemma resolved_all_saved id fs : all_saved (map (resolve id) fs).
Proof.
  induction fs as [|[[r|] v] fs IH]; simpl; constructor; auto;
    [exists r|exists id]; reflexivity.
Qed.
Lemma agreement_prefix image current fs tail :
  agrees image current (fs ++ tail) -> agrees image current fs.
Proof. intros [C F]. apply Forall_app in F; split; tauto. Qed.

Inductive root_step : V -> option nat -> list boundary -> V -> option nat -> list boundary -> Prop :=
| root_begin image current fs : length fs < 6 ->
    root_step image current fs image current (fs ++ [(current,image)])
| root_save image current fs id : decoded id = Some image ->
    root_step image current fs image (Some id) (map (resolve id) fs)
| root_edit image current fs next : all_saved fs ->
    root_step image current fs next None fs
| root_accept image current fs last :
    root_step image current (fs ++ [last]) image current fs
| root_rollback_saved image current fs id old :
    root_step image current (fs ++ [(Some id,old)]) old (Some id) fs
| root_rollback_deferred image current fs old :
    root_step image current (fs ++ [(None,old)]) image current fs
| root_reject image current fs : root_step image current fs image current fs.

Theorem root_step_inductive image current fs image' current' fs' :
  roots_invariant image current fs -> root_step image current fs image' current' fs' ->
  roots_invariant image' current' fs'.
Proof.
  intros [D [O [C F]]] STEP. destruct STEP.
  - split; [rewrite length_app; simpl; lia|]. split.
    + destruct current as [r|].
      * apply all_saved_ordered. apply Forall_app; split.
        -- apply (current_materialized_all_saved image r fs); split; assumption.
        -- constructor; [exists r; reflexivity|constructor].
      * apply ordered_append_none; exact O.
    + split; [exact C|]. apply Forall_app; split; [exact F|].
      constructor; [|constructor]. simpl. destruct current as [r|]; auto.
  - split; [rewrite length_map; exact D|]. split.
    + apply all_saved_ordered. apply resolved_all_saved.
    + split; [intros r E; inversion E; subst; assumption|].
      apply Forall_map. eapply Forall_impl; [|exact F].
      intros [[r|] v] Eframe; simpl in *; auto. destruct Eframe as [-> _]; assumption.
  - split; [exact D|]. split; [exact O|]. split; [intros r E; discriminate|].
    apply Forall_forall. intros [[r|] v] I; simpl.
    + apply (proj1 (Forall_forall _ _) F _ I).
    + destruct (proj1 (Forall_forall _ _) H _ I) as [r E]; discriminate.
  - split; [rewrite length_app in D; simpl in D; exact (Nat.le_trans _ _ _ (Nat.le_add_r (length fs) 1) D)|]. split.
    + eapply ordered_prefix; exact O.
    + apply agreement_prefix with (tail:=[last]); split; assumption.
  - apply Forall_app in F. destruct F as [F LAST]. pose proof (Forall_inv LAST) as VALID.
    simpl in VALID. unfold roots_invariant. split.
    + rewrite length_app in D; simpl in D. exact (Nat.le_trans _ _ _ (Nat.le_add_r (length fs) 1) D).
    + split.
      * eapply ordered_prefix; exact O.
      * split; [intros r E; inversion E; subst; exact VALID|].
      apply Forall_forall. intros [[r|] v] I; simpl.
      -- apply (proj1 (Forall_forall _ _) F _ I).
      -- exfalso.
        (* A saved last element rules out any preceding deferred element. *)
        clear C D F VALID LAST.
        induction fs as [|[[r|] w] fs IH]; simpl in *.
        ++ contradiction.
        ++ destruct I as [E|I]; [discriminate|apply IH; assumption].
        ++ apply Forall_app in O. destruct O as [_ H]. inversion H; discriminate.
  - split; [rewrite length_app in D; simpl in D; exact (Nat.le_trans _ _ _ (Nat.le_add_r (length fs) 1) D)|]. split.
    + eapply ordered_prefix; exact O.
    + apply agreement_prefix with (tail:=[(None,old)]); split; assumption.
  - split; [exact D|]. split; [exact O|]. split; assumption.
Qed.

Lemma deferred_views_repeat image (current : option nat) fs :
  Forall (fun b : boundary => fst b = None) fs ->
  Forall (fun b : boundary => match fst b with
    | Some r => decoded r = Some (snd b)
    | None => snd b = image /\ current = None end) fs ->
  fs = repeat (None,image) (length fs).
Proof.
  induction fs as [|[[r|] v] fs IH]; intros N A; simpl; [reflexivity| |].
  - pose proof (Forall_inv N) as E; discriminate.
  - pose proof (Forall_inv A) as E; simpl in E. destruct E as [-> _].
    f_equal. apply IH; eauto using Forall_inv_tail.
Qed.
Theorem deferred_suffix_derived image current fs :
  roots_invariant image current fs ->
  exists prefix count, all_saved prefix /\
    fs = prefix ++ repeat (None,image) count.
Proof.
  intros [_ [O [_ F]]]. revert O F.
  induction fs as [|[[r|] v] fs IH]; intros O F.
  - exists [], 0. split; [constructor|reflexivity].
  - simpl in O.
    destruct (IH O (Forall_inv_tail F)) as [prefix [count [S E]]].
    exists ((Some r,v)::prefix), count. split.
    + constructor; [exists r; reflexivity|exact S].
    + simpl. rewrite E; reflexivity.
  - exists [], (length ((None,v)::fs)). split; [constructor|].
    change ((None,v)::fs = repeat (None,image) (length ((None,v)::fs))).
    apply deferred_views_repeat with (current:=current); [|exact F].
    constructor; [reflexivity|exact O].
Qed.
Inductive root_trace : V -> option nat -> list boundary -> V -> option nat -> list boundary -> Prop :=
| roots_refl image current fs : root_trace image current fs image current fs
| roots_cons image current fs middle mr mf last lr lf :
    root_step image current fs middle mr mf -> root_trace middle mr mf last lr lf ->
    root_trace image current fs last lr lf.
Theorem finite_roots_preserve_agreement image current fs image' current' fs' :
  roots_invariant image current fs -> root_trace image current fs image' current' fs' ->
  roots_invariant image' current' fs'.
Proof.
  intros I T. induction T; [exact I|]. apply IHT. eapply root_step_inductive; eauto.
Qed.
Theorem reachable_deferred_suffix image current fs image' current' fs' :
  roots_invariant image current fs -> root_trace image current fs image' current' fs' ->
  exists prefix count, all_saved prefix /\ fs' = prefix ++ repeat (None,image') count.
Proof.
  intros I T. apply deferred_suffix_derived with (current:=current').
  eapply finite_roots_preserve_agreement; eauto.
Qed.
End Roots.
