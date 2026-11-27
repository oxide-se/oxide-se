From Coq Require Import List Arith NArith Bool Lia.
From OxideSE.Registry Require Import Types CompactImage CompactProjection Slots RetentionCoverage.
Import ListNotations.

(* Runtime kind (not state bits) is supplied by the kind-word decoder. *)
Definition object_key := (list byte * (nat * list byte))%type.
Definition object_key_eq_dec : forall x y : object_key, {x=y}+{x<>y}.
Proof. unfold object_key. repeat decide equality. Defined.
Global Opaque object_key_eq_dec.
Definition entry_key (runtime_kind : list byte -> nat) e : object_key :=
  (parent_aid e, (runtime_kind (kind_word e), object_aid e)).
Fixpoint image_replace (xs : list compact_slot) i x :=
  match xs, i with
  | [], _ => [] | _::tail, 0 => x::tail
  | head::tail, S j => head::image_replace tail j x
  end.
Lemma image_replace_length xs i x : length (image_replace xs i x) = length xs.
Proof. revert i; induction xs; intros [|i]; simpl; auto. Qed.
Lemma image_replace_here xs i x : i < length xs -> nth_error (image_replace xs i x) i = Some x.
Proof. revert i; induction xs; intros [|i] H; simpl in *; try lia; auto; apply IHxs; lia. Qed.
Lemma image_replace_other xs i j x : i <> j ->
  nth_error (image_replace xs i x) j = nth_error xs j.
Proof.
  revert i j; induction xs; intros [|i] [|j] H; simpl; auto; try congruence.
Qed.
Lemma image_replace_shadow xs i a b :
  image_replace (image_replace xs i a) i b = image_replace xs i b.
Proof. revert i; induction xs; intros [|i]; simpl; auto; f_equal; auto. Qed.

Section Identity.
Variable kind : list byte -> nat.
Definition key := entry_key kind.
Fixpoint lookup_entry xs q : option compact_entry :=
  match xs with
  | [] => None | None::tail => lookup_entry tail q
  | Some e::tail => if object_key_eq_dec q (key e) then Some e else lookup_entry tail q
  end.
Fixpoint find_identity xs q : option nat :=
  match xs with
  | [] => None
  | None::tail => option_map S (find_identity tail q)
  | Some e::tail => if object_key_eq_dec q (key e) then Some 0
                   else option_map S (find_identity tail q)
  end.
Fixpoint find_hole (xs : list compact_slot) : option nat :=
  match xs with [] => None | None::_ => Some 0
  | Some _::tail => option_map S (find_hole tail) end.
(* Data/Key branch of slot_for. Other kinds have an extra cross-parent check. *)
Definition data_slot_for xs q :=
  match find_identity xs q with Some i => Some i | None => find_hole xs end.
Fixpoint image_unique xs : Prop :=
  match xs with [] => True | None::tail => image_unique tail
  | Some e::tail => lookup_entry tail (key e) = None /\ image_unique tail end.
Fixpoint image_writable xs i q : Prop :=
  match xs with [] => False | head::tail =>
    match i with
    | 0 => (head = None \/ exists e, head = Some e /\ key e = q) /\ lookup_entry tail q = None
    | S j => match head with None => image_writable tail j q
             | Some e => key e <> q /\ image_writable tail j q end
    end
  end.
Lemma find_none_lookup xs q : find_identity xs q = None -> lookup_entry xs q = None.
Proof.
  induction xs as [|[e|] tail IH]; simpl; auto.
  - destruct (object_key_eq_dec q (key e)); [discriminate|].
    destruct (find_identity tail q); simpl; [discriminate|intros; apply IH; reflexivity].
  - destruct (find_identity tail q); simpl; [discriminate|intros; apply IH; reflexivity].
Qed.
Lemma find_identity_writable xs q i : image_unique xs -> find_identity xs q = Some i -> image_writable xs i q.
Proof.
  revert i; induction xs as [|[e|] tail IH]; intros i U F; simpl in *; try discriminate.
  - destruct U as [A U]. destruct (object_key_eq_dec q (key e)) as [E|E].
    + inversion F; subst. split; [right; exists e; auto|exact A].
    + destruct (find_identity tail q) as [j|] eqn:J; simpl in F; try discriminate.
      inversion F; subst. split; [congruence|apply IH; auto].
  - destruct (find_identity tail q) as [j|] eqn:J; simpl in F; try discriminate.
    inversion F; subst. apply IH; auto.
Qed.
Lemma hole_writable xs q i : lookup_entry xs q = None -> find_hole xs = Some i -> image_writable xs i q.
Proof.
  revert i; induction xs as [|[e|] tail IH]; intros i A H; simpl in *; try discriminate.
  - destruct (object_key_eq_dec q (key e)) as [E|E]; try discriminate.
    destruct (find_hole tail) as [j|] eqn:J; simpl in H; try discriminate.
    inversion H; subst. split; [congruence|apply IH; auto].
  - inversion H; subst. split; auto.
Qed.
Theorem data_slot_for_admissible xs q i :
  image_unique xs -> data_slot_for xs q = Some i -> image_writable xs i q.
Proof.
  intros U H. unfold data_slot_for in H. destruct (find_identity xs q) eqn:F.
  - inversion H; subst; eapply find_identity_writable; eauto.
  - eapply hole_writable; [apply find_none_lookup; exact F|exact H].
Qed.
Lemma image_writable_bound xs i q : image_writable xs i q -> i < length xs.
Proof.
  revert i; induction xs as [|[e|] tail IH]; intros [|i] W; simpl in *; try contradiction; try lia.
  - destruct W as [_ W]; specialize (IH i W); lia.
  - specialize (IH i W); lia.
Qed.
Theorem lookup_image_replace xs i q x :
  image_writable xs i q -> (forall e, x = Some e -> key e = q) ->
  forall k, lookup_entry (image_replace xs i x) k =
    if object_key_eq_dec k q then x else lookup_entry xs k.
Proof.
  revert i; induction xs as [|head tail IH]; intros [|i] W X k; simpl in W; try contradiction.
  - destruct W as [[H|[old [H K]]] ABS]; subst head; destruct x as [e|]; simpl;
      try specialize (X e eq_refl); try subst q;
      repeat match goal with |- context[object_key_eq_dec ?a ?b] => destruct (object_key_eq_dec a b) end;
      subst; try congruence; auto.
  - destruct head as [e|]; simpl in *.
    + destruct W as [NE W]. rewrite (IH i W X k).
      destruct (object_key_eq_dec k (key e)); destruct (object_key_eq_dec k q); congruence.
    + apply IH; assumption.
Qed.
Lemma image_replace_unique xs i q x :
  image_unique xs -> image_writable xs i q ->
  (forall e, x = Some e -> key e = q) -> image_unique (image_replace xs i x).
Proof.
  revert i; induction xs as [|head tail IH]; intros [|i] U W X; simpl in *; try contradiction.
  - destruct W as [_ A]. destruct head as [old|]; simpl in U; [destruct U as [_ U]|];
      destruct x as [e|]; simpl; auto; rewrite (X e eq_refl); auto.
  - destruct head as [e|]; simpl in *.
    + destruct U as [A U]. destruct W as [NE W]. split.
      * rewrite (lookup_image_replace tail i q x W X (key e)).
        destruct (object_key_eq_dec (key e) q); congruence.
      * eapply IH; eauto.
    + eapply IH; eauto.
Qed.
Theorem selected_insert_exact xs e i :
  image_unique xs -> data_slot_for xs (key e) = Some i ->
  nth_error (image_replace xs i (Some e)) i = Some (Some e) /\
  image_unique (image_replace xs i (Some e)) /\
  forall q, lookup_entry (image_replace xs i (Some e)) q =
    if object_key_eq_dec q (key e) then Some e else lookup_entry xs q.
Proof.
  intros U SEL. pose proof (data_slot_for_admissible xs (key e) i U SEL) as W.
  split; [apply image_replace_here; eapply image_writable_bound; eauto|]. split.
  - eapply image_replace_unique; eauto; intros; congruence.
  - apply lookup_image_replace; auto; intros; congruence.
Qed.
Theorem repeated_identity_last_wins xs a b i j :
  image_unique xs -> key a = key b -> data_slot_for xs (key a) = Some i ->
  data_slot_for (image_replace xs i (Some a)) (key b) = Some j ->
  forall q, lookup_entry (image_replace (image_replace xs i (Some a)) j (Some b)) q =
    if object_key_eq_dec q (key b) then Some b else lookup_entry xs q.
Proof.
  intros U K A B q. destruct (selected_insert_exact xs a i U A) as [_ [U1 L1]].
  destruct (selected_insert_exact _ b j U1 B) as [_ [_ L2]]. rewrite L2, L1, K.
  destruct (object_key_eq_dec q (key b)); reflexivity.
Qed.
End Identity.

(* Exact multiset enumeration: duplicates are retained. Shared references
   therefore survive removal of just one occurrence. The resolver includes
   every physical extent needed by an entry, possibly several pages/blocks. *)
Definition slot_dependencies (ranges : compact_entry -> list extent) x :=
  match x with None => [] | Some e => ranges e end.
Definition image_dependencies ranges xs := flat_map (slot_dependencies ranges) xs.
Lemma dependencies_occurrence ranges xs r :
  In r (image_dependencies ranges xs) <->
  exists i e, nth_error xs i = Some (Some e) /\ In r (ranges e).
Proof.
  unfold image_dependencies. rewrite in_flat_map. split.
  - intros [[e|] [IN R]]; simpl in R; [|contradiction].
    apply In_nth_error in IN. destruct IN as [i IN]. eauto.
  - intros [i [e [IN R]]]. exists (Some e); split; [eapply nth_error_In; eauto|exact R].
Qed.
Theorem dependencies_replace_exact ranges before after x :
  image_dependencies ranges (before ++ x::after) =
    image_dependencies ranges before ++ slot_dependencies ranges x ++ image_dependencies ranges after.
Proof. unfold image_dependencies; rewrite flat_map_app; reflexivity. Qed.
Lemma dependencies_replace_subset ranges xs i x r :
  In r (image_dependencies ranges (image_replace xs i x)) ->
  In r (slot_dependencies ranges x) \/ In r (image_dependencies ranges xs).
Proof.
  revert i; induction xs as [|h tail IH]; intros [|i] H; simpl in H; try contradiction.
  - unfold image_dependencies in *; simpl in *.
    apply in_app_or in H. destruct H as [H|H]; [auto|]. right; apply in_or_app; auto.
  - unfold image_dependencies in *; simpl in *.
    apply in_app_or in H. destruct H as [H|H].
    + right; apply in_or_app; auto.
    + destruct (IH i H); [auto|right; apply in_or_app; auto].
Qed.
Theorem shared_occurrence_survives ranges xs i j e x r :
  i <> j -> nth_error xs j = Some (Some e) -> In r (ranges e) ->
  In r (image_dependencies ranges (image_replace xs i x)).
Proof.
  intros N E R. apply dependencies_occurrence. exists j,e; split; [rewrite image_replace_other; auto|exact R].
Qed.
Theorem compact_update_resolves resolve xs logical i x y :
  resolve_slots resolve xs = Some logical ->
  (match x with None => y = None | Some e => exists o, resolve e = Some o /\ y = Some o end) ->
  resolve_slots resolve (image_replace xs i x) = Some (Slots.replace_slot logical i y).
Proof.
  revert logical i. induction xs as [|[e|] tail IH]; intros logical [|i] H X; simpl in *;
    try (inversion H; reflexivity).
  all: try (destruct (resolve e) as [o|] eqn:E; try discriminate).
  all: destruct (resolve_slots resolve tail) as [rest|] eqn:T; try discriminate;
    inversion H; subst logical; simpl.
  - destruct x as [a|]; simpl in *; [destruct X as [b [B ->]]; rewrite B|subst y]; rewrite ?T; reflexivity.
  - rewrite (IH rest i eq_refl X); reflexivity.
  - destruct x as [a|]; simpl in *; [destruct X as [b [B ->]]; rewrite B|subst y]; rewrite ?T; reflexivity.
  - rewrite (IH rest i eq_refl X); reflexivity.
Qed.

(* The Rust prepass consults the entry view before either attachment. Original
   producer indices are the result; a repeated tag forces the second index. *)
Definition changed_pair (same_tag equal_first equal_second : bool) : list nat :=
  (if equal_first then [] else [0]) ++
  (if same_tag then [1] else if equal_second then [] else [1]).
Theorem repeated_tag_keeps_second a b : In 1 (changed_pair true a b).
Proof. destruct a,b; simpl; auto. Qed.
Example second_only_original_index : changed_pair false true false = [1].
Proof. reflexivity. Qed.
Example entirely_unchanged_indices : changed_pair false true true = [].
Proof. reflexivity. Qed.
Example return_to_initial_is_not_eliminated : changed_pair true false true = [0;1].
Proof. reflexivity. Qed.

Theorem repeated_identity_uses_same_slot kind xs e i :
  image_writable kind xs i (entry_key kind e) ->
  data_slot_for kind (image_replace xs i (Some e)) (entry_key kind e) = Some i.
Proof.
  intros W. unfold data_slot_for.
  assert (F : find_identity kind (image_replace xs i (Some e)) (entry_key kind e) = Some i).
  { revert i W. induction xs as [|[a|] tail IH]; intros [|i] W; simpl in *; unfold key in *;
      try contradiction.
    - destruct (object_key_eq_dec (entry_key kind e) (entry_key kind e)); congruence.
    - destruct W as [NE W]. destruct (object_key_eq_dec (entry_key kind e) (entry_key kind a));
        [congruence|rewrite (IH i W); reflexivity].
    - destruct (object_key_eq_dec (entry_key kind e) (entry_key kind e)); congruence.
    - rewrite (IH i W); reflexivity. }
  rewrite F; reflexivity.
Qed.
Theorem two_replacements_lookup kind xs a b i j :
  image_unique kind xs -> data_slot_for kind xs (entry_key kind a) = Some i ->
  data_slot_for kind (image_replace xs i (Some a)) (entry_key kind b) = Some j ->
  forall q, lookup_entry kind (image_replace (image_replace xs i (Some a)) j (Some b)) q =
    if object_key_eq_dec q (entry_key kind b) then Some b
    else if object_key_eq_dec q (entry_key kind a) then Some a else lookup_entry kind xs q.
Proof.
  intros U A B q. destruct (selected_insert_exact kind xs a i U A) as [_ [U1 L1]].
  destruct (selected_insert_exact kind _ b j U1 B) as [_ [_ L2]]. rewrite L2, L1; reflexivity.
Qed.
Theorem selected_delete_exact kind xs q i :
  image_unique kind xs -> find_identity kind xs q = Some i ->
  forall k, lookup_entry kind (image_replace xs i None) k =
    if object_key_eq_dec k q then None else lookup_entry kind xs k.
Proof.
  intros U F. apply lookup_image_replace; [eapply find_identity_writable; eauto|intros; discriminate].
Qed.
Theorem removed_dependency_absent ranges xs i x r :
  ~ In r (slot_dependencies ranges x) ->
  (forall j e, nth_error xs j = Some (Some e) -> In r (ranges e) -> j = i) ->
  ~ In r (image_dependencies ranges (image_replace xs i x)).
Proof.
  intros NEW ONLY H. apply dependencies_occurrence in H. destruct H as [j [e [E R]]].
  destruct (Nat.eq_dec i j) as [EQ|NE].
  - subst j. destruct (Nat.lt_ge_cases i (length xs)) as [L|L].
    + rewrite image_replace_here in E by exact L. inversion E; subst x. apply NEW; exact R.
    + assert (BOUND : i < length (image_replace xs i x)).
      { apply nth_error_Some. intro BAD. pose proof (eq_trans (eq_sym E) BAD) as CLASH. discriminate CLASH. }
      rewrite image_replace_length in BOUND. exact (Nat.lt_irrefl i (Nat.lt_le_trans _ _ _ BOUND L)).
  - rewrite image_replace_other in E by exact NE. specialize (ONLY j e E R); congruence.
Qed.
Definition data_tag_aid (tag : nat) : list byte :=
  [68%N;65%N;84%N;65%N;N.of_nat (tag / 256);N.of_nat (tag mod 256)].
Theorem data_tag_aid_injective a b : data_tag_aid a = data_tag_aid b -> a = b.
Proof.
  unfold data_tag_aid. intros E. injection E as HI LO.
  apply Nat2N.inj in HI. apply Nat2N.inj in LO.
  change (a / 256 = b / 256) in HI. change (a mod 256 = b mod 256) in LO.
  rewrite (Nat.div_mod a 256 ltac:(lia)), (Nat.div_mod b 256 ltac:(lia)). rewrite HI, LO; reflexivity.
Qed.

Definition plan_pair (same_tag : bool) (equal_first equal_second : option bool) : option (list nat) :=
  match equal_first with
  | None => None
  | Some a => if same_tag then Some (changed_pair true a false)
              else match equal_second with None => None | Some b => Some (changed_pair false a b) end
  end.
Theorem plan_pair_empty same a b :
  plan_pair same a b = Some [] <-> same = false /\ a = Some true /\ b = Some true.
Proof. destruct same, a as [[]|], b as [[]|]; simpl; intuition discriminate. Qed.
Theorem duplicate_does_not_compare_second a ignored :
  plan_pair true (Some a) ignored = Some (changed_pair true a false).
Proof. reflexivity. Qed.
Theorem plan_pair_indices_original same a b indices :
  plan_pair same a b = Some indices -> Forall (fun i => i = 0 \/ i = 1) indices.
Proof.
  destruct same, a as [[]|], b as [[]|]; simpl; intros E; try discriminate;
    inversion E; subst; repeat (apply Forall_cons; [auto|]); apply Forall_nil.
Qed.
