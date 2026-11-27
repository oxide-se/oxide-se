From Coq Require Import List Arith Bool Lia.
From OxideSE.Registry Require Import Types.
Import ListNotations.

(* A finite table. Indices remain stable; removal creates a tombstone. *)
Definition data_object := (identity * payload)%type.
Definition cell := option data_object.
Definition slots := list cell.
Fixpoint replace_slot (t : slots) (i : nat) (x : cell) : slots :=
  match t, i with
  | [], _ => []
  | _::tail, 0 => x::tail
  | head::tail, S n => head::replace_slot tail n x
  end.
Definition slot_at (t : slots) (i : nat) : cell := nth i t None.
Fixpoint project (t : slots) : view :=
  match t with
  | [] => empty_view
  | None::tail => project tail
  | Some (k,data)::tail => fun q =>
      if identity_eq_dec q k then Some data else project tail q
  end.
Fixpoint unique_slots (t : slots) : Prop :=
  match t with
  | [] => True
  | None::tail => unique_slots tail
  | Some (k,_)::tail => project tail k = None /\ unique_slots tail
  end.
(* Successful identity/slot resolution: the selected slot is free or already
   contains k, and no other slot has k. Does not assume all other keys unique. *)
Fixpoint writable (t : slots) (i : nat) (k : identity) : Prop :=
  match t with
  | [] => False
  | head::tail => match i with
      | 0 => (head = None \/ exists d, head = Some (k,d)) /\ project tail k = None
      | S n => match head with
          | None => writable tail n k
          | Some (q,_) => q <> k /\ writable tail n k
          end
      end
  end.
Definition keyed (k : identity) (x : option payload) : cell :=
  option_map (fun d => (k,d)) x.
Fixpoint live_count (t : slots) : nat :=
  match t with [] => 0 | None::tail => live_count tail
  | Some _::tail => S (live_count tail) end.

Lemma replace_length t i x : length (replace_slot t i x) = length t.
Proof. revert i; induction t; intros [|i]; simpl; auto. Qed.
Lemma replace_shadow t i x y :
  replace_slot (replace_slot t i x) i y = replace_slot t i y.
Proof. revert i; induction t; intros [|i]; simpl; auto; f_equal; auto. Qed.
Lemma replace_original t i : replace_slot t i (slot_at t i) = t.
Proof. revert i; induction t; intros [|i]; simpl in *; auto; f_equal; auto. Qed.
Lemma replace_commute t i j x y : i <> j ->
  replace_slot (replace_slot t i x) j y = replace_slot (replace_slot t j y) i x.
Proof.
  revert i j; induction t; intros [|i] [|j] H; simpl; auto; try congruence.
  f_equal; apply IHt; congruence.
Qed.
Lemma at_replaced t i x : i < length t -> slot_at (replace_slot t i x) i = x.
Proof. revert i; induction t; intros [|i] H; simpl in *; try lia; auto; apply IHt; lia. Qed.
Lemma writable_bound t i k : writable t i k -> i < length t.
Proof.
  revert i; induction t as [|head tail IH]; intros [|i] H; simpl in *; try contradiction; try lia.
  destruct head as [[q d]|]; simpl in H; [destruct H as [_ H]|]; specialize (IH i H); lia.
Qed.
Lemma project_replace t i k x : writable t i k ->
  same_view (project (replace_slot t i (keyed k x))) (put (project t) k x).
Proof.
  revert i; induction t as [|head tail IH]; intros [|i] H q; simpl in H; try contradiction.
  - destruct H as [[H|[d H]] A]; subst head; destruct x as [d'|];
      simpl; unfold put, empty_view; destruct (identity_eq_dec q k); subst; auto.
  - destruct head as [[key d]|].
    + destruct H as [N H]. simpl. unfold put.
      destruct (identity_eq_dec q key) as [E|E]; destruct (identity_eq_dec q k) as [F|F];
        try congruence; auto.
      all: specialize (IH i H q); unfold put in IH;
        destruct (identity_eq_dec q k); congruence.
    + simpl. apply IH; exact H.
Qed.
Lemma replace_preserves_unique t i k x :
  unique_slots t -> writable t i k -> unique_slots (replace_slot t i (keyed k x)).
Proof.
  revert i; induction t as [|head tail IH]; intros [|i] U W; simpl in *; try contradiction.
  - destruct W as [_ A]. destruct head as [[q d]|]; simpl in U;
      [destruct U as [_ U]|]; destruct x; simpl; auto.
  - destruct head as [[q d]|].
    + destruct U as [A U]. destruct W as [N W]. split.
      * rewrite (project_replace tail i k x W q). rewrite put_other; auto.
      * apply IH; auto.
    + apply IH; auto.
Qed.
Lemma live_count_bounded t : live_count t <= length t.
Proof. induction t as [|[o|] tail IH]; simpl; lia. Qed.

Lemma deletion_preserves_absence t i k :
  project t k = None -> project (replace_slot t i None) k = None.
Proof.
  revert i; induction t as [|head tail IH]; intros [|i] H; simpl in *; auto.
  - destruct head as [[q d]|]; simpl in H; auto.
    destruct (identity_eq_dec k q); try discriminate; exact H.
  - destruct head as [[q d]|]; simpl in *.
    + destruct (identity_eq_dec k q); try discriminate. apply IH; exact H.
    + apply IH; exact H.
Qed.
Theorem deletion_preserves_unique t i :
  unique_slots t -> unique_slots (replace_slot t i None).
Proof.
  revert i; induction t as [|head tail IH]; intros [|i] H; simpl in *; auto.
  - destruct head as [[q d]|]; simpl in H; tauto.
  - destruct head as [[q d]|]; simpl in *.
    + destruct H as [A U]; split; [apply deletion_preserves_absence|apply IH]; auto.
    + apply IH; exact H.
Qed.

Lemma slot_at_other t i q x : q <> i ->
  slot_at (replace_slot t i x) q = slot_at t q.
Proof.
  revert i q; induction t as [|head tail IH]; intros [|i] [|q] N; simpl in *;
    try congruence; auto. apply IH; congruence.
Qed.
