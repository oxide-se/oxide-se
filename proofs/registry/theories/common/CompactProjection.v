From Coq Require Import List.
From OxideSE.Registry Require Import Types CompactImage Slots.
Import ListNotations.

(* Resolution is deliberately partial: a malformed occupied entry makes the
   whole projection fail instead of silently becoming an empty slot. The
   resolver is a future authenticated decoder/load obligation. *)
Fixpoint resolve_slots (resolve : compact_entry -> option data_object)
    (image : list compact_slot) : option slots :=
  match image with
  | [] => Some []
  | None :: tail =>
      match resolve_slots resolve tail with
      | Some rest => Some (None :: rest)
      | None => None
      end
  | Some entry :: tail =>
      match resolve entry, resolve_slots resolve tail with
      | Some object, Some rest => Some (Some object :: rest)
      | _, _ => None
      end
  end.

Lemma resolve_empty_suffix resolve n :
  resolve_slots resolve (repeat None n) = Some (repeat None n).
Proof. induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma resolve_append_empty_suffix resolve image n logical :
  resolve_slots resolve image = Some logical ->
  resolve_slots resolve (image ++ repeat None n) =
    Some (logical ++ repeat None n).
Proof.
  revert logical. induction image as [|[entry|] tail IH]; intros logical H;
    simpl in *.
  - inversion H; subst. apply resolve_empty_suffix.
  - destruct (resolve entry) as [object|] eqn:E; try discriminate.
    destruct (resolve_slots resolve tail) as [rest|] eqn:R;
      try discriminate.
    inversion H; subst. simpl. rewrite (IH _ eq_refl). reflexivity.
  - destruct (resolve_slots resolve tail) as [rest|] eqn:R;
      try discriminate.
    inversion H; subst. simpl. rewrite (IH _ eq_refl). reflexivity.
Qed.

Lemma project_append_empty_suffix logical n :
  same_view (project (logical ++ repeat None n)) (project logical).
Proof.
  revert n. induction logical as [|[object|] tail IH]; intros n q; simpl.
  - induction n; simpl; [reflexivity|exact IHn].
  - destruct object as [key data]. simpl.
    destruct (identity_eq_dec q key); [reflexivity|apply IH].
  - apply IH.
Qed.

Theorem trailing_holes_preserve_projection resolve image logical n :
  resolve_slots resolve image = Some logical ->
  exists logical',
    resolve_slots resolve (image ++ repeat None n) = Some logical' /\
    same_view (project logical') (project logical).
Proof.
  intro H. exists (logical ++ repeat None n). split.
  - apply resolve_append_empty_suffix; exact H.
  - apply project_append_empty_suffix.
Qed.

Lemma unresolved_entry_fails resolve entry tail :
  resolve entry = None ->
  resolve_slots resolve (Some entry :: tail) = None.
Proof. intro H; simpl; rewrite H; reflexivity. Qed.

Lemma resolved_hole_stays_hole resolve image logical i :
  resolve_slots resolve image = Some logical ->
  nth_error image i = Some None ->
  nth_error logical i = Some None.
Proof.
  revert logical i.
  induction image as [|[entry|] tail IH]; intros logical [|i] H R;
    simpl in *; try discriminate.
  - destruct (resolve entry) as [object|];
      destruct (resolve_slots resolve tail) as [rest|];
      try discriminate. inversion H; subst. apply IH with (logical:=rest);
      [reflexivity|exact R].
  - destruct (resolve_slots resolve tail) as [rest|] eqn:E;
      try discriminate. inversion H; subst. reflexivity.
  - destruct (resolve_slots resolve tail) as [rest|] eqn:E;
      try discriminate. inversion H; subst.
    apply IH with (logical:=rest); [reflexivity|exact R].
Qed.
