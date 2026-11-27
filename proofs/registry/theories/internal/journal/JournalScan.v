From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import JournalComplement.
Import ListNotations.

(* Pure model of journal.rs::latest_in's reverse slot order. [boss_ok] is the
   result of format::decode_registry_block_at, supplied by the crypto/format
   component; no authenticity or durability property is assumed here. *)
Definition physical_slot (sector : list N) (index : nat) : list N :=
  firstn 8 (skipn (8 * index) sector).

Definition checked_slot (boss_ok : N -> bool) (data_len page : N)
    (sector : list N) (index : nat) : option N :=
  match decode_slot (physical_slot sector index) data_len page with
  | Some offset => if boss_ok offset then Some offset else None
  | None => None
  end.

Fixpoint latest_scan (boss_ok : N -> bool) (data_len page : N)
    (sector : list N) (count : nat) : option (nat * N) :=
  match count with
  | O => None
  | S prior =>
      match checked_slot boss_ok data_len page sector prior with
      | Some offset => Some (prior, offset)
      | None => latest_scan boss_ok data_len page sector prior
      end
  end.

Definition latest_in_model boss_ok data_len page sector :=
  latest_scan boss_ok data_len page sector (length sector / 8).

Theorem latest_scan_sound boss_ok data_len page sector count index offset :
  latest_scan boss_ok data_len page sector count = Some (index, offset) ->
  index < count /\
  checked_slot boss_ok data_len page sector index = Some offset /\
  (forall higher, index < higher < count ->
     checked_slot boss_ok data_len page sector higher = None).
Proof.
  revert index offset. induction count as [|prior IH]; intros index offset H.
  - discriminate.
  - simpl in H.
    destruct (checked_slot boss_ok data_len page sector prior) eqn:E.
    + inversion H; subst. split; [lia|]. split; [exact E|].
      intros higher Hhigher. lia.
    + specialize (IH _ _ H) as [Hlt [Hvalid Hhigher]].
      split; [lia|]. split; [exact Hvalid|].
      intros higher Hrange. destruct (Nat.eq_dec higher prior) as [Heq|Hne].
      * subst. exact E.
      * apply Hhigher. lia.
Qed.

Theorem latest_scan_none boss_ok data_len page sector count :
  latest_scan boss_ok data_len page sector count = None ->
  forall i, i < count -> checked_slot boss_ok data_len page sector i = None.
Proof.
  induction count as [|prior IH]; intros H i Hi; [lia|].
  simpl in H.
  destruct (checked_slot boss_ok data_len page sector prior) eqn:E;
    try discriminate.
  destruct (Nat.eq_dec i prior) as [Heq|Hne].
  - subst. exact E.
  - apply IH; [exact H|lia].
Qed.

Theorem latest_scan_some_if_checked boss_ok data_len page sector count
    index offset :
  index < count ->
  checked_slot boss_ok data_len page sector index = Some offset ->
  exists found_index found_offset,
    latest_scan boss_ok data_len page sector count =
      Some (found_index, found_offset).
Proof.
  intros Hindex Hchecked.
  destruct (latest_scan boss_ok data_len page sector count)
    as [[found_index found_offset]|] eqn:Hscan.
  - eauto.
  - pose proof (latest_scan_none _ _ _ _ _ Hscan index Hindex) as Hnone.
    rewrite Hchecked in Hnone. discriminate.
Qed.

Theorem latest_scan_selects_given boss_ok data_len page sector count
    index offset :
  index < count ->
  checked_slot boss_ok data_len page sector index = Some offset ->
  (forall higher, index < higher < count ->
    checked_slot boss_ok data_len page sector higher = None) ->
  latest_scan boss_ok data_len page sector count = Some (index, offset).
Proof.
  revert index offset. induction count as [|prior IH];
    intros index offset Hindex Hvalid Hhigher; [lia|].
  simpl. destruct (Nat.eq_dec index prior) as [Heq|Hneq].
  - subst. rewrite Hvalid. reflexivity.
  - assert (Hlt : index < prior) by lia.
    rewrite (Hhigher prior ltac:(lia)).
    apply IH; [exact Hlt|exact Hvalid|].
    intros j Hj. apply Hhigher. lia.
Qed.

Theorem latest_in_has_validated_slot boss_ok data_len page sector index offset :
  latest_in_model boss_ok data_len page sector = Some (index, offset) ->
  index < length sector / 8 /\
  decode_slot (physical_slot sector index) data_len page = Some offset /\
  boss_ok offset = true.
Proof.
  intro H. unfold latest_in_model in H.
  pose proof (latest_scan_sound _ _ _ _ _ _ _ H) as [Hindex [Hvalid _]].
  unfold checked_slot in Hvalid.
  destruct (decode_slot (physical_slot sector index) data_len page) eqn:E;
    try discriminate.
  destruct (boss_ok n) eqn:B; inversion Hvalid; subst.
  repeat split; assumption.
Qed.

Theorem latest_in_selects_highest boss_ok data_len page sector index offset :
  latest_in_model boss_ok data_len page sector = Some (index, offset) ->
  forall higher, index < higher < length sector / 8 ->
    checked_slot boss_ok data_len page sector higher = None.
Proof.
  exact (fun H => proj2 (proj2
    (latest_scan_sound _ _ _ _ _ _ _ H))).
Qed.

Theorem authentic_but_unpublished_boss_not_selected boss_ok data_len page
    sector offset :
  (forall index, index < length sector / 8 ->
     decode_slot (physical_slot sector index) data_len page <> Some offset) ->
  forall index,
    latest_in_model boss_ok data_len page sector <> Some (index, offset).
Proof.
  intros Hnoindex index Hselected.
  pose proof (latest_in_has_validated_slot _ _ _ _ _ _ Hselected)
    as [Hindex [Hdecode _]].
  exact (Hnoindex index Hindex Hdecode).
Qed.

(* Publication is a physical, validated complete slot, not observation of
   write_entry's return. A Reset after completion can therefore publish. *)
Theorem complete_slot_physically_published boss_ok data_len page sector
    index offset :
  index < length sector / 8 ->
  physical_slot sector index = code_bytes offset ->
  u32 offset ->
  (page <= offset < data_len)%N ->
  (offset mod page = 0)%N ->
  boss_ok offset = true ->
  (forall higher, index < higher < length sector / 8 ->
    checked_slot boss_ok data_len page sector higher = None) ->
  latest_in_model boss_ok data_len page sector = Some (index, offset).
Proof.
  intros Hindex Hcode Hu32 Hrange Halign Hboss Hhigher.
  unfold latest_in_model.
  apply latest_scan_selects_given; [exact Hindex| |exact Hhigher].
  unfold checked_slot. rewrite Hcode.
  rewrite (decode_code_bytes offset data_len page Hu32 Hrange Halign).
  rewrite Hboss. reflexivity.
Qed.
