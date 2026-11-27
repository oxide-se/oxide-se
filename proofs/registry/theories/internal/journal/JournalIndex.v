From Coq Require Import List Arith Lia NArith.
From OxideSE.Registry Require Import FlashSpec JournalFlashBridge
  JournalScan JournalComplement.
Import ListNotations.

(* Relative addresses are used here. The sector starts at zero; the caller
   adds the checked absolute journal base. Rust's iterator tests whole
   eight-byte slices in increasing order. *)
Definition empty_slot (sector : list N) (index : nat) : bool :=
  if list_eq_dec N.eq_dec (physical_slot sector index) (repeat 255%N 8)
  then true else false.

Fixpoint first_empty_from (sector : list N) (index remaining : nat) : option nat :=
  match remaining with
  | 0 => None
  | S rest => if empty_slot sector index
              then Some index else first_empty_from sector (S index) rest
  end.

Definition first_empty_slot sector :=
  first_empty_from sector 0 (length sector / 8).

Definition sector_bytes (f : flash) (base size : nat) : list N :=
  map f (seq base size).

Lemma physical_slot_of_flash f base size index :
  8 * index + 8 <= size ->
  physical_slot (sector_bytes f base size) index =
    flash_slot f (base + 8 * index).
Proof.
  intro Hwithin. apply nth_error_ext. intro i.
  unfold physical_slot, sector_bytes, flash_slot.
  rewrite nth_error_firstn, nth_error_skipn, nth_error_map,
    nth_error_seq.
  rewrite nth_error_map, nth_error_seq.
  destruct (i <? 8) eqn:Hi; [|reflexivity].
  apply Nat.ltb_lt in Hi.
  assert (Hbound : 8 * index + i < size) by lia.
  apply Nat.ltb_lt in Hbound. rewrite Hbound.
  replace (base + (8 * index + i))%nat
    with (base + 8 * index + i)%nat by lia.
  reflexivity.
Qed.

Lemma first_empty_from_sound sector index remaining found :
  first_empty_from sector index remaining = Some found ->
  index <= found < index + remaining /\
  empty_slot sector found = true /\
  (forall earlier, index <= earlier < found ->
     empty_slot sector earlier = false).
Proof.
  revert index found. induction remaining as [|rest IH];
    intros index found Hfind; [discriminate|].
  simpl in Hfind. destruct (empty_slot sector index) eqn:E.
  - inversion Hfind; subst. repeat split; try lia; try exact E.
  - specialize (IH (S index) found Hfind) as [Hrange [Hempty Hbefore]].
    repeat split; try lia; try exact Hempty.
    intros earlier Hearlier.
    destruct (Nat.eq_dec earlier index) as [Heq|Hneq].
    + subst. exact E.
    + apply Hbefore. lia.
Qed.

Lemma first_empty_from_none sector index remaining :
  first_empty_from sector index remaining = None ->
  forall slot, index <= slot < index + remaining ->
    empty_slot sector slot = false.
Proof.
  revert index. induction remaining as [|rest IH];
    intros index Hnone slot Hrange; [lia|].
  simpl in Hnone.
  destruct (empty_slot sector index) eqn:E; try discriminate.
  destruct (Nat.eq_dec slot index) as [Heq|Hneq].
  - subst. exact E.
  - apply (IH (S index) Hnone). lia.
Qed.

Theorem first_empty_slot_sound sector found :
  first_empty_slot sector = Some found ->
  found < length sector / 8 /\
  physical_slot sector found = repeat 255%N 8 /\
  (forall earlier, earlier < found ->
     physical_slot sector earlier <> repeat 255%N 8).
Proof.
  intro Hfound.
  pose proof (first_empty_from_sound _ _ _ _ Hfound)
    as [Hrange [Hempty Hbefore]].
  split; [lia|]. split.
  - unfold empty_slot in Hempty.
    destruct (list_eq_dec N.eq_dec (physical_slot sector found)
      (repeat 255%N 8)); [exact e|discriminate].
  - intros earlier Hearlier Heq.
    specialize (Hbefore earlier ltac:(lia)).
    unfold empty_slot in Hbefore. rewrite Heq in Hbefore.
    destruct (list_eq_dec N.eq_dec (repeat 255%N 8)
      (repeat 255%N 8)); congruence.
Qed.

Theorem first_empty_slot_none sector :
  first_empty_slot sector = None ->
  forall index, index < length sector / 8 ->
    physical_slot sector index <> repeat 255%N 8.
Proof.
  intros Hnone index Hindex Heq.
  pose proof (first_empty_from_none _ _ _ Hnone index ltac:(lia))
    as Hnot.
  unfold empty_slot in Hnot. rewrite Heq in Hnot.
  destruct (list_eq_dec N.eq_dec (repeat 255%N 8)
    (repeat 255%N 8)); congruence.
Qed.

Lemma slot_fits_page size index :
  8 <= size -> size mod 8 = 0 ->
  (8 * index) mod size + 8 <= size.
Proof.
  intros Hsize Hmultiple.
  apply Nat.Div0.mod_divides in Hmultiple.
  destruct Hmultiple as [k Hsizek]. subst size.
  assert (Hk : k > 0) by lia.
  rewrite Nat.Div0.mul_mod_distr_l.
  pose proof (Nat.mod_upper_bound index k ltac:(lia)).
  lia.
Qed.

Lemma slot_fits_sector size sector index :
  8 <= size -> size mod 8 = 0 ->
  sector mod size = 0 ->
  index < sector / 8 ->
  8 * index + 8 <= sector /\
  (8 * index) mod size + 8 <= size.
Proof.
  intros Hsize Hpage8 Hsector Hindex.
  split; [|apply slot_fits_page; assumption].
  apply Nat.Div0.mod_divides in Hsector.
  destruct Hsector as [k Hsector].
  apply Nat.Div0.mod_divides in Hpage8.
  destruct Hpage8 as [j Hsizej].
  assert (Hsector8 : sector mod 8 = 0).
  { rewrite Hsector, Hsizej.
    replace (8 * j * k) with ((j*k)*8) by nia.
    apply Nat.Div0.mod_mul. }
  pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv.
  rewrite Hsector8 in Hdiv. nia.
Qed.
