From Coq Require Import List Arith NArith Lia Bool.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement JournalFlashBridge.
Import ListNotations.

(* The page buffer in journal.rs::write_entry: a mapped page copy with exactly
   one eight-byte slice replaced. This is constructed before FlashProgram. *)
Definition write_entry_page (f : flash) (page size within : nat)
    (entry : list byte) : payload :=
  map (fun i => if (within <=? i) && (i <? within + 8)
                then nth (i-within) entry 255%N else f (page+i))
      (seq 0 size).

(* [write_entry] tests the target eight-byte slice before borrowing a physical
   command. This is a caller condition, not a flash contract premise. *)
Definition erased_target f page within :=
  forall i, i < 8 -> f (page + within + i) = 255%N.

Lemma erased_target_of_slot f page within :
  flash_slot f (page+within) = repeat 255%N 8 ->
  erased_target f page within.
Proof.
  intros Hslot i Hi.
  pose proof (f_equal (fun xs => nth i xs 0%N) Hslot) as Hnth.
  cbn beta in Hnth.
  rewrite flash_slot_nth in Hnth by exact Hi.
  replace (page+within+i)%nat with ((page+within)+i)%nat by lia.
  rewrite (nth_indep (repeat 255%N 8) 0%N 255%N) in Hnth
    by (rewrite repeat_length; lia).
  rewrite nth_repeat in Hnth. exact Hnth.
Qed.

Lemma write_entry_page_byte f page size within entry i b :
  nth_error (write_entry_page f page size within entry) i = Some b ->
  i < size /\
  ((within <= i < within+8 /\ b = nth (i-within) entry 255%N) \/
   ((i < within \/ within+8 <= i) /\ b = f (page+i))).
Proof.
  intro Hnth. unfold write_entry_page in Hnth.
  rewrite nth_error_map, nth_error_seq in Hnth.
  destruct (i <? size) eqn:Hi; [|discriminate].
  apply Nat.ltb_lt in Hi. simpl in Hnth.
  destruct ((within <=? i) && (i <? within + 8)) eqn:Htarget.
  - inversion Hnth; subst b. split; [exact Hi|]. left.
    apply andb_true_iff in Htarget as [Hlow Hhigh].
    apply Nat.leb_le in Hlow. apply Nat.ltb_lt in Hhigh.
    split; [lia|reflexivity].
  - inversion Hnth; subst b. split; [exact Hi|]. right.
    apply andb_false_iff in Htarget.
    destruct Htarget as [Hlow|Hhigh].
    + apply Nat.leb_gt in Hlow. split; [lia|reflexivity].
    + apply Nat.ltb_ge in Hhigh. split; [lia|reflexivity].
Qed.

Lemma write_entry_page_valid f page size within entry :
  valid_flash f -> valid_payload entry ->
  length entry = 8 -> within + 8 <= size ->
  valid_payload (write_entry_page f page size within entry).
Proof.
  intros Hflash Hentry Hlen Hwithin.
  apply (proj2 (Forall_nth valid_byte _)).
  intros i d Hi.
  destruct (nth_error (write_entry_page f page size within entry) i)
    eqn:E.
  - rewrite (nth_error_nth _ _ _ E).
    pose proof (write_entry_page_byte _ _ _ _ _ _ _ E) as [_ [Htarget|Hother]].
    + destruct Htarget as [[Hlow Hhigh] Heq]. rewrite Heq.
      apply (proj1 (Forall_nth valid_byte entry) Hentry
        (i-within) 255%N). lia.
    + destruct Hother as [_ Heq]. rewrite Heq. apply Hflash.
  - apply nth_error_None in E. lia.
Qed.

Lemma write_entry_page_length f page size within entry :
  length (write_entry_page f page size within entry) = size.
Proof.
  unfold write_entry_page. rewrite length_map, length_seq. reflexivity.
Qed.

Theorem write_entry_page_request g f aligned size slot_start entry :
  page_size g = size ->
  aligned mod size = 0 -> FlashSpec.within g aligned size ->
  valid_flash f -> valid_payload entry -> length entry = 8 ->
  slot_start + 8 <= size -> erased_target f aligned slot_start ->
  program_request g f aligned
    (write_entry_page f aligned size slot_start entry).
Proof.
  intros Hsize Halign Harea Hflash Hentry Hlen Hslot Herased.
  unfold program_request. repeat split.
  - rewrite write_entry_page_length. symmetry. exact Hsize.
  - rewrite Hsize. exact Halign.
  - exact (proj1 Harea).
  - rewrite write_entry_page_length. exact (proj2 Harea).
  - apply write_entry_page_valid; assumption.
  - intros i b Hnth.
    pose proof (write_entry_page_byte _ _ _ _ _ _ _ Hnth)
      as [_ [Htarget|Hother]].
    + destruct Htarget as [[Hlow Hhigh] Hbyte].
      assert (Hbefore : f (aligned+i) = 255%N).
      { replace (aligned+i)%nat
          with (aligned+slot_start+(i-slot_start))%nat by lia.
        apply Herased. lia. }
      assert (Hb : valid_byte b).
      { apply (proj1 (Forall_forall valid_byte _)
          (write_entry_page_valid f aligned size slot_start entry
            Hflash Hentry Hlen Hslot) b).
        eapply nth_error_In; eauto. }
      unfold program_bits. rewrite Hbefore.
      rewrite N.land_comm.
      change 255%N with (N.ones 8). rewrite N.land_ones.
      apply N.mod_small. exact Hb.
    + destruct Hother as [_ Hbyte].
      unfold program_bits. rewrite Hbyte, N.land_diag. reflexivity.
Qed.

Corollary write_entry_code_request g f aligned size slot_start a :
  page_size g = size ->
  aligned mod size = 0 -> FlashSpec.within g aligned size ->
  valid_flash f -> slot_start + 8 <= size ->
  erased_target f aligned slot_start ->
  program_request g f aligned
    (write_entry_page f aligned size slot_start (code_bytes a)).
Proof.
  intros Hsize Halign Harea Hflash Hslot Herased.
  eapply write_entry_page_request; eauto.
  exact (code_bytes_valid a).
Qed.

Lemma write_entry_page_old_byte f page size within entry i :
  i < size -> (i < within \/ within + 8 <= i) ->
  nth_error (write_entry_page f page size within entry) i =
    Some (f (page+i)).
Proof.
  intros Hi Houtside. unfold write_entry_page.
  rewrite nth_error_map, nth_error_seq.
  apply Nat.ltb_lt in Hi. rewrite Hi. simpl.
  destruct Houtside as [Hleft|Hright].
  - apply Nat.leb_gt in Hleft. rewrite Hleft. reflexivity.
  - apply Nat.ltb_ge in Hright. rewrite Hright.
    rewrite andb_false_r. reflexivity.
Qed.

Lemma write_entry_page_target_byte f page size within entry i b :
  length entry = 8 -> within + 8 <= size ->
  nth_error entry i = Some b ->
  nth_error (write_entry_page f page size within entry) (within+i) = Some b.
Proof.
  intros Hlen Hwithin Hentry.
  assert (Hi : i < 8).
  { rewrite <- Hlen. apply (proj1 (nth_error_Some entry i)).
    congruence. }
  unfold write_entry_page. rewrite nth_error_map, nth_error_seq.
  assert (Hrange : within+i < size) by lia.
  apply Nat.ltb_lt in Hrange. rewrite Hrange. simpl.
  assert (Hlow : (within <=? within+i) = true)
    by (apply Nat.leb_le; lia).
  assert (Hhigh : (within+i <? within+8) = true)
    by (apply Nat.ltb_lt; lia).
  rewrite Hlow, Hhigh. simpl.
  replace (within+i-within)%nat with i by lia.
  f_equal. exact (nth_error_nth entry i 255%N Hentry).
Qed.

Theorem write_entry_page_target_slot f page size within entry :
  length entry = 8 -> within + 8 <= size ->
  requested_slot (write_entry_page f page size within entry) within = entry.
Proof.
  intros Hlen Hwithin.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold requested_slot.
    rewrite length_firstn, length_skipn, write_entry_page_length.
    lia.
  - intros i Hi.
    unfold requested_slot in Hi.
    rewrite length_firstn, length_skipn, write_entry_page_length in Hi.
    assert (Hi8 : i < 8) by lia.
    destruct (nth_error entry i) eqn:E.
    + pose proof (write_entry_page_target_byte f page size within entry
        i b Hlen Hwithin E) as Hbyte.
      destruct (requested_slot_nth (write_entry_page f page size within entry)
        within i ltac:(rewrite write_entry_page_length; exact Hwithin) Hi8)
        as [b' [Hdata Hslot]].
      rewrite Hbyte in Hdata. injection Hdata as Ebb.
      rewrite Hslot. rewrite (nth_error_nth entry i 0%N E).
      congruence.
    + apply nth_error_None in E. lia.
Qed.

Theorem write_entry_preserves_disjoint_slot g f f' page size within entry
    result offset :
  program_step g f page (write_entry_page f page size within entry) result f' ->
  offset + 8 <= size ->
  offset + 8 <= within \/ within + 8 <= offset ->
  flash_slot f' (page+offset) = flash_slot f (page+offset).
Proof.
  intros Hstep Hslot Hdisjoint.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    replace (page+offset+i)%nat with (page+(offset+i))%nat by lia.
    eapply identical_byte_preserved; [exact Hstep| |reflexivity].
    apply write_entry_page_old_byte; [lia|].
    destruct Hdisjoint as [Hbefore|Hafter]; [left|right]; lia.
Qed.

Theorem write_entry_preserves_other_page g f f' page size within entry
    result slot :
  program_step g f page (write_entry_page f page size within entry) result f' ->
  slot + 8 <= page \/ page + size <= slot ->
  flash_slot f' slot = flash_slot f slot.
Proof.
  intros Hstep Houtside.
  pose proof (program_locality _ _ _ _ _ _ Hstep) as Hframe.
  rewrite write_entry_page_length in Hframe.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    apply Hframe. destruct Houtside as [Hleft|Hright]; [left|right]; lia.
Qed.

Theorem write_entry_cannot_publish_other_address g f f' page size within
    result a b data_len logical_page :
  program_step g f page
    (write_entry_page f page size within (code_bytes a)) result f' ->
  within + 8 <= size -> u32 a ->
  decode_slot (flash_slot f' (page+within)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Ha Hdecode.
  eapply page_copy_cannot_retarget_any_outcome; eauto.
  - rewrite write_entry_page_length. exact Hwithin.
  - apply write_entry_page_target_slot; [apply code_bytes_length|].
    exact Hwithin.
Qed.
