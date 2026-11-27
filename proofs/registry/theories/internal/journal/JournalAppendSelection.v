From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalScan JournalIndex.
Import ListNotations.

(* A physical shape invariant, not a freshness assumption: an erased slot
   cannot occur before a later non-erased slot. Invalid partial entries before
   the first erased slot are permitted. *)
Definition erased_suffix (sector : list N) : Prop :=
  forall i j, i < j < length sector / 8 ->
    physical_slot sector i = repeat 255%N 8 ->
    physical_slot sector j = repeat 255%N 8.

Lemma all_erased_has_erased_suffix sector :
  (forall b, In b sector -> b = 255%N) -> erased_suffix sector.
Proof.
  intros Hall i j Hrange _.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold physical_slot.
    rewrite length_firstn, length_skipn, repeat_length.
    assert (8*j+8 <= length sector).
    { pose proof (Nat.div_mod (length sector) 8 ltac:(lia)) as Hdiv.
      lia. }
    lia.
  - intros k Hk.
    unfold physical_slot in Hk.
    rewrite length_firstn, length_skipn in Hk.
    assert (Hfit : 8*j+8 <= length sector).
    { pose proof (Nat.div_mod (length sector) 8 ltac:(lia)) as Hdiv.
      lia. }
    assert (Hk8 : k < 8) by lia.
    unfold physical_slot.
    rewrite (nth_indep (repeat 255%N 8) 0%N 255%N)
      by (rewrite repeat_length; exact Hk8).
    rewrite nth_repeat.
    rewrite nth_firstn by exact Hk8.
    assert (Hlt : (k <? 8) = true) by (apply Nat.ltb_lt; exact Hk8).
    rewrite Hlt.
    rewrite nth_skipn.
    apply Hall. apply nth_In. lia.
Qed.

Lemma first_empty_has_erased_tail sector index :
  erased_suffix sector -> first_empty_slot sector = Some index ->
  forall higher, index < higher < length sector / 8 ->
    physical_slot sector higher = repeat 255%N 8.
Proof.
  intros Hshape Hfirst higher Hrange.
  destruct (first_empty_slot_sound _ _ Hfirst) as [_ [Hempty _]].
  eapply Hshape; eauto.
Qed.

Lemma successful_page_write_preserves_outside_target_byte
    g f f' aligned size within entry p :
  program_step g f aligned (write_entry_page f aligned size within entry)
    Success f' ->
  (p < aligned + within \/ aligned + within + 8 <= p) ->
  f' p = f p.
Proof.
  intros Hstep Houtside.
  destruct (Nat.lt_ge_cases p aligned) as [Hleft|Hfrom].
  - apply (program_locality _ _ _ _ _ _ Hstep).
    left. exact Hleft.
  - destruct (Nat.lt_ge_cases p (aligned + size)) as [Hinside|Hright].
    + assert (Hi : p-aligned < size) by lia.
      pose proof (write_entry_page_old_byte f aligned size within entry
        (p-aligned) Hi) as Hbyte.
      assert (Hdisjoint : p-aligned < within \/ within+8 <= p-aligned)
        by lia.
      specialize (Hbyte Hdisjoint).
      unfold programmed in *.
      replace p with (aligned+(p-aligned)) by lia.
      rewrite (program_success_contents _ _ _ _ _ Hstep _ _ Hbyte).
      reflexivity.
    + apply (program_locality _ _ _ _ _ _ Hstep).
      right. rewrite write_entry_page_length. exact Hright.
Qed.

Lemma page_write_preserves_outside_target_byte_any
    g f f' aligned size within entry result p :
  program_step g f aligned (write_entry_page f aligned size within entry)
    result f' ->
  (p < aligned + within \/ aligned + within + 8 <= p) ->
  f' p = f p.
Proof.
  intros Hstep Houtside.
  destruct (Nat.lt_ge_cases p aligned) as [Hleft|Hfrom].
  - apply (program_locality _ _ _ _ _ _ Hstep).
    left. exact Hleft.
  - destruct (Nat.lt_ge_cases p (aligned + size)) as [Hinside|Hright].
    + assert (Hi : p-aligned < size) by lia.
      pose proof (write_entry_page_old_byte f aligned size within entry
        (p-aligned) Hi) as Hbyte.
      assert (Hdisjoint : p-aligned < within \/ within+8 <= p-aligned)
        by lia.
      specialize (Hbyte Hdisjoint).
      replace p with (aligned+(p-aligned)) by lia.
      eapply identical_byte_preserved; [exact Hstep|exact Hbyte|reflexivity].
    + apply (program_locality _ _ _ _ _ _ Hstep).
      right. rewrite write_entry_page_length. exact Hright.
Qed.

Lemma page_write_preserves_other_slot_any
    g f f' aligned size within entry target other result :
  aligned + within = 8 * target -> other <> target ->
  program_step g f aligned (write_entry_page f aligned size within entry)
    result f' ->
  flash_slot f' (8*other) = flash_slot f (8*other).
Proof.
  intros Haddr Hother Hstep.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    eapply page_write_preserves_outside_target_byte_any;
      [exact Hstep|].
    destruct (Nat.lt_ge_cases other target); [left|right]; lia.
Qed.

Lemma aligned_page_stays_in_primary addr sector page aligned :
  0 < page -> sector mod page = 0 -> addr < sector ->
  aligned = addr / page * page -> aligned + page <= sector.
Proof.
  intros Hpage Hsector Haddr Haligned.
  pose proof (Nat.div_mod sector page ltac:(lia)) as Hs.
  pose proof (Nat.div_mod addr page ltac:(lia)) as Ha.
  pose proof (Nat.mod_upper_bound addr page ltac:(lia)) as Hrem.
  assert (Hquot : addr / page < sector / page).
  { apply Nat.Div0.div_lt_upper_bound. nia. }
  nia.
Qed.

Theorem primary_page_write_preserves_clean_secondary
    g f f' sector page aligned within d result :
  aligned + page <= sector ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) result f' ->
  (forall i, i < sector -> f (sector+i) = 255%N) ->
  forall i, i < sector -> f' (sector+i) = 255%N.
Proof.
  intros Hbound Hstep Hclean i Hi.
  rewrite (program_locality _ _ _ _ _ _ Hstep (sector+i)).
  - exact (Hclean i Hi).
  - right. rewrite write_entry_page_length. lia.
Qed.

Lemma successful_page_write_preserves_higher_slot
    g f f' aligned size within entry target higher :
  aligned + within = 8 * target ->
  target < higher ->
  program_step g f aligned (write_entry_page f aligned size within entry)
    Success f' ->
  flash_slot f' (8*higher) = flash_slot f (8*higher).
Proof.
  intros Haddr Hhigher Hstep.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    eapply successful_page_write_preserves_outside_target_byte;
      [exact Hstep|].
    right. lia.
Qed.

Lemma successful_page_write_preserves_other_slot
    g f f' aligned size within entry target other :
  aligned + within = 8 * target ->
  other <> target ->
  program_step g f aligned (write_entry_page f aligned size within entry)
    Success f' ->
  flash_slot f' (8*other) = flash_slot f (8*other).
Proof.
  intros Haddr Hother Hstep.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    eapply successful_page_write_preserves_outside_target_byte;
      [exact Hstep|].
    destruct (Nat.lt_ge_cases other target); [left|right]; lia.
Qed.

Lemma code_bytes_not_erased d data_len page :
  u32 d -> (page <= d < data_len)%N ->
  (d mod page = 0)%N ->
  code_bytes d <> repeat 255%N 8.
Proof.
  intros Hd Hrange Halign Heq.
  pose proof (decode_code_bytes d data_len page Hd Hrange Halign) as Hdecode.
  rewrite Heq, erased_slot_invalid in Hdecode. discriminate.
Qed.

(* This is the normal no-rotation [append] branch, including the actual
   copied-page program. Selection of D is a conclusion. The erased-suffix
   premise is an invariant still to be established for all reachable states. *)
Theorem successful_nonrotation_append_selects
    g f f' sector page index aligned within d data_len boss_ok :
  sector mod 8 = 0 -> 8 <= page ->
  aligned + within = 8*index -> within + 8 <= page ->
  first_empty_slot (sector_bytes f 0 sector) = Some index ->
  erased_suffix (sector_bytes f 0 sector) ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) Success f' ->
  u32 d ->
  (N.of_nat page <= d < data_len)%N ->
  (d mod N.of_nat page = 0)%N ->
  boss_ok d = true ->
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f' 0 sector) = Some (index, d).
Proof.
  intros Hsector8 Hpage Haddr Hwithin Hfirst Hshape Hstep
    Hd Hrange Halign Hboss.
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hindex [Hempty _]].
  assert (Hcount : length (sector_bytes f 0 sector) / 8 = sector / 8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  rewrite Hcount in Hindex.
  assert (Htarget : physical_slot (sector_bytes f' 0 sector) index =
      code_bytes d).
  { assert (Hfit : 8*index+8 <= sector).
    { pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv. lia. }
    rewrite (physical_slot_of_flash _ _ _ _ Hfit).
    replace (0+8*index) with (aligned+within) by lia.
    assert (Hpayloadfit : within + 8 <=
      length (write_entry_page f aligned page within (code_bytes d)))
      by (rewrite write_entry_page_length; exact Hwithin).
    rewrite (success_program_slot_exact _ _ _ _ _ _ Hstep Hpayloadfit).
    apply write_entry_page_target_slot; [apply code_bytes_length|exact Hwithin]. }
  apply complete_slot_physically_published; try assumption.
  - unfold sector_bytes. rewrite length_map, length_seq. exact Hindex.
  - intros higher Hhigher.
    assert (Hfit : 8*higher+8 <= sector).
    { unfold sector_bytes in Hhigher.
      rewrite length_map, length_seq in Hhigher.
      pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv. lia. }
    unfold checked_slot.
    rewrite (physical_slot_of_flash _ _ _ _ Hfit).
    replace (0+8*higher) with (8*higher) by lia.
    rewrite (successful_page_write_preserves_higher_slot _ _ _ _ _ _ _ _ _
      Haddr (proj1 Hhigher) Hstep).
    replace (8*higher) with (0+8*higher) by lia.
    rewrite <- (physical_slot_of_flash f 0 sector higher Hfit).
    rewrite (first_empty_has_erased_tail _ _ Hshape Hfirst higher).
    + rewrite erased_slot_invalid. reflexivity.
    + unfold sector_bytes in Hhigher.
      rewrite length_map, length_seq in Hhigher.
      rewrite Hcount. exact Hhigher.
Qed.

(* The physical suffix shape is preserved by a successful append. Partial
   slots before the chosen FF position are allowed; no constraint is placed
   on their validator outcome. *)
Theorem successful_nonrotation_preserves_erased_suffix
    g f f' sector page index aligned within d data_len :
  sector mod 8 = 0 ->
  aligned + within = 8*index -> within + 8 <= page ->
  first_empty_slot (sector_bytes f 0 sector) = Some index ->
  erased_suffix (sector_bytes f 0 sector) ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) Success f' ->
  u32 d -> (N.of_nat page <= d < data_len)%N ->
  (d mod N.of_nat page = 0)%N ->
  erased_suffix (sector_bytes f' 0 sector).
Proof.
  intros Hsector8 Haddr Hwithin Hfirst Hshape Hstep Hd Hrange Halign.
  destruct (first_empty_slot_sound _ _ Hfirst)
    as [Hindex [Hempty Hbefore]].
  unfold erased_suffix in *. intros x y Hxy Hx.
  assert (Hcount : length (sector_bytes f 0 sector) / 8 = sector / 8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  assert (Hcount' : length (sector_bytes f' 0 sector) / 8 = sector / 8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  rewrite Hcount' in Hxy.
  assert (Hfit : forall j, j < sector / 8 -> 8*j+8 <= sector).
  { intros j Hj. pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv.
    lia. }
  assert (Hother : forall j, j < sector / 8 -> j <> index ->
    physical_slot (sector_bytes f' 0 sector) j =
    physical_slot (sector_bytes f 0 sector) j).
  { intros j Hj Hne.
    rewrite !physical_slot_of_flash by (apply Hfit; exact Hj).
    replace (0+8*j) with (8*j) by lia.
    eapply successful_page_write_preserves_other_slot; eauto. }
  destruct (Nat.lt_trichotomy x index) as [Hbeforex|[Heqx|Hafterx]].
  - rewrite (Hother x ltac:(lia) ltac:(lia)) in Hx.
    exact (False_rect _ (Hbefore x Hbeforex Hx)).
  - subst x.
    assert (Htarget : physical_slot (sector_bytes f' 0 sector) index =
      code_bytes d).
    { rewrite (physical_slot_of_flash _ _ _ _ (Hfit index ltac:(lia))).
      replace (0+8*index) with (aligned+within) by lia.
      assert (Hpayloadfit : within + 8 <=
        length (write_entry_page f aligned page within (code_bytes d)))
        by (rewrite write_entry_page_length; exact Hwithin).
      rewrite (success_program_slot_exact _ _ _ _ _ _ Hstep Hpayloadfit).
      apply write_entry_page_target_slot;
        [apply code_bytes_length|exact Hwithin]. }
    rewrite Htarget in Hx.
    exfalso. eapply code_bytes_not_erased; eauto.
  - rewrite (Hother x ltac:(lia) ltac:(lia)) in Hx.
    rewrite (Hother y ltac:(lia) ltac:(lia)).
    eapply Hshape; [rewrite Hcount; exact Hxy|exact Hx].
Qed.

(* Returned errors and resets may leave the target slot erased or partial.
   Neither outcome can change any other slot, so the empty-tail shape remains
   true. This is a physical fact; an error still freezes the caller. *)
Theorem any_outcome_nonrotation_preserves_erased_suffix
    g f f' sector page index aligned within d result :
  sector mod 8 = 0 ->
  aligned + within = 8*index -> within + 8 <= page ->
  first_empty_slot (sector_bytes f 0 sector) = Some index ->
  erased_suffix (sector_bytes f 0 sector) ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) result f' ->
  erased_suffix (sector_bytes f' 0 sector).
Proof.
  intros Hsector8 Haddr Hwithin Hfirst Hshape Hstep.
  destruct (first_empty_slot_sound _ _ Hfirst)
    as [Hindex [Hempty Hbefore]].
  unfold erased_suffix in *. intros x y Hxy Hx.
  assert (Hcount : length (sector_bytes f 0 sector) / 8 = sector / 8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  assert (Hcount' : length (sector_bytes f' 0 sector) / 8 = sector / 8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  rewrite Hcount' in Hxy.
  assert (Hfit : forall j, j < sector / 8 -> 8*j+8 <= sector).
  { intros j Hj. pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv.
    lia. }
  assert (Hother : forall j, j < sector / 8 -> j <> index ->
    physical_slot (sector_bytes f' 0 sector) j =
    physical_slot (sector_bytes f 0 sector) j).
  { intros j Hj Hne.
    rewrite !physical_slot_of_flash by (apply Hfit; exact Hj).
    replace (0+8*j) with (8*j) by lia.
    eapply page_write_preserves_other_slot_any; eauto. }
  destruct (Nat.lt_trichotomy x index) as [Hbeforex|[Heqx|Hafterx]].
  - rewrite (Hother x ltac:(lia) ltac:(lia)) in Hx.
    exact (False_rect _ (Hbefore x Hbeforex Hx)).
  - subst x. rewrite (Hother y ltac:(lia) ltac:(lia)).
    eapply Hshape; [rewrite Hcount; exact Hxy|exact Hempty].
  - rewrite (Hother x ltac:(lia) ltac:(lia)) in Hx.
    rewrite (Hother y ltac:(lia) ltac:(lia)).
    eapply Hshape; [rewrite Hcount; exact Hxy|exact Hx].
Qed.

Lemma erased_primary_slot f sector j :
  erased f 0 sector -> 8*j+8 <= sector ->
  flash_slot f (8*j) = repeat 255%N 8.
Proof.
  intros Herased Hfit.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. rewrite length_map, length_seq, repeat_length.
    reflexivity.
  - intros k Hk. unfold flash_slot in Hk.
    rewrite length_map, length_seq in Hk.
    rewrite flash_slot_nth by exact Hk.
    rewrite (nth_indep (repeat 255%N 8) 0%N 255%N)
      by (rewrite repeat_length; exact Hk).
    rewrite nth_repeat.
    replace (8*j+k) with (0+(8*j+k)) by lia.
    apply Herased. lia.
Qed.

Lemma secondary_erase_preserves_primary_slot g f f' sector j result :
  erase_step g f sector result f' -> 8*j+8 <= sector ->
  flash_slot f' (8*j) = flash_slot f (8*j).
Proof.
  intros Hstep Hfit.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros k Hk. unfold flash_slot in Hk.
    rewrite length_map, length_seq in Hk.
    rewrite !flash_slot_nth by exact Hk.
    apply (erase_locality _ _ _ _ _ Hstep).
    left. lia.
Qed.

Lemma first_empty_after_single_entry f sector a data_len page :
  16 <= sector -> sector mod 8 = 0 ->
  flash_slot f 0 = code_bytes a ->
  u32 a -> (page <= a < data_len)%N -> (a mod page = 0)%N ->
  (forall j, 0 < j < sector / 8 ->
     flash_slot f (8*j) = repeat 255%N 8) ->
  first_empty_slot (sector_bytes f 0 sector) = Some 1 /\
  erased_suffix (sector_bytes f 0 sector).
Proof.
  intros Hsector Hsector8 Hzero Ha Hrange Halign Htail.
  assert (Hcount2 : 2 <= sector/8).
  { pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv. lia. }
  assert (Hfit : forall j, j < sector/8 -> 8*j+8 <= sector).
  { intros j Hj. pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv.
    lia. }
  assert (Hslot : forall j, j < sector/8 ->
      physical_slot (sector_bytes f 0 sector) j = flash_slot f (8*j)).
  { intros j Hj. rewrite (physical_slot_of_flash _ _ _ _ (Hfit j Hj)).
    reflexivity. }
  assert (Hlen : length (sector_bytes f 0 sector) / 8 = sector/8).
  { unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  assert (Hnot : empty_slot (sector_bytes f 0 sector) 0 = false).
  { unfold empty_slot. rewrite (Hslot 0 ltac:(lia)).
    replace (8*0) with 0 by lia. rewrite Hzero.
    destruct (list_eq_dec N.eq_dec (code_bytes a) (repeat 255%N 8))
      as [Heq|Hne].
    - exfalso. eapply code_bytes_not_erased; eauto.
    - reflexivity. }
  assert (Hone : empty_slot (sector_bytes f 0 sector) 1 = true).
  { unfold empty_slot. rewrite (Hslot 1 ltac:(lia)).
    rewrite (Htail 1 ltac:(lia)).
    destruct (list_eq_dec N.eq_dec (repeat 255%N 8)
      (repeat 255%N 8)); [reflexivity|contradiction]. }
  split.
  - unfold first_empty_slot. rewrite Hlen.
    replace (sector/8) with (S (S (sector/8-2))) by lia.
    simpl. rewrite Hnot, Hone. reflexivity.
  - unfold erased_suffix. intros i j Hrangeij _.
    rewrite (Hslot j ltac:(rewrite Hlen in Hrangeij; lia)).
    apply Htail. rewrite Hlen in Hrangeij. lia.
Qed.

(* The successful physical suffix of Rust's full-sector rotation. The prior
   [latest] and copy-to-secondary calls choose/protect A; they do not affect
   the slot-order argument here. Their refinement and error cases remain in
   the enclosing recovery machine. *)
Theorem successful_rotation_suffix_selects_D
    g f0 f1 f2 f3 f4 sector page a d data_len boss_ok :
  sector_size g = sector -> sector mod 8 = 0 ->
  16 <= page <= sector -> 16 <= sector ->
  erase_step g f0 0 Success f1 ->
  program_step g f1 0
    (write_entry_page f1 0 page 0 (code_bytes a)) Success f2 ->
  erase_step g f2 sector Success f3 ->
  program_step g f3 0
    (write_entry_page f3 0 page 8 (code_bytes d)) Success f4 ->
  u32 a -> (N.of_nat page <= a < data_len)%N ->
  (a mod N.of_nat page = 0)%N ->
  u32 d -> (N.of_nat page <= d < data_len)%N ->
  (d mod N.of_nat page = 0)%N -> boss_ok d = true ->
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f4 0 sector) = Some (1,d).
Proof.
  intros Hsector Hsector8 Hpage Hsize Herase Hrestore Hclear Happend
    Ha Harange Haalign Hd Hdrange Hdalign Hboss.
  pose proof (erase_success_contents _ _ _ _ Herase) as Herased.
  rewrite Hsector in Herased.
  assert (Hslot0 : flash_slot f3 0 = code_bytes a).
  { change (flash_slot f3 (8*0) = code_bytes a).
    rewrite (secondary_erase_preserves_primary_slot _ _ _ _ 0 _ Hclear
      ltac:(lia)).
    assert (Hfit : 0+8 <= length
      (write_entry_page f1 0 page 0 (code_bytes a)))
      by (rewrite write_entry_page_length; lia).
    pose proof (success_program_slot_exact _ _ _ _ _ 0 Hrestore Hfit)
      as Hslot.
    rewrite Nat.add_0_r in Hslot.
    change (flash_slot f2 0 = code_bytes a). rewrite Hslot.
    apply write_entry_page_target_slot;
      [apply code_bytes_length|lia]. }
  assert (Htail : forall j, 0 < j < sector/8 ->
    flash_slot f3 (8*j) = repeat 255%N 8).
  { intros j Hj.
    assert (Hfit : 8*j+8 <= sector).
    { pose proof (Nat.div_mod sector 8 ltac:(lia)) as Hdiv. lia. }
    rewrite (secondary_erase_preserves_primary_slot _ _ _ _ j _
      Hclear Hfit).
    rewrite (page_write_preserves_other_slot_any g f1 f2 0 page 0
      (code_bytes a) 0 j Success ltac:(lia) ltac:(lia) Hrestore).
    eapply erased_primary_slot; eauto. }
  destruct (first_empty_after_single_entry f3 sector a data_len
    (N.of_nat page) Hsize Hsector8 Hslot0 Ha Harange Haalign Htail)
    as [Hfirst Hshape].
  eapply (successful_nonrotation_append_selects g f3 f4 sector page 1
    0 8 d data_len boss_ok); eauto; lia.
Qed.

Theorem successful_rotation_suffix_cleans_secondary
    g f2 f3 f4 sector page d :
  sector_size g = sector -> page <= sector ->
  erase_step g f2 sector Success f3 ->
  program_step g f3 0
    (write_entry_page f3 0 page 8 (code_bytes d)) Success f4 ->
  forall i, i < sector -> f4 (sector+i) = 255%N.
Proof.
  intros Hsector Hpage Hclear Happend i Hi.
  pose proof (erase_success_contents _ _ _ _ Hclear) as Herased.
  rewrite Hsector in Herased.
  rewrite (program_locality _ _ _ _ _ _ Happend (sector+i)).
  - exact (Herased i Hi).
  - right. rewrite write_entry_page_length. lia.
Qed.

(* Publication history records physical completions. It permits the same BOSS
   address more than once, and does not identify completion with caller
   acknowledgement. This fragment covers successful no-rotation appends;
   rotation, error and reset transitions are added at the enclosing registry
   level. *)
Record append_state := AppendState {
  append_image : flash;
  physical_publications : list N
}.

Definition erased_journal_flash : flash := fun _ => 255%N.

Section RepeatedNonrotation.
Variable g : geometry.
Variable sector page : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hsector8 : sector mod 8 = 0.
Hypothesis Hpage : 8 <= page.

Inductive successful_append_step : append_state -> append_state -> Prop :=
| append_into_first_ff s after index aligned within d :
    aligned + within = 8*index -> within + 8 <= page ->
    first_empty_slot (sector_bytes (append_image s) 0 sector) = Some index ->
    program_step g (append_image s) aligned
      (write_entry_page (append_image s) aligned page within (code_bytes d))
      Success after ->
    u32 d -> (N.of_nat page <= d < data_len)%N ->
    (d mod N.of_nat page = 0)%N -> boss_ok d = true ->
    successful_append_step s
      (AppendState after (d :: physical_publications s)).

Definition append_shape (s : append_state) :=
  erased_suffix (sector_bytes (append_image s) 0 sector).

Definition newest_selected (s : append_state) :=
  match physical_publications s with
  | [] => True
  | d :: _ => exists index,
      latest_in_model boss_ok data_len (N.of_nat page)
        (sector_bytes (append_image s) 0 sector) = Some (index, d)
  end.

Theorem successful_append_preserves_shape_and_selects s s' :
  append_shape s -> successful_append_step s s' ->
  append_shape s' /\ newest_selected s'.
Proof.
  intros Hshape Hstep. inversion Hstep; subst.
  unfold append_shape, newest_selected in *.
  cbn [append_image physical_publications].
  split.
  - eapply (successful_nonrotation_preserves_erased_suffix
      g (append_image s) after sector page index aligned within d data_len);
      eauto.
  - exists index.
    eapply (successful_nonrotation_append_selects
      g (append_image s) after sector page index aligned within d data_len
      boss_ok); eauto.
Qed.

Theorem finite_successful_appends_select_newest s s' :
  append_shape s -> newest_selected s ->
  clos_refl_trans append_state successful_append_step s s' ->
  append_shape s' /\ newest_selected s'.
Proof.
  intros Hshape Hnew Htrace.
  revert Hshape Hnew.
  induction Htrace.
  - intros Hshape Hnew.
    destruct (successful_append_preserves_shape_and_selects _ _ Hshape H)
      as [Hshape' Hselected]. split; assumption.
  - intros Hshape Hnew. split; assumption.
  - intros Hshape Hnew.
    destruct (IHHtrace1 Hshape Hnew) as [Hmid Hmidnew].
    exact (IHHtrace2 Hmid Hmidnew).
Qed.

Corollary finite_successful_appends_from_erased_select_newest s' :
  clos_refl_trans append_state successful_append_step
    (AppendState erased_journal_flash []) s' ->
  append_shape s' /\ newest_selected s'.
Proof.
  intro Htrace.
  eapply (finite_successful_appends_select_newest
    (AppendState erased_journal_flash []) s');
    [|simpl; exact I|exact Htrace].
  unfold append_shape. apply all_erased_has_erased_suffix.
  intros b Hb. unfold sector_bytes, erased_journal_flash in Hb.
  apply in_map_iff in Hb. destruct Hb as [i [Heq _]].
  symmetry. exact Heq.
Qed.
End RepeatedNonrotation.
