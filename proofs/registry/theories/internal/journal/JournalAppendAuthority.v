From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalScan JournalIndex JournalAppendSelection.
Import ListNotations.

Lemma latest_scan_ext boss_ok data_len page before after count :
  (forall i, i < count ->
    checked_slot boss_ok data_len page after i =
    checked_slot boss_ok data_len page before i) ->
  latest_scan boss_ok data_len page after count =
    latest_scan boss_ok data_len page before count.
Proof.
  induction count as [|n IH]; intro Hsame; [reflexivity|].
  simpl. rewrite (Hsame n ltac:(lia)).
  destruct (checked_slot boss_ok data_len page before n); [reflexivity|].
  apply IH. intros i Hi. apply Hsame. lia.
Qed.

(* The event is local completion of the candidate slot, independent of the
   return code and of the observer's acknowledgement. *)
Definition candidate_completed (f : flash) (index : nat) (d : N) : bool :=
  if list_eq_dec N.eq_dec (flash_slot f (8*index)) (code_bytes d)
  then true else false.
Definition authority_after_candidate before after index d :=
  if candidate_completed after index d then Some d else before.

Lemma erased_candidate_not_completed f index d data_len page :
  flash_slot f (8*index) = repeat 255%N 8 ->
  u32 d -> (page <= d < data_len)%N -> (d mod page = 0)%N ->
  candidate_completed f index d = false.
Proof.
  intros Hff Hu Hr Hal. unfold candidate_completed. rewrite Hff.
  destruct (list_eq_dec N.eq_dec (repeat 255%N 8) (code_bytes d));
    [|reflexivity].
  exfalso. apply (code_bytes_not_erased d data_len page Hu Hr Hal).
  symmetry. exact e.
Qed.

Lemma successful_candidate_completed g f f' aligned page within index d :
  aligned+within = 8*index -> within+8 <= page ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) Success f' ->
  candidate_completed f' index d = true.
Proof.
  intros Haddr Hfit Hstep. unfold candidate_completed.
  assert (Hcode : flash_slot f' (8*index) = code_bytes d).
  { rewrite <- Haddr.
    rewrite (success_program_slot_exact _ _ _ _ _ within Hstep)
      by (rewrite write_entry_page_length; exact Hfit).
    apply write_entry_page_target_slot; [apply code_bytes_length|exact Hfit]. }
  rewrite Hcode. destruct (list_eq_dec N.eq_dec (code_bytes d) (code_bytes d));
    [reflexivity|contradiction].
Qed.

Theorem any_candidate_outcome_updates_authority
    g f f' sector page index aligned within d data_len boss_ok result :
  sector mod 8 = 0 -> aligned+within = 8*index -> within+8 <= page ->
  first_empty_slot (sector_bytes f 0 sector) = Some index ->
  erased_suffix (sector_bytes f 0 sector) ->
  program_step g f aligned
    (write_entry_page f aligned page within (code_bytes d)) result f' ->
  u32 d -> (N.of_nat page <= d < data_len)%N ->
  (d mod N.of_nat page = 0)%N -> boss_ok d = true ->
  option_map snd (latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f' 0 sector)) =
  authority_after_candidate
    (option_map snd (latest_in_model boss_ok data_len (N.of_nat page)
      (sector_bytes f 0 sector))) f' index d.
Proof.
  intros Hsector8 Haddr Hwithin Hfirst Hshape Hstep Hu Hr Hal Hb.
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hi [Hempty Hbefore]].
  assert (Hlen : forall image, length (sector_bytes image 0 sector) = sector).
  { intro image. unfold sector_bytes. rewrite length_map, length_seq. reflexivity. }
  rewrite Hlen in Hi.
  assert (Hfit : forall j, j < sector/8 -> 8*j+8 <= sector).
  { intros j Hj. pose proof (Nat.div_mod sector 8 ltac:(lia)). lia. }
  assert (Hslot : forall image j, j < sector/8 ->
    physical_slot (sector_bytes image 0 sector) j = flash_slot image (8*j)).
  { intros image j Hj. rewrite physical_slot_of_flash by (apply Hfit; exact Hj).
    reflexivity. }
  assert (Hother : forall j, j < sector/8 -> j <> index ->
    checked_slot boss_ok data_len (N.of_nat page) (sector_bytes f' 0 sector) j =
    checked_slot boss_ok data_len (N.of_nat page) (sector_bytes f 0 sector) j).
  { intros j Hj Hne. unfold checked_slot. rewrite !Hslot by exact Hj.
    rewrite (page_write_preserves_other_slot_any _ _ _ _ _ _ _ _ _ _
      Haddr Hne Hstep). reflexivity. }
  assert (Htail : forall j, index < j < sector/8 ->
    checked_slot boss_ok data_len (N.of_nat page) (sector_bytes f' 0 sector) j = None).
  { intros j Hj. rewrite Hother by lia. unfold checked_slot.
    rewrite (first_empty_has_erased_tail _ _ Hshape Hfirst j)
      by (rewrite Hlen; exact Hj).
    rewrite erased_slot_invalid. reflexivity. }
  unfold authority_after_candidate, candidate_completed.
  destruct (list_eq_dec N.eq_dec (flash_slot f' (8*index)) (code_bytes d))
    as [Hcomplete|Hincomplete].
  - assert (Hscan : latest_in_model boss_ok data_len (N.of_nat page)
      (sector_bytes f' 0 sector) = Some (index,d)).
    { apply complete_slot_physically_published; try assumption.
      - rewrite Hlen. exact Hi.
      - rewrite Hslot by exact Hi. exact Hcomplete.
      - intros higher Hhigher. apply Htail. rewrite Hlen in Hhigher. exact Hhigher. }
    rewrite Hscan. reflexivity.
  - assert (Hnone : checked_slot boss_ok data_len (N.of_nat page)
      (sector_bytes f' 0 sector) index = None).
    { unfold checked_slot. rewrite Hslot by exact Hi.
      destruct (decode_slot (flash_slot f' (8*index)) data_len (N.of_nat page))
        as [found|] eqn:Hdecode; [|reflexivity].
      assert (Hrequested : slot_byte_subset (code_bytes d) (flash_slot f' (8*index))).
      { pose proof (program_slot_requested_only_any_outcome g f aligned
          (write_entry_page f aligned page within (code_bytes d)) result f'
          within Hstep ltac:(rewrite write_entry_page_length; exact Hwithin)) as Hp.
        rewrite Haddr in Hp.
        rewrite (write_entry_page_target_slot f aligned page within (code_bytes d)
          (code_bytes_length d) Hwithin) in Hp. exact Hp. }
      assert (Hfound : found = d).
      { destruct (decode_slot_sound _ _ _ _ Hdecode) as [Hfu [_ [_ Hcode]]].
        symmetry. apply (distinct_byte_codes_incomparable d found Hu Hfu).
        rewrite Hcode. exact Hrequested. }
      subst found. destruct (decode_slot_sound _ _ _ _ Hdecode) as [_ [_ [_ Heq]]].
      exfalso. apply Hincomplete. symmetry. exact Heq. }
    unfold latest_in_model. rewrite !Hlen.
    rewrite (latest_scan_ext boss_ok data_len (N.of_nat page)
      (sector_bytes f 0 sector) (sector_bytes f' 0 sector) (sector/8));
      [reflexivity|].
    intros j Hj. destruct (Nat.eq_dec j index) as [Heq|Hne].
    + subst j. rewrite Hnone. unfold checked_slot. rewrite Hempty.
      rewrite erased_slot_invalid. reflexivity.
    + apply Hother; assumption.
Qed.
