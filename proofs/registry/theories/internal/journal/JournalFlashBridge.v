From Coq Require Import List Arith Lia NArith.
From OxideSE.Registry Require Import Types FlashSpec JournalComplement.
Import ListNotations.

(* Extract the eight physical bytes of one slot. This is a pure observation
   of FlashSpec's address-to-byte witness, not an atomic slot operation. *)
Definition flash_slot (f : flash) (address : nat) : list byte :=
  map f (seq address 8).
Definition requested_slot (data : payload) (offset : nat) : list byte :=
  firstn 8 (skipn offset data).

Lemma flash_slot_nth f address i :
  i < 8 -> nth i (flash_slot f address) 0%N = f (address+i).
Proof.
  intro Hi. apply nth_error_nth with (x:=f (address+i)).
  unfold flash_slot. rewrite nth_error_map, nth_error_seq.
  apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
Qed.

Theorem erase_preserves_outside_slot g f sector result f' slot :
  erase_step g f sector result f' ->
  slot + 8 <= sector \/ sector + sector_size g <= slot ->
  flash_slot f' slot = flash_slot f slot.
Proof.
  intros Hstep Houtside.
  pose proof (erase_locality _ _ _ _ _ Hstep) as Hframe.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    rewrite !flash_slot_nth by exact Hi.
    apply Hframe. destruct Houtside as [Hleft|Hright]; [left|right]; lia.
Qed.

Lemma requested_slot_nth data offset i :
  offset + 8 <= length data -> i < 8 ->
  exists b, nth_error data (offset+i) = Some b /\
    nth i (requested_slot data offset) 0%N = b.
Proof.
  intros Hwithin Hi.
  assert (Hbound : offset+i < length data) by lia.
  pose proof (nth_error_nth' data (n:=offset+i) 0%N Hbound) as Hdata.
  exists (nth (offset+i) data 0%N). split; [exact Hdata|].
  apply nth_error_nth with (x:=nth (offset+i) data 0%N).
  unfold requested_slot.
  rewrite nth_error_firstn, nth_error_skipn.
  apply Nat.ltb_lt in Hi. rewrite Hi. exact Hdata.
Qed.

Theorem page_rewrite_preserves_copied_slot g f page data result f' offset :
  program_step g f page data result f' ->
  offset + 8 <= length data ->
  requested_slot data offset = flash_slot f (page+offset) ->
  flash_slot f' (page+offset) = flash_slot f (page+offset).
Proof.
  intros Hstep Hwithin Hcopy.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot. repeat rewrite length_map, length_seq. reflexivity.
  - intros i Hi. unfold flash_slot in Hi.
    rewrite length_map, length_seq in Hi.
    destruct (requested_slot_nth data offset i Hwithin Hi)
      as [b [Hdata Hrequested]].
    rewrite Hcopy in Hrequested.
    rewrite flash_slot_nth in Hrequested by exact Hi.
    rewrite !flash_slot_nth by exact Hi.
    replace (page+offset+i)%nat with (page+(offset+i))%nat by lia.
    replace (page+offset+i)%nat with (page+(offset+i))%nat in Hrequested
      by lia.
    rewrite Hrequested.
    eapply identical_byte_preserved; eauto.
Qed.

Theorem interrupted_program_slot_requested_only g f page data f' offset :
  program_step g f page data Reset f' ->
  offset + 8 <= length data ->
  slot_byte_subset (requested_slot data offset)
                   (flash_slot f' (page+offset)).
Proof.
  intros Hstep Hwithin i Hi.
  assert (Hnat : N.to_nat i < 8) by lia.
  destruct (requested_slot_nth data offset (N.to_nat i) Hwithin Hnat)
    as [b [Hdata Hslot]].
  unfold word_subset.
  rewrite flash_slot_nth by exact Hnat.
  replace (page + offset + N.to_nat i)%nat
    with (page + (offset + N.to_nat i))%nat by lia.
  pose proof (interrupted_program_requested_only _ _ _ _ _ Hstep)
    as Hrequested.
  specialize (Hrequested (offset+N.to_nat i) b Hdata).
  unfold program_bits in Hrequested.
  rewrite <- Hslot in Hrequested.
  rewrite N.land_comm. exact Hrequested.
Qed.

Theorem failed_program_slot_requested_only g f page data f' offset :
  program_step g f page data VerifyFailed f' ->
  offset + 8 <= length data ->
  slot_byte_subset (requested_slot data offset)
                   (flash_slot f' (page+offset)).
Proof.
  intros Hstep Hwithin i Hi.
  assert (Hnat : N.to_nat i < 8) by lia.
  destruct (requested_slot_nth data offset (N.to_nat i) Hwithin Hnat)
    as [b [Hdata Hslot]].
  unfold word_subset.
  rewrite flash_slot_nth by exact Hnat.
  replace (page + offset + N.to_nat i)%nat
    with (page + (offset + N.to_nat i))%nat by lia.
  pose proof (failed_program_requested_only _ _ _ _ _ Hstep)
    as Hrequested.
  specialize (Hrequested (offset+N.to_nat i) b Hdata).
  unfold program_bits in Hrequested.
  rewrite <- Hslot in Hrequested.
  rewrite N.land_comm. exact Hrequested.
Qed.

Theorem failed_page_copy_cannot_retarget g f page data f'
    offset a b data_len logical_page :
  program_step g f page data VerifyFailed f' ->
  offset + 8 <= length data ->
  requested_slot data offset = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f' (page+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Htarget Ha Hdecode.
  pose proof (failed_program_slot_requested_only _ _ _ _ _ _
    Hstep Hwithin) as Hmono.
  rewrite Htarget in Hmono.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  rewrite <- Hbytes in Hmono. symmetry.
  apply (distinct_byte_codes_incomparable a b Ha Hb Hmono).
Qed.

Lemma success_program_slot_exact g f page data f' offset :
  program_step g f page data Success f' ->
  offset + 8 <= length data ->
  flash_slot f' (page+offset) = requested_slot data offset.
Proof.
  intros Hstep Hwithin.
  apply nth_ext with (d:=0%N) (d':=0%N).
  - unfold flash_slot, requested_slot.
    rewrite length_map, length_seq, length_firstn, length_skipn.
    lia.
  - intros i Hi.
    unfold flash_slot in Hi. rewrite length_map, length_seq in Hi.
    destruct (requested_slot_nth data offset i Hwithin Hi)
      as [b [Hdata Hnth]].
    rewrite flash_slot_nth by exact Hi.
    rewrite Hnth.
    replace (page+offset+i)%nat with (page+(offset+i))%nat by lia.
    exact (program_success_contents _ _ _ _ _ Hstep _ _ Hdata).
Qed.

Theorem program_slot_requested_only_any_outcome g f page data result f'
    offset :
  program_step g f page data result f' ->
  offset + 8 <= length data ->
  slot_byte_subset (requested_slot data offset)
                   (flash_slot f' (page+offset)).
Proof.
  intros Hstep Hwithin. destruct result.
  - rewrite (success_program_slot_exact _ _ _ _ _ _ Hstep Hwithin).
    unfold slot_byte_subset, word_subset.
    intros i Hi. rewrite N.land_diag. reflexivity.
  - eapply failed_program_slot_requested_only; eauto.
  - eapply interrupted_program_slot_requested_only; eauto.
Qed.

Theorem page_copy_cannot_retarget_any_outcome g f page data result f'
    offset a b data_len logical_page :
  program_step g f page data result f' ->
  offset + 8 <= length data ->
  requested_slot data offset = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f' (page+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Htarget Ha Hdecode.
  destruct result.
  - rewrite (success_program_slot_exact _ _ _ _ _ _ Hstep Hwithin)
      in Hdecode.
    rewrite Htarget in Hdecode.
    pose proof (decode_slot_sound _ _ _ _ Hdecode)
      as [Hb [_ [_ Heq]]].
    symmetry. apply (distinct_byte_codes_incomparable a b Ha Hb).
    rewrite Heq. unfold slot_byte_subset, word_subset.
    intros i Hi. rewrite N.land_diag. reflexivity.
  - eapply failed_page_copy_cannot_retarget; eauto.
  - pose proof (interrupted_program_slot_requested_only _ _ _ _ _ _
      Hstep Hwithin) as Hmono.
    rewrite Htarget in Hmono.
    pose proof (decode_slot_sound _ _ _ _ Hdecode)
      as [Hb [_ [_ Hbytes]]].
    rewrite <- Hbytes in Hmono. symmetry.
    apply (distinct_byte_codes_incomparable a b Ha Hb Hmono).
Qed.

Theorem interrupted_erase_slot_monotone g f sector f' offset :
  erase_step g f sector Reset f' ->
  offset + 8 <= sector_size g ->
  slot_byte_subset (flash_slot f (sector+offset))
                   (flash_slot f' (sector+offset)).
Proof.
  intros Hstep Hwithin i Hi.
  assert (Hnat : N.to_nat i < 8) by lia.
  unfold word_subset.
  rewrite !flash_slot_nth by exact Hnat.
  replace (sector + offset + N.to_nat i)%nat
    with (sector + (offset + N.to_nat i))%nat by lia.
  inversion Hstep; subst; clear Hstep.
  destruct H0 as [_ Hbits].
  specialize (Hbits (offset + N.to_nat i) ltac:(lia)).
  destruct Hbits as [_ Hmono].
  unfold erase_bits in Hmono. exact Hmono.
Qed.

Theorem erase_slot_monotone_any_outcome g f sector result f' offset :
  erase_step g f sector result f' ->
  (forall i, i < sector_size g -> valid_byte (f (sector+i))) ->
  offset + 8 <= sector_size g ->
  slot_byte_subset (flash_slot f (sector+offset))
                   (flash_slot f' (sector+offset)).
Proof.
  intros Hstep Hvalid Hwithin. destruct result.
  - eapply interrupted_erase_slot_monotone; [|exact Hwithin].
    eapply erase_completed_before_reset; eauto.
  - eapply interrupted_erase_slot_monotone; [|exact Hwithin].
    apply failed_erase_image_can_be_reset. exact Hstep.
  - eapply interrupted_erase_slot_monotone; eauto.
Qed.

Theorem erase_cannot_retarget_any_outcome g f sector result f' offset
    a b data_len logical_page :
  erase_step g f sector result f' ->
  (forall i, i < sector_size g -> valid_byte (f (sector+i))) ->
  offset + 8 <= sector_size g ->
  flash_slot f (sector+offset) = code_bytes a -> u32 a ->
  decode_slot (flash_slot f' (sector+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hvalid Hwithin Hold Ha Hdecode.
  pose proof (erase_slot_monotone_any_outcome _ _ _ _ _ _
    Hstep Hvalid Hwithin) as Hmono.
  rewrite Hold in Hmono.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  rewrite <- Hbytes in Hmono. symmetry.
  apply (distinct_byte_codes_incomparable a b Ha Hb Hmono).
Qed.

Theorem interrupted_page_copy_cannot_retarget g f page data f'
    offset a b data_len logical_page :
  program_step g f page data Reset f' ->
  offset + 8 <= length data ->
  requested_slot data offset = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f' (page+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Htarget Ha Hdecode.
  pose proof (interrupted_program_slot_requested_only _ _ _ _ _ _
    Hstep Hwithin) as Hmono.
  rewrite Htarget in Hmono.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  rewrite <- Hbytes in Hmono. symmetry.
  apply (distinct_byte_codes_incomparable a b Ha Hb Hmono).
Qed.

Theorem interrupted_sector_erase_cannot_retarget g f sector f'
    offset a b data_len logical_page :
  erase_step g f sector Reset f' ->
  offset + 8 <= sector_size g ->
  flash_slot f (sector+offset) = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f' (sector+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Hold Ha Hdecode.
  pose proof (interrupted_erase_slot_monotone _ _ _ _ _ Hstep Hwithin)
    as Hmono.
  rewrite Hold in Hmono.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  rewrite <- Hbytes in Hmono. symmetry.
  apply (distinct_byte_codes_incomparable a b Ha Hb Hmono).
Qed.

Theorem interrupted_program_then_erase_cannot_retarget
    gp ge f0 f1 f2 program_page data program_offset
    erase_sector erase_offset a b data_len logical_page :
  program_step gp f0 program_page data Reset f1 ->
  erase_step ge f1 erase_sector Reset f2 ->
  program_offset + 8 <= length data ->
  erase_offset + 8 <= sector_size ge ->
  program_page + program_offset = erase_sector + erase_offset ->
  requested_slot data program_offset = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f2 (erase_sector+erase_offset))
    data_len logical_page = Some b -> b = a.
Proof.
  intros Hprogram Herase Hprogram_range Herase_range Haddr Htarget Ha Hdecode.
  pose proof (interrupted_program_slot_requested_only _ _ _ _ _ _
    Hprogram Hprogram_range) as Hp.
  rewrite Htarget, Haddr in Hp.
  pose proof (interrupted_erase_slot_monotone _ _ _ _ _
    Herase Herase_range) as He.
  eapply torn_byte_program_then_erase_cannot_retarget;
    [exact Ha|exact Hp|exact He|exact Hdecode].
Qed.

(* VerifyFailed is a returned error, not a reset. Its physical image obeys
   the same requested-only partial-program contract. *)
Lemma failed_program_slot_monotone g f page data f' offset :
  program_step g f page data VerifyFailed f' ->
  offset + 8 <= length data ->
  slot_byte_subset (flash_slot f' (page+offset))
                   (flash_slot f (page+offset)).
Proof.
  intros Hstep Hwithin i Hi.
  assert (Hnat : N.to_nat i < 8) by lia.
  unfold word_subset.
  rewrite !flash_slot_nth by exact Hnat.
  replace (page + offset + N.to_nat i)%nat
    with (page + (offset + N.to_nat i))%nat by lia.
  inversion Hstep; subst; clear Hstep.
  destruct H0 as [_ Hprogress].
  assert (Hidx : offset + N.to_nat i < length data) by lia.
  destruct (nth_error data (offset + N.to_nat i)) eqn:E.
  - destruct (Hprogress _ _ E) as [_ [Hbits _]].
    unfold program_bits in Hbits.
    rewrite N.land_comm. exact Hbits.
  - apply nth_error_None in E. lia.
Qed.

Theorem failed_page_rewrite_cannot_retarget g f page data f' offset
    a b data_len logical_page :
  program_step g f page data VerifyFailed f' ->
  offset + 8 <= length data ->
  flash_slot f (page+offset) = code_bytes a ->
  u32 a ->
  decode_slot (flash_slot f' (page+offset)) data_len logical_page = Some b ->
  b = a.
Proof.
  intros Hstep Hwithin Hold Ha Hdecode.
  pose proof (failed_program_slot_monotone _ _ _ _ _ _ Hstep Hwithin)
    as Hmono.
  rewrite Hold in Hmono.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  rewrite <- Hbytes in Hmono.
  exact (distinct_byte_codes_incomparable b a Hb Ha Hmono).
Qed.
