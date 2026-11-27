From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalIndex JournalAppendSelection.
Import ListNotations.

(* Relative journal geometry. These are layout/backend obligations, not
   assumptions about authority or about a successful physical outcome. *)
Definition journal_geometry g sector page :=
  sector_size g = sector /\ page_size g = page /\
  area_start g = 0 /\ 2*sector <= area_length g /\
  16 <= page <= sector /\ page mod 8 = 0 /\ sector mod page = 0.

Lemma slot_erased_target f address aligned offset :
  aligned + offset = address ->
  flash_slot f address = repeat 255%N 8 ->
  erased_target f aligned offset.
Proof.
  intros Haddr Hslot i Hi. unfold erased_target in *.
  pose proof (f_equal (fun xs => nth i xs 0%N) Hslot) as Hbyte.
  change (nth i (flash_slot f address) 0%N =
    nth i (repeat 255%N 8) 0%N) in Hbyte.
  rewrite flash_slot_nth in Hbyte by exact Hi.
  rewrite (nth_indep (repeat 255%N 8) 0%N 255%N) in Hbyte
    by (rewrite repeat_length; exact Hi).
  rewrite nth_repeat in Hbyte. rewrite Haddr. exact Hbyte.
Qed.

Theorem first_ff_write_request g sector page f index d :
  journal_geometry g sector page -> valid_flash f ->
  first_empty_slot (sector_bytes f 0 sector) = Some index ->
  program_request g f (8*index/page*page)
    (write_entry_page f (8*index/page*page) page (8*index mod page)
      (code_bytes d)).
Proof.
  intros [Hsector [Hpage [Hstart [Harea [Hsize [Hpage8 Hmultiple]]]]]]
    Hvalid Hfirst.
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hindex [Hff _]].
  unfold sector_bytes in Hindex. rewrite length_map, length_seq in Hindex.
  destruct (slot_fits_sector page sector index ltac:(lia) Hpage8 Hmultiple
    Hindex) as [Hfit Hwithin].
  pose proof (Nat.div_mod (8*index) page ltac:(lia)) as Haddr.
  assert (Hbound : 8*index/page*page+page <= sector).
  { eapply aligned_page_stays_in_primary; eauto; lia. }
  eapply write_entry_code_request; eauto.
  - apply Nat.Div0.mod_mul.
  - unfold FlashSpec.within. rewrite Hstart. split; lia.
  - eapply (slot_erased_target f (8*index)); [nia|].
    rewrite physical_slot_of_flash in Hff by exact Hfit.
    exact Hff.
Qed.

Theorem primary_erase_request g sector page :
  journal_geometry g sector page -> erase_request g 0.
Proof.
  intros [Hs [Hp [Hstart [Harea [Hsize Hrest]]]]].
  unfold erase_request, FlashSpec.within. rewrite Hs, Hstart.
  split; [apply Nat.mod_0_l; lia|]. split; lia.
Qed.

Theorem secondary_erase_request g sector page :
  journal_geometry g sector page -> erase_request g sector.
Proof.
  intros [Hs [Hp [Hstart [Harea [Hsize Hrest]]]]].
  unfold erase_request, FlashSpec.within. rewrite Hs, Hstart.
  split; [apply Nat.mod_same; lia|]. split; lia.
Qed.

Theorem backup_copy_request g sector page f a :
  journal_geometry g sector page -> valid_flash f ->
  (forall i, i < sector -> f (sector+i) = 255%N) ->
  program_request g f sector
    (write_entry_page f sector page 0 (code_bytes a)).
Proof.
  intros [Hs [Hp [Hstart [Harea [Hsize [Hpage8 Hmultiple]]]]]] Hv Hclean.
  eapply write_entry_code_request; eauto; try lia.
  - unfold FlashSpec.within. rewrite Hstart. split; lia.
  - intros i Hi. replace (sector+0+i) with (sector+i) by lia.
    apply Hclean. lia.
Qed.

Theorem primary_restore_request g sector page f a :
  journal_geometry g sector page -> valid_flash f -> erased f 0 sector ->
  program_request g f 0 (write_entry_page f 0 page 0 (code_bytes a)).
Proof.
  intros [Hs [Hp [Hstart [Harea [Hsize Hrest]]]]] Hv Herased.
  eapply write_entry_code_request; eauto; try lia.
  - apply Nat.mod_0_l. lia.
  - unfold FlashSpec.within. rewrite Hstart. split; lia.
  - intros i Hi. apply Herased. lia.
Qed.

Theorem second_slot_write_request g sector page f d :
  journal_geometry g sector page -> valid_flash f ->
  flash_slot f 8 = repeat 255%N 8 ->
  program_request g f 0 (write_entry_page f 0 page 8 (code_bytes d)).
Proof.
  intros [Hs [Hp [Hstart [Harea [Hsize Hrest]]]]] Hv Hff.
  eapply write_entry_code_request; eauto; try lia.
  - apply Nat.mod_0_l. lia.
  - unfold FlashSpec.within. rewrite Hstart. split; lia.
  - eapply slot_erased_target; [reflexivity|exact Hff].
Qed.
