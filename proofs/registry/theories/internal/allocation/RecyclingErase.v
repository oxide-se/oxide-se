From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PageOwnership
 AllocationAdmission Neutralization RecyclingSearch PublicationPreparation JournalHistory
 PreparedAuthority.
Import ListNotations.

(* Physical command prefix of storage::erase_reusable_span. The address advances
   only on Success. Reset abandons the continuation, including at loop boundaries.
   This is an execution relation over the existing flash, not storage state. *)
Inductive erase_run (g:geometry) : nat -> nat -> flash -> neutral_observation -> Prop :=
| erase_done a f : erase_run g a 0 f (NeutralObservation f [] NeutralSuccess)
| erase_cut a n f : erase_run g a n f (NeutralObservation f [] NeutralReset)
| erase_next a n f f' result :
    erase_step g f a Success f' -> erase_run g (a+sector_size g) n f' result ->
    erase_run g a (S n) f
      (NeutralObservation (neutral_flash result) ((a,Success)::neutral_events result) (neutral_end_ result))
| erase_error a n f f' : erase_step g f a VerifyFailed f' ->
    erase_run g a (S n) f (NeutralObservation f' [(a,VerifyFailed)] NeutralError)
| erase_reset a n f f' : erase_step g f a Reset f' ->
    erase_run g a (S n) f (NeutralObservation f' [(a,Reset)] NeutralReset).

Theorem erase_run_frame g a n f result : erase_run g a n f result ->
 frame a (n*sector_size g) f (neutral_flash result).
Proof.
 intro RUN; induction RUN; simpl; intros x OUT; try reflexivity.
 - rewrite IHRUN by (destruct OUT; [left|right]; lia).
   apply (erase_locality _ _ _ _ _ H); destruct OUT; [left|right]; lia.
 - apply (erase_locality _ _ _ _ _ H); destruct OUT; [left|right]; lia.
 - apply (erase_locality _ _ _ _ _ H); destruct OUT; [left|right]; lia.
Qed.
Theorem erase_run_valid g a n f result : valid_flash f -> erase_run g a n f result ->
 valid_flash (neutral_flash result).
Proof.
 intros V RUN; induction RUN; simpl; eauto using erase_step_preserves_valid_flash.
Qed.
Theorem erase_run_complete g a n f result : erase_run g a n f result ->
 neutral_end_ result=NeutralSuccess -> erased (neutral_flash result) a (n*sector_size g).
Proof.
 intro RUN; induction RUN; simpl; intro OK; try discriminate.
 - intros i I; lia.
 - intros i I. destruct (Nat.lt_ge_cases i (sector_size g)).
   + rewrite (erase_run_frame _ _ _ _ _ RUN) by (left; lia).
     exact (erase_success_contents _ _ _ _ H i H0).
   + replace (a+i) with ((a+sector_size g)+(i-sector_size g)) by lia.
     apply (IHRUN OK); lia.
Qed.

(* Explicit local numeric admission: it concerns geometry only, never roots.
   The rounded erase extent is distinct from the useful object extent. *)
Definition erase_geometry g sector r count :=
 sector_size g=sector /\ 0<sector /\
 256*erase_pages r=count*sector /\
 (2*sector+256*recycle_lo r) mod sector=0 /\
 within g (2*sector+256*recycle_lo r) (count*sector) /\
 useful_pages r<=erase_pages r.
Theorem erase_command_admissible g sector r count i :
 erase_geometry g sector r count -> i<count ->
 erase_request g (2*sector+256*recycle_lo r+i*sector).
Proof.
 intros [SIZE [POS [LEN [ALIGN [[LOW HIGH] USE]]]]] I.
 unfold erase_request, within; rewrite SIZE. split.
 - rewrite Nat.add_mod by lia. rewrite ALIGN.
   rewrite Nat.mul_mod by lia. rewrite Nat.mod_same by lia. simpl.
   rewrite Nat.mul_0_r. now rewrite !Nat.mod_0_l by lia.
 - split; nia.
Qed.

Lemma touches_subextent r small p :
 offset r<=offset small -> offset small+span small<=offset r+span r ->
 touches 256 small p=true -> touches 256 r p=true.
Proof.
 intros L U T; unfold touches in *; apply Bool.andb_true_iff in T.
 destruct T as [A B]; apply Nat.leb_le in A; apply Nat.ltb_lt in B.
 apply Bool.andb_true_iff; split; [apply Nat.leb_le|apply Nat.ltb_lt].
 - pose proof (Nat.Div0.div_le_mono _ _ 256 L); lia.
 - assert (D:(offset small+span small+256-1)/256 <= (offset r+span r+256-1)/256).
   { apply Nat.Div0.div_le_mono; lia. } lia.
Qed.
Theorem selected_sector_free sector fuel recognize f t req round alignment pages start r count i :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 256*erase_pages r=count*sector -> i<count ->
 free_range 256 t {|offset:=256*recycle_lo r+i*sector;span:=sector|}.
Proof.
 intros SEARCH LEN I.
 pose proof (reusable_search_derives_guard _ _ _ _ _ _ _ _ _ _ _ SEARCH) as SELECT.
 destruct SELECT as [POS [FREE SCAN]]. apply vacantb_spec in FREE.
 unfold free_range in *; intros p T; apply FREE.
 eapply touches_subextent; [| |exact T]; unfold block_pages; simpl; nia.
Qed.

Theorem selected_erase_preserves g sector fuel recognize f t req round alignment pages start r count
 before result live :
 protected (needed 256 live) t ->
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 valid_flash before -> erase_run g (2*sector+256*recycle_lo r) count before result ->
 valid_flash (neutral_flash result) /\
 unchanged live (object_flash sector before) (object_flash sector (neutral_flash result)) /\
 (forall x, x<2*sector -> neutral_flash result x=before x) /\
 (neutral_end_ result=NeutralSuccess ->
   free_range 256 t (block_pages (recycle_lo r) (useful_pages r)) /\
   erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r))).
Proof.
 intros COVER SEARCH GEO V RUN.
 destruct GEO as [SIZE [POS [LEN [ALIGN [WITH USE]]]]].
 pose proof (reusable_search_derives_guard _ _ _ _ _ _ _ _ _ _ _ SEARCH) as [RANGE [FREE SCAN]]. apply vacantb_spec in FREE.
 assert (FRAME:=erase_run_frame _ _ _ _ _ RUN).
 rewrite SIZE, <-LEN in FRAME.
 split; [eapply erase_run_valid; eauto|]. split.
 - intros live_r x IN AT. unfold object_flash. apply FRAME.
   destruct (Nat.lt_ge_cases x (256*recycle_lo r)); [left; lia|].
   destruct (Nat.le_gt_cases (256*recycle_lo r+256*erase_pages r) x); [right; lia|].
   exfalso. replace (recycle_lo r+erase_pages r-recycle_lo r) with (erase_pages r) in FREE by lia.
   exact (covered_free_range_disjoint 256 live t
     (block_pages (recycle_lo r) (erase_pages r)) x ltac:(lia) COVER FREE
     ltac:(unfold contains, block_pages; simpl; lia) live_r IN AT).
 - split; [intros x X; apply FRAME; left; lia|]. intro OK; split.
   + intros p T; apply FREE. eapply touches_subextent; [| |exact T]; unfold block_pages; simpl; nia.
   + intros x AT. unfold contains, block_pages in AT; simpl in AT.
     unfold object_flash. replace (2*sector+x) with ((2*sector+256*recycle_lo r)+(x-256*recycle_lo r)) by lia.
     apply (erase_run_complete _ _ _ _ _ RUN OK); rewrite SIZE, <-LEN; nia.
Qed.

Theorem erased_late_reserve sector f s r :
 data_invariant s -> protection_frozen s=false -> pending_preparation s=None ->
 free_range 256 (protection_table s) r -> erased_object_extent sector f r ->
 data_caller (DataReserve r) s /\ data_invariant (data_next (DataReserve r) s) /\
 pending_preparation (data_next (DataReserve r) s)=Some (Build_preparation ObjectPreparation r Reserved) /\
 erased_object_extent sector f r.
Proof.
 intros I F P FREE BLANK. assert (CALL:data_caller (DataReserve r) s) by (simpl; auto).
 split; [exact CALL|]. split; [apply data_command_preserves; assumption|]. split; [reflexivity|exact BLANK].
Qed.

Example two_sector_reset_after_first :
 erase_run {|area_start:=0;area_length:=8;page_size:=1;sector_size:=4|} 0 2
 (fun _=>0%N)
 (NeutralObservation (fun x=>if x <? 4 then 255%N else 0%N) [(0,Success)] NeutralReset).
Proof.
 eapply erase_next with (f':=fun x=>if x <? 4 then 255%N else 0%N)
   (result:=NeutralObservation (fun x=>if x <? 4 then 255%N else 0%N) [] NeutralReset).
 - apply erase_success.
   + split; [reflexivity|split; simpl; lia].
   + intros x OUT; simpl in OUT; destruct (x <? 4) eqn:E; [apply Nat.ltb_lt in E; lia|reflexivity].
   + intros i I; simpl in I |- *; assert (E:(i <? 4)=true) by (apply Nat.ltb_lt; exact I); rewrite E; reflexivity.
 - apply erase_cut.
Qed.

(* No non-reappearance postulate: a zeroed byte can regain ANY valid value
   under interrupted erase. This is about bits, not acceptance by the decoder. *)
Example neutralized_byte_can_reappear b :
 Types.valid_byte b -> erase_bits 0%N b.
Proof. intros _; unfold erase_bits; apply N.land_0_l. Qed.
