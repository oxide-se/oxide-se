From Coq Require Import List Arith NArith Bool Lia.
From OxideSE.Registry Require Import FlashSpec Types PageOwnership RetentionCoverage
  AllocationAdmission JournalHistory PublicationPreparation.
Import ListNotations.

(* Page-indexed observations of recognized_block_header. Addresses in returned
   extents are object-relative; the existing object_flash provides displacement.
   This is a local decoder contract, not stability of any root. *)
Definition block_pages i n := {| offset:=256*i; span:=256*n |}.
Definition suffix_equal sector i (f f' : flash) :=
  forall a, 256*i <= a -> object_flash sector f' a=object_flash sector f a.
Definition recognizer_local sector (recognize : flash -> nat -> option nat) :=
  forall f f' i, suffix_equal sector i f f' -> recognize f' i=recognize f i.

(* The actual successful recycling_preserves_boundaries traversal, including
   None -> one page, recognized extent -> jump, and the overlap checks.
   No list of pages assumed safe is an input. *)
Inductive checked_scan (recognize : flash -> nat -> option nat) f lo hi t : nat -> Prop :=
| scan_end i : hi <= i -> checked_scan recognize f lo hi t i
| scan_none i : i < hi -> recognize f i=None ->
    checked_scan recognize f lo hi t (S i) -> checked_scan recognize f lo hi t i
| scan_block i n : i < hi -> recognize f i=Some n -> 0<n ->
    (i+n<=lo \/ (lo<=i /\ vacantb t (block_pages i n)=true)) ->
    checked_scan recognize f lo hi t (i+n) -> checked_scan recognize f lo hi t i.

Lemma selection_reaches_start recognize f lo hi t i :
  checked_scan recognize f lo hi t i -> i<=lo -> lo<hi ->
  checked_scan recognize f lo hi t lo.
Proof.
  intros WALK; induction WALK; intros LOW RANGE.
  - lia.
  - destruct (Nat.eq_dec i lo) as [->|NE]; [eapply scan_none; eauto|apply IHWALK; lia].
  - destruct (Nat.eq_dec i lo) as [->|NE]; [eapply scan_block; eauto|].
    apply IHWALK; [destruct H2 as [END|[BAD _]]; lia|exact RANGE].
Qed.
Lemma checked_scan_transport sector recognize f f' lo hi t i :
  recognizer_local sector recognize -> suffix_equal sector i f f' ->
  checked_scan recognize f lo hi t i -> checked_scan recognize f' lo hi t i.
Proof.
  intros LOCAL SAME WALK. revert SAME; induction WALK; intro SAME.
  - constructor; assumption.
  - eapply scan_none; [exact H|rewrite (LOCAL _ _ _ SAME); exact H0|].
    apply IHWALK. intros a A; apply SAME; lia.
  - eapply scan_block; [exact H|rewrite (LOCAL _ _ _ SAME); exact H0|exact H1|exact H2|].
    apply IHWALK. intros a A; apply SAME; lia.
Qed.

Definition clear_page sector (f : flash) p : list N :=
  map (fun k => if k <? 4 then 0%N else f (2*sector+256*p+k)) (seq 0 256).
Lemma clear_page_length sector f p : length (clear_page sector f p)=256.
Proof. unfold clear_page; rewrite map_length, seq_length; reflexivity. Qed.
Lemma clear_page_nth sector f p k b : nth_error (clear_page sector f p) k=Some b ->
  k<256 /\ b=if k <? 4 then 0%N else f (2*sector+256*p+k).
Proof.
  unfold clear_page. rewrite nth_error_map. intro H.
  destruct (nth_error (seq 0 256) k) eqn:E; [|discriminate].
  rewrite nth_error_seq in E. destruct (k <? 256) eqn:K; [|discriminate].
  apply Nat.ltb_lt in K. inversion E; subst n. inversion H; subst; auto.
Qed.
Lemma clear_page_request g sector f p :
  valid_flash f -> page_size g=256 -> sector mod 256=0 ->
  within g (2*sector+256*p) 256 ->
  program_request g f (2*sector+256*p) (clear_page sector f p).
Proof.
  intros VALID PAGE ALIGN BOUNDS. unfold program_request.
  rewrite clear_page_length, PAGE. split; [reflexivity|]. split.
  - assert (A : (2*sector) mod 256=0) by (rewrite Nat.mul_mod by lia; rewrite ALIGN; reflexivity).
    assert (B : (256*p) mod 256=0) by (rewrite Nat.mul_comm; apply Nat.mod_mul; lia).
    rewrite Nat.add_mod by lia; rewrite A, B; reflexivity.
  - split; [exact BOUNDS|]. split.
    + unfold valid_payload. apply Forall_forall. intros b IN.
      apply In_nth_error in IN. destruct IN as [k K].
      destruct (clear_page_nth _ _ _ _ _ K) as [_ ->].
      destruct (k <? 4); [unfold valid_byte; lia|apply VALID].
    + intros k b K. destruct (clear_page_nth _ _ _ _ _ K) as [_ ->].
      unfold program_bits. destruct (k <? 4); [apply N.land_0_r|apply N.land_diag].
Qed.

Inductive neutral_end := NeutralSuccess | NeutralError | NeutralReset | NeutralFatal.
Record neutral_observation := NeutralObservation {
  neutral_flash : flash; neutral_events : list (nat * outcome); neutral_end_ : neutral_end
}.
(* A readback service may report failure after program returned Success. This
   is explicit and conservative; coherent exact reads make that branch
   unreachable, without affecting its safety proof. Reset is NEVER a reply. *)
Inductive clear_pages g sector (magic : flash -> nat -> bool) header :
    list nat -> flash -> neutral_observation -> Prop :=
| clear_done f : clear_pages g sector magic header [] f (NeutralObservation f [] NeutralSuccess)
| clear_between ps f : clear_pages g sector magic header ps f (NeutralObservation f [] NeutralReset)
| clear_skip p ps f r : p<>header -> magic f p=false ->
    clear_pages g sector magic header ps f r -> clear_pages g sector magic header (p::ps) f r
| clear_continue p ps f f' r : (p=header \/ magic f p=true) ->
    program_step g f (2*sector+256*p) (clear_page sector f p) Success f' ->
    clear_pages g sector magic header ps f' r ->
    clear_pages g sector magic header (p::ps) f
      (NeutralObservation (neutral_flash r) ((p,Success)::neutral_events r) (neutral_end_ r))
| clear_failed p ps f f' : (p=header \/ magic f p=true) ->
    program_step g f (2*sector+256*p) (clear_page sector f p) VerifyFailed f' ->
    clear_pages g sector magic header (p::ps) f (NeutralObservation f' [(p,VerifyFailed)] NeutralError)
| clear_read_failed p ps f f' : (p=header \/ magic f p=true) ->
    program_step g f (2*sector+256*p) (clear_page sector f p) Success f' ->
    clear_pages g sector magic header (p::ps) f (NeutralObservation f' [(p,Success)] NeutralError)
| clear_reset p ps f f' : (p=header \/ magic f p=true) ->
    program_step g f (2*sector+256*p) (clear_page sector f p) Reset f' ->
    clear_pages g sector magic header (p::ps) f (NeutralObservation f' [(p,Reset)] NeutralReset).
Definition block_schedule i n := seq (S i) (n-1) ++ [i].
Lemma block_schedule_bounds i n p : 0<n -> In p (block_schedule i n) -> i<=p<i+n.
Proof. unfold block_schedule. rewrite in_app_iff. intros N [IN|[<-|[]]]; [apply in_seq in IN|]; lia. Qed.

Lemma clear_single_frame g sector f f' p i n result :
  valid_flash f -> i<=p<i+n -> program_step g f (2*sector+256*p) (clear_page sector f p) result f' ->
  object_write_frame sector (block_pages i n) f f'.
Proof.
  intros VALID POS STEP. split; [eapply program_step_preserves_valid_flash; eauto|].
  intros x OUT. apply (program_locality _ _ _ _ _ _ STEP). rewrite clear_page_length.
  unfold block_pages in OUT; cbn [offset span] in OUT.
  destruct (Nat.lt_ge_cases x (2*sector+256*p)); [auto|]. right.
  destruct (Nat.lt_ge_cases x (2*sector+256*p+256)); [exfalso; apply OUT; nia|lia].
Qed.
Lemma clear_pages_frame g sector magic header ps f r i n :
  valid_flash f -> (forall p, In p ps -> i<=p<i+n) ->
  clear_pages g sector magic header ps f r ->
  object_write_frame sector (block_pages i n) f (neutral_flash r).
Proof.
  intros V B RUN. revert V B; induction RUN; intros V B; try (split; [exact V|intros; reflexivity]).
  - apply IHRUN; [exact V|intros p0 IN; apply B; right; exact IN].
  - pose proof (clear_single_frame _ _ _ _ _ _ _ _ V (B p (or_introl eq_refl)) H0) as [V' F].
    destruct (IHRUN V' ltac:(intros p0 IN; apply B; right; exact IN)) as [VR FR].
    split; [exact VR|]. intros x OUT. simpl. rewrite (FR x OUT); apply F; exact OUT.
  - apply (clear_single_frame _ _ _ _ _ _ _ _ V (B p (or_introl eq_refl)) H0).
  - apply (clear_single_frame _ _ _ _ _ _ _ _ V (B p (or_introl eq_refl)) H0).
  - apply (clear_single_frame _ _ _ _ _ _ _ _ V (B p (or_introl eq_refl)) H0).
Qed.

Inductive neutral_run g sector recognize magic hi : nat -> flash -> neutral_observation -> Prop :=
| neutral_done i f : hi<=i -> neutral_run g sector recognize magic hi i f (NeutralObservation f [] NeutralSuccess)
| neutral_between i f : neutral_run g sector recognize magic hi i f (NeutralObservation f [] NeutralReset)
(* Conservative lower-service stop before header recognition completes. The
   Rust realization additionally checks header bounds/magic before calling crypto.
   No caller continuation, scratch cleanup or freeze is executed by this edge. *)
| neutral_crypto_stop i f : i<hi ->
    neutral_run g sector recognize magic hi i f (NeutralObservation f [] NeutralFatal)
| neutral_skip i f r : i<hi -> recognize f i=None ->
    neutral_run g sector recognize magic hi (S i) f r -> neutral_run g sector recognize magic hi i f r
| neutral_stop i n f r : i<hi -> recognize f i=Some n -> 0<n ->
    clear_pages g sector magic i (block_schedule i n) f r -> neutral_end_ r<>NeutralSuccess ->
    neutral_run g sector recognize magic hi i f r
| neutral_next i n f block final : i<hi -> recognize f i=Some n -> 0<n ->
    clear_pages g sector magic i (block_schedule i n) f block -> neutral_end_ block=NeutralSuccess ->
    neutral_run g sector recognize magic hi (i+n) (neutral_flash block) final ->
    neutral_run g sector recognize magic hi i f
      (NeutralObservation (neutral_flash final) (neutral_events block++neutral_events final) (neutral_end_ final)).

Lemma write_frame_next_suffix sector i n f f' :
  object_write_frame sector (block_pages i n) f f' -> suffix_equal sector (i+n) f f'.
Proof.
  intros [_ FRAME] a A. unfold object_flash. apply FRAME.
  unfold block_pages; cbn [offset span]; nia.
Qed.
Lemma write_frame_journal sector i n f f' :
  object_write_frame sector (block_pages i n) f f' ->
  forall a, a<2*sector -> f' a=f a.
Proof. intros FRAME; apply (object_write_keeps_journal _ _ _ _ FRAME). Qed.

(* Successful selection implies every block processed at/after lo is free.
   Crucially n may extend beyond hi: the WHOLE block is checked. *)
Lemma selected_block_free recognize f lo hi t i n :
  checked_scan recognize f lo hi t i -> lo<=i -> i<hi -> recognize f i=Some n ->
  free_range 256 t (block_pages i n) /\ checked_scan recognize f lo hi t (i+n).
Proof.
  intros SCAN LOW HIGH REC. inversion SCAN; subst; try lia; try congruence.
  assert (n0=n) by congruence; subst n0.
  split; [apply vacantb_spec|assumption].
  match goal with C : _ \/ _ |- _ => destruct C as [BAD|[_ FREE]]; [lia|exact FREE] end.
Qed.

Theorem selected_neutralization_preserves g sector recognize magic lo hi t i f result live :
  recognizer_local sector recognize -> valid_flash f ->
  protected (needed 256 live) t -> checked_scan recognize f lo hi t i -> lo<=i ->
  neutral_run g sector recognize magic hi i f result ->
  valid_flash (neutral_flash result) /\
  unchanged live (object_flash sector f) (object_flash sector (neutral_flash result)) /\
  (forall a, a<2*sector -> neutral_flash result a=f a).
Proof.
  intros LOCAL VALID COVER SCAN LOW RUN. revert VALID SCAN LOW.
  induction RUN; intros VALID SCAN LOW.
  - split; [exact VALID|]. split; [intros r a IN AT; reflexivity|intros; reflexivity].
  - split; [exact VALID|]. split; [intros r a IN AT; reflexivity|intros; reflexivity].
  - split; [exact VALID|]. split; [intros r a IN AT; reflexivity|intros; reflexivity].
  - apply IHRUN; [exact VALID| |lia].
    inversion SCAN; subst; try lia; try congruence; assumption.
  - destruct (selected_block_free _ _ _ _ _ _ _ SCAN LOW H H0) as [FREE TAIL].
    pose proof (clear_pages_frame _ _ _ _ _ _ _ _ _ VALID
      (fun p IN => block_schedule_bounds i n p H1 IN) H2) as FRAME.
    split; [exact (proj1 FRAME)|]. split.
    + eapply free_object_write_preserves; eauto.
    + exact (write_frame_journal _ _ _ _ _ FRAME).
  - destruct (selected_block_free _ _ _ _ _ _ _ SCAN LOW H H0) as [FREE TAIL].
    pose proof (clear_pages_frame _ _ _ _ _ _ _ _ _ VALID
      (fun p IN => block_schedule_bounds i n p H1 IN) H2) as FRAME.
    assert (TAIL' : checked_scan recognize (neutral_flash block) lo hi t (i+n)).
    { eapply checked_scan_transport; [exact LOCAL|eapply write_frame_next_suffix; exact FRAME|exact TAIL]. }
    destruct (IHRUN (proj1 FRAME) TAIL' ltac:(lia)) as [V [KEEP J]].
    split; [exact V|]. split.
    + intros r a IN AT. simpl. rewrite (KEEP r a IN AT).
      exact (free_object_write_preserves _ _ _ _ _ _ COVER FREE FRAME r a IN AT).
    + intros a A. simpl. rewrite (J a A). exact (write_frame_journal _ _ _ _ _ FRAME a A).
Qed.

Definition selected_recycling recognize f lo hi t :=
  lo<hi /\ vacantb t (block_pages lo (hi-lo))=true /\ checked_scan recognize f lo hi t 0.
Theorem neutralization_consumer g sector recognize magic lo hi t f result live :
  recognizer_local sector recognize -> valid_flash f -> protected (needed 256 live) t ->
  selected_recycling recognize f lo hi t -> neutral_run g sector recognize magic hi lo f result ->
  free_range 256 t (block_pages lo (hi-lo)) /\
  valid_flash (neutral_flash result) /\
  unchanged live (object_flash sector f) (object_flash sector (neutral_flash result)) /\
  (forall a, a<2*sector -> neutral_flash result a=f a).
Proof.
  intros LOCAL V C [RANGE [FREE SCAN]] RUN. split; [apply vacantb_spec; exact FREE|].
  pose proof (selection_reaches_start recognize f lo hi t 0 SCAN (Nat.le_0_l lo) RANGE) as CUT.
  exact (selected_neutralization_preserves g sector recognize magic lo hi t lo f result live
    LOCAL V C CUT (Nat.le_refl lo) RUN).
Qed.

Fixpoint recycling_check fuel (recognize : flash -> nat -> option nat) (f : flash) lo hi t i : bool :=
  if hi <=? i then true else match fuel with
  | 0 => false
  | S fuel' => match recognize f i with
    | None => recycling_check fuel' recognize f lo hi t (S i)
    | Some n => (0 <? n) &&
      ((i+n <=? lo) || ((lo <=? i) && vacantb t (block_pages i n))) &&
      recycling_check fuel' recognize f lo hi t (i+n)
    end end.
Lemma recycling_check_sound fuel recognize f lo hi t i :
  recycling_check fuel recognize f lo hi t i=true -> checked_scan recognize f lo hi t i.
Proof.
  revert i; induction fuel; intros i; cbn [recycling_check];
  destruct (hi <=? i) eqn:E; try (intro; apply scan_end; apply Nat.leb_le; exact E); try discriminate.
  apply Nat.leb_gt in E. destruct (recognize f i) as [n|] eqn:R.
  - repeat rewrite andb_true_iff. intros [[POS GUARD] NEXT].
    eapply scan_block; [exact E|exact R|apply Nat.ltb_lt; exact POS| |apply IHfuel; exact NEXT].
    apply orb_true_iff in GUARD. destruct GUARD as [END|PAIR].
    + left; apply Nat.leb_le; exact END.
    + right. apply andb_true_iff in PAIR. destruct PAIR as [LOW FREE]. split; [apply Nat.leb_le; exact LOW|exact FREE].
  - intro NEXT. eapply scan_none; [exact E|exact R|apply IHfuel; exact NEXT].
Qed.
Definition recycling_selection_check fuel recognize f lo hi t :=
  (lo <? hi) && vacantb t (block_pages lo (hi-lo)) && recycling_check fuel recognize f lo hi t 0.
Lemma selected_check_sound fuel recognize f lo hi t :
  recycling_selection_check fuel recognize f lo hi t=true -> selected_recycling recognize f lo hi t.
Proof.
  unfold recycling_selection_check. repeat rewrite andb_true_iff.
  intros [[R FREE] WALK]. split; [apply Nat.ltb_lt; exact R|]. split; [exact FREE|].
  eapply recycling_check_sound; exact WALK.
Qed.

Lemma selected_page_disjoint t live i n p :
  protected (needed 256 live) t -> free_range 256 t (block_pages i n) -> i<=p<i+n ->
  forall r a, In r live -> contains r a -> ~ contains (block_pages p 1) a.
Proof.
  intros COVER FREE POS r a IN AT HIT.
  eapply (covered_free_range_disjoint 256 live t (block_pages i n) a ltac:(lia) COVER FREE).
  - unfold contains, block_pages in *; cbn [offset span] in *; nia.
  - exact IN.
  - exact AT.
Qed.

Theorem selected_block_commands_admissible g sector pages recognize f i n p :
  valid_flash f -> page_size g=256 -> sector mod 256=0 -> area_start g=0 ->
  2*sector+256*pages <= area_length g ->
  (forall f i n, recognize f i=Some n -> i+n<=pages) ->
  recognize f i=Some n -> 0<n -> In p (block_schedule i n) ->
  program_request g f (2*sector+256*p) (clear_page sector f p).
Proof.
  intros V PAGE ALIGN START SIZE BOUND REC POS IN.
  apply clear_page_request; try assumption.
  specialize (BOUND f i n REC). pose proof (block_schedule_bounds i n p POS IN).
  unfold within; rewrite START; split; nia.
Qed.

Theorem selected_clear_page_is_separated recognize f lo hi t i n p live :
  protected (needed 256 live) t -> checked_scan recognize f lo hi t i ->
  lo<=i -> i<hi -> recognize f i=Some n -> 0<n -> In p (block_schedule i n) ->
  forall r a, In r live -> contains r a -> ~ contains (block_pages p 1) a.
Proof.
  intros C S LOW HIGH REC POS IN.
  destruct (selected_block_free _ _ _ _ _ _ _ S LOW HIGH REC) as [F _].
  apply selected_page_disjoint with (t:=t) (i:=i) (n:=n); auto.
  exact (block_schedule_bounds i n p POS IN).
Qed.

(* Concrete selector witness: block [2,6) is touched by erase [2,4).
   Inner pages 4 and 5 are outside the erased sectors and still checked free.
   A protected page 5 rejects this candidate. *)
Definition example_recognize (_ : flash) i := if Nat.eqb i 2 then Some 4 else None.
Example beyond_erase_selected :
  recycling_selection_check 8 example_recognize (fun _=>255%N) 2 4 (fun _=>free_cell)=true.
Proof. vm_compute; reflexivity. Qed.
Example protected_tail_rejected :
  recycling_selection_check 8 example_recognize (fun _=>255%N) 2 4
    (fun p=> {|owner:=if Nat.eqb p 5 then 1 else 0; validated:=false|})=false.
Proof. vm_compute; reflexivity. Qed.
Example inner_schedule_outside_erase : In 5 (block_schedule 2 4).
Proof. simpl; auto. Qed.

Lemma clear_events_in_schedule g sector magic header ps f result :
 clear_pages g sector magic header ps f result ->
 forall p out, In (p,out) (neutral_events result) -> In p ps.
Proof.
 intro RUN; induction RUN; intros q out IN; simpl in IN; try contradiction.
 - right; eapply IHRUN; eauto.
 - destruct IN as [EQ|IN]; [inversion EQ; left; reflexivity|right; eapply IHRUN; eauto].
 - destruct IN as [EQ|[]]; inversion EQ; left; reflexivity.
 - destruct IN as [EQ|[]]; inversion EQ; left; reflexivity.
 - destruct IN as [EQ|[]]; inversion EQ; left; reflexivity.
Qed.

Theorem selected_neutralization_events_separated g sector recognize magic lo hi t i f result live :
 recognizer_local sector recognize -> valid_flash f -> protected (needed 256 live) t ->
 checked_scan recognize f lo hi t i -> lo<=i ->
 neutral_run g sector recognize magic hi i f result ->
 forall p out, In (p,out) (neutral_events result) ->
 forall r a, In r live -> contains r a -> ~ contains (block_pages p 1) a.
Proof.
 intros LOCAL VALID COVER SCAN LOW RUN. revert VALID SCAN LOW.
 induction RUN; intros VALID SCAN LOW p out EVENT; simpl in EVENT; try contradiction.
 - apply IHRUN with (out:=out); [exact VALID| |lia|exact EVENT].
   inversion SCAN; subst; try lia; try congruence; assumption.
 - eapply selected_clear_page_is_separated; eauto.
   eapply clear_events_in_schedule; eauto.
 - apply in_app_iff in EVENT; destruct EVENT as [FIRST|LAST].
   + eapply selected_clear_page_is_separated; eauto.
     eapply clear_events_in_schedule; eauto.
   + destruct (selected_block_free _ _ _ _ _ _ _ SCAN LOW H H0) as [FREE TAIL].
     pose proof (clear_pages_frame _ _ _ _ _ _ _ _ _ VALID
       (fun p IN=>block_schedule_bounds i n p H1 IN) H2) as FRAME.
     apply IHRUN with (out:=out); [exact (proj1 FRAME)| |lia|exact LAST].
     eapply checked_scan_transport; [exact LOCAL|eapply write_frame_next_suffix; exact FRAME|exact TAIL].
Qed.
