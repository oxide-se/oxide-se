From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalComplement
  JournalFlashBridge JournalWriteEntry JournalScan JournalIndex
  JournalAppendSelection JournalRecoveryTrace JournalRequests JournalPhaseShape.
Import ListNotations.

(* A small-step enclosing journal machine. Running retains ghost source
   information across reset, never the abandoned Rust continuation. Boot is
   the clean-secondary path of latest; Running/Inspect is its repair path.
   This is a journal control witness, not the whole registry boot certificate. *)
Inductive control :=
| Ready (f : flash)
| Boot (f : flash)
| Frozen (f : flash)
| Writing (f : flash) (index : nat) (candidate : N)
| AwaitAck (f : flash) (index : nat) (candidate : N)
| Running (old_slot : nat) (old candidate : N) (s : JournalRecoveryTrace.state).

Section Reachable.
Variable g : geometry.
Variable sector page : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hgeom : journal_geometry g sector page.
Hypothesis Hsector8 : sector mod 8 = 0.

Definition candidate_valid d :=
  u32 d /\ (N.of_nat page <= d < data_len)%N /\
  (d mod N.of_nat page = 0)%N /\ boss_ok d = true.
Definition selected f i d :=
  latest_in_model boss_ok data_len (N.of_nat page)
    (sector_bytes f 0 sector) = Some (i,d).
Definition ready_image f := valid_flash f /\
  JournalPhaseShape.shape sector f /\ JournalRecoveryTrace.clean_backup sector f.
Definition running_invariant old_slot a c s :=
  old_slot + 8 <= sector /\ candidate_valid a /\ candidate_valid c /\
  JournalRecoveryTrace.recovery_invariant sector old_slot a s /\
  JournalPhaseShape.phase_shape sector a s /\
  JournalRecoveryTrace.clean_at_append_or_done sector s.

(* The invariants are separate from the step relation below. In particular,
   no step assumes ready_image, erased_suffix, or a freshness conclusion. *)
Definition invariant s :=
  match s with
  | Ready f | Boot f | Frozen f => ready_image f
  | Writing f i d => ready_image f /\ candidate_valid d /\
      first_empty_slot (sector_bytes f 0 sector) = Some i
  | AwaitAck f i d => ready_image f /\ selected f i d
  | Running old_slot a c r => running_invariant old_slot a c r
  end.

Definition candidate_buffer f i d :=
  write_entry_page f (8*i/page*page) page (8*i mod page) (code_bytes d).

Inductive step : control -> control -> Prop :=
| begin_append f i d :
    candidate_valid d -> first_empty_slot (sector_bytes f 0 sector) = Some i ->
    step (Ready f) (Writing f i d)
| begin_rotation f i a d :
    candidate_valid d -> first_empty_slot (sector_bytes f 0 sector) = None ->
    selected f i a ->
    step (Ready f) (Running (8*i) a d (State RotCopy f))
| candidate_program f f' i d result :
    program_step g f (8*i/page*page) (candidate_buffer f i d) result f' ->
    step (Writing f i d)
      (match result with Success => AwaitAck f' i d |
         VerifyFailed => Frozen f' | Reset => Boot f' end)
| acknowledge f i d : step (AwaitAck f i d) (Ready f)
| postwrite_readback_error f i d : step (AwaitAck f i d) (Frozen f)
| boot_clean_latest f : step (Boot f) (Ready f)
| reset_ready f : step (Ready f) (Boot f)
| reset_before_program f i d : step (Writing f i d) (Boot f)
| reset_before_ack f i d : step (AwaitAck f i d) (Boot f)
| reset_frozen f : step (Frozen f) (Boot f)
| advance_protocol old_slot a d s s' :
    phase_of s <> ReturnedError ->
    (phase_of s <> RotAppend \/ phase_of s' <> Done) ->
    protocol_step g sector page a data_len boss_ok d s s' ->
    step (Running old_slot a d s) (Running old_slot a d s')
| final_rotation_program old_slot a d f f' :
    program_step g f 0 (appended_buffer page d f) Success f' ->
    step (Running old_slot a d (State RotAppend f)) (AwaitAck f' 1 d)
| return_from_latest old_slot a d f :
    step (Running old_slot a d (State Done f)) (Ready f)
| reset_protocol old_slot a d s :
    step (Running old_slot a d s)
      (Running old_slot a d (State Inspect (flash_of s)))
| reject_or_frozen_cleanup s : step s s.

Lemma selected_has_code f i a : selected f i a ->
  8*i+8 <= sector /\ candidate_valid a /\ flash_slot f (8*i) = code_bytes a.
Proof.
  intro Hselected.
  destruct (latest_in_has_validated_slot _ _ _ _ _ _ Hselected)
    as [Hi [Hdecode Hboss]].
  unfold sector_bytes in Hi. rewrite length_map, length_seq in Hi.
  assert (Hfit : 8*i+8 <= sector).
  { pose proof (Nat.div_mod sector 8 ltac:(lia)). lia. }
  rewrite physical_slot_of_flash in Hdecode by exact Hfit.
  destruct (decode_slot_sound _ _ _ _ Hdecode) as [Ha [Hr [Hal Hcode]]].
  split; [exact Hfit|]. split.
  - unfold candidate_valid; tauto.
  - symmetry. exact Hcode.
Qed.

Lemma start_rotation_invariant f i a d :
  ready_image f -> candidate_valid d -> selected f i a ->
  running_invariant (8*i) a d (State RotCopy f).
Proof.
  intros [Hv [Hs Hclean]] Hd Hselected.
  destruct (selected_has_code f i a Hselected) as [Hfit [Ha Hcode]].
  destruct Ha as [Hu [Hr [Hal Hb]]].
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize _]]]]].
  unfold running_invariant. split; [exact Hfit|].
  split; [unfold candidate_valid; tauto|]. split; [exact Hd|]. split.
  - apply initial_rotation_invariant; try assumption.
    exact (clean_backup_slot g sector page (8*i) a data_len Hsector Hpage
      Hsize Hfit Hr Hal f Hclean).
  - split; [split; assumption|exact I].
Qed.

Lemma candidate_program_preserves_ready f f' i d result :
  ready_image f -> first_empty_slot (sector_bytes f 0 sector) = Some i ->
  program_step g f (8*i/page*page) (candidate_buffer f i d) result f' ->
  ready_image f'.
Proof.
  intros [Hv [Hs Hclean]] Hfirst Hstep.
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize [Hpage8 Hmultiple]]]]]].
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hi _].
  unfold sector_bytes in Hi. rewrite length_map, length_seq in Hi.
  destruct (slot_fits_sector page sector i ltac:(lia) Hpage8 Hmultiple Hi)
    as [Hfit Hwithin].
  pose proof (Nat.div_mod (8*i) page ltac:(lia)) as Haddr.
  split.
  - eapply program_step_preserves_valid_flash; eauto.
  - split.
    + eapply (any_outcome_nonrotation_preserves_erased_suffix
        g f f' sector page i (8*i/page*page) (8*i mod page) d result);
        eauto; nia.
    + intros j Hj. eapply (primary_page_write_preserves_clean_secondary
        g f f' sector page (8*i/page*page) (8*i mod page) d result); eauto.
      eapply (aligned_page_stays_in_primary (8*i) sector page); eauto; lia.
Qed.

Lemma candidate_success_selects f f' i d :
  ready_image f -> candidate_valid d ->
  first_empty_slot (sector_bytes f 0 sector) = Some i ->
  program_step g f (8*i/page*page) (candidate_buffer f i d) Success f' ->
  selected f' i d.
Proof.
  intros [Hv [Hs Hclean]] [Hu [Hr [Hal Hb]]] Hfirst Hstep.
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize [Hpage8 Hmultiple]]]]]].
  pose proof (Nat.div_mod (8*i) page ltac:(lia)) as Haddr.
  eapply (successful_nonrotation_append_selects g f f' sector page i
    (8*i/page*page) (8*i mod page) d data_len boss_ok); eauto; try nia.
  apply slot_fits_page; lia.
Qed.

Lemma running_advance_preserves old_slot a d s s' :
  running_invariant old_slot a d s ->
  protocol_step g sector page a data_len boss_ok d s s' ->
  running_invariant old_slot a d s'.
Proof.
  intros [Hfit [Ha [Hd [Hi [Hs Hclean]]]]] Hstep.
  destruct Ha as [Hu [Hr [Hal Hb]]].
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize _]]]]].
  unfold running_invariant. split; [exact Hfit|].
  split; [unfold candidate_valid; tauto|]. split; [exact Hd|]. split.
  - eapply protocol_step_preserves_invariant; eauto.
  - split.
    + eapply JournalPhaseShape.protocol_step_preserves_phase_shape; eauto.
    + eapply protocol_step_preserves_clean_phase; eauto.
Qed.

Lemma running_reset_preserves old_slot a d s :
  running_invariant old_slot a d s ->
  running_invariant old_slot a d (State Inspect (flash_of s)).
Proof.
  intros [Hfit [Ha [Hd [Hi [Hs Hclean]]]]].
  destruct Ha as [Hu [Hr [Hal Hb]]].
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize _]]]]].
  destruct (reset_between_commands_preserves_phase_shape g sector page
    old_slot a data_len Hsector Hpage Hsize Hsector8 Hfit Hu Hr Hal s Hi Hs) as [Hi' Hs'].
  unfold running_invariant. split; [exact Hfit|].
  split; [unfold candidate_valid; tauto|]. split; [exact Hd|].
  split; [exact Hi'|]. split; [exact Hs'|exact I].
Qed.

Lemma final_rotation_establishes_pending old_slot a d f f' :
  running_invariant old_slot a d (State RotAppend f) ->
  program_step g f 0 (appended_buffer page d f) Success f' ->
  ready_image f' /\ selected f' 1 d.
Proof.
  intros [Hfit [Ha [Hd [Hi [Hs Hclean]]]]] Hstep.
  destruct Ha as [Hu [Hr [Hal Hb]]].
  destruct Hd as [Hdu [Hdr [Hdal Hdb]]].
  destruct Hi as [Hv Hrest].
  change (JournalPhaseShape.single sector a f) in Hs.
  destruct Hs as [Hzero Htail].
  change (clean_backup sector f) in Hclean.
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize _]]]]].
  destruct (first_empty_after_single_entry f sector a data_len
    (N.of_nat page) ltac:(lia) Hsector8 Hzero Hu Hr Hal Htail)
    as [Hfirst Hshape].
  split.
  - split; [eapply program_step_preserves_valid_flash; eauto|]. split.
    + eapply (any_outcome_nonrotation_preserves_erased_suffix
        g f f' sector page 1 0 8 d Success); eauto; lia.
    + intros j Hj. eapply (primary_page_write_preserves_clean_secondary
        g f f' sector page 0 8 d Success); eauto; lia.
  - eapply (successful_nonrotation_append_selects g f f' sector page 1
      0 8 d data_len boss_ok); eauto; lia.
Qed.

Theorem step_preserves_invariant s s' : invariant s -> step s s' -> invariant s'.
Proof.
  intros Hi Hstep. destruct Hstep; cbn [invariant] in *.
  - auto.
  - eapply start_rotation_invariant; eauto.
  - destruct Hi as [Hr [Hd Hfirst]].
    pose proof (candidate_program_preserves_ready _ _ _ _ _ Hr Hfirst H) as Hr'.
    destruct result; cbn [invariant]; auto.
    split; [exact Hr'|]. eapply (candidate_success_selects f f' i d); eauto.
  - exact (proj1 Hi).
  - exact (proj1 Hi).
  - exact Hi.
  - exact Hi.
  - exact (proj1 Hi).
  - exact (proj1 Hi).
  - exact Hi.
  - eapply running_advance_preserves; eauto.
  - eapply final_rotation_establishes_pending; eauto.
  - destruct Hi as [Hfit [Ha [Hd [Hinv [Hs Hclean]]]]].
    exact (conj (proj1 Hinv) (conj Hs Hclean)).
  - eapply running_reset_preserves; eauto.
  - exact Hi.
Qed.

(* Bootstrap boundary: successful initialize has erased both journal sectors.
   Object format, keys and first BOSS construction are external obligations. *)
Definition initialized f :=
  valid_flash f /\ erased f 0 sector /\ clean_backup sector f.

Theorem successful_initialize_establishes_bootstrap f f1 f2 :
  valid_flash f -> erase_step g f 0 Success f1 ->
  erase_step g f1 sector Success f2 -> initialized f2.
Proof.
  intros Hv Hprimary Hsecondary.
  destruct Hgeom as [Hsector Hrest]. split.
  - eapply erase_step_preserves_valid_flash; [|exact Hsecondary].
    eapply erase_step_preserves_valid_flash; eauto.
  - split.
    + intros i Hi. rewrite (erase_locality _ _ _ _ _ Hsecondary (0+i)) by (left; lia).
      apply (erase_success_contents _ _ _ _ Hprimary). rewrite Hsector. exact Hi.
    + intros i Hi. apply (erase_success_contents _ _ _ _ Hsecondary).
      rewrite Hsector. exact Hi.
Qed.

Lemma initialized_invariant f : initialized f -> invariant (Boot f).
Proof.
  intros [Hv [Herased Hclean]]. split; [exact Hv|]. split; [|exact Hclean].
  apply all_erased_has_erased_suffix. intros b Hin.
  unfold sector_bytes in Hin. apply in_map_iff in Hin.
  destruct Hin as [p [Hb Hp]]. subst b.
  apply in_seq in Hp. replace p with (0+p) by lia. apply Herased. lia.
Qed.

Definition reachable s := exists f, initialized f /\
  clos_refl_trans control step (Boot f) s.

Theorem finite_trace_preserves_invariant s s' :
  invariant s -> clos_refl_trans control step s s' -> invariant s'.
Proof.
  intros Hi Htrace. induction Htrace.
  - eapply step_preserves_invariant; eauto.
  - exact Hi.
  - apply IHHtrace2. apply IHHtrace1. exact Hi.
Qed.

Theorem reachable_invariant s : reachable s -> invariant s.
Proof.
  intros [f [Hinit Htrace]]. eapply finite_trace_preserves_invariant;
    [apply initialized_invariant; exact Hinit|exact Htrace].
Qed.

Theorem reachable_ready_has_shape_and_clean_secondary f :
  reachable (Ready f) ->
  erased_suffix (sector_bytes f 0 sector) /\ clean_backup sector f.
Proof. intro H. exact (proj2 (reachable_invariant _ H)). Qed.

Theorem reachable_candidate_request f i d :
  reachable (Writing f i d) ->
  program_request g f (8*i/page*page) (candidate_buffer f i d).
Proof.
  intro H. destruct (reachable_invariant _ H) as [[Hv _] [_ Hfirst]].
  eapply first_ff_write_request; eauto.
Qed.

Theorem reachable_protocol_request old_slot a d s :
  reachable (Running old_slot a d s) ->
  JournalPhaseShape.next_request_valid g sector page a d s.
Proof.
  intro H. destruct (reachable_invariant _ H)
    as [Hfit [Ha [Hd [Hi [Hs Hclean]]]]].
  destruct Ha as [Hu [Hr [Hal Hb]]].
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize _]]]]].
  eapply JournalPhaseShape.phase_invariant_establishes_requests; eauto.
Qed.

Theorem reachable_acknowledgement_selects f i d :
  reachable (AwaitAck f i d) -> selected f i d /\ clean_backup sector f.
Proof.
  intro H. destruct (reachable_invariant _ H) as [[Hv [Hs Hclean]] Hselect].
  auto.
Qed.

Theorem reachable_holey_inspect_has_valid_backup old_slot a d f :
  reachable (Running old_slot a d (State Inspect f)) ->
  ~ erased_suffix (sector_bytes f 0 sector) ->
  checked_backup sector page data_len boss_ok f = Some a.
Proof.
  intros Hreach Hhole.
  destruct (reachable_invariant _ Hreach)
    as [Hfit [[Hu [Hr [Hal Hb]]] [Hd [Hi [Hs Hclean]]]]].
  change (JournalPhaseShape.shape sector f \/ JournalPhaseShape.backup sector a f) in Hs.
  destruct Hs as [Hshape|Hbackup]; [contradiction|].
  apply (backup_A_checked sector page a data_len boss_ok Hu Hr Hal Hb f Hbackup).
Qed.

(* A frozen error phase has no outgoing physical command. Reset is explicit;
   it enters Inspect, never Ready. The stutter covers rejected calls/cleanup. *)
Theorem frozen_idle_only_stutters_or_resets f s' :
  step (Frozen f) s' -> s' = Frozen f \/ s' = Boot f.
Proof. intro H; inversion H; subst; auto. Qed.

Theorem frozen_protocol_only_stutters_or_resets old_slot a d f s' :
  step (Running old_slot a d (State ReturnedError f)) s' ->
  s' = Running old_slot a d (State ReturnedError f) \/
  s' = Running old_slot a d (State Inspect f).
Proof. intro H; inversion H; subst; cbn in *; auto; contradiction. Qed.

End Reachable.
