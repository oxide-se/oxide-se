From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec PageOwnership ScopeOwnership RetentionCoverage
  CompactImage CompactUpdates CollectionRoots PreparedAuthority JournalHistory JournalReachableShape
  JournalRecoveryTrace JournalRequests JournalAppendAuthority PublicationPreparation PreparationOutcomes
  BootReconstruction BootTransaction TransactionBoundary PersistentBoundary.
Import ListNotations.

(* Restrictions of existing operational traces, not a new journal machine.
   The last edge may execute a physical Reset outcome and change flash. *)
Definition reset_destination c := match c with
  | Boot _ => True
  | Running _ _ _ r => phase_of r = Inspect
  | _ => False end.
Definition publication_reset_prefix g sector data_len boss_ok candidate initial cut :=
  exists before,
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok candidate) initial before /\
    uncertain_append_control candidate (journal_control before) /\
    logged_step g sector 256 data_len boss_ok before cut /\
    reset_destination (journal_control cut).

Lemma cut_step_heads g sector data_len boss_ok candidate before cut :
  uncertain_append_control candidate (journal_control before) ->
  logged_step g sector 256 data_len boss_ok before cut ->
  reset_destination (journal_control cut) ->
  (hd_error (publications cut)=hd_error (publications before) \/ hd_error (publications cut)=Some candidate) /\
  acknowledgements cut=acknowledgements before.
Proof.
  intros BEFORE STEP DEST. destruct STEP as [c c' hist acks STEP]; cbn in BEFORE, DEST |- *.
  split.
  - destruct c; cbn [publication_history_after]; try (left; reflexivity).
    + cbn in BEFORE; subst. unfold record_candidate; destruct candidate_completed; [right|left]; reflexivity.
    + cbn in BEFORE. destruct BEFORE as [E PH]; subst.
      destruct s as [phase f]; destruct phase; cbn [phase_of]; try (left; reflexivity).
      unfold record_candidate; destruct candidate_completed; [right|left]; reflexivity.
  - unfold acknowledgement_history_after. destruct c; try reflexivity.
    destruct c'; try reflexivity; contradiction.
Qed.
Lemma reset_destination_recovers c : reset_destination c -> recovering_control c.
Proof. destruct c; simpl; try contradiction; auto. destruct s as [p f]; simpl; intros E; subst p; exact I. Qed.

Section Episode.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8 = 0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.

(* A postcondition over existing boot executions, never a trace premise. *)
Definition episode_boot_post initial e :=
  forall final, clos_refl_trans boot_state
    (boot_step g sector data_len boss_ok marker ranges decode topology pages) (initial,Selecting) final ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (boot_journal final,RebuildingBoundary (boot_pc final)) e /\
    forall j id d ram, final=(j,Usable id d ram) ->
      enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary id d ram) e /\
      (exists c, In c (live_certificates e) /\ certificate_id c=id /\ certificate_decoded c=d) /\
      data_caller DataBegin ram /\
      enriched_invariant sector data_len boss_ok view marker ranges decode pages
        (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)) e.
Lemma boot_entry_post initial e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (initial,RebuildingBoundary Selecting) e ->
  episode_boot_post initial e.
Proof.
  intros ENTRY final TRACE.
  destruct (enriched_boot_transport g sector data_len boss_ok view marker ranges decode topology pages G DIV CONTRACT
    (initial,Selecting) final e ENTRY TRACE) as [FINAL FRAME].
  split; [exact FINAL|]. intros j id d ram EQ; subst final.
  exact (enriched_boot_usable sector data_len boss_ok view marker ranges decode pages j id d ram e FINAL).
Qed.

Lemma journal_evidence_transport initial final e candidate :
  logged_invariant sector 256 data_len boss_ok initial ->
  persistent_evidence sector view ranges decode initial e ->
  (exists c, In c (live_certificates e) /\ N.of_nat (certificate_id c)=candidate) ->
  clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok) initial final ->
  (hd_error (publications final)=hd_error (publications initial) \/ hd_error (publications final)=Some candidate) ->
  logged_invariant sector 256 data_len boss_ok final /\ persistent_evidence sector view ranges decode final e.
Proof.
  intros J EV C TRACE CHOICE. split; [eapply arbitrary_finite_history_preserves_invariant; eauto|].
  assert (FRAME : forall x, 2*sector<=x -> control_image (journal_control final) x=control_image (journal_control initial) x).
  { intros; eapply logged_trace_frame_after_journal; eauto. }
  destruct (logged_history_extension _ _ _ _ _ _ _ TRACE) as [prefix EXT].
  split.
  - eapply Forall_impl; [|exact (proj1 EV)]. intros c CERT.
    exact (proj1 (certificate_frame sector view ranges decode DIV CONTRACT initial final c CERT FRAME)).
  - split.
    + intros id H. destruct CHOICE as [SAME|NEW].
      * apply (proj1 (proj2 EV) id); congruence.
      * destruct C as [c [IN ID]]. exists c; split; [exact IN|]. apply Nat2N.inj; congruence.
    + rewrite EXT; apply receipts_extend; exact (proj2 (proj2 EV)).
Qed.

(* Even a finite, unfinished publication prefix transports the same evidence.
   No Ready/returned-error endpoint is required. *)
Theorem publication_prefix_evidence initial middle id d ram e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (initial,PublishingBoundary CandidatePrepared id d ram) e ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) initial middle ->
  logged_invariant sector 256 data_len boss_ok middle /\
  persistent_evidence sector view ranges decode middle e /\
  (hd_error (publications middle)=hd_error (publications initial) \/ hd_error (publications middle)=Some (N.of_nat id)) /\
  acknowledgements middle=acknowledgements initial.
Proof.
  intros [[JI CORE] [EV IN]] TRACE.
  destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ TRACE) as [CHOICE [ACK LOG]].
  destruct (journal_evidence_transport initial middle e (N.of_nat id) JI EV
    ltac:(exists (Certificate id d); split; [exact IN|reflexivity]) LOG CHOICE) as [JM EM].
  split; [exact JM|]. split; [exact EM|]. split; assumption.
Qed.

Theorem direct_publication_reset initial cut id d ram e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (initial,PublishingBoundary CandidatePrepared id d ram) e ->
  publication_reset_prefix g sector data_len boss_ok (N.of_nat id) initial cut ->
  (hd_error (publications cut)=hd_error (publications initial) \/ hd_error (publications cut)=Some (N.of_nat id)) /\
  acknowledgements cut=acknowledgements initial /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (cut,RebuildingBoundary Selecting) e /\
  episode_boot_post cut e.
Proof.
  intros [[JI CORE] [EV IN]] [before [PREFIX [BEFORE [STEP DEST]]]].
  destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX) as [H1 [A1 LOG]].
  destruct (cut_step_heads _ _ _ _ _ _ _ BEFORE STEP DEST) as [H2 A2].
  assert (CHOICE : hd_error (publications cut)=hd_error (publications initial) \/ hd_error (publications cut)=Some (N.of_nat id)).
  { destruct H1,H2; [left|right|right|right]; congruence. }
  assert (TRACE : clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok) initial cut).
  { eapply rt_trans; [exact LOG|apply rt_step; exact STEP]. }
  destruct (journal_evidence_transport initial cut e (N.of_nat id) JI EV
    ltac:(exists (Certificate id d); split; [exact IN|reflexivity]) TRACE CHOICE) as [JC EC].
  assert (ENTRY : enriched_invariant sector data_len boss_ok view marker ranges decode pages (cut,RebuildingBoundary Selecting) e).
  { split; [apply rebuilding_common; split; [exact JC|split; [apply reset_destination_recovers; exact DEST|exact I]]|split; [exact EC|exact I]]. }
  split; [exact CHOICE|]. split; [congruence|]. split; [exact ENTRY|apply boot_entry_post; exact ENTRY].
Qed.

(* Append returned, but client delivery has not happened. All represented RAM
   exit prefixes leave this journal untouched. No receipt is inserted here. *)
Theorem append_return_before_client_reset initial out slot pubs acks id d ram e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (initial,PublishingBoundary CandidatePrepared id d ram) e ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    initial (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id::acks)) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting) e /\
  episode_boot_post (Logged (Boot out) pubs (N.of_nat id::acks)) e.
Proof.
  intros [[JI CORE] [EV IN]] TRACE ACK.
  pose proof (successful_trace_is_logged _ _ _ _ _ _ _ _ TRACE) as LOG.
  pose proof (arbitrary_finite_history_preserves_invariant _ _ _ _ _ G DIV _ _ JI LOG) as AWAIT.
  assert (HEAD : hd_error pubs=Some (N.of_nat id)) by (exact (proj2 (proj1 (proj2 AWAIT)))).
  assert (ALL : clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok)
    initial (Logged (Boot out) pubs (N.of_nat id::acks))).
  { eapply rt_trans; [exact LOG|]. eapply rt_trans; [apply rt_step; exact ACK|].
    apply rt_step. apply (record_step g sector 256 data_len boss_ok); apply reset_ready. }
  destruct (journal_evidence_transport initial _ e (N.of_nat id) JI EV
    ltac:(exists (Certificate id d); split; [exact IN|reflexivity]) ALL ltac:(right; exact HEAD)) as [JB EB].
  assert (ENTRY : enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting) e).
  { split; [apply rebuilding_common; split; [exact JB|split; exact I]|split; [exact EB|exact I]]. }
  split; [exact ENTRY|apply boot_entry_post; exact ENTRY].
Qed.
Definition failure_phase old d resolved rolled :=
  if collection_enabled true (Some old) (Some old) rolled then
    match resolved with None => FatalBoundary | Some _ =>
      if protection_frozen (preparation_collection old resolved rolled)
      then FrozenBoundary (N.of_nat old) (N.of_nat old) None (preparation_collection old resolved rolled)
      else IdleBoundary old d (preparation_collection old resolved rolled) end
  else if protection_frozen rolled then FrozenBoundary (N.of_nat old) (N.of_nat old) None rolled
       else IdleBoundary old d rolled.

Lemma failed_return_shape old resolved saved termination reserved :
  writer_returned_error termination ->
  let final := preparation_collection old resolved (preparation_rollback saved termination reserved) in
  protection_current final ++ attached_ranges final = saved /\
  protection_saved final=[] /\ pending_preparation final=None /\
  protection_base final=protection_base reserved /\
  physical_authority final=physical_authority reserved /\
  acknowledged_authority final=acknowledged_authority reserved.
Proof.
  intros ERROR final. unfold final, preparation_collection.
  destruct (collection_enabled true (Some old) (Some old) (preparation_rollback saved termination reserved));
    [destruct resolved|]; destruct ERROR as [E|[E|E]]; subst termination;
    simpl; rewrite app_nil_r; repeat split; reflexivity.
Qed.

Lemma failed_writer_return_boundary old d s f h a e reserved saved result resolved :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (Logged (Ready f) h a,IdleBoundary old d s) e ->
  saved=protection_current s ++ attached_ranges s ->
  protection_base reserved=protection_base s -> physical_authority reserved=physical_authority s ->
  acknowledged_authority reserved=acknowledged_authority s ->
  preparation_failed_post g sector data_len boss_ok view marker ranges decode old d h a reserved saved result ->
  writer_returned_error (writer_end result) ->
  (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready (writer_flash result)) h a,
      failure_phase old d resolved (preparation_rollback saved (writer_end result) reserved))
    (evidence_with_live e [Certificate old d]).
Proof.
  intros [[JI [IDLE [FMT COR]]] [EV IN]] SAVED RB RP RA POST ERROR MASK.
  destruct POST as [J [READ [PREFIX [RI [RETURN REC]]]]].
  destruct (RETURN ERROR) as [DI [CUR [STACK [COVER [FREEZE [CLEAN COLLECT]]]]]].
  destruct (COLLECT resolved MASK) as [FI FP].
  destruct (failed_return_shape old resolved saved (writer_end result) reserved ERROR) as [FC [FS [FN [FB [PH ACK]]]]].
  destruct IDLE as [[I [F [S [P [C [B [A AA]]]]]]] [JI' [READY [HEAD LINK]]]].
  assert (BASE : protection_base (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)) = marker::root_extents (view old)) by congruence.
  assert (CURRENT : protection_current (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)) ++ attached_ranges (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)) = root_extents (view old)) by congruence.
  assert (ACKED : acknowledged_authority (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)) = root_extents (view old)) by congruence.
  assert (PE : persistent_evidence sector view ranges decode (Logged (Ready (writer_flash result)) h a)
    (evidence_with_live e [Certificate old d])).
  { split; [constructor; [split; assumption|constructor]|]. split; [|exact (proj2 (proj2 EV))].
    intros chosen H. change (hd_error h=Some (N.of_nat chosen)) in H.
    change (hd_error h=Some (N.of_nat old)) in HEAD.
    assert (chosen=old) by (apply Nat2N.inj; congruence). subst chosen; exists (Certificate old d); simpl; auto. }
  assert (HISTORY : protection_history_link view
    (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)) (Logged (Ready (writer_flash result)) h a)).
  { unfold protection_history_link; simpl. change (hd_error h=Some (N.of_nat old)) in HEAD.
    rewrite HEAD; simpl; rewrite Nat2N.id; exact FP. }
  assert (NORMAL : protection_frozen (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved))=false ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready (writer_flash result)) h a,IdleBoundary old d (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)))
    (evidence_with_live e [Certificate old d])).
  { intros NF. split; [apply journal_idle_common; [|exact FMT]|split; [exact PE|unfold boundary_certificate_link; simpl; auto]].
    split; [unfold idle_root; split; [exact FI|]; split; [exact NF|]; split; [exact FS|]; split; [exact FN|]; split; [exact CURRENT|]; split; [exact BASE|]; split; assumption|]. split; [exact J|]. split; [exists (writer_flash result); reflexivity|]. split; assumption. }
  assert (FROZEN : protection_frozen (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved))=true ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready (writer_flash result)) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) None (preparation_collection old resolved (preparation_rollback saved (writer_end result) reserved)))
    (evidence_with_live e [Certificate old d])).
  { intros FF. split; [|split; [exact PE|exact Logic.I]]. split; [exact J|].
    split; [exact FI|]. split; [exact FF|]. split; [exact HISTORY|]. split; [left; exact HEAD|].
    rewrite Nat2N.id. eapply protected_subset; [|exact (proj1 (proj1 (proj1 FI)))].
    intros r R. unfold required_ranges; repeat rewrite in_app_iff. right; right; left. rewrite FP.
    apply in_app_or in R; tauto. }
  unfold failure_phase. destruct (collection_enabled true (Some old) (Some old) (preparation_rollback saved (writer_end result) reserved)) eqn:ENABLE.
  - destruct resolved as [mask|].
    + destruct (protection_frozen (preparation_collection old (Some mask) (preparation_rollback saved (writer_end result) reserved))) eqn:FR; [apply FROZEN|apply NORMAL]; reflexivity.
    + split; [split; [exact J|exact Logic.I]|split; [exact PE|exact Logic.I]].
  - unfold preparation_collection in NORMAL,FROZEN; rewrite ENABLE in NORMAL,FROZEN.
    destruct (protection_frozen (preparation_rollback saved (writer_end result) reserved)) eqn:FR; [apply FROZEN|apply NORMAL]; reflexivity.
Qed.

Definition failed_writer_episode_post old d h a e reserved saved result :=
  preparation_failed_post g sector data_len boss_ok view marker ranges decode old d h a reserved saved result /\
  (forall resolved, writer_returned_error (writer_end result) ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (Logged (Ready (writer_flash result)) h a,failure_phase old d resolved (preparation_rollback saved (writer_end result) reserved))
      (evidence_with_live e [Certificate old d])) /\
  episode_boot_post (Logged (Boot (writer_flash result)) h a) (evidence_with_live e [Certificate old d]).

Lemma failed_writer_episode old d s f h a e reserved saved result :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (Logged (Ready f) h a,IdleBoundary old d s) e ->
  saved=protection_current s ++ attached_ranges s ->
  protection_base reserved=protection_base s -> physical_authority reserved=physical_authority s ->
  acknowledged_authority reserved=acknowledged_authority s ->
  preparation_failed_post g sector data_len boss_ok view marker ranges decode old d h a reserved saved result ->
  failed_writer_episode_post old d h a e reserved saved result.
Proof.
  intros START SAVED B PH ACK POST. split; [exact POST|]. split.
  - intros resolved ERROR MASK. eapply failed_writer_return_boundary; eauto.
  - intros final TRACE.
    pose proof (failed_writer_boot_evidence g sector data_len boss_ok view marker ranges decode topology pages
      G DIV CONTRACT old d s f h a e reserved saved result final START POST TRACE) as FINAL.
    split; [exact FINAL|]. intros jf chosen decoded restored EQ; subst final.
    exact (enriched_boot_usable sector data_len boss_ok view marker ranges decode pages jf chosen decoded restored _ FINAL).
Qed.
Definition publication_episode_post old id image index entry span s prepared ready old_decoded e :=
  let d := RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)) in
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (ready,PublishingBoundary CandidatePrepared id d prepared) e /\
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded /\
  (forall out slot pubs acks,
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    episode_boot_post (Logged (Boot out) pubs (N.of_nat id::acks)) e) /\
  (forall error_j commands,
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) ready error_j ->
    returned_error_control (journal_control error_j) ->
    let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
    data_calls commands (uncertain_return selected prepared) ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (error_j,FrozenBoundary (N.of_nat old) (N.of_nat id) None (execute_data commands (uncertain_return selected prepared))) e /\
    episode_boot_post (logged_after_reset error_j) e) /\
  (forall cut, publication_reset_prefix g sector data_len boss_ok (N.of_nat id) ready cut ->
    (hd_error (publications cut)=hd_error (publications ready) \/ hd_error (publications cut)=Some (N.of_nat id)) /\
    acknowledgements cut=acknowledgements ready /\
    enriched_invariant sector data_len boss_ok view marker ranges decode pages (cut,RebuildingBoundary Selecting) e /\
    episode_boot_post cut e) /\
  (forall middle,
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) ready middle ->
    logged_invariant sector 256 data_len boss_ok middle /\
    persistent_evidence sector view ranges decode middle e /\
    (hd_error (publications middle)=hd_error (publications ready) \/ hd_error (publications middle)=Some (N.of_nat id)) /\
    acknowledgements middle=acknowledgements ready).

Lemma publication_episode_compose old id image index entry span s prepared ready old_decoded e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (ready,PublishingBoundary CandidatePrepared id
      (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) prepared) e ->
  hd_error (publications ready)=Some (N.of_nat old) ->
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded ->
  publication_episode_post old id image index entry span s prepared ready old_decoded e.
Proof.
  intros PREP HEAD CONT. split; [exact PREP|]. split; [exact CONT|]. split.
  - intros out slot pubs acks TRACE ACK.
    exact (proj2 (append_return_before_client_reset ready out slot pubs acks id _ prepared e PREP TRACE ACK)).
  - split.
    + intros error_j commands TRACE ERROR selected CALL.
      pose proof (uncertain_cleanup_evidence g sector data_len boss_ok view marker ranges decode pages G DIV CONTRACT
        id _ prepared ready error_j commands e PREP (N.of_nat old) HEAD TRACE CALL) as FROZEN.
      split; [exact FROZEN|]. apply boot_entry_post.
      eapply enriched_reset; [exact G|exact DIV|exact CONTRACT|exact FROZEN|].
      apply returned_error_reset_step; exact ERROR.
    + split.
      * intros cut CUT. exact (direct_publication_reset ready cut id _ prepared e PREP CUT).
      * intros middle TRACE. exact (publication_prefix_evidence ready middle id _ prepared e PREP TRACE).
Qed.

(* One consumer for the complete writer outcome match. Only the second
   allocation's resource guards are requested after the first writer succeeds. *)
Definition data_episode_post data_writer boss_writer data_plan boss_plan
    old id d index entry span s f history acks e :=
  let dr := data_writer f span entry in
  let saved := protection_current s ++ attached_ranges s in
  writer_execution g sector span false f (data_plan f span entry) dr /\
  unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector (writer_flash dr)) /\
  match writer_end dr with
  | WriterComplete => forall
      (BF : free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)))
      (BE : erased_object_extent sector (writer_flash dr) (boss_extent (view id))),
      let br := boss_writer (writer_flash dr) id (image_replace (recovered_image d) index (Some entry)) in
      writer_execution g sector (boss_extent (view id)) true (writer_flash dr)
        (boss_plan (writer_flash dr) id (image_replace (recovered_image d) index (Some entry))) br /\
      unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector (writer_flash br)) /\
      match writer_end br with
      | WriterComplete => publication_episode_post old id (recovered_image d) index entry span s
          (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s)
          (Logged (Ready (writer_flash br)) history acks) d
          (evidence_with_live e [Certificate old d; Certificate id (RecoveryDecoding (boss_extent (view id))
            (image_replace (recovered_image d) index (Some entry)))])
      | _ => failed_writer_episode_post old d history acks e
          (boss_reservation_state view id ranges (recovered_image d) index entry span s) saved br
      end
  | _ => failed_writer_episode_post old d history acks e (data_reservation_state span s) saved dr
  end.

Theorem enriched_data_episode data_bytes data_writer boss_writer data_plan boss_plan
    old id d index entry span s f history acks e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
  erased_object_extent sector f span ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  data_episode_post data_writer boss_writer data_plan boss_plan old id d index entry span s f history acks e.
Proof.
  intros START RANGE FREE ERASED WRITERS.
  unfold data_episode_post.
  set (dr := data_writer f span entry).
  set (saved := protection_current s ++ attached_ranges s).
  destruct START as [[JI [IDLE [FMT COR]]] [EV IN]].
  assert (ENTRY : enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e).
  { split; [split; [exact JI|split; [exact IDLE|split; assumption]]|split; assumption]. }
  assert (READ : decode (object_flash sector f) old=Some d).
  { assert (C : certificate_valid sector view ranges decode (Logged (Ready f) history acks) (Certificate old d)).
    { eapply Forall_forall; [exact (proj1 EV)|exact IN]. } exact (proj1 C). }
  pose proof (preparation_outcomes_transaction g sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer data_plan boss_plan decode old id (recovered_image d) index entry span s f history acks d
    G DIV IDLE (eq_sym (proj2 FMT)) RANGE FREE ERASED WRITERS CONTRACT READ) as ALL.
  cbn zeta in ALL. fold dr in ALL. fold saved in ALL.
  destruct ALL as [DRUN [DKEEP REST]]. split; [exact DRUN|]. split; [exact DKEEP|].
  destruct (writer_end dr) eqn:DE;
    try (eapply failed_writer_episode; [exact ENTRY|reflexivity|reflexivity|reflexivity|reflexivity|exact REST]).
  intros BF BE. set (br := boss_writer (writer_flash dr) id (image_replace (recovered_image d) index (Some entry))). specialize (REST BF BE). cbn zeta in REST; fold br in REST. fold saved in REST.
  destruct REST as [BRUN [BKEEP REST]]. split; [exact BRUN|]. split; [exact BKEEP|].
  destruct (writer_end br) eqn:BRE;
    try (eapply failed_writer_episode; [exact ENTRY|reflexivity|reflexivity|reflexivity|reflexivity|exact REST]).
  assert (DS : successful_data_writer data_writer f span entry=Some (writer_flash dr)).
  { unfold successful_data_writer,successful_observation. change (match writer_end dr with WriterComplete=>Some (writer_flash dr)|_=>None end=Some (writer_flash dr)); rewrite DE; reflexivity. }
  assert (BS : successful_boss_writer boss_writer (writer_flash dr) id (image_replace (recovered_image d) index (Some entry))=Some (writer_flash br)).
  { unfold successful_boss_writer,successful_observation. change (match writer_end br with WriterComplete=>Some (writer_flash br)|_=>None end=Some (writer_flash br)); rewrite BRE; reflexivity. }
  pose proof (prepared_certificates sector data_len boss_ok view marker ranges decode pages CONTRACT
    data_bytes (successful_data_writer data_writer) (successful_boss_writer boss_writer)
    old id d index entry span s f (writer_flash dr) (writer_flash br) history acks e
    ENTRY RANGE FREE BF ERASED BE (writer_success_codec _ _ _ _ _ _ _ _ _ WRITERS) DS BS) as PREP.
  apply publication_episode_compose; [exact PREP| |exact REST].
  exact (proj1 (proj2 (proj2 (proj2 IDLE)))).
Qed.
(* The next operation receives only operation-specific resource/service guards;
   its structural and semantic entry conditions come from the previous boot. *)
Theorem boot_to_next_episode initial e f history acks old d ram
    data_bytes data_writer boss_writer data_plan boss_plan id index entry span :
  episode_boot_post initial e ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (initial,Selecting) (Logged (Ready f) history acks,Usable old d ram) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  data_episode_post data_writer boss_writer data_plan boss_plan old id d index entry span ram f history acks e.
Proof.
  intros BOOT TRACE RANGE FREE ERASED WRITERS.
  destruct (BOOT _ TRACE) as [PREFIX USE].
  destruct (USE _ _ _ _ eq_refl) as [ENTRY REST].
  eapply enriched_data_episode; eauto.
Qed.
Theorem client_to_next_episode f history acks old d ram e
    data_bytes data_writer boss_writer data_plan boss_plan id index entry span :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,ClientBoundary old d ram) e ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  data_episode_post data_writer boss_writer data_plan boss_plan old id d index entry span ram f history acks e.
Proof.
  intros CLIENT RANGE FREE ERASED WRITERS.
  destruct (enriched_client_next sector data_len boss_ok view marker ranges decode pages _ _ _ _ _ CLIENT) as [ENTRY REST].
  eapply enriched_data_episode; eauto.
Qed.
End Episode.
