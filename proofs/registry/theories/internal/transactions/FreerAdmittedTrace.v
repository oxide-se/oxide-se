From Stdlib Require Import List Arith NArith Lia Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage ScopeOwnership CompactImage CompactUpdates
  CollectionRoots PreparedAuthority JournalHistory JournalRequests JournalReachableShape JournalRecoveryTrace
  PublicationPreparation PreparationOutcomes BootReconstruction BootTransaction TransactionBoundary
  PersistentBoundary DataEpisode PublicationResetWitness JournalAppendAuthority FreerPrepared FreerPublicationReturn FreerPersistentBoundary FreerDataEpisode AllocationAdmission FreerAllocationAdmission FreerGlobalDataTrace.
Import ListNotations.


From OxideSE.Registry Require Export FreerAllocationAdmission.

Section Admitted.
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
Variable data_bytes : compact_entry -> nat -> N.
Variable data_writer : flash -> extent -> compact_entry -> writer_observation.
Variable boss_writer : flash -> nat -> list compact_slot -> writer_observation.
Variable data_plan : flash -> extent -> compact_entry -> list writer_command.
Variable boss_plan : flash -> nat -> list compact_slot -> list writer_command.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8=0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.
Hypothesis WRITERS : outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode.

Inductive admitted_execution old id d index entry span s f h a e :
    option client_receipt -> execution_boundary -> Prop :=
| admitted_data_error resolved :
    writer_returned_error (writer_end (data_writer f span entry)) ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    admitted_execution old id d index entry span s f h a e None
      (collected_failure old d (Logged (Ready f) h a,data_reservation_state span s)
        (protection_current s++attached_ranges s) (data_writer f span entry) resolved (advance_allocation_evidence span e))
| admitted_data_reset : writer_end (data_writer f span entry)=WriterInterrupted ->
    admitted_execution old id d index entry span s f h a e None
      ((Logged (Boot (writer_flash (data_writer f span entry))) h a,RebuildingBoundary Selecting),forget_volatile_evidence (old_evidence old d e))
| admitted_boss_error resolved :
    writer_end (data_writer f span entry)=WriterComplete ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_returned_error (writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))) ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    admitted_execution old id d index entry span s f h a e None
      (collected_failure old d (Logged (Ready f) h a,boss_reservation_state view id ranges (recovered_image d) index entry span s)
        (protection_current s++attached_ranges s)
        (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))) resolved (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e)))
| admitted_boss_reset :
    writer_end (data_writer f span entry)=WriterComplete ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterInterrupted ->
    admitted_execution old id d index entry span s f h a e None
      ((Logged (Boot (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a,
        RebuildingBoundary Selecting),forget_volatile_evidence (old_evidence old d e))
| admitted_prepared_execution event next :
    writer_end (data_writer f span entry)=WriterComplete ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterComplete ->
    publication_execution g sector data_len boss_ok view marker ranges old id (recovered_image d) index entry span s
      (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s)
      (Logged (Ready (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a)
      (prepared_evidence view old id d index entry (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e))) event next ->
    admitted_execution old id d index entry span s f h a e event next.


Lemma admitted_execution_refines old id d index entry span s f h a e event next :
  admitted_execution old id d index entry span s f h a e event next ->
  reserved_execution g sector data_len boss_ok view marker ranges pages data_writer boss_writer
    old id d index entry span s f h a e event next.
Proof.
  intro RUN; destruct RUN.
  - apply data_error; assumption.
  - apply data_reset; assumption.
  - destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ H0)) as [FREE ERASED].
    eapply boss_error; eauto using erased_admission_numeric, runtime_erased_admission_forget.
  - destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ H0)) as [FREE ERASED].
    eapply boss_reset; eauto using erased_admission_numeric, runtime_erased_admission_forget.
  - destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ H0)) as [FREE ERASED].
    eapply prepared_execution; eauto using erased_admission_numeric, runtime_erased_admission_forget.
Qed.
End Admitted.
(* An operational simulation for rejection AFTER Data attachment but BEFORE
   BOSS reservation. The same successful Data commands end with a local error;
   rollback below proves this has the SAME resulting RAM, not the same source
   program. It neither erases reached flash nor invents a BOSS reservation. *)
Definition reject_completed (r : writer_observation) :=
  match writer_end r with
  | WriterComplete => WriterObservation (writer_flash r) (writer_prefix r) WriterLocalError
  | _ => r end.
Lemma reject_completed_execution g sector r boss f plan result :
  writer_execution g sector r boss f plan result ->
  writer_execution g sector r boss f plan (reject_completed result).
Proof.
  intro RUN; induction RUN; try (simpl; constructor; assumption).
  - pose proof (writer_successful_command g sector r boss f c tail after
      (reject_completed result) H H0 IHRUN) as W.
    destruct result as [rf rp re]; destruct re; exact W.
Qed.
Lemma reject_completed_not_success result :
  successful_observation (reject_completed result)=None.
Proof. destruct result as [f prefix [| | | |]]; reflexivity. Qed.
Lemma rejected_data_contracts g sector view bytes dw bw dp bp decode :
  outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
  outcome_writer_contracts g sector view bytes
    (fun f r e => reject_completed (dw f r e)) bw dp bp decode.
Proof.
  intros [D B [DF DE BF BR]]. constructor; [intros; apply reject_completed_execution; apply D|exact B|].
  constructor.
  - intros f r e f' ERASED SUCCESS. unfold successful_data_writer in SUCCESS.
    rewrite reject_completed_not_success in SUCCESS; discriminate.
  - intros f r e f' ERASED SUCCESS. unfold successful_data_writer in SUCCESS.
    rewrite reject_completed_not_success in SUCCESS; discriminate.
  - exact BF.
  - exact BR.
Qed.
Definition rejected_boss_rollback ranges image index entry r s :=
  data_next (DataClose [] (protection_current s++attached_ranges s) false)
    (modified_transaction ranges image index entry r s).
Lemma rejected_boss_rollback_same ranges image index entry r s :
  protection_saved s=[] ->
  rejected_boss_rollback ranges image index entry r s =
    preparation_rollback (protection_current s++attached_ranges s) WriterLocalError
      (data_reservation_state r s).
Proof.
  intro STACK.
  unfold rejected_boss_rollback, modified_transaction, exact_member, exact_attach,
    replace_current_dependencies, preparation_rollback, preparation_error_state,
    snapshot_error, data_reservation_state, execute_data.
  cbn [data_next set_phase prep_range prep_phase pending_preparation protection_table
    protection_saved change_preparation protection_frozen protection_current
    protection_base context_scopes attached_ranges protection_bits protection_dirty].
  rewrite STACK. cbn.
  assert (TABLE : finish_table 1 false (reserve_extent 256 r 1 (protection_table s)) =
    finish_table 1 false (release_extent 256 r (reserve_extent 256 r 1 (protection_table s)))).
  { apply boolp.functional_extensionality_dep; intro p.
    unfold finish_table, release_extent, reserve_extent.
    destruct (touches 256 r p); reflexivity. }
  rewrite TABLE. reflexivity.
Qed.

(* Exact checked-add rejection in align_up(required,256); unlike a probe
   miss this returns Persistence before any allocation command. word_max is
   supplied by the local usize-conversion contract, not a safety hypothesis. *)
Definition alignment_rejected (required_at : nat -> option nat) cursor word_max :=
  exists n, required_at cursor=Some n /\ word_max < n+255.

(* Local arithmetic observations, supplied by the format/usize services.
   size_of is evaluated on the ACTUAL post-attachment image. Counter values
   are observations of runtime mutation_counter, not identities of offsets. *)
Definition boss_precheck_error image (size_of : list compact_slot -> option nat) generation :=
  size_of image=None \/
  (exists total, size_of image=Some total /\ 4096 < total) \/
  generation = Nat.pred (Nat.pow 2 32).
Definition boss_refusal image size_of generation req cursor word_max :=
  boss_precheck_error image size_of generation \/ alignment_rejected req cursor word_max.

Section GlobalAdmission.
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
Hypothesis DIV : sector mod 8=0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.
Local Notation Safe := (boundary_safe sector data_len boss_ok view marker ranges decode pages).

(* A refinement of the existing A11 edge relation on the SAME boundaries.
   Only resource premises are replaced. No destination invariant occurs here. *)
Inductive erased_episode_step : execution_boundary -> option client_receipt -> execution_boundary -> Prop :=
| erased_run bytes dw bw dp bp old id d index entry span s f h a e event next :
    outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
    ranges entry=[span] ->
    runtime_erased_admission sector pages e (data_next DataBegin s) f span ->
    admitted_execution g sector data_len boss_ok view marker ranges pages dw bw
      old id d index entry span s f h a e event next ->
    erased_episode_step ((Logged (Ready f) h a,IdleBoundary old d s),e) event next
| erased_boss_rejected bytes dw bw dp bp old d index entry span s f h a e size_of generation req word_max resolved :
    outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
    ranges entry=[span] -> runtime_erased_admission sector pages e (data_next DataBegin s) f span ->
    writer_end (dw f span entry)=WriterComplete ->
    boss_refusal (image_replace (recovered_image d) index (Some entry)) size_of generation
      req (offset span + RetentionCoverage.span span) word_max ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    erased_episode_step ((Logged (Ready f) h a,IdleBoundary old d s),e) None
      ((Logged (Ready (writer_flash (dw f span entry))) h a,
        failure_phase old d resolved (rejected_boss_rollback ranges (recovered_image d) index entry span s)),phase_evidence (snd ((Logged (Ready (writer_flash (dw f span entry))) h a,
        failure_phase old d resolved (rejected_boss_rollback ranges (recovered_image d) index entry span s)))) (old_evidence old d (advance_allocation_evidence span e)))
| erased_frozen_refusal j old candidate current ram e : protection_frozen ram=true ->
    erased_episode_step ((j,FrozenBoundary old candidate current ram),e) None
      ((j,FrozenBoundary old candidate current ram),e)
| erased_frozen_continue j old candidate current ram e commands : data_calls commands ram ->
    erased_episode_step ((j,FrozenBoundary old candidate current ram),e) None
      ((j,FrozenBoundary old candidate (opaque_frozen_root current commands) (execute_data commands ram)),e)
| erased_client_resume j id d ram e :
    erased_episode_step ((j,ClientBoundary id d ram),e) None ((j,IdleBoundary id d ram),e)
| erased_reset_boundary j phase e :
    logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
    erased_episode_step ((j,phase),e) None ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence (e))
| erased_run_boot initial final e :
    clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) initial final ->
    erased_episode_step ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) None
      ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))
| erased_boot_resume j id d ram e :
    erased_episode_step ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence (e)) None ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e))
| erased_boot_stop j e :
    erased_episode_step ((j,RebuildingBoundary Stopped),forget_volatile_evidence (e)) None ((j,FatalBoundary),forget_volatile_evidence (e)).


(* Non-writing edges need no fictitious writer run. A provider exists as a
   local component contract; it is used only to inject those edges into A11. *)
Variable idle_bytes : compact_entry -> nat -> N.
Variable idle_dw : flash -> extent -> compact_entry -> writer_observation.
Variable idle_bw : flash -> nat -> list compact_slot -> writer_observation.
Variable idle_dp : flash -> extent -> compact_entry -> list writer_command.
Variable idle_bp : flash -> nat -> list compact_slot -> list writer_command.
Hypothesis IDLE_WRITERS : outcome_writer_contracts g sector view idle_bytes idle_dw idle_bw idle_dp idle_bp decode.
Lemma erased_step_refines x event y : Safe x -> erased_episode_step x event y ->
  stationary_episode_step g sector data_len boss_ok view marker ranges decode topology pages x event y.
Proof.
  intros SAFE RUN; destruct RUN.
  - destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ H1)) as [FREE ERASED].
    eapply execute_services; [exact CONTRACT|exact H|]. eapply run_reserved; eauto using erased_admission_numeric, runtime_erased_admission_forget.
    eapply admitted_execution_refines; eauto.
  - destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ H1)) as [FREE ERASED].
    assert (STACK : protection_saved s=[]).
    { exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj1 SAFE))))))). }
    rewrite (rejected_boss_rollback_same ranges (recovered_image d) index entry span s STACK).
    eapply execute_services; [exact CONTRACT|exact (rejected_data_contracts _ _ _ _ _ _ _ _ _ H)|].
    assert (OBS : reject_completed (dw f span entry)=
      WriterObservation (writer_flash (dw f span entry)) (writer_prefix (dw f span entry)) WriterLocalError).
    { unfold reject_completed; rewrite H2; reflexivity. }
    assert (ERR : writer_returned_error (writer_end (reject_completed (dw f span entry)))).
    { rewrite OBS; left; reflexivity. }
    pose proof (data_error g sector data_len boss_ok view marker ranges
      pages (fun f r e => reject_completed (dw f r e)) bw old old d index entry span s f h a e resolved ERR H4) as RUN.
    cbn beta in RUN. unfold collected_failure in RUN. rewrite OBS in RUN.
    eapply run_reserved; [exact H0|exact FREE|exact ERASED|exact RUN|eapply erased_admission_numeric; eapply runtime_erased_admission_forget;exact H1|exact H1].
  - destruct current as [observed|].
    + eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|].
      change (boundary_step g sector data_len boss_ok view marker ranges decode topology pages idle_dw idle_bw
        ((j,FrozenBoundary old candidate (Some observed) ram),e) None
        ((j,FrozenBoundary old candidate (Some observed) (execute_data [] ram)),e)).
      apply frozen_continue with (commands:=[]); exact I.
    + eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|].
      change (boundary_step g sector data_len boss_ok view marker ranges decode topology pages idle_dw idle_bw
        ((j,FrozenBoundary old candidate None ram),e) None
        ((j,FrozenBoundary old candidate None (execute_data [] ram)),e)).
      apply frozen_continue with (commands:=[]); exact I.
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply frozen_continue; assumption].
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply client_resume].
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply reset_boundary; assumption].
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply run_boot; assumption].
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply boot_resume].
  - eapply execute_services; [exact CONTRACT|exact IDLE_WRITERS|apply boot_stop].
Qed.
Inductive erased_episode_trace : execution_boundary -> list client_receipt -> execution_boundary -> Prop :=
| erased_nil x : erased_episode_trace x [] x
| erased_cons x event y events z : erased_episode_step x event y -> erased_episode_trace y events z ->
    erased_episode_trace x (events++emitted_receipts event) z.
Lemma erased_trace_refines x events y : Safe x -> erased_episode_trace x events y ->
  stationary_episode_trace g sector data_len boss_ok view marker ranges decode topology pages x events y.
Proof.
  intros INIT RUN; induction RUN; [apply episodes_nil|].
  pose proof (erased_step_refines _ _ _ INIT H) as STEP.
  eapply episodes_cons; [exact STEP|]. apply IHRUN.
  exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
    G DIV _ _ _ _ _ _ _ INIT STEP)).
Qed.
Lemma erased_emission_delivery x event y :
 erased_episode_step x event y -> forall r, event=Some r -> actual_client_delivery view marker r.
Proof.
 intros RUN r EQ; destruct RUN; try discriminate.
 eapply reserved_emission_is_delivery; [eapply admitted_execution_refines;exact H2|exact EQ].
Qed.
Theorem a11_erased_allocations_safety initial events final :
  Safe initial -> erased_episode_trace initial events final ->
  Safe final /\ boundary_receipts final=events++boundary_receipts initial /\
  Forall (receipt_valid view ranges (publications (boundary_journal final))) (boundary_receipts final) /\
  Forall (actual_client_delivery view marker) events.
Proof.
  intros INIT TRACE.
  pose proof (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
    G DIV _ _ _ _ _ _ _ INIT (erased_trace_refines _ _ _ INIT TRACE)) as [LAST [RECEIPTS [VALID DELIVERY]]].
  split; [exact LAST|]. split; [exact RECEIPTS|]. split; [exact VALID|].
  clear INIT LAST RECEIPTS VALID DELIVERY. induction TRACE; [constructor|].
  apply Forall_app; split; [exact IHTRACE|]. destruct event as [r|]; [|constructor].
  constructor; [eapply erased_emission_delivery; [exact H|reflexivity]|constructor].
Qed.
Theorem admitted_episode_success_durable initial events j id d ram e later jf chosen decoded restored ef :
  Safe initial -> erased_episode_trace initial events ((j,ClientBoundary id d ram),e) ->
  erased_episode_trace ((j,ClientBoundary id d ram),e) later ((jf,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (ef)) ->
  publications jf=publications j ->
  chosen=id /\ decoded=d /\ data_caller DataBegin restored /\
  unchanged (certificate_ranges ranges (Certificate id d))
    (object_flash sector (control_image (journal_control j)))
    (object_flash sector (control_image (journal_control jf))).
Proof.
  intros INIT PREFIX SUFFIX HIST.
  pose proof (proj1 (a11_erased_allocations_safety _ _ _ INIT PREFIX)) as MID.
  pose proof (erased_trace_refines _ _ _ INIT PREFIX) as P.
  pose proof (erased_trace_refines _ _ _ MID SUFFIX) as S.
  eapply episode_success_durable; [exact G|exact DIV|exact INIT|exact P|exact S|exact HIST].
Qed.
Theorem admitted_episode_before_publication initial events j id d ram e later jf chosen decoded restored ef :
  Safe initial -> erased_episode_trace initial events ((j,IdleBoundary id d ram),e) ->
  erased_episode_trace ((j,IdleBoundary id d ram),e) later ((jf,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (ef)) ->
  publications jf=publications j ->
  chosen=id /\ decoded=d /\ data_caller DataBegin restored.
Proof.
  intros INIT PREFIX SUFFIX HIST.
  pose proof (proj1 (a11_erased_allocations_safety _ _ _ INIT PREFIX)) as MID.
  pose proof (erased_trace_refines _ _ _ INIT PREFIX) as P.
  pose proof (erased_trace_refines _ _ _ MID SUFFIX) as S.
  eapply episode_before_publication; [exact G|exact DIV|exact INIT|exact P|exact S|exact HIST].
Qed.
Theorem admitted_episode_next_begin initial events j id d ram e :
  Safe initial -> erased_episode_trace initial events ((j,IdleBoundary id d ram),e) ->
  data_caller DataBegin ram /\
  Safe ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e).
Proof.
  intros INIT TRACE.
  pose proof (erased_trace_refines _ _ _ INIT TRACE) as RUN.
  eapply episode_next_begin; [exact G|exact DIV|exact INIT|exact RUN].
Qed.
Theorem admitted_episode_uncertain_no_hybrid f h a root initial_decoded initial_ram initial_e events
    j phase old before candidate after receipts later jf chosen decoded ram ef :
  Safe ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) ->
  erased_episode_trace ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) events
    ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) ->
  erased_episode_trace ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) later
    ((jf,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (ef)) ->
  publications jf=publications j ->
  ((chosen=old /\ decoded=before) \/ (chosen=candidate /\ decoded=after)) /\ data_caller DataBegin ram.
Proof.
  intros INIT PREFIX SUFFIX HIST.
  pose proof (proj1 (a11_erased_allocations_safety _ _ _ INIT PREFIX)) as MID.
  pose proof (erased_trace_refines _ _ _ INIT PREFIX) as P.
  pose proof (erased_trace_refines _ _ _ MID SUFFIX) as S.
  eapply episode_uncertain_no_hybrid; [exact G|exact DIV|exact INIT|exact P|exact S|exact HIST].
Qed.

Theorem admitted_next_episode_prefixes initial events f h a old d ram e id index entry span bytes dw bw dp bp :
  Safe initial -> erased_episode_trace initial events ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
  ranges entry=[span] -> runtime_erased_admission sector pages e (data_next DataBegin ram) f span ->
  outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
  data_episode_post g sector data_len boss_ok view marker ranges decode topology pages dw bw dp bp old id d index entry span ram f h a e /\
  data_episode_delivery g sector data_len boss_ok view marker ranges decode topology pages dw bw old id d index entry span ram f h a e.
Proof.
  intros INIT TRACE RANGE ADMIT WRITERS.
  destruct (erased_admission_guards _ _ _ _ (runtime_erased_admission_forget _ _ _ _ _ _ ADMIT)) as [FREE ERASED].
  pose proof (erased_trace_refines _ _ _ INIT TRACE) as RUN.
  eapply episode_prefixes; [exact G|exact DIV|exact CONTRACT|exact INIT|exact RUN|exact RANGE|exact FREE|exact ERASED|exact WRITERS].
Qed.

Theorem boss_admission_rejection_safe bytes dw bw dp bp old d index entry span s f h a e
    size_of generation req word_max resolved :
  Safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
  outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
  ranges entry=[span] -> runtime_erased_admission sector pages e (data_next DataBegin s) f span ->
  writer_end (dw f span entry)=WriterComplete -> boss_refusal (image_replace (recovered_image d) index (Some entry)) size_of generation
      req (offset span + RetentionCoverage.span span) word_max ->
  (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
  let final := ((Logged (Ready (writer_flash (dw f span entry))) h a,
    failure_phase old d resolved (rejected_boss_rollback ranges (recovered_image d) index entry span s)),phase_evidence (snd ((Logged (Ready (writer_flash (dw f span entry))) h a,
    failure_phase old d resolved (rejected_boss_rollback ranges (recovered_image d) index entry span s)))) (old_evidence old d (advance_allocation_evidence span e))) in
  Safe final /\ boundary_receipts final=client_receipts e /\
  publications (boundary_journal final)=h /\
  control_image (journal_control (boundary_journal final))=writer_flash (dw f span entry).
Proof.
  intros INIT W R DA COMPLETE REJECT MASK final.
  assert (STEP : erased_episode_step ((Logged (Ready f) h a,IdleBoundary old d s),e) None final).
  { unfold final. eapply erased_boss_rejected; eauto. }
  pose proof (erased_step_refines _ _ _ INIT STEP) as RUN.
  split; [exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
    G DIV _ _ _ _ _ _ _ INIT RUN))|]. repeat split; reflexivity.
Qed.

(* Concatenation uses the result of the first trace; no second invariant input. *)
Theorem erased_traces_append x events y more z :
  erased_episode_trace x events y -> erased_episode_trace y more z ->
  erased_episode_trace x (more++events) z.
Proof.
  intros P Q; induction P.
  - rewrite app_nil_r; exact Q.
  - rewrite app_assoc. eapply erased_cons; [exact H|apply IHP; exact Q].
Qed.
End GlobalAdmission.
