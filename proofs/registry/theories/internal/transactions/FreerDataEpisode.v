From Stdlib Require Import List Arith NArith Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage CompactUpdates
  PreparedAuthority JournalHistory JournalRequests JournalReachableShape PublicationPreparation
  PreparationOutcomes BootReconstruction BootTransaction TransactionBoundary PersistentBoundary
  DataEpisode CollectionRoots FreerPrepared FreerPublicationReturn FreerPersistentBoundary.
Import ListNotations.

(* A prefix returns an internal service result, not a client success. Reset
   discards its RAM. There is deliberately no Drop/rollback in this program. *)
Definition collection_service_prefix : impure ClientFinishAPI (option (list extent)) :=
  request_then ClientCollect (fun resolved => local resolved).
Lemma collection_service_prefix_post view marker id saved s resolved final :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id saved) collection_service_prefix) s resolved final ->
  final = client_collection_next id resolved s.
Proof.
  intros H. simpl in H. unroll_post H.
  destruct H as [reply [middle [[CALL EQ] REST]]]. subst middle.
  unroll_post REST. destruct REST as [R S]. subst; reflexivity.
Qed.

Lemma collection_service_prefix_mask view marker id saved s resolved final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract view marker id saved) collection_service_prefix) s resolved final ->
 forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some id) (object_extents (view id)) [].
Proof.
 intros H. simpl in H;unroll_post H.
 destruct H as [reply [middle [[CALL EQ] REST]]].
 unroll_post REST;destruct REST as [R S];subst;exact CALL.
Qed.

Section Consumer.
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

Definition episode_client_post j boot id image final result e :=
  match result with
  | ClientReturned reply =>
      reply=DataClientSuccess id image /\
      client_restart_post g sector data_len boss_ok view marker ranges decode topology pages
        j id (RecoveryDecoding (boss_extent (view id)) image) final
        (client_return_evidence view j result e)
  | ClientStopped => protection_frozen final=true /\
      enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,FatalBoundary) e /\
      episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages boot e
  end.

(* This consumes the successful writer branch of enriched_data_episode. Neither
   decoding nor a certificate/coverage invariant is supplied anew. *)
Theorem episode_client_finish old id image index entry span s prepared ready old_decoded e
    out slot pubs acks final result :
  publication_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready old_decoded e ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id::acks)) ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id (protection_current s++attached_ranges s))
    (client_finish_program id (image_replace image index (Some entry))
      [SlotCompleted;DurableRamWritten;ExternalAccepted]))
    (prepared_transaction_candidate view id ranges image index entry span s) result final ->
  episode_client_post (Logged (Ready out) pubs (N.of_nat id::acks))
    (Logged (Boot out) pubs (N.of_nat id::acks)) id
    (image_replace image index (Some entry)) final result e.
Proof.
  intros [PREP [CONT [SUCCESS REST]]] TRACE ACK POST. destruct result as [reply|].
  - eapply prepared_freer_client_boot; eauto. exact (proj1 (proj2 PREP)).
  - split; [eapply client_collection_failure_stops; exact POST|].
    pose proof (SUCCESS _ _ _ _ TRACE ACK) as BOOT.
    split; [|exact BOOT].
    destruct (BOOT _ (rt_refl _ _ _)) as [[[JI PC] [EV LINK]] USE].
    split; [split; [exact JI|exact I]|split; [exact EV|exact I]].
Qed.

(* Prefixes of the represented RAM exit only: no fabricated reorderings. *)
Theorem episode_exit_prefix_reset old id image index entry span s prepared ready old_decoded e
    out slot pubs acks phases suffix partial :
  publication_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready old_decoded e ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id::acks)) ->
  phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    (exit_contract marker (root_extents (view id)) (protection_current s++attached_ranges s))
    (exit_program phases)) prepared tt partial ->
  partial=execute_exit marker (root_extents (view id)) (protection_current s++attached_ranges s) phases prepared /\
  episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
    (Logged (Boot out) pubs (N.of_nat id::acks)) e.
Proof.
  intros [PREP [CONT [SUCCESS REST]]] TRACE ACK PREFIX POST.
  split; [eapply exit_program_post; exact POST|exact (SUCCESS _ _ _ _ TRACE ACK)].
Qed.

Theorem episode_collection_prefix_reset old id image index entry span s prepared ready old_decoded e
    out slot pubs acks closed resolved partial :
  publication_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready old_decoded e ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id::acks)) ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    (exit_contract marker (root_extents (view id)) (protection_current s++attached_ranges s))
    (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) prepared tt closed ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id (protection_current s++attached_ranges s))
    collection_service_prefix) closed resolved partial ->
  closed=execute_exit marker (root_extents (view id)) (protection_current s++attached_ranges s)
    [SlotCompleted;DurableRamWritten;ExternalAccepted] prepared /\
  partial=client_collection_next id resolved closed /\
  episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
    (Logged (Boot out) pubs (N.of_nat id::acks)) e.
Proof.
  intros [PREP [CONT [SUCCESS REST]]] TRACE ACK EXIT COLLECT.
  split; [eapply exit_program_post; exact EXIT|].
  split; [eapply collection_service_prefix_post; exact COLLECT|exact (SUCCESS _ _ _ _ TRACE ACK)].
Qed.
(* Actual delivery is an additional execution premise, not inferred from the
   slot, writer success, or append acknowledgement. The other branches of the
   SAME writer match retain all the error/reset postconditions above. *)
Definition data_episode_delivery data_writer boss_writer old id d index entry span s (f : flash) h a e :=
  let dr := data_writer f span entry in
  match writer_end dr with
  | WriterComplete => forall
      (BF : free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)))
      (BE : erased_object_extent sector (writer_flash dr) (boss_extent (view id))),
      let br := boss_writer (writer_flash dr) id (image_replace (recovered_image d) index (Some entry)) in
      match writer_end br with
      | WriterComplete =>
          exit_calls marker (root_extents (view id)) (protection_current s++attached_ranges s)
            [SlotCompleted;DurableRamWritten;ExternalAccepted]
            (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s) /\
          collection_boundary view marker (Some id) (Some id) (object_extents (view id)) []
            (successful_external_close marker (root_extents (view id)) (protection_current s++attached_ranges s)
              (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s)) /\
          forall out slot pubs acks final result,
          clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
            (Logged (Ready (writer_flash br)) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
          logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
            (Logged (Ready out) pubs (N.of_nat id::acks)) ->
          post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
            (client_finish_contract view marker id (protection_current s++attached_ranges s))
            (client_finish_program id (image_replace (recovered_image d) index (Some entry))
              [SlotCompleted;DurableRamWritten;ExternalAccepted]))
            (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s) result final ->
          episode_client_post (Logged (Ready out) pubs (N.of_nat id::acks))
            (Logged (Boot out) pubs (N.of_nat id::acks)) id
            (image_replace (recovered_image d) index (Some entry)) final result
            (evidence_with_live e [Certificate old d;Certificate id (RecoveryDecoding (boss_extent (view id))
              (image_replace (recovered_image d) index (Some entry)))])
      | _ => True end
  | _ => True end.

Theorem enriched_data_episode_freer data_bytes data_writer boss_writer data_plan boss_plan
    old id d index entry span s f h a e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) h a,IdleBoundary old d s) e ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
  erased_object_extent sector f span ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  data_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    data_writer boss_writer data_plan boss_plan old id d index entry span s f h a e /\
  data_episode_delivery data_writer boss_writer old id d index entry span s f h a e.
Proof.
  intros ENTRY RANGE FREE ERASED WRITERS.
  pose proof (enriched_data_episode g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT data_bytes data_writer boss_writer data_plan boss_plan old id d index entry span s f h a e
    ENTRY RANGE FREE ERASED WRITERS) as EPISODE.
  split; [exact EPISODE|]. unfold data_episode_post in EPISODE. unfold data_episode_delivery.
  set (dr := data_writer f span entry) in *.
  destruct EPISODE as [RUN [FRAME CASE]]. destruct (writer_end dr); try exact I.
  intros BF BE. specialize (CASE BF BE).
  set (br := boss_writer (writer_flash dr) id (image_replace (recovered_image d) index (Some entry))) in *.
  destruct CASE as [BRUN [BFRAME PUB]]. destruct (writer_end br); try exact I.
  destruct (proj1 ENTRY) as [J0 [IDLE [OLD IMAGE]]].
  destruct (proj1 (proj1 PUB)) as [JP [PI [NF [PENDING [FORMAT OTHER]]]]].
  destruct (prepared_client_callers view marker old id ranges (recovered_image d) index entry span s
    (proj1 IDLE) (eq_sym (proj2 OLD)) RANGE FREE BF (eq_sym (proj2 FORMAT))) as [CALL COLLECT].
  split; [exact CALL|]. split; [exact COLLECT|].
  intros out slot pubs acks final result TRACE ACK POST.
  eapply episode_client_finish; eauto.
Qed.
End Consumer.
