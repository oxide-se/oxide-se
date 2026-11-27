From Stdlib Require Import List Arith NArith Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage CompactUpdates
  PreparedAuthority JournalHistory JournalRequests JournalReachableShape
  PublicationPreparation TransactionBoundary PersistentBoundary FreerPrepared FreerPublicationReturn.
Import ListNotations.

(* Observation fold of the existing exit program, not another transition
   relation. Only DurableRamWritten installs the decoded runtime fields. *)
Fixpoint runtime_exit_evidence j c phases e := match phases with
 | []=>e
 | DurableRamWritten::tail=>runtime_exit_evidence j c tail (synchronize_publication j c e)
 | _::tail=>runtime_exit_evidence j c tail e end.
Lemma runtime_exit_reset j c phases e :
 forget_volatile_evidence (runtime_exit_evidence j c phases e)=forget_volatile_evidence e.
Proof.
 revert e;induction phases;intro e;[reflexivity|].
 destruct a;cbn;rewrite IHphases;reflexivity.
Qed.
Lemma runtime_exit_receipts j c phases e :
 client_receipts (runtime_exit_evidence j c phases e)=client_receipts e.
Proof.
 revert e;induction phases;intro e;[reflexivity|].
 destruct a;cbn;rewrite IHphases;reflexivity.
Qed.

(* A ghost observation of the existing result, not a new firmware service.
   Stop is not a return, and neither case changes the physical history. *)
Definition client_return_evidence view j result e := match result with
  | ClientStopped => e
  | ClientReturned (DataClientSuccess id image) =>
      let c := Certificate id (RecoveryDecoding (boss_extent (view id)) image) in
      deliver_published j c (runtime_exit_evidence j c
        [SlotCompleted;DurableRamWritten;ExternalAccepted] (evidence_with_live e [c]))
  end.
Theorem stopped_no_receipt view j e : client_return_evidence view j ClientStopped e = e.
Proof. reflexivity. Qed.
Theorem return_adds_one_receipt view j reply e :
  length (client_receipts (client_return_evidence view j (ClientReturned reply) e)) =
    S (length (client_receipts e)).
Proof. destruct reply; reflexivity. Qed.

Theorem prepared_freer_client_boot g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready old_decoded e out slot pubs acks final reply :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  persistent_evidence sector view ranges decode ready e ->
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id :: acks)) ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id (protection_current s ++ attached_ranges s))
    (client_finish_program id (image_replace image index (Some entry))
      [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    (prepared_transaction_candidate view id ranges image index entry span s)
    (ClientReturned reply) final ->
  let j := Logged (Ready out) pubs (N.of_nat id :: acks) in
  reply = DataClientSuccess id (image_replace image index (Some entry)) /\
  client_restart_post g sector data_len boss_ok view marker ranges decode topology pages
    j id (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) final
    (client_return_evidence view j (ClientReturned reply) e).
Proof.
  intros G DIV CONTRACT E CONT TRACE ACK POST j.
  pose proof (prepared_client_return_matches view marker id ranges image index entry span s final reply POST) as MATCH.
  destruct (publication_success_boot g sector data_len boss_ok view marker ranges decode topology pages G DIV CONTRACT
    old id image index entry span s prepared ready old_decoded e out slot pubs acks E CONT TRACE ACK)
    as [RETURN BOOT].
  assert (R : reply = DataClientSuccess id (image_replace image index (Some entry))).
  { exact (f_equal snd MATCH). }
  assert (F : final = fst (finish_data_client view marker id ranges image index entry span s)).
  { exact (f_equal fst MATCH). }
  subst reply final. split; [reflexivity|exact BOOT].
Qed.

Theorem stopped_client_keeps_evidence sector data_len boss_ok view marker ranges decode pages
    j id d s e image saved final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary AppendReturned id d s) e ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id saved)
    (client_finish_program id image [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    s ClientStopped final ->
  protection_frozen final = true /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,FatalBoundary)
    (client_return_evidence view j ClientStopped e) /\
  client_receipts (client_return_evidence view j ClientStopped e) = client_receipts e.
Proof.
  intros INV POST. split; [eapply client_collection_failure_stops; exact POST|].
  split; [eapply enriched_fatal_view; exact INV|reflexivity].
Qed.

(* Both returned and stopped executions expose the synchronization BEFORE the
   external close and collection. Delivery does not choose the runtime value. *)
Theorem executed_client_runtime_prefix view marker id d saved j e s result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract view marker id saved)
   (client_finish_program id (recovered_image d) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   s result final ->
 let middle:=runtime_exit_evidence j (Certificate id d) [SlotCompleted;DurableRamWritten] e in
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract view marker id saved)
   (client_finish_program id (recovered_image d) [ExternalAccepted]))
   (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s))
   result final /\
 volatile_latest_registry middle=Some id /\
 volatile_counter middle=read_counter (counter_decoder e) (control_image (journal_control j)) id /\
 volatile_allocation middle=option_map (fun a=>AllocationRuntime (allocation_append a) (recovered_boss d)) (volatile_allocation e) /\
 client_receipts middle=client_receipts e /\
 forget_volatile_evidence middle=forget_volatile_evidence e.
Proof.
 intros RUN middle;split;[eapply client_finish_after_runtime;exact RUN|].
 repeat split;reflexivity.
Qed.
