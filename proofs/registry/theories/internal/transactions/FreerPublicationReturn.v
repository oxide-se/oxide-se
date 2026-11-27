From Stdlib Require Import List.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import PublicationPreparation PreparedAuthority
  FreerPrepared CollectionRoots RetentionCoverage.
Import ListNotations.

(* Internal control result. ClientStopped is a terminal panic/fatal branch,
   not an Err returned to a caller that may continue. No reset is a reply. *)
Inductive client_completion := ClientReturned (reply : data_client_result) | ClientStopped.
Inductive ClientFinishAPI : interface :=
| ClientExit : PublicationExitPhase -> ClientFinishAPI unit
| ClientCollect : ClientFinishAPI (option (list extent)).
Section Finish.
Variable view : nat -> root_view.
Variable marker : extent.
Variable id : nat.
Variable image : list CompactImage.compact_slot.
Variable saved : list extent.
Definition client_collection_next resolved s := match resolved with
  | Some mask => collection_return 256 true (Some id) (Some id) (Some mask) s
  | None => data_next DataFreeze s end.
Definition client_finish_caller s A (e : ClientFinishAPI A) := match e with
  | ClientExit p => exit_caller marker (root_extents (view id)) saved p s
  | ClientCollect => collection_boundary view marker (Some id) (Some id)
      (object_extents (view id)) [] s end.
Definition client_finish_callee (s : protection_state) A (e : ClientFinishAPI A) : A -> Prop := match e with
  | ClientExit _ => fun _ => True
  | ClientCollect => fun resolved => forall mask, resolved = Some mask ->
      mask = collect_ranges view marker (Some id) (object_extents (view id)) [] end.
Definition client_finish_update s A (e : ClientFinishAPI A) : A -> protection_state := match e with
  | ClientExit p => fun _ => exit_next marker (root_extents (view id)) saved p s
  | ClientCollect => fun resolved => client_collection_next resolved s end.
Definition client_finish_contract := make_contract client_finish_update client_finish_caller client_finish_callee.
Definition completion (resolved : option (list extent)) := match resolved with
  | Some _ => ClientReturned (DataClientSuccess id image)
  | None => ClientStopped end.
Fixpoint client_finish_program phases : impure ClientFinishAPI client_completion := match phases with
  | [] => request_then ClientCollect (fun resolved => local (completion resolved))
  | p :: tail => request_then (ClientExit p) (fun _ => client_finish_program tail) end.

Lemma client_finish_post phases s result final :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    client_finish_contract (client_finish_program phases)) s result final ->
  exists resolved,
    result = completion resolved /\
    final = client_collection_next resolved (execute_exit marker (root_extents (view id)) saved phases s) /\
    (forall mask, resolved = Some mask -> mask = collect_ranges view marker (Some id) (object_extents (view id)) []).
Proof.
  revert s result final. induction phases as [|p tail IH]; intros s result final H.
  - simpl in H. unroll_post H.
    destruct H as [reply [middle [[CALL EQ] REST]]]. subst middle.
    unroll_post REST. destruct REST as [R S]. subst result final. exists reply. split; [reflexivity|]. split; [reflexivity|exact CALL].
  - simpl in H. unroll_post H.
    destruct H as [reply [middle [[CALL EQ] REST]]]. subst middle.
    apply IH in REST. exact REST.
Qed.

(* Expose executed intermediate states of the existing service, including a
   terminal collection failure. This does not assume a successful suffix. *)
Lemma client_finish_uncons phase tail s result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program (phase::tail))) s result final ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program tail))
   (exit_next marker (root_extents (view id)) saved phase s) result final.
Proof.
 intro RUN;cbn [client_finish_program] in RUN;unroll_post RUN.
 destruct H as [middle [[CALL EQ] REST]];subst middle;exact REST.
Qed.
Theorem client_finish_after_runtime s result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   s result final ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program [ExternalAccepted]))
   (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s))
   result final.
Proof.
 intro RUN;apply client_finish_uncons in RUN;apply client_finish_uncons in RUN;exact RUN.
Qed.

(* Forward composition: the supplied service starts at the synchronized RAM
   state. The two preceding deterministic effects are enabled by derived
   callers; neither append nor delivery is replayed by this continuation. *)
Lemma client_finish_cons phase tail s result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program tail))
   (exit_next marker (root_extents (view id)) saved phase s) result final ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program (phase::tail))) s result final.
Proof.
 intro RUN;cbn [client_finish_program].
 exists tt,(exit_next marker (root_extents (view id)) saved phase s).
 split;[split;[exact I|reflexivity]|exact RUN].
Qed.
Theorem client_finish_from_runtime s result final :
 exit_calls marker (root_extents (view id)) saved
   [SlotCompleted;DurableRamWritten;ExternalAccepted] s ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program [ExternalAccepted]))
   (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s))
   result final ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   client_finish_contract (client_finish_program [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   s result final.
Proof. intros CALL RUN;apply client_finish_cons;apply client_finish_cons;exact RUN. Qed.

Theorem client_success_only_after_close_collection s final reply :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    client_finish_contract (client_finish_program [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    s (ClientReturned reply) final ->
  reply = DataClientSuccess id image /\ final = finish_collected view marker id saved s.
Proof.
  intros H. apply client_finish_after_runtime in H. apply client_finish_post in H.
  destruct H as [resolved [RETURN [FINAL MASK]]]. destruct resolved as [mask|]; simpl in RETURN; try discriminate.
  inversion RETURN; subst reply. specialize (MASK mask eq_refl). subst mask.
  split; [reflexivity|exact FINAL].
Qed.

Theorem client_collection_failure_stops s final :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    client_finish_contract (client_finish_program [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    s ClientStopped final -> protection_frozen final = true.
Proof.
  intros H. apply client_finish_after_runtime in H. apply client_finish_post in H.
  destruct H as [resolved [RETURN [FINAL MASK]]]. destruct resolved; simpl in RETURN; try discriminate.
  subst final; reflexivity.
Qed.
End Finish.

(* Link the impure return sequence to the continuation actually consumed by
   prepared_publication_client_or_uncertain; no independent final state. *)
Theorem prepared_client_return_matches view marker id ranges image index entry span initial final reply :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
    (client_finish_contract view marker id (protection_current initial ++ attached_ranges initial))
    (client_finish_program id (CompactUpdates.image_replace image index (Some entry))
      [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    (prepared_transaction_candidate view id ranges image index entry span initial)
    (ClientReturned reply) final ->
  (final, reply) = finish_data_client view marker id ranges image index entry span initial.
Proof.
  intros H. apply client_success_only_after_close_collection in H.
  destruct H as [R S]. subst reply final. reflexivity.
Qed.

Theorem prepared_client_callers view marker old id ranges image index entry span s :
  idle_root view marker old s ->
  object_extents (view old) = CompactUpdates.image_dependencies ranges image ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges image index entry span s)) (boss_extent (view id)) ->
  object_extents (view id) = CompactUpdates.image_dependencies ranges (CompactUpdates.image_replace image index (Some entry)) ->
  let prepared := prepared_transaction_candidate view id ranges image index entry span s in
  let saved := protection_current s ++ attached_ranges s in
  exit_calls marker (root_extents (view id)) saved [SlotCompleted; DurableRamWritten; ExternalAccepted] prepared /\
  collection_boundary view marker (Some id) (Some id) (object_extents (view id)) []
    (successful_external_close marker (root_extents (view id)) saved prepared).
Proof.
  intros IDLE OLD RANGE FREE BFREE ENC prepared saved.
  destruct (transaction_candidate_context view marker old id ranges image index entry span s
    IDLE OLD RANGE FREE BFREE ENC) as [MI [PI [P [CUR REST]]]].
  destruct IDLE as [I [F [STACK [P0 [C [BASE OTHER]]]]]].
  split.
  - apply successful_exit_callers; try reflexivity.
    + change (protection_saved s ++ [saved] = [saved]). rewrite STACK; reflexivity.
    + change (In marker (protection_base s)). rewrite BASE; simpl; auto.
    + exact CUR.
  - apply successful_close_boundary; exact CUR.
Qed.

(* Rust 87537f2: finalization and API observations are NOT durable receipts.
   These pure adapters observe an already returned result. A panic/reset has
   no value of finalization_result and does not execute either adapter. *)
Inductive finalization_result := RetainedResult | AbortedResult | FinalizationError.
Inductive operation_observation (A E:Type) :=
| OperationValue (value:A)
| OperationProvisional (value:A)
| OperationError (error:E)
| OperationInvalidState.
Arguments OperationValue {A E} _.
Arguments OperationProvisional {A E} _.
Arguments OperationError {A E} _.
Arguments OperationInvalidState {A E}.
Definition observe_retained_or_aborted {A E} owns (value:A) (failure:E) result : operation_observation A E :=
 if owns then match result with
 | RetainedResult => OperationValue value
 | AbortedResult => OperationInvalidState
 | FinalizationError => OperationError failure
 end else OperationProvisional value.
Definition successful_status (sw1:nat) := (Nat.eqb sw1 144 || Nat.eqb sw1 97)%bool.
Definition observe_apdu {A} result (payload:list A) sw1 sw2 error1 error2 :=
 match result with
 | RetainedResult => (payload,sw1,sw2)
 | AbortedResult => if successful_status sw1 then ([],105,133) else ([],sw1,sw2)
 | FinalizationError => ([],error1,error2)
 end.
Lemma owned_aborted_is_invalid A E (value:A) (failure:E) :
 observe_retained_or_aborted true value failure AbortedResult=OperationInvalidState.
Proof. reflexivity. Qed.
Lemma joined_success_is_provisional A E (value:A) (failure:E) result :
 observe_retained_or_aborted false value failure result=OperationProvisional value.
Proof. reflexivity. Qed.
Lemma aborted_apdu_no_payload_or_success A (payload:list A) sw1 sw2 error1 error2 :
 let observed:=observe_apdu AbortedResult payload sw1 sw2 error1 error2 in
 fst (fst observed)=[] /\ successful_status (snd (fst observed))=false /\
 (successful_status sw1=false -> observed=([],sw1,sw2)).
Proof.
 unfold observe_apdu;destruct (successful_status sw1) eqn:STATUS;cbn.
 - split;[reflexivity|]. split;[reflexivity|discriminate].
 - split;[reflexivity|]. split;[exact STATUS|reflexivity].
Qed.
Lemma retained_apdu_unchanged A (payload:list A) sw1 sw2 error1 error2 :
 observe_apdu RetainedResult payload sw1 sw2 error1 error2=(payload,sw1,sw2).
Proof. reflexivity. Qed.
Lemma failed_finalization_apdu A (payload:list A) sw1 sw2 error1 error2 :
 observe_apdu FinalizationError payload sw1 sw2 error1 error2=([],error1,error2).
Proof. reflexivity. Qed.
