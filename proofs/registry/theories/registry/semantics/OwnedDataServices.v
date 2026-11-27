From Stdlib Require Import List Arith NArith Lia Relation_Operators Bool.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FreerRecyclingErase RecycledWriter FreerRawBoundary
 FreerGlobalDataTrace FreerAdmittedTrace RecyclingErase RecyclingEraseBoundary RawNeutralizationBoundary
 JournalRawOrder JournalHistory JournalReachableShape JournalRequests Neutralization NeutralizationBoundary
 RecyclingSearch PreparedAuthority PreparationOutcomes PublicationPreparation RetentionCoverage
 CollectionRoots TransactionBoundary PersistentBoundary DataEpisode BootReconstruction BootTransaction FlashSpec CompactImage CompactUpdates PageOwnership.
From OxideSE.Registry Require Import AllocationAdmission FreerPrepared FreerPublicationReturn FreerDataEpisode.
From OxideSE.Registry Require Import PreAppendValidation FreerPreAppend.
(* Explicit supplier dependencies; historical modules re-export the same definitions. *)
From OxideSE.Registry Require Import BossDecodingContract DecodedGeometryContract
 IncarnationReaderContract BossEncodingContract BossValidationContract.
Import ListNotations.

From OxideSE.Registry Require Import OwnedDataTypes OwnedDataResponses OwnedDataInvariant OwnedDataRequirements OwnedDataOffered IncarnationBoundary.
Import ListNotations.
Section Extracted.
Variable g:geometry.
Variable sector:nat.
Variable data_len:N.
Variable marker:extent.
Variable ranges:compact_entry->list extent.
Variable decode:flash->nat->option recovery_decoding.
Variable topology:recovery_decoding->bool.
Variable pages:nat.
Variable validate:flash->N->bool.
Variable runtime_kind:list N->nat.
Variable argument_key:nat->object_key.
Variable argument_plan:nat->extent->list writer_command.
Local Notation Safe v o := (boundary_safe sector data_len v o marker ranges decode pages).
Local Notation Trace := (episode_trace g sector data_len marker ranges decode topology pages).
Local Notation owner_invariants := (owner_invariants sector data_len marker ranges decode pages).
Local Notation controller_result_post := (controller_result_post g sector data_len marker ranges decode topology pages).

Definition owned_local_evidence old d s e :=
 let armed:=controller_evidence ArmOwned (IdleBoundary old d s) e in
 controller_evidence OpenLocal (OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)) armed.

Definition acquisition_pc ending := match ending with
 | NeutralSuccess => BodyWriting | NeutralError => BodyFailed
 | NeutralReset | NeutralFatal => BodyInterrupted end.

Definition preparation_pc ending := match ending with
 | WriterComplete => BodyPrepared | WriterInterrupted => BodyInterrupted
 | _ => BodyFailed end.

Inductive owned_body_edge : owned_body_pc -> list nat -> (N->bool) ->
 (nat->root_view) -> execution_boundary -> list owned_attachment ->
 owned_body_pc -> list nat -> (N->bool) -> (nat->root_view) -> execution_boundary -> Prop :=
| body_start valid view x i todo :
 owned_body_edge BodyWaiting (i::todo) valid view x []
   BodyAcquiring (i::todo) valid view x
| body_numeric_refused valid view f h a image root s e i todo :
 pending_preparation s=None -> operation_payload_rejection sector f h a image root s e ->
 (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
  outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
 owned_body_edge BodyAcquiring (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   BodyFailed (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)
| body_search_refused valid view f h a image root s e i todo fuel recognize req round alignment start reply word_max :
 pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
  outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
 runtime_search_inputs sector pages word_max e s f req start ->
 owned_body_edge BodyAcquiring (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   BodyFailed (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)
| body_search_stopped valid view f h a image root s e i todo fuel shape verify req round alignment start target fatal word_max :
 pending_preparation s=None ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table s) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 runtime_search_inputs sector pages word_max e s f req start ->
 owned_body_edge BodyAcquiring (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   BodyInterrupted (i::todo) valid view
   (if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
    else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e))
| body_erased valid view j image root s e i todo r :
 pending_preparation s=None ->
 runtime_erased_admission sector pages e s (control_image (journal_control j)) r ->
 owned_body_edge BodyAcquiring (i::todo) valid view ((j,OperationBoundary image root s),e) []
   BodyWriting (i::todo) valid view ((j,OperationBoundary image root (reservation_state false r s)),advance_allocation_evidence r e)
| body_recycled valid view f h a old previous image root s e i todo
 recognize magic fuel req round alignment start r count result word_max :
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 recognizer_local sector recognize -> pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 runtime_search_inputs sector pages word_max e s f req start ->
 owned_body_edge BodyAcquiring (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (acquisition_pc (neutral_end_ result)) (i::todo) (validate (neutral_flash result)) view
   (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)),
    phase_evidence (snd (operation_acquisition_boundary old image root s h a result
      (block_pages (recycle_lo r) (useful_pages r)))) (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e)))
| body_written valid view f h a old previous image root s e i todo p plan result :
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 pending_writer_run g sector s p false f plan result -> prep_kind p=ObjectPreparation ->
 plan=argument_plan i (prep_range p) ->
 owned_body_edge BodyWriting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (preparation_pc (writer_end result)) (i::todo) (validate (writer_flash result)) view
   (operation_writer_exit old image root s h a result,
    phase_evidence (snd (operation_writer_exit old image root s h a result)) (selected_evidence old previous e))
| body_attached valid view j image root s e i todo p index entry :
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 nth_error image index<>Some (Some entry) ->
 owned_body_edge BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e)
   [OwnedAttachment i index entry] BodyWaiting todo valid view
   ((j,OperationBoundary (image_replace image index (Some entry)) []
     (exact_attach ranges image index entry (data_next DataWritten s))),e)
| body_identical valid view j image root s e i todo p index entry :
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 nth_error image index=Some (Some entry) ->
 owned_body_edge BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e)
   [OwnedAttachment i index entry] BodyWaiting todo valid view
   ((j,OperationBoundary image root (identical_attach_state s)),e)
| body_attach_rejected valid view j image root s e i todo p :
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 prepared_local_rejection runtime_kind image (argument_key i) (prep_range p) ->
 owned_body_edge BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e) []
   BodyFailed (i::todo) valid view ((j,OperationBoundary image root s),body_error_evidence e)
| body_reset_reserved valid view j phase e i todo :
 logged_step g sector 256 data_len valid j (logged_after_reset j) ->
 owned_body_edge BodyWriting (i::todo) valid view ((j,phase),e) []
   BodyInterrupted (i::todo) valid view
   ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e)
| body_reset_prepared valid view j phase e i todo :
 logged_step g sector 256 data_len valid j (logged_after_reset j) ->
 owned_body_edge BodyPrepared (i::todo) valid view ((j,phase),e) []
   BodyInterrupted (i::todo) valid view
   ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e)
| body_request_abort valid view j image root s e todo :
 controller_caller RequestAbort (OperationBoundary image root s) (controller_read e) ->
 owned_body_edge BodyWaiting todo valid view ((j,OperationBoundary image root s),e) []
   BodyWaiting todo valid view
   ((j,OperationBoundary image root s),controller_evidence RequestAbort (OperationBoundary image root s) e)
| body_done valid view x :
 owned_body_edge BodyWaiting [] valid view x [] BodyFinished [] valid view x.

Inductive owned_body_run : owned_body_pc -> list nat -> (N->bool) ->
 (nat->root_view) -> execution_boundary -> list owned_attachment ->
 owned_body_pc -> list nat -> (N->bool) -> (nat->root_view) -> execution_boundary -> Prop :=
| body_nil pc todo valid view x : owned_body_run pc todo valid view x [] pc todo valid view x
| body_cons pc todo vi oi x log mid rest vm om y logs last tail vf of_ z :
 owned_body_edge pc todo vi oi x log mid rest vm om y ->
 owned_body_run mid rest vm om y logs last tail vf of_ z ->
 owned_body_run pc todo vi oi x (log++logs) last tail vf of_ z.

Definition owned_error_observation (x:execution_boundary) :=
 match snd (fst x) with
 | OperationBoundary _ root _ => Some (false,root)
 | FrozenBoundary _ _ (Some root) _ => Some (true,root)
 | _=>None end.

Definition owned_restore_reply (old:nat) (view:nat->root_view) x read inspect check outcome :=
 match owned_error_observation x with
 | None=>True
 | Some (frozen,current) =>
   if frozen then
    ((root_address current=root_address [boss_extent (view old)] /\ outcome=RestoreValidated) \/
     (root_address current<>root_address [boss_extent (view old)] /\
      post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract read inspect check) restore_probe) tt outcome tt))
   else
    ((current=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
     (current<>[boss_extent (view old)] /\
      post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract read inspect check) restore_probe) tt outcome tt))
 end.

Definition owned_restore_cut_guard (old:nat) (view:nat->root_view) x read inspect check point :=
 match owned_error_observation x with
 | None=>False
 | Some (frozen,current) =>
   (if frozen then root_address current<>root_address [boss_extent (view old)]
    else current<>[boss_extent (view old)]) /\
   restore_cut_reached read inspect check point
 end.

Definition marked_boss_requested result pc (final:execution_boundary) :=
 match result,pc,snd (fst final) with
 | PairSelected (_::_),BodyFinished,OperationBoundary image root ram=>
   negb (abort_requested (controller_read (snd final))) &&
   phase_dirty (OpenBoundary image root
     (data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram))
 | _,_,_=>false end.

Definition marked_selected_boundary (final:execution_boundary) :=
 match final with
 | ((j,OperationBoundary image root ram),ev)=>
   let accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram in
   let taken:=controller_evidence (TakeLocal true) (OperationBoundary image root ram) ev in
   let closed:=controller_evidence LocalClosed (OpenBoundary image root accepted) taken in
   ((j,OpenBoundary image root accepted),controller_evidence SelectFinish (OpenBoundary image root accepted) closed)
 | _=>final end.

Definition boss_search_inputs word_max total e s f req start :=
 exists a,volatile_allocation e=Some a /\
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector (pages*256) (fun _=>Some total) (allocation_append a) f)
   (probe_cursor_checked word_max)) s ProbeMiss s /\
 req=search_requirement word_max (fun _=>Some total) /\
 start=Nat.min word_max (extent_end (allocation_latest a))/256.

Definition boss_erased_admission word_max total e s f r :=
 (exists a final,volatile_allocation e=Some a /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
     (cursor_contract sector (pages*256) (fun _=>Some total) (allocation_append a) f)
     probe_cursor) s (Some r) final /\ pages<=1024) \/
 (exists fuel recognize req round alignment start i n,
   boss_search_inputs word_max total e s f req start /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundErased i n /\
   r=block_pages i n /\ pages<=1024).

Definition append_services valid view f h a id d s reply :=
 (exists out slot pubs acks,
   clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) /\
   logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
     (Logged (Ready out) pubs (N.of_nat id::acks)) /\
   ((exists final delivered,reply=AppendFinishReply delivered (pred (length pubs)) /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
       (client_finish_contract view marker id (List.hd [] (protection_saved s)))
       (client_finish_program id (recovered_image d) [ExternalAccepted]))
       (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s))
       (if delivered then ClientReturned (DataClientSuccess id (recovered_image d)) else ClientStopped) final) \/
    (exists point:runtime_sync_point, reply=AppendSyncCutReply point) \/
    (exists phases suffix partial,reply=AppendExitCutReply phases /\ phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program phases)) s tt partial) \/
    (exists closed resolved partial,reply=AppendCollectionCutReply resolved /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) s tt closed /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
       (client_finish_contract view marker id (List.hd [] (protection_saved s)))
       collection_service_prefix) closed resolved partial))) \/
 (exists error_j read inspect check outcome,reply=AppendRestoreReply outcome /\
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j /\ returned_error_control (journal_control error_j) /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt) \/
 (reply=AppendPhysicalCutReply /\ exists cut,publication_reset_prefix g sector data_len valid (N.of_nat id) (Logged (Ready f) h a) cut) \/
 (exists error_j read inspect check point,reply=AppendRestoreCutReply point /\
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j /\ returned_error_control (journal_control error_j) /\
   restore_cut_reached read inspect check point).

Definition cleanup_response observed resolved cut :=
 match cut with Some point=>CleanupInterrupted point | None=>CleanupReturned observed resolved end.

Definition restoration_services_at view old response :=
 exists rd ins chk observed resolved (cut:option RestoreCut),
 response=cleanup_response observed resolved cut /\
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) /\
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []).

Definition generated_candidate_ram s r counter :=
 install_candidate_observed (image_generation_set (N.succ (counter_value counter))
   (remember_recovered_boss pages r (snapshot_rehome (length (protection_saved s)) (snapshot_written s)))).

Inductive validation_service_response :=
| ValidationRejectedReply (reason:boss_check_error) (cleanup:cleanup_service_response)
| ValidationAcceptedReply (generation:N) (reply:append_service_reply)
| ValidationInterruptedReply (prefix:list boss_check_event).

Definition validation_services_at read view f h a id d s old response :=
 match response with
 | ValidationRejectedReply reason cleanup=>exists observe after,
   boss_check_provider read observe /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
     (boss_check_contract observe) (boss_check_program id true)) f (BossCheckFailed reason) after /\
   restoration_services_at view old cleanup
 | ValidationAcceptedReply generation reply=>exists observe after,
   boss_check_provider read observe /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
     (boss_check_contract observe) (boss_check_program id true)) f (BossCheckReady generation) after /\
   append_services (validate after) view after h a id d s reply
 | ValidationInterruptedReply prefix=>exists observe,boss_check_cut true (observe f id) prefix
 end.

Definition prebody_response entry pc outcome resolved cut :=
 match pair_prepass_return entry with
 | Some _=>EntryResponse entry
 | None=>BeforeBossResponse pc (cleanup_response outcome resolved cut) end.

Definition local_cleanup_mask pc final outcome (resolved:option (list extent)) (cut:option RestoreCut) : option (list extent) :=
 match pc,owned_error_observation final,outcome,resolved,cut with
 | BodyFailed,Some(false,_),RestoreValidated,Some mask,None=>Some mask
 | _,_,_,_,_=>None end.

Definition indexed_prebody_response entry pc final outcome resolved cut :=
 match pair_prepass_return entry with
 | Some _=>EntryResponse entry
 | None=>match local_cleanup_mask pc final outcome resolved cut with
   | Some mask=>LocalBodyCleanupResponse mask
   | None=>prebody_response entry pc outcome resolved cut end end.

Definition validation_response_owner id decoded response :=
 match response with
 | ValidationRejectedReply reason cleanup=>ValidationFailureResponse reason cleanup
 | ValidationAcceptedReply _ reply=>AppendResponse id decoded reply
 | ValidationInterruptedReply prefix=>ValidationCutResponse prefix end.

Definition restoration_services_for (Q:cleanup_service_response->Prop) view old :=
 exists reply,restoration_services_at view old reply /\ Q reply.

Definition writer_tail_services_for (Q:owner_service_response->Prop) view h a old s read counter r result :=
 match writer_end result with
 | WriterComplete=>(exists point:preparation_ram_cut,Q (PreparationCutResponse point)) \/
   (forall decoded encoded,read (writer_flash result) (offset r)=Some (decoded,encoded) ->
     exists response,validation_services_at read
       (install_decoded_view view ranges (offset r) decoded) (writer_flash result) h a
       (offset r) decoded (generated_candidate_ram s r counter) old response /\
       Q (validation_response_owner (offset r) decoded response))
 | WriterLocalError | WriterRetainError | WriterPhysicalError=>
   restoration_services_for (fun reply=>Q (WriterFailureResponse (writer_end result) reply)) view old
 | WriterInterrupted=>Q WriterInterruptedResponse end.

Definition recycling_cleanup_response reply :=
 match reply with CleanupReturned observed _=>CleanupReturned observed None
 | CleanupInterrupted point=>CleanupInterrupted point end.

Definition boss_writer_services_for (Q:owner_service_response->Prop) view f h a old image s read counter r :=
 exists encode plan result,
 boss_generation_format g sector encode read /\
 checked_boss_plan encode image counter r=Some plan /\
 writer_execution g sector r true f plan result /\
 writer_tail_services_for Q view h a old s read counter r result.

Definition boss_acquisition_services_for (Q:owner_service_response->Prop) word_max total view f h a old image s e counter :=
 (exists cursor probe_final,
   option_map allocation_append (volatile_allocation e)=Some cursor /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
     (cursor_contract sector (pages*256) (fun _=>Some total) cursor f)
     (probe_cursor_checked word_max)) s ProbeRejected probe_final /\
   restoration_services_for (fun reply=>Q (AcquisitionResponse 0 reply)) view old) \/
 (exists fuel recognize req round alignment start reply,
   boss_search_inputs word_max total e s f req start /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply /\
   (reply=SearchMiss \/ reply=SearchError) /\ restoration_services_for (fun reply=>Q (AcquisitionResponse 1 reply)) view old) \/
 (exists fuel shape verify req round alignment start target fatal,
   boss_search_inputs word_max total e s f req start /\
   reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
     f (protection_table s) req round alignment pages start target /\
   recognition_interruption shape verify f target fatal /\ Q (SearchInterruptedResponse fatal)) \/
 (exists span,
   boss_erased_admission word_max total e s f span /\
   ((boss_writer_services_for Q view f h a old image (reservation_state true span s)
       (counter_decoder e) counter span) \/ (exists point:acquisition_ram_point,Q (AcquisitionCutResponse point)))) \/
 (exists recognize magic fuel req round alignment start r nsectors recycled,
   recognizer_local sector recognize /\
   boss_search_inputs word_max total e s f req start /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r /\
   erase_geometry g sector r nsectors /\ recycling_run g sector recognize magic r nsectors f recycled /\
   match neutral_end_ recycled with
   | NeutralSuccess=>
     boss_writer_services_for Q view (neutral_flash recycled) h a old image
       (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)
       (counter_decoder e) counter (block_pages (recycle_lo r) (useful_pages r)) \/
       (exists point:acquisition_ram_point,Q (AcquisitionCutResponse point))
   | NeutralError=>restoration_services_for (fun reply=>Q (AcquisitionResponse 2 (recycling_cleanup_response reply))) view old
   | NeutralFatal=>Q (RecyclingInterruptedResponse NeutralFatal)
   | NeutralReset=>Q (RecyclingInterruptedResponse NeutralReset)
   end).

Definition boss_pipeline_services_for (Q:owner_service_response->Prop) word_max view f h a old image s e :=
 match boss_size_preflight word_max image with
 | BossLengthRejected=>restoration_services_for (fun reply=>Q (PreflightResponse 0 reply)) view old
 | BossScratchRejected _=>restoration_services_for (fun reply=>Q (PreflightResponse 1 reply)) view old
 | BossSizeReady total=>forall counter,volatile_counter e=Some counter ->
   match boss_checked_generation (counter_value counter) with
   | None=>restoration_services_for (fun reply=>Q (PreflightResponse 2 reply)) view old
   | Some _=>boss_acquisition_services_for Q word_max total view f h a old image s e counter
   end
 end.

Definition owned_nonentry_services_for (Q:owner_service_response->Prop) word_max valid view f h a old d s e (result:pair_prepass_result) :=
 exists count same compare log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut),
post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt /\
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) /\
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) /\
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) /\
 (local_cleanup_mask pc final outcome resolved cut=None -> forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   (marked_boss_requested result pc final=true -> vo=vf /\ oo=of_ /\
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)=marked_selected_boundary final) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services_for Q word_max oo ff h aa old image ram ev) /\
 (marked_boss_requested result pc final=false -> Q (indexed_prebody_response result pc final outcome resolved cut)).

Definition owned_call_services_for (Q:owner_service_response->Prop)
 word_max valid view f h a old d s e result :=
 match pair_prepass_return result with
 | Some _=>exists count same compare,
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
     (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt /\
   Q (EntryResponse result)
 | None=>owned_nonentry_services_for Q word_max valid view f h a old d s e result end.

Inductive owned_service_schedule (word_max:nat) : nat -> list (owner_service_response->Prop) -> (N->bool) -> (nat->root_view) -> execution_boundary -> Prop :=
| schedule_stop n valid view state : owned_service_schedule word_max n [] valid view state
| schedule_call n requests (Q:owner_service_response->Prop) valid view f h a old d s e result :
    owned_call_services_for Q word_max valid view f h a old d s e result ->
    (forall (receipts:list client_receipt) vo oo reached (exit:operation_exit) (response:owner_service_response),
      completed_operation g sector data_len marker ranges decode topology pages
        valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
      controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
      owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
      owner_response_matches response exit -> Q response -> owner_reply_ready response reached ->
      prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
      owned_service_schedule word_max n requests vo oo reached) ->
    owned_service_schedule word_max (S n) (Q::requests) valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
| schedule_resume n requests valid view j id d ram e :
    owned_service_schedule word_max n requests valid view ((j,IdleBoundary id d ram),e) ->
    owned_service_schedule word_max (S n) requests valid view ((j,ClientBoundary id d ram),e)
| schedule_reset n requests valid view j phase e :
    logged_step g sector 256 data_len valid j (logged_after_reset j) ->
    owned_service_schedule word_max n requests valid view
      ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e) ->
    owned_service_schedule word_max (S n) requests valid view ((j,phase),e)
| schedule_boot n requests valid view j e recovered id d ram :
    clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
      (j,Selecting) (recovered,Usable id d ram) ->
    owned_service_schedule word_max n requests valid view
      ((recovered,IdleBoundary id d ram),recovered_page_evidence recovered id (forget_volatile_evidence e)) ->
    owned_service_schedule word_max (S n) requests valid view
      ((j,RebuildingBoundary Selecting),forget_volatile_evidence e).

Definition owned_data_executions word_max n requests (Q:owner_service_response->Prop)
 valid view f h a old d s e result : Prop :=
 owned_call_services_for Q word_max valid view f h a old d s e result /\
  (forall receipts vo oo reached exit response,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
      owner_response_matches response exit -> Q response -> owner_reply_ready response reached ->
   prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max n requests vo oo reached).

End Extracted.
