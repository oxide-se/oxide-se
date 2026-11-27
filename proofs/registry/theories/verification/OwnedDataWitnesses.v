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
From OxideSE.Registry Require Import FreerRecycledWriter IncarnationBoundary.

Section OwnerWitnesses.
Variable g:geometry.
Variable sector:nat.
Variable data_len:N.
Variable marker:extent.
Variable ranges:compact_entry->list extent.
Variable decode:flash->nat->option recovery_decoding.
Variable topology:recovery_decoding->bool.
Variable pages:nat.
Variable validate:flash->N->bool.
Hypothesis G:journal_geometry g sector 256.
Hypothesis DIV:sector mod 8=0.
Hypothesis ACCEPT:validator_accepts_decoded sector decode validate.
(* A local reader law for each actual decoded incarnation, not a fixed view. *)
Hypothesis READERS:forall c,incarnation_reader_local ranges decode c.
Variable runtime_kind : list N -> nat.
Variable argument_key : nat -> object_key.
Variable argument_plan : nat -> extent -> list writer_command.

Local Notation owner_invariants := (owner_invariants sector data_len marker ranges decode pages).
Local Notation controller_result_post := (controller_result_post g sector data_len marker ranges decode topology pages).
Local Notation owner_safe := (owner_safe sector data_len marker ranges decode pages).
Local Notation Trace := (episode_trace g sector data_len marker ranges decode topology pages).
Local Notation owned_body_run := (owned_body_run g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation boss_pipeline_services_for := (boss_pipeline_services_for g sector data_len marker ranges pages validate).
Local Notation owned_call_services_for := (owned_call_services_for g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation owned_service_schedule := (owned_service_schedule g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_call := (schedule_call g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_resume := (schedule_resume g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_reset := (schedule_reset g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_boot := (schedule_boot g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation owned_calls_from_idle := (owned_calls_from_idle g sector data_len marker ranges decode topology pages validate G DIV ACCEPT READERS runtime_kind argument_key argument_plan).
Local Notation owned_services_from_finished_body := (owned_services_from_finished_body g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation owned_services_from_local_failed_body := (owned_services_from_local_failed_body g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation owned_pair_entry_return := (owned_pair_entry_return g sector data_len marker ranges decode topology pages G DIV).

Lemma response_requests_two_exact first second responses :
 Forall2 (fun (predicate:owner_service_response->Prop) response=>predicate response)
   [eq first;eq second] responses -> responses=[first;second].
Proof.
 intro RUN;inversion RUN;subst;clear RUN.
 match goal with H:Forall2 _ [_] _ |- _=>inversion H;subst;clear H end.
 match goal with H:Forall2 _ [] _ |- _=>inversion H;subst;clear H end.
 reflexivity.
Qed.
Lemma unchanged_published_exits id decoded stamp exits :
 Forall2 owner_response_matches
   [EntryResponse (PairSelected []);AppendResponse id decoded (AppendFinishReply true stamp)] exits ->
 exits=[ReturnedEntry true;ReturnedPublished (Receipt stamp (Certificate id decoded))].
Proof.
 intro RUN;inversion RUN;subst;clear RUN.
 match goal with H:Forall2 _ [_] _ |- _=>inversion H;subst;clear H end.
 match goal with H:Forall2 _ [] _ |- _=>inversion H;subst;clear H end.
 repeat match goal with H:owner_response_matches _ _ |- _=>cbn [owner_response_matches pair_prepass_return append_reply_exit] in H end.
 subst;reflexivity.
Qed.

(* The second premise contains only executed local services: it does not
   contain a completed_operation, a destination invariant or a safe suffix.
   Its singleton response index fixes the replies of those executions.
   The unchanged first call uses only its prepass; no BOSS callback is asked. *)
Theorem owned_unchanged_then_published word_max base (checked:bool)
 valid view f h a old d s e count same compare result2 id decoded stamp :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected []) tt ->
 owned_call_services_for (eq (AppendResponse id decoded (AppendFinishReply true stamp)))
   word_max valid view f h a old d s e result2 ->
 exists vf of_ final,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
     ((Logged (Ready f) h a,IdleBoundary old d s),e) (ReturnedEntry true) /\
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp (Certificate id decoded)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=Receipt stamp (Certificate id decoded)::client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp (Certificate id decoded)] /\
 exists exits responses,
 exits=[ReturnedEntry true;ReturnedPublished (Receipt stamp (Certificate id decoded))] /\
 responses=[EntryResponse (PairSelected []);AppendResponse id decoded (AppendFinishReply true stamp)] /\
 Forall2 owner_response_matches responses exits /\
 delivered_observations exits=[RetainedResult;RetainedResult] /\
 delivered_receipt_log exits=[Receipt stamp (Certificate id decoded)].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED ENTRY SECOND.
 assert (FIRST:owned_call_services_for (eq (EntryResponse (PairSelected [])))
   word_max valid view f h a old d s e (PairSelected [])).
 { exists count,same,compare;split;[exact ENTRY|reflexivity]. }
 assert (NEXT:forall receipts vo oo reached exit response,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
   owner_response_matches response exit -> EntryResponse (PairSelected [])=response -> owner_reply_ready response reached ->
   prepass_completion_matches (PairSelected []) valid vo view oo
     ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max 1 [eq (AppendResponse id decoded (AppendFinishReply true stamp))] vo oo reached).
 { intros receipts vo oo reached exit response DONE POST INV' EXACT MATCH INDEX REPLY_READY PREPASS.
   cbn [prepass_completion_matches pair_prepass_return] in PREPASS.
   destruct PREPASS as [V [O [STATE EXIT]]];subst vo oo reached.
   eapply schedule_call;[exact SECOND|intros;constructor]. }
 destruct (owned_calls_from_idle word_max base checked 1
   [eq (AppendResponse id decoded (AppendFinishReply true stamp))]
   (eq (EntryResponse (PairSelected []))) valid view f h a old d s e (PairSelected [])
   HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED FIRST NEXT)
   as [vf [of_ [final [exits [responses [PATH [LAST [NUMBER [CONTROL [RECEIPTS [VALID [HIST [ORDER [PREFIX [MATCH [INDICES EXACT]]]]]]]]]]]]]]]].
 pose proof (response_requests_two_exact _ _ _ INDICES) as RESPONSES;subst responses.
 pose proof (unchanged_published_exits _ _ _ _ MATCH) as EXITS;subst exits.
 cbn [delivered_receipt_log delivered_receipts] in PATH,RECEIPTS,HIST.
 destruct CLOSED as [OUT ARM].
 destruct (owned_pair_entry_return valid view (Logged (Ready f) h a) old d s e count same compare
   (PairSelected []) true word_max MARK DEC WORD GEO (owner_safe _ _ _ INV) OUT ARM ENTRY eq_refl)
   as [DONE [POST OTHER]].
 exists vf,of_,final;split;[exact DONE|]. split;[exact PATH|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HIST|].
 eexists _,_;split;[reflexivity|]. split;[reflexivity|]. split;[exact MATCH|]. split;reflexivity.
Qed.

Theorem owned_unchanged_then_published_from_body word_max base (checked:bool)
 valid view f h a old d s e count same compare count2 same2 compare2 first rest log tail vb ob fb hb ab image ram ev id decoded stamp :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected []) tt ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count2 compare2) (pair_prepass_program count2 same2)) tt (PairSelected (first::rest)) tt ->
 owned_body_run BodyWaiting (first::rest) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFinished tail vb ob ((Logged (Ready fb) hb ab,OperationBoundary image [] ram),ev) ->
 abort_requested (controller_read ev)=false ->
 let accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram in
 let taken:=controller_evidence (TakeLocal true) (OperationBoundary image [] ram) ev in
 let closed:=controller_evidence LocalClosed (OpenBoundary image [] accepted) taken in
 let selected:=controller_evidence SelectFinish (OpenBoundary image [] accepted) closed in
 boss_pipeline_services_for (eq (AppendResponse id decoded (AppendFinishReply true stamp)))
   word_max ob fb h ab old image accepted selected ->
 exists vf of_ final,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
     ((Logged (Ready f) h a,IdleBoundary old d s),e) (ReturnedEntry true) /\
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp (Certificate id decoded)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=Receipt stamp (Certificate id decoded)::client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp (Certificate id decoded)] /\
 exists exits responses,
 exits=[ReturnedEntry true;ReturnedPublished (Receipt stamp (Certificate id decoded))] /\
 responses=[EntryResponse (PairSelected []);AppendResponse id decoded (AppendFinishReply true stamp)] /\
 Forall2 owner_response_matches responses exits /\
 delivered_observations exits=[RetainedResult;RetainedResult] /\
 delivered_receipt_log exits=[Receipt stamp (Certificate id decoded)].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED
   ENTRY FIRST_BODY BODY AB accepted taken closed selected PIPELINE.
 eapply (owned_unchanged_then_published word_max base checked valid view f h a old d s e count same compare
   (PairSelected (first::rest)) id decoded stamp);try eassumption.
 eapply (owned_services_from_finished_body _ word_max valid view f h a old d s e count2 same2 compare2 first rest
   log tail vb ob fb hb ab image ram ev);eassumption.
Qed.


Definition ready_client_destination (state:execution_boundary) : Prop :=
 exists f h a id d ram ev,state=((Logged (Ready f) h a,ClientBoundary id d ram),ev).
Lemma publication_receipt_destination valid view old id image index entry span s prepared ready e event next :
 publication_execution g sector data_len valid view marker ranges old id image index entry span s prepared ready e event next ->
 forall receipt,event=Some receipt -> ready_client_destination next.
Proof. intros RUN receipt EQ;destruct RUN;try discriminate;repeat eexists. Qed.
Lemma reserved_receipt_destination valid view bytes dw bw old id d index entry span s f h a e event next :
 reserved_execution g sector data_len valid view marker ranges bytes dw bw old id d index entry span s f h a e event next ->
 forall receipt,event=Some receipt -> ready_client_destination next.
Proof. intros RUN receipt EQ;destruct RUN;try discriminate;eapply publication_receipt_destination;eauto. Qed.
Lemma boundary_receipt_destination valid view dw bw x event y :
 boundary_step g sector data_len valid view marker ranges decode topology pages dw bw x event y ->
 forall receipt,event=Some receipt -> ready_client_destination y.
Proof. intros RUN receipt EQ;destruct RUN;try discriminate;eapply reserved_receipt_destination;eauto. Qed.
Lemma episode_receipt_destination vi oi x event vf of_ y :
 episode_step g sector data_len marker ranges decode topology pages vi oi x event vf of_ y ->
 forall receipt,event=Some receipt -> ready_client_destination y.
Proof.
 intros RUN receipt EQ;destruct RUN;try discriminate.
 - eapply boundary_receipt_destination;eauto.
 - repeat eexists.
Qed.
Lemma operation_published_destination vi oi x events vf of_ y exit :
 operation_execution g sector data_len marker ranges decode topology pages vi oi x events vf of_ y exit ->
 forall receipt,exit=ReturnedPublished receipt -> ready_client_destination y.
Proof.
 intro RUN;induction RUN;intros receipt EQ;try discriminate.
 - subst exit;destruct event as [r|].
   + eapply episode_receipt_destination;[exact H|reflexivity].
   + unfold edge_exit in H0;destruct y as [[j phase] ev];destruct phase;cbn in H0;try discriminate;
       destruct (finish_selected (controller_read (snd x)));
       destruct (finish_selected (controller_read ev));cbn in H0;try discriminate;
       repeat match type of H0 with context [if ?b then _ else _]=>destruct b end;discriminate.
 - eapply IHRUN;eassumption.
Qed.
Lemma completed_published_destination vi oi x events vf of_ y receipt :
 completed_operation g sector data_len marker ranges decode topology pages vi oi x events vf of_ y
   (ReturnedPublished receipt) -> ready_client_destination y.
Proof.
 intros [vm [om [middle [before [last [PREFIX [RUN EQ]]]]]]].
 eapply operation_published_destination;[exact RUN|reflexivity].
Qed.

(* A repeated hardware reset is explicit in this recovery witness.  In
   particular the proof never turns an arbitrary interrupted reconstruction
   phase into Selecting by an equality of RAM states. *)
Definition owner_reset_response response : Prop :=
 match response with
 | PreparationCutResponse _ | AcquisitionCutResponse _ | ValidationCutResponse _ |
   WriterInterruptedResponse => True
 | AppendResponse _ _ (AppendRestoreCutReply _) => True
 | _ => False end.
Lemma owner_reset_response_exit response exit :
 owner_reset_response response -> owner_response_matches response exit ->
 exit=InterruptedReset.
Proof.
 destruct response;cbn [owner_reset_response owner_response_matches];try tauto.
 destruct reply;cbn [owner_reset_response append_reply_exit];tauto.
Qed.
Lemma reset_published_exits response id decoded stamp exits :
 owner_reset_response response ->
 Forall2 owner_response_matches
   [response;AppendResponse id decoded (AppendFinishReply true stamp)] exits ->
 exits=[InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))].
Proof.
 intros RESET RUN;inversion RUN;subst;clear RUN.
 match goal with H:Forall2 _ [_] _ |- _=>inversion H;subst;clear H end.
 match goal with H:Forall2 _ [] _ |- _=>inversion H;subst;clear H end.
 match goal with H:owner_response_matches response ?x |- _=>
   pose proof (owner_reset_response_exit _ _ RESET H);subst x end.
 match goal with H:owner_response_matches (AppendResponse _ _ _) _ |- _=>
   cbn [owner_response_matches append_reply_exit] in H;rewrite H end.
 reflexivity.
Qed.

(* Only local recovery and next-call services are requested at the reached
   state. No invariant, closed owner, receipt or successful destination is a
   premise of this family. The next-call packet still contains its marked body. *)
Definition recovered_published_services word_max id decoded stamp valid view reached :=
 exists recovered chosen chosen_decoded ram result,
 logged_step g sector 256 data_len valid (boundary_journal reached)
   (logged_after_reset (boundary_journal reached)) /\
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (logged_after_reset (boundary_journal reached),Selecting)
   (recovered,Usable chosen chosen_decoded ram) /\
 exists flash history acks,recovered=Logged (Ready flash) history acks /\
 owned_call_services_for (eq (AppendResponse id decoded (AppendFinishReply true stamp)))
   word_max valid view flash history acks chosen chosen_decoded ram
   (recovered_page_evidence recovered chosen (forget_volatile_evidence (snd reached))) result.

Lemma recovered_published_schedule word_max id decoded stamp valid view reached :
 recovered_published_services word_max id decoded stamp valid view reached ->
 owned_service_schedule word_max 3
   [eq (AppendResponse id decoded (AppendFinishReply true stamp))] valid view reached.
Proof.
 intros [recovered [chosen [d [ram [result [RESET [BOOT [f [h [a [EQ SERVICES]]]]]]]]]]].
 destruct reached as [[j phase] ev];cbn [boundary_journal] in *.
 eapply schedule_reset;[exact RESET|].
 eapply schedule_boot;[exact BOOT|].
 subst recovered;eapply schedule_call;[exact SERVICES|intros;constructor].
Qed.

Theorem owned_cut_recovered_then_published word_max base (checked:bool)
 valid view f h a old d s e result response id decoded stamp :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owner_reset_response response ->
 owned_call_services_for (eq response) word_max valid view f h a old d s e result ->
 (forall receipts vo oo reached exit,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   owner_response_matches response exit ->
   recovered_published_services word_max id decoded stamp vo oo reached) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp (Certificate id decoded)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=Receipt stamp (Certificate id decoded)::client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp (Certificate id decoded)] /\
 Forall2 owner_response_matches
   [response;AppendResponse id decoded (AppendFinishReply true stamp)]
   [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))] /\
 delivered_observations [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))]=[RetainedResult].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED CUT FIRST RECOVER.
 assert (NEXT:forall receipts vo oo reached exit response',
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
   owner_response_matches response' exit -> response=response' -> owner_reply_ready response' reached ->
   prepass_completion_matches result valid vo view oo
     ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max 3 [eq (AppendResponse id decoded (AppendFinishReply true stamp))] vo oo reached).
 { intros receipts vo oo reached exit response' DONE POST INV' EXACT MATCH INDEX REPLY_READY PREPASS.
   subst response';apply recovered_published_schedule;eapply RECOVER;eassumption. }
 destruct (owned_calls_from_idle word_max base checked 3
   [eq (AppendResponse id decoded (AppendFinishReply true stamp))] (eq response)
   valid view f h a old d s e result HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
   INV NUM CLOSED FIRST NEXT)
   as [vf [of_ [final [exits [responses [PATH [LAST [NUMBER [CONTROL [RECEIPTS [VALID [HIST [ORDER [PREFIX [MATCH [INDICES EXACT]]]]]]]]]]]]]]]].
 pose proof (response_requests_two_exact _ _ _ INDICES) as RESPONSES;subst responses.
 pose proof (reset_published_exits _ _ _ _ _ CUT MATCH) as EXITS;subst exits.
 cbn [delivered_receipt_log delivered_receipts] in PATH,RECEIPTS,HIST.
 exists vf,of_,final;split;[exact PATH|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HIST|].
 split;[exact MATCH|reflexivity].
Qed.

Lemma published_pair_exits id1 d1 stamp1 id2 d2 stamp2 exits :
 Forall2 owner_response_matches
   [AppendResponse id1 d1 (AppendFinishReply true stamp1);AppendResponse id2 d2 (AppendFinishReply true stamp2)] exits ->
 exits=[ReturnedPublished (Receipt stamp1 (Certificate id1 d1));ReturnedPublished (Receipt stamp2 (Certificate id2 d2))].
Proof.
 intro RUN;inversion RUN;subst;clear RUN.
 match goal with H:Forall2 _ [_] _ |- _=>inversion H;subst;clear H end.
 match goal with H:Forall2 _ [] _ |- _=>inversion H;subst;clear H end.
 repeat match goal with H:owner_response_matches _ _ |- _=>cbn [owner_response_matches append_reply_exit] in H end.
 subst;reflexivity.
Qed.
Theorem owned_two_published word_max base (checked:bool)
 valid view f h a old d s e result id1 d1 stamp1 id2 d2 stamp2 :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owned_call_services_for (eq (AppendResponse id1 d1 (AppendFinishReply true stamp1)))
   word_max valid view f h a old d s e result ->
 (forall receipts vo oo ff hh aa chosen dec ram ev,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo
       ((Logged (Ready ff) hh aa,ClientBoundary chosen dec ram),ev)
       (ReturnedPublished (Receipt stamp1 (Certificate id1 d1))) ->
   exists next_result,owned_call_services_for (eq (AppendResponse id2 d2 (AppendFinishReply true stamp2)))
     word_max vo oo ff hh aa chosen dec ram ev next_result) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=[Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)]++client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)] /\
 Forall2 owner_response_matches
   [AppendResponse id1 d1 (AppendFinishReply true stamp1);AppendResponse id2 d2 (AppendFinishReply true stamp2)]
   [ReturnedPublished (Receipt stamp1 (Certificate id1 d1));ReturnedPublished (Receipt stamp2 (Certificate id2 d2))].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED FIRST SECOND.
 assert (NEXT:forall receipts vo oo reached exit response,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
   owner_response_matches response exit -> AppendResponse id1 d1 (AppendFinishReply true stamp1)=response -> owner_reply_ready response reached ->
   prepass_completion_matches result valid vo view oo
     ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max 2 [eq (AppendResponse id2 d2 (AppendFinishReply true stamp2))] vo oo reached).
 { intros receipts vo oo reached exit response DONE POST INV' EXACT MATCH INDEX REPLY_READY PREPASS.
   subst response;cbn [owner_response_matches append_reply_exit] in MATCH;subst exit.
   destruct (completed_published_destination _ _ _ _ _ _ _ _ DONE)
     as [ff [hh [aa [chosen [dec [ram [ev EQ]]]]]]];subst reached.
   destruct (SECOND _ _ _ _ _ _ _ _ _ _ DONE) as [next_result SERVICES].
   apply schedule_resume;eapply schedule_call;[exact SERVICES|intros;constructor]. }
 destruct (owned_calls_from_idle word_max base checked 2
   [eq (AppendResponse id2 d2 (AppendFinishReply true stamp2))]
   (eq (AppendResponse id1 d1 (AppendFinishReply true stamp1)))
   valid view f h a old d s e result HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
   INV NUM CLOSED FIRST NEXT)
   as [vf [of_ [final [exits [responses [PATH [LAST [NUMBER [CONTROL [RECEIPTS [VALID [HIST [ORDER [PREFIX [MATCH [INDICES EXACT]]]]]]]]]]]]]]]].
 pose proof (response_requests_two_exact _ _ _ INDICES) as RESPONSES;subst responses.
 pose proof (published_pair_exits _ _ _ _ _ _ _ MATCH) as EXITS;subst exits.
 cbn [delivered_receipt_log delivered_receipts] in PATH,RECEIPTS,HIST.
 exists vf,of_,final;split;[exact PATH|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HIST|exact MATCH].
Qed.

Theorem owned_append_restorecut_recovered_then_published word_max base (checked:bool)
 valid view f h a old d s e result failed_id failed_decoded point id decoded stamp :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owned_call_services_for (eq (AppendResponse failed_id failed_decoded (AppendRestoreCutReply point))) word_max valid view f h a old d s e result ->
 (forall receipts vo oo reached exit,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   owner_response_matches (AppendResponse failed_id failed_decoded (AppendRestoreCutReply point)) exit ->
   recovered_published_services word_max id decoded stamp vo oo reached) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp (Certificate id decoded)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=Receipt stamp (Certificate id decoded)::client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp (Certificate id decoded)] /\
 Forall2 owner_response_matches
   [AppendResponse failed_id failed_decoded (AppendRestoreCutReply point);AppendResponse id decoded (AppendFinishReply true stamp)]
   [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))] /\
 delivered_observations [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))]=[RetainedResult].
Proof.
 intros; eapply (owned_cut_recovered_then_published word_max base checked);try eassumption;exact I.
Qed.

Theorem owned_preparation_cut_recovered_then_published word_max base (checked:bool)
 valid view f h a old d s e result point id decoded stamp :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owned_call_services_for (eq (PreparationCutResponse point)) word_max valid view f h a old d s e result ->
 (forall receipts vo oo reached exit,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   owner_response_matches (PreparationCutResponse point) exit ->
   recovered_published_services word_max id decoded stamp vo oo reached) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp (Certificate id decoded)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=Receipt stamp (Certificate id decoded)::client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp (Certificate id decoded)] /\
 Forall2 owner_response_matches
   [PreparationCutResponse point;AppendResponse id decoded (AppendFinishReply true stamp)]
   [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))] /\
 delivered_observations [InterruptedReset;ReturnedPublished (Receipt stamp (Certificate id decoded))]=[RetainedResult].
Proof.
 intros; eapply (owned_cut_recovered_then_published word_max base checked);try eassumption;exact I.
Qed.


Theorem owned_publications_historical_reuse word_max base (checked:bool)
 valid view f h a old d s e result id1 d1 stamp1 id2 d2 stamp2 historical_stamp historical_decoded :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owned_call_services_for (eq (AppendResponse id1 d1 (AppendFinishReply true stamp1)))
   word_max valid view f h a old d s e result ->
 (forall receipts vo oo ff hh aa chosen dec ram ev,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo
       ((Logged (Ready ff) hh aa,ClientBoundary chosen dec ram),ev)
       (ReturnedPublished (Receipt stamp1 (Certificate id1 d1))) ->
   exists next_result,owned_call_services_for (eq (AppendResponse id2 d2 (AppendFinishReply true stamp2)))
     word_max vo oo ff hh aa chosen dec ram ev next_result) ->
 In (Receipt historical_stamp (Certificate id2 historical_decoded)) (client_receipts e) ->
 recovered_image historical_decoded<>recovered_image d2 ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=[Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)]++client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp2 (Certificate id2 d2);Receipt stamp1 (Certificate id1 d1)] /\
 Forall2 owner_response_matches
   [AppendResponse id1 d1 (AppendFinishReply true stamp1);AppendResponse id2 d2 (AppendFinishReply true stamp2)]
   [ReturnedPublished (Receipt stamp1 (Certificate id1 d1));ReturnedPublished (Receipt stamp2 (Certificate id2 d2))] /\
 In (Receipt historical_stamp (Certificate id2 historical_decoded)) (boundary_receipts final) /\
 recovered_image historical_decoded<>recovered_image d2.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED FIRST SECOND OLD DISTINCT.
 destruct (owned_two_published word_max base checked valid view f h a old d s e result
   id1 d1 stamp1 id2 d2 stamp2 HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
   INV NUM CLOSED FIRST SECOND)
   as [vf [of_ [final [PATH [LAST [NUMBER [CONTROL [RECEIPTS [VALID [HIST MATCH]]]]]]]]]].
 exists vf,of_,final;split;[exact PATH|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HIST|].
 split;[exact MATCH|]. split;[rewrite RECEIPTS;cbn;auto|exact DISTINCT].
Qed.

Lemma local_error_published_exits mask id decoded stamp exits :
 Forall2 owner_response_matches
   [LocalBodyCleanupResponse mask;AppendResponse id decoded (AppendFinishReply true stamp)] exits ->
 exits=[ReturnedBodyError;ReturnedPublished (Receipt stamp (Certificate id decoded))].
Proof.
 intro RUN;inversion RUN;subst;clear RUN.
 match goal with H:Forall2 _ [_] _ |- _=>inversion H;subst;clear H end.
 match goal with H:Forall2 _ [] _ |- _=>inversion H;subst;clear H end.
 repeat match goal with H:owner_response_matches _ _ |- _=>cbn [owner_response_matches append_reply_exit] in H end.
 subst;reflexivity.
Qed.

Theorem owned_local_error_then_published word_max base (checked:bool)
 valid view f h a old d s e result mask id2 d2 stamp2 :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 owned_call_services_for (eq (LocalBodyCleanupResponse mask))
   word_max valid view f h a old d s e result ->
 (forall receipts vo oo ff hh aa chosen dec ram ev,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo
       ((Logged (Ready ff) hh aa,IdleBoundary chosen dec ram),ev)
       (ReturnedBodyError) ->
   exists next_result,owned_call_services_for (eq (AppendResponse id2 d2 (AppendFinishReply true stamp2)))
     word_max vo oo ff hh aa chosen dec ram ev next_result) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp2 (Certificate id2 d2)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=[Receipt stamp2 (Certificate id2 d2)]++client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp2 (Certificate id2 d2)] /\
 Forall2 owner_response_matches
   [LocalBodyCleanupResponse mask;AppendResponse id2 d2 (AppendFinishReply true stamp2)]
   [ReturnedBodyError;ReturnedPublished (Receipt stamp2 (Certificate id2 d2))] /\
 delivered_observations [ReturnedBodyError;ReturnedPublished (Receipt stamp2 (Certificate id2 d2))]=
   [FinalizationError;RetainedResult].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED FIRST SECOND.
 assert (NEXT:forall receipts vo oo reached exit response,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
   owner_response_matches response exit -> LocalBodyCleanupResponse mask=response -> owner_reply_ready response reached ->
   prepass_completion_matches result valid vo view oo
     ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max 1 [eq (AppendResponse id2 d2 (AppendFinishReply true stamp2))] vo oo reached).
 { intros receipts vo oo reached exit response DONE POST INV' EXACT MATCH INDEX REPLY_READY PREPASS.
   subst response;cbn [owner_response_matches append_reply_exit] in MATCH;subst exit.
   change (exists ff hh aa chosen dec ram ev,
     reached=((Logged (Ready ff) hh aa,IdleBoundary chosen dec ram),ev)) in REPLY_READY.
   destruct REPLY_READY as [ff [hh [aa [chosen [dec [ram [ev EQ]]]]]]];subst reached.
   destruct (SECOND _ _ _ _ _ _ _ _ _ _ DONE) as [next_result SERVICES].
   eapply schedule_call;[exact SERVICES|intros;constructor]. }
 destruct (owned_calls_from_idle word_max base checked 1
   [eq (AppendResponse id2 d2 (AppendFinishReply true stamp2))]
   (eq (LocalBodyCleanupResponse mask))
   valid view f h a old d s e result HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
   INV NUM CLOSED FIRST NEXT)
   as [vf [of_ [final [exits [responses [PATH [LAST [NUMBER [CONTROL [RECEIPTS [VALID [HIST [ORDER [PREFIX [MATCH [INDICES EXACT]]]]]]]]]]]]]]]].
 pose proof (response_requests_two_exact _ _ _ INDICES) as RESPONSES;subst responses.
 pose proof (local_error_published_exits _ _ _ _ _ MATCH) as EXITS;subst exits.
 cbn [delivered_receipt_log delivered_receipts] in PATH,RECEIPTS,HIST.
 exists vf,of_,final;split;[exact PATH|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HIST|]. split;[exact MATCH|reflexivity].
Qed.
Theorem owned_local_error_then_published_from_body word_max base (checked:bool)
 valid view f h a old d s e count same compare first rest log tail vb ob fb hb ab image root ram ev read inspect check mask id2 d2 stamp2 :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) -> delivered_owner_closed e ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (first::rest)) tt ->
 owned_body_run BodyWaiting (first::rest) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFailed tail vb ob ((Logged (Ready fb) hb ab,OperationBoundary image root ram),ev) ->
 owned_restore_reply old ob ((Logged (Ready fb) hb ab,OperationBoundary image root ram),ev)
   read inspect check RestoreValidated ->
 mask=collect_ranges ob marker (Some old) (object_extents (ob old)) [] ->
 (forall receipts vo oo ff hh aa chosen dec ram ev,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo
       ((Logged (Ready ff) hh aa,IdleBoundary chosen dec ram),ev)
       (ReturnedBodyError) ->
   exists next_result,owned_call_services_for (eq (AppendResponse id2 d2 (AppendFinishReply true stamp2)))
     word_max vo oo ff hh aa chosen dec ram ev next_result) ->
 exists vf of_ final,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   [Receipt stamp2 (Certificate id2 d2)] vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=[Receipt stamp2 (Certificate id2 d2)]++client_receipts e /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) [Receipt stamp2 (Certificate id2 d2)] /\
 Forall2 owner_response_matches
   [LocalBodyCleanupResponse mask;AppendResponse id2 d2 (AppendFinishReply true stamp2)]
   [ReturnedBodyError;ReturnedPublished (Receipt stamp2 (Certificate id2 d2))] /\
 delivered_observations [ReturnedBodyError;ReturnedPublished (Receipt stamp2 (Certificate id2 d2))]=
   [FinalizationError;RetainedResult].
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED
   ENTRY BODY RESTORE MASK SECOND.
 eapply (owned_local_error_then_published word_max base checked valid view f h a old d s e
   (PairSelected (first::rest)) mask id2 d2 stamp2);try eassumption.
 eapply owned_services_from_local_failed_body;try eassumption;reflexivity.
Qed.

End OwnerWitnesses.
