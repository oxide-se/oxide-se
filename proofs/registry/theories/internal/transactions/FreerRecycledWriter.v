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
Theorem a12f_reservation_to_writer g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r count result validate boss plan written :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate ->
 boundary_safe sector data_len prior_valid view marker ranges decode pages initial ->
 logged_reachable g sector 256 data_len prior_valid (boundary_journal initial) ->
 stationary_episode_trace g sector data_len prior_valid view marker ranges decode topology pages initial events
  ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 recycling_run g sector recognize magic r count f result ->
 neutral_end_ result=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) boss (neutral_flash result) plan written ->
 let reserved:=data_next (DataReserve (block_pages (recycle_lo r) (useful_pages r))) (data_next DataBegin ram) in
 erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r)) /\
 exists decoded,
 decode (object_flash sector (writer_flash written)) old=Some decoded /\
 unchanged (protected_roots reserved) (object_flash sector (neutral_flash result)) (object_flash sector (writer_flash written)) /\
 enriched_invariant sector data_len (validate (writer_flash written)) view marker ranges decode pages
  (writer_exit_boundary old (recovered_image d) [recovered_boss d] reserved h a written)
  (selected_evidence old decoded e) /\
 episode_boot_post g sector data_len (validate (writer_flash written)) view marker ranges decode topology pages
  (logged_after_reset (Logged (Ready (writer_flash written)) h a)) (selected_evidence old decoded e).
Proof.
 intros G DIV C L PROVIDER INITIAL REACH TRACE SEARCH GEO RUN OK WRITE reserved.
 destruct (a11_reachable_recycling_reservation g sector data_len prior_valid view marker ranges decode topology pages
  initial events f h a old d ram e recognize magic fuel req round alignment start r count result validate
  G DIV C L PROVIDER INITIAL REACH TRACE SEARCH GEO RUN)
  as [BEGIN [CALLS [decoded [SAFE [RAW [BOOT DONE]]]]]].
 destruct (DONE OK) as [BLANK [CALL LATE]].
 pose proof (proj1 (LATE ReservedReturn)) as RESERVED.
 unfold neutral_open_boundary in RAW; rewrite OK in RAW.
 destruct (initialized_a11_trace_raw g sector data_len prior_valid view marker ranges decode topology pages
  G DIV initial events _ INITIAL REACH TRACE) as [FINAL ORDER].
 pose proof FINAL as [[JI [IDLE REST]] OTHER].
 split; [exact BLANK|].
 exact (reserved_writer_outcomes g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
  (neutral_flash result) h a old (recovered_image d) [recovered_boss d] reserved (selected_evidence old decoded e)
  (Build_preparation ObjectPreparation (block_pages (recycle_lo r) (useful_pages r)) Reserved)
  boss plan written validate G DIV C PROVIDER RESERVED RAW
  (proj1 (proj2 (proj2 (proj2 IDLE)))) eq_refl WRITE).
Qed.

Theorem admitted_a12f_reservation_to_writer g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r count result validate boss plan written bytes dw bw dp bp :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate ->
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 boundary_safe sector data_len prior_valid view marker ranges decode pages initial ->
 logged_reachable g sector 256 data_len prior_valid (boundary_journal initial) ->
 erased_episode_trace g sector data_len prior_valid view marker ranges decode topology pages initial events
  ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 recycling_run g sector recognize magic r count f result ->
 neutral_end_ result=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) boss (neutral_flash result) plan written ->
 let reserved:=data_next (DataReserve (block_pages (recycle_lo r) (useful_pages r))) (data_next DataBegin ram) in
 erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r)) /\
 exists decoded,
 decode (object_flash sector (writer_flash written)) old=Some decoded /\
 unchanged (protected_roots reserved) (object_flash sector (neutral_flash result)) (object_flash sector (writer_flash written)) /\
 enriched_invariant sector data_len (validate (writer_flash written)) view marker ranges decode pages
  (writer_exit_boundary old (recovered_image d) [recovered_boss d] reserved h a written)
  (selected_evidence old decoded e) /\
 episode_boot_post g sector data_len (validate (writer_flash written)) view marker ranges decode topology pages
  (logged_after_reset (Logged (Ready (writer_flash written)) h a)) (selected_evidence old decoded e).
Proof.
 intros G DIV C L PROVIDER W INITIAL REACH TRACE SEARCH GEO RUN OK WRITE.
 eapply a12f_reservation_to_writer; [exact G|exact DIV|exact C|exact L|exact PROVIDER|
  exact INITIAL|exact REACH| |exact SEARCH|exact GEO|exact RUN|exact OK|exact WRITE].
 exact (erased_trace_refines g sector data_len prior_valid view marker ranges decode topology pages G DIV C
  bytes dw bw dp bp W initial events _ INITIAL TRACE).
Qed.

From OxideSE.Registry Require Export OwnedDataTypes OwnedDataResponses OwnedDataInvariant OwnedDataRequirements OwnedDataOffered OwnedDataServices.
From OxideSE.Registry Require Import IncarnationBoundary.

#[local] Hint Resolve runtime_erased_admission_forget runtime_erased_admission_mapped : core.

Section EvolvingConsumption.
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
Local Notation Safe v o := (boundary_safe sector data_len v o marker ranges decode pages).
Local Notation owner_invariants := (owner_invariants sector data_len marker ranges decode pages).
Local Notation owned_data_entry := (owned_data_entry sector data_len marker ranges decode pages).
Local Notation owned_data_offered := (owned_data_offered g sector data_len marker ranges decode topology pages).
Local Notation controller_result_post := (controller_result_post g sector data_len marker ranges decode topology pages).
Local Notation owner_safe := (owner_safe sector data_len marker ranges decode pages).
Local Notation owner_latest := (owner_latest sector data_len marker ranges decode pages).
Local Notation owned_data_suppliers := (owned_data_suppliers g sector data_len marker ranges decode pages validate).
Local Notation Trace := (episode_trace g sector data_len marker ranges decode topology pages).
Local Notation Step := (episode_step g sector data_len marker ranges decode topology pages).

Theorem recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result boss :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 exists previous,
 let final:=(recycling_acquisition_boundary old image root s h a result span boss,phase_evidence (snd (recycling_acquisition_boundary old image root s h a result span boss)) (selected_evidence old previous (recycling_cursor_evidence result span e))) in
 Trace vi oi initial events (validate (neutral_flash result)) view final /\
 Safe (validate (neutral_flash result)) view final /\
 raw_order sector 256 data_len (boundary_journal final) /\
 (neutral_end_ result=NeutralSuccess -> reservation_handoff sector (neutral_flash result)
   (reservation_state boss span s) (reservation_token boss span)).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN span.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 pose proof (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
   f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss
   G DIV SOURCE ORDER HEAD IN (READERS _) LOCAL ACCEPT P SEARCH GEO RUN) as [LAST [KEEP [ORDER' HANDOFF]]].
 exists previous. split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].

   eapply episodes_cons with (event:=None) (events:=[]);[eapply acquire_recycled;eauto|apply episodes_nil].
 - split;[exact LAST|]. split;[exact ORDER'|exact HANDOFF].
Qed.

Theorem recycled_writer_episode vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled boss plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) boss (neutral_flash recycled) plan result ->
 let reserved:=reservation_state boss (block_pages (recycle_lo r) (useful_pages r)) s in
 exists previous,
 let final:=(writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 boundary_receipts final=events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE reserved.
 destruct (recycling_acquisition_from_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _
   recognize magic fuel req round alignment start r count recycled boss INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH [SOURCE [ORDER HANDOFF]]]].
 unfold recycling_cursor_evidence,recycling_acquisition_boundary in PATH,SOURCE,ORDER;rewrite OK in PATH,SOURCE,ORDER.
 assert (STEP:Step (validate (neutral_flash recycled)) view
    ((Logged (Ready (neutral_flash recycled)) h a,OpenBoundary image root reserved),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) None
    (validate (writer_flash result)) view
    (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)))).
 { eapply consume_pending with (e:=selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e));[exact ORDER|exact HEAD|simpl;auto|apply READERS|exact ACCEPT| |].
   - split;[exact (HANDOFF OK)|exact WRITE].
   - destruct boss;reflexivity. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)))).
 { eapply episodes_append with (more:=[]);[exact PATH|].

   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 exists previous. split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]]. auto.
Qed.

Theorem recycled_decoded_episode vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result id fresh :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 contains (block_pages (recycle_lo r) (useful_pages r)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r) (useful_pages r) -> recovered_image fresh=image ->
 let reserved:=reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s in
 let next_view:=install_decoded_view view ranges id fresh in
 exists previous,
 let final:=(writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh])) in
 Trace vi oi initial events (validate (writer_flash result)) next_view final /\
 Safe (validate (writer_flash result)) next_view final /\
 boundary_receipts final=events++boundary_receipts initial /\
 publications (boundary_journal final)=h /\ acknowledgements (boundary_journal final)=a.
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE reserved next_view.
 destruct (recycling_acquisition_from_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _
   recognize magic fuel req round alignment start r count recycled true INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH [SOURCE [ORDER HANDOFF]]]].
 unfold recycling_cursor_evidence,recycling_acquisition_boundary in PATH,SOURCE,ORDER;rewrite OK in PATH,SOURCE,ORDER.
 assert (READLOCAL:forall after,
   unchanged (root_extents (view old)) (object_flash sector (neutral_flash recycled)) (object_flash sector after) ->
   decode (object_flash sector (neutral_flash recycled)) old=decode (object_flash sector after) old).
 { pose proof (Forall_inv (proj1 (proj1 (proj2 SOURCE)))) as [BEFORE [B O]].
   intros after FRAME; simpl in BEFORE,B,O.
   rewrite BEFORE. symmetry. apply (READERS (Certificate old previous) _ _ BEFORE).
   unfold certificate_ranges;simpl;rewrite B;rewrite O;exact FRAME. }
 assert (STEP:Step (validate (neutral_flash recycled)) view
    ((Logged (Ready (neutral_flash recycled)) h a,OpenBoundary image root reserved),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) None
    (validate (writer_flash result)) next_view
    (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]))).
 { eapply consume_decoded with (e:=selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))
     (p:=Build_preparation BossPreparation (block_pages (recycle_lo r) (useful_pages r)) Reserved);[exact ORDER|exact HEAD|simpl;auto|exact AT|exact OLDAT|exact READLOCAL|exact ACCEPT|
     split;[exact (HANDOFF OK)|exact WRITE]|exact COMPLETE|exact READ|exact BOSS|exact IMAGE|reflexivity]. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) next_view
    (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]))).
 { eapply episodes_append with (more:=[]);[exact PATH|].

   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 exists previous. split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]].
 split;[exact LAST|]. split;[exact OBS|].
 unfold boundary_journal; simpl;unfold writer_exit_boundary;rewrite COMPLETE;split;reflexivity.
Qed.

Theorem erased_writer_episode vi oi initial events valid view f h a old image root s e
 span boss plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 mapped_erased_admission sector pages s f span ->
 writer_execution g sector span boss f plan result ->
 let reserved:=reservation_state boss span s in
 exists previous,
 let final:=(writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence span e))) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 boundary_receipts final=events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD P MAPPED WRITE reserved.
 pose proof (mapped_erased_admission_forget _ _ _ _ _ MAPPED) as HIT.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 destruct (erased_admission_guards _ _ _ _ HIT) as [FREE BLANK].
 assert (ACQUIRE:Step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
   ((Logged (Ready f) h a,OpenBoundary image root reserved),advance_allocation_evidence span e)).
 { eapply acquire_erased with (boss:=boss);[exact P|exact HIT|exact MAPPED]. }
 assert (WRITE_STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image root reserved),advance_allocation_evidence span e) None
   (validate (writer_flash result)) view (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence span e)))).
 { eapply consume_pending with (p:=reservation_token boss span);[exact ORDER|exact HEAD|exact IN|apply READERS|exact ACCEPT| |].
   - split;[split;[destruct boss;reflexivity|exact BLANK]|exact WRITE].
   - destruct boss;reflexivity. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   (writer_exit_boundary old image root reserved h a result,phase_evidence (snd (writer_exit_boundary old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence span e)))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].

   eapply episodes_cons with (event:=None) (events:=[]);[exact ACQUIRE|].

   eapply episodes_cons with (event:=None) (events:=[]);[exact WRITE_STEP|apply episodes_nil]. }
 exists previous. split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]]. auto.
Qed.


Theorem recycled_data_attach_episode vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result index entry :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) false (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete -> ranges entry=[block_pages (recycle_lo r) (useful_pages r)] ->
 let prepared:=snapshot_written (data_next (DataReserve (block_pages (recycle_lo r) (useful_pages r))) s) in
 exists previous,
 let final:=((Logged (Ready (writer_flash result)) h a,
   OpenBoundary (image_replace image index (Some entry)) []
     (exact_attach ranges image index entry (data_next DataWritten prepared))),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final.
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE RANGE prepared.
 destruct (recycled_writer_episode vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled false plan result
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SOURCE OBS]]].
 unfold writer_exit_boundary in PATH,SOURCE;rewrite COMPLETE in PATH,SOURCE.
 assert (ATTACH:Step (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary image root prepared),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) None
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary (image_replace image index (Some entry)) []
      (exact_attach ranges image index entry (data_next DataWritten prepared))),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))).
 { eapply attach_pending with (p:=Build_preparation ObjectPreparation (block_pages (recycle_lo r) (useful_pages r)) Written);
   [reflexivity|reflexivity|reflexivity|exact RANGE]. }
 exists previous. split.
 - eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact ATTACH|apply episodes_nil].
 - exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ SOURCE ATTACH)).
Qed.


Theorem recycled_installed_episode vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result id fresh :
 Safe vi oi initial -> external_structure marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 contains (block_pages (recycle_lo r) (useful_pages r)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r) (useful_pages r) -> recovered_image fresh=image ->
 let prepared:=install_candidate (snapshot_written
   (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)) in
 let next_view:=install_decoded_view view ranges id fresh in
 exists previous,
 let final:=((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared id fresh prepared),
   evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]) in
 Trace vi oi initial events (validate (writer_flash result)) next_view final /\
 Safe (validate (writer_flash result)) next_view final /\ external_structure marker final /\
 boundary_receipts final=events++boundary_receipts initial.
Proof.
 intros INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE prepared next_view.
 destruct (recycled_decoded_episode vi oi initial events valid view f h a old image [] s e
   recognize magic fuel req round alignment start r count recycled plan result id fresh
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE)
   as [previous [PATH [SOURCE [OBS REST]]]].
 unfold writer_exit_boundary in PATH,SOURCE;rewrite COMPLETE in PATH,SOURCE.
 assert (STEP:Step (validate (writer_flash result)) next_view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
     (snapshot_written (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s))),
     evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]) None
   (validate (writer_flash result)) next_view
   ((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared id fresh prepared),
     evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh])).
 { eapply install_prepared with (p:=Build_preparation BossPreparation (block_pages (recycle_lo r) (useful_pages r)) Written);
   [reflexivity|reflexivity|reflexivity|simpl;auto|exact BOSS|exact IMAGE]. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) next_view
   ((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared id fresh prepared),
     evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh])).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 exists previous;split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [LAST [RECEIPTS REST']].
 split;[exact LAST|]. split;[|exact RECEIPTS].
 exact (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT FULL).
Qed.

(* The saved scope and marker are obtained from the prefix, not parameters of
   the publication service or assertions of a safe final state. *)
Theorem installed_exit_callers_from_trace vi oi initial events valid view ready id d s e :
 Safe vi oi initial -> external_structure marker initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 let saved:=List.hd [] (protection_saved s) in
 exit_calls marker (root_extents (view id)) saved [SlotCompleted;DurableRamWritten;ExternalAccepted] s /\
 collection_boundary view marker (Some id) (Some id) (object_extents (view id)) []
   (successful_external_close marker (root_extents (view id)) saved s).
Proof.
 intros INIT STRUCT PREFIX saved.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT PREFIX)) as [[J [PI [F [P [FMT [COR REST]]]]]] E].
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [scope [STACK MARK]].
 assert (CUR:protection_current s++attached_ranges s=root_extents (view id)).
 { unfold image_current_correspondence in COR;destruct FMT as [B OB];rewrite B in COR;rewrite OB in COR;exact COR. }
 unfold saved;rewrite STACK;simpl.
 split;[apply successful_exit_callers;assumption|apply successful_close_boundary;exact CUR].
Qed.

Theorem installed_client_from_trace vi oi initial events valid view ready id d s e out slot pubs acks final :
 Safe vi oi initial -> external_structure marker initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract view marker id (List.hd [] (protection_saved s)))
   (client_finish_program id (recovered_image d) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   s (ClientReturned (DataClientSuccess id (recovered_image d))) final ->
 let receipt:=Receipt (pred (length pubs)) (Certificate id d) in
 let destination:=((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id d final),
   observe_client (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id d)
     (evidence_with_live e [Certificate id d])) in
 Trace vi oi initial (receipt::events) valid view destination /\ Safe valid view destination /\
 boundary_receipts destination=receipt::events++boundary_receipts initial.
Proof.
 intros INIT STRUCT PREFIX TRACE ACK POST receipt destination.
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [saved [STACK MARK]].
 assert (STEP:Step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e)
   (Some receipt) valid view destination).
 { eapply return_prepared with (saved:=saved);[intros;apply READERS|exact STACK|exact MARK|exact TRACE|exact ACK|].
   rewrite STACK in POST;simpl in POST;exact POST. }
 assert (FULL:Trace vi oi initial (receipt::events) valid view destination).
 { change (Trace vi oi initial ([receipt]++events) valid view destination).
   eapply episodes_append;[exact PREFIX|].
   eapply episodes_cons with (event:=Some receipt) (events:=[]);[exact STEP|apply episodes_nil]. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]]. auto.
Qed.

Theorem recycled_publication_client_episode vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result id fresh out slot pubs acks final :
 Safe vi oi initial -> external_structure marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 contains (block_pages (recycle_lo r) (useful_pages r)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r) (useful_pages r) -> recovered_image fresh=image ->
 let prepared:=install_candidate (snapshot_written
   (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)) in
 let next_view:=install_decoded_view view ranges id fresh in
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len (validate (writer_flash result)) (N.of_nat id))
   (Logged (Ready (writer_flash result)) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len (validate (writer_flash result)) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract next_view marker id (List.hd [] (protection_saved prepared)))
   (client_finish_program id (recovered_image fresh) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   prepared (ClientReturned (DataClientSuccess id (recovered_image fresh))) final ->
 let receipt:=Receipt (pred (length pubs)) (Certificate id fresh) in
 let destination:=((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id fresh final),
   observe_client (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id fresh)
     (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate id fresh])) in
 Trace vi oi initial (receipt::events) (validate (writer_flash result)) next_view destination /\
 Safe (validate (writer_flash result)) next_view destination /\
 boundary_receipts destination=receipt::events++boundary_receipts initial.
Proof.
 intros INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE
   prepared next_view TRACE ACK POST receipt destination.
 destruct (recycled_installed_episode vi oi initial events valid view f h a old image s e
   recognize magic fuel req round alignment start r count recycled plan result id fresh
   INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE)
   as [previous [PATH [SOURCE [SCOPE OBS]]]].
 exact (installed_client_from_trace vi oi initial events (validate (writer_flash result)) next_view
   (Logged (Ready (writer_flash result)) h a) id fresh prepared
   (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]) out slot pubs acks final
   INIT STRUCT PATH TRACE ACK POST).
Qed.


(* All operational suffix branches are constructors of the SAME episode_step.
   This continuation consumes them without a post-invariant assumption. *)
Theorem installed_suffix_from_trace vi oi initial events valid view ready id d s e event vf of_ destination :
 Safe vi oi initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 Step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) event vf of_ destination ->
 Trace vi oi initial (emitted_receipts event++events) vf of_ destination /\
 Safe vf of_ destination /\
 boundary_receipts destination=emitted_receipts event++events++boundary_receipts initial.
Proof.
 intros INIT PREFIX SUFFIX.
 assert (FULL:Trace vi oi initial (emitted_receipts event++events) vf of_ destination).
 { eapply episodes_append;[exact PREFIX|].
   rewrite <- (app_nil_l (emitted_receipts event)).
   eapply episodes_cons;[exact SUFFIX|apply episodes_nil]. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]]. split;[exact LAST|].
 rewrite <- app_assoc in OBS;exact OBS.
Qed.

Theorem client_trace_opens vi oi initial events valid view j id d ram e :
 Safe vi oi initial -> Trace vi oi initial events valid view ((j,ClientBoundary id d ram),e) ->
 Trace vi oi initial events valid view
   ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e) /\
 Safe valid view ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e) /\
 data_caller DataBegin ram.
Proof.
 intros INIT PREFIX.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply resume_client_episode|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply begin_episode|apply episodes_nil].
 - destruct (enriched_client_next sector data_len valid view marker ranges decode pages _ _ _ _ _ SOURCE)
     as [IDLE [CALL OPEN]]. auto.
Qed.

(* The reused X was authoritative BEFORE the first episode. The first return
   publishes Y; only then may the second publish X with another decoding.
   Reusing the still-selected X in two consecutive commits would be illegal. *)
Theorem two_client_episodes_reusing_offset vi oi j0 x old initial_ram e0 first_receipt
 v1 o1 j1 y first ram1 e1 second_receipt v2 o2 j2 fresh ram2 e2 old_receipt :
 Safe vi oi ((j0,IdleBoundary x old initial_ram),e0) ->
 In old_receipt (client_receipts e0) -> receipt_certificate old_receipt=Certificate x old ->
 Trace vi oi ((j0,IdleBoundary x old initial_ram),e0) [first_receipt] v1 o1
   ((j1,ClientBoundary y first ram1),e1) ->
 Trace v1 o1 ((j1,OpenBoundary (recovered_image first) [recovered_boss first] (data_next DataBegin ram1)),e1)
   [second_receipt] v2 o2 ((j2,ClientBoundary x fresh ram2),e2) ->
 receipt_certificate second_receipt=Certificate x fresh ->
 image_dependencies ranges (recovered_image old) <> image_dependencies ranges (recovered_image fresh) ->
 Trace vi oi ((j0,IdleBoundary x old initial_ram),e0) [second_receipt;first_receipt] v2 o2
   ((j2,ClientBoundary x fresh ram2),e2) /\
 Safe v2 o2 ((j2,ClientBoundary x fresh ram2),e2) /\
 In old_receipt (client_receipts e2) /\ In second_receipt (client_receipts e2) /\
 receipt_valid o2 ranges (publications j2) old_receipt /\
 receipt_valid o2 ranges (publications j2) second_receipt /\
 receipt_certificate old_receipt <> receipt_certificate second_receipt.
Proof.
 intros INIT OLDIN OLD FIRST SECOND NEW DIFFERENT.
 destruct (client_trace_opens _ _ _ _ _ _ _ _ _ _ _ INIT FIRST) as [OPEN [SAFE CALL]].
 assert (FULL:Trace vi oi ((j0,IdleBoundary x old initial_ram),e0) [second_receipt;first_receipt] v2 o2
   ((j2,ClientBoundary x fresh ram2),e2)).
 { change (Trace vi oi ((j0,IdleBoundary x old initial_ram),e0) ([second_receipt]++[first_receipt]) v2 o2
     ((j2,ClientBoundary x fresh ram2),e2));eapply episodes_append;[exact OPEN|exact SECOND]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS [VALID RETURN]]].
 change (client_receipts e2=[second_receipt;first_receipt]++client_receipts e0) in OBS.
 assert (O:In old_receipt (client_receipts e2)) by (rewrite OBS;simpl;auto).
 assert (N:In second_receipt (client_receipts e2)) by (rewrite OBS;simpl;auto).
 split;[exact FULL|]. split;[exact LAST|]. split;[exact O|]. split;[exact N|].
 split;[exact (proj1 (Forall_forall _ _) VALID old_receipt O)|].
 split;[exact (proj1 (Forall_forall _ _) VALID second_receipt N)|].
 rewrite OLD;rewrite NEW;intro EQ;inversion EQ;subst fresh;contradiction.
Qed.

Theorem installed_publication_prefix_from_trace vi oi initial events valid view ready id d s e middle :
 Safe vi oi initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) ready middle ->
 logged_invariant sector 256 data_len valid middle /\ persistent_evidence sector view ranges decode middle e /\
 (hd_error (publications middle)=hd_error (publications ready) \/ hd_error (publications middle)=Some (N.of_nat id)) /\
 acknowledgements middle=acknowledgements ready.
Proof.
 intros INIT PREFIX RUN.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT PREFIX)) as [[J CORE] [EV IN]].
 destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ RUN) as [CHOICE [ACK LOG]].
 destruct (certified_journal_transport g sector data_len valid view ranges decode ready middle e (N.of_nat id)
   G DIV J EV (fun c _=>READERS c) (ex_intro _ (Certificate id d) (conj IN eq_refl)) LOG CHOICE) as [JI E].
 auto.
Qed.

Theorem recycled_publication_suffixes vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result id fresh :
 Safe vi oi initial -> external_structure marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 contains (block_pages (recycle_lo r) (useful_pages r)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r) (useful_pages r) -> recovered_image fresh=image ->
 let prepared:=install_candidate (snapshot_written
   (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)) in
 let next_view:=install_decoded_view view ranges id fresh in
 exists previous,
 let candidate:=((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared id fresh prepared),
   evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]) in
 Trace vi oi initial events (validate (writer_flash result)) next_view candidate /\
 external_structure marker candidate /\
 exit_calls marker (root_extents (next_view id)) (List.hd [] (protection_saved prepared))
   [SlotCompleted;DurableRamWritten;ExternalAccepted] prepared /\
 collection_boundary next_view marker (Some id) (Some id) (object_extents (next_view id)) []
   (successful_external_close marker (root_extents (next_view id)) (List.hd [] (protection_saved prepared)) prepared) /\
 (forall middle,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len (validate (writer_flash result)) (N.of_nat id))
     (Logged (Ready (writer_flash result)) h a) middle ->
   logged_invariant sector 256 data_len (validate (writer_flash result)) middle /\
   persistent_evidence sector next_view ranges decode middle (snd candidate) /\
   (hd_error (publications middle)=hd_error h \/ hd_error (publications middle)=Some (N.of_nat id)) /\
   acknowledgements middle=a) /\
 (forall event vf of_ next,
   Step (validate (writer_flash result)) next_view candidate event vf of_ next ->
   Trace vi oi initial (emitted_receipts event++events) vf of_ next /\ Safe vf of_ next /\
   boundary_receipts next=emitted_receipts event++events++boundary_receipts initial).
Proof.
 intros INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE prepared next_view.
 destruct (recycled_installed_episode vi oi initial events valid view f h a old image s e
   recognize magic fuel req round alignment start r count recycled plan result id fresh
   INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE)
   as [previous [PATH [SOURCE [SCOPE OBS]]]].
 exists previous;split;[exact PATH|]. split;[exact SCOPE|].
 destruct (installed_exit_callers_from_trace _ _ _ _ _ _ _ _ _ _ _ INIT STRUCT PATH) as [CALL COLLECT].
 split;[exact CALL|]. split;[exact COLLECT|].
 split.
 - intros middle RUN_PREFIX.
   exact (installed_publication_prefix_from_trace vi oi initial events (validate (writer_flash result)) next_view
     (Logged (Ready (writer_flash result)) h a) id fresh prepared
     (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e) [Certificate old previous;Certificate id fresh]) middle INIT PATH RUN_PREFIX).
 - intros event vf of_ next RUN_SUFFIX.
 eapply installed_suffix_from_trace;[exact INIT|exact PATH|exact RUN_SUFFIX].
Qed.


(* One consumer actually feeds Data attachment into the BOSS service. Both
   searches see the table and flash reached by their own predecessors. *)
Theorem recycled_data_boss_client vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan dr index entry
 fuel2 req2 round2 alignment2 start2 r2 count2 recycled2 plan2 br id fresh out slot pubs acks final :
 Safe vi oi initial -> external_structure marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) false (neutral_flash recycled) plan dr ->
 writer_end dr=WriterComplete -> ranges entry=[block_pages (recycle_lo r) (useful_pages r)] ->
 let image1:=image_replace image index (Some entry) in
 let s1:=exact_attach ranges image index entry
   (data_next DataWritten (snapshot_written (data_next (DataReserve (block_pages (recycle_lo r) (useful_pages r))) s))) in
 reusable_search sector fuel2 recognize (writer_flash dr) (protection_table s1)
   req2 round2 alignment2 pages start2=FoundRecyclable r2 ->
 erase_geometry g sector r2 count2 -> recycling_run g sector recognize magic r2 count2 (writer_flash dr) recycled2 ->
 neutral_end_ recycled2=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r2) (useful_pages r2)) true (neutral_flash recycled2) plan2 br ->
 writer_end br=WriterComplete ->
 contains (block_pages (recycle_lo r2) (useful_pages r2)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash br)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r2) (useful_pages r2) -> recovered_image fresh=image1 ->
 let prepared:=install_candidate (snapshot_written
   (reservation_state true (block_pages (recycle_lo r2) (useful_pages r2)) s1)) in
 let next_view:=install_decoded_view view ranges id fresh in
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len (validate (writer_flash br)) (N.of_nat id))
   (Logged (Ready (writer_flash br)) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len (validate (writer_flash br)) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract next_view marker id (List.hd [] (protection_saved prepared)))
   (client_finish_program id (recovered_image fresh) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   prepared (ClientReturned (DataClientSuccess id (recovered_image fresh))) final ->
 let receipt:=Receipt (pred (length pubs)) (Certificate id fresh) in
 let destination:=((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id fresh final),
   observe_client (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id fresh)
     (evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r2) (useful_pages r2)) (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) [Certificate id fresh])) in
 Trace vi oi initial (receipt::events) (validate (writer_flash br)) next_view destination /\
 Safe (validate (writer_flash br)) next_view destination /\
 boundary_receipts destination=receipt::events++boundary_receipts initial.
Proof.
 intros INIT STRUCT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE RANGE image1 s1
   SEARCH2 GEO2 RUN2 OK2 WRITE2 COMPLETE2 AT OLDAT READ BOSS IMAGE prepared next_view TRACE ACK POST receipt destination.
 destruct (recycled_data_attach_episode vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled plan dr index entry
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE RANGE) as [previous [PATH SOURCE]].
 exact (recycled_publication_client_episode vi oi initial events (validate (writer_flash dr)) view
   (writer_flash dr) h a old image1 s1 (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))
   recognize magic fuel2 req2 round2 alignment2 start2 r2 count2 recycled2 plan2 br id fresh out slot pubs acks final
   INIT STRUCT RAW PATH HEAD eq_refl LOCAL SEARCH2 GEO2 RUN2 OK2 WRITE2 COMPLETE2 AT OLDAT READ BOSS IMAGE
   TRACE ACK POST).
Qed.

(* The old certificate and rollback caller are obtained from the preceding
   trace. [resolved] is the local range resolver response, not a coverage
   premise; collection's executed/skipped/fatal decision remains explicit. *)
Theorem normal_rollback_from_trace vi oi initial events valid view f h a image root s e old resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists d,
 let destination:=((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e)) in
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall restored, snd (fst destination)=IdleBoundary old d restored ->
   data_caller DataBegin restored /\
   Trace vi oi initial events valid view
    ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin restored)),e) /\
   Safe valid view
    ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin restored)),e)).
Proof.
 intros INIT CONTEXT PREFIX P HEAD MASK.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CONTEXT PREFIX) as CTX.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [c [IN ID]].
 destruct c as [id d];simpl in ID;subst id.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
    ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))).
 { apply rollback_external_episode;assumption. }
 assert (FULL:Trace vi oi initial events valid view
    ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [FINAL [OBS REST]].
 exists d;split;[exact FULL|]. split;[exact FINAL|]. split;[exact OBS|].
 intros restored EQ;simpl in EQ;rewrite EQ in FULL,FINAL;cbn [fst snd] in FULL,FINAL;autorewrite with control_evidence in FULL,FINAL.
 destruct (common_begin sector data_len valid view marker ranges decode pages
    (Logged (Ready f) h a) old d restored (proj1 FINAL)) as [CALL NEXT].
 split;[exact CALL|]. split.
 - eapply episodes_append with (more:=[]);[exact FULL|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply begin_episode|apply episodes_nil].
 - exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages G DIV
      _ _ _ _ _ _ _ FINAL (begin_episode g sector data_len marker ranges decode topology pages
        valid view (Logged (Ready f) h a) old d restored e))).
Qed.

Theorem drop_then_rollback_from_trace vi oi initial events valid view f h a image root s e p old resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=Some p -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists d,
 Trace vi oi initial events valid view
  ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback (data_next DataDrop s))),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback (data_next DataDrop s))))) (e)) /\
 Safe valid view
  ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback (data_next DataDrop s))),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback (data_next DataDrop s))))) (e)).
Proof.
 intros INIT CTX PREFIX P HEAD MASK.
 assert (PATH:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OpenBoundary image root (data_next DataDrop s)),e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply drop_unattached_episode;exact P|apply episodes_nil]. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root (data_next DataDrop s) e old resolved
   INIT CTX PATH eq_refl HEAD MASK) as [d [FULL [SAFE REST]]]. exists d;auto.
Qed.

Theorem recycled_writer_local_rollback vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled boss plan result resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) boss (neutral_flash recycled) plan result ->
 (writer_end result=WriterLocalError \/ writer_end result=WriterRetainError) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 let reserved:=reservation_state boss (block_pages (recycle_lo r) (useful_pages r)) s in
 exists previous d,
 let cleaned:=preparation_error_state (writer_end result) reserved in
 let destination:=((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)),phase_evidence (snd ((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)))) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall restored,snd (fst destination)=IdleBoundary old d restored -> data_caller DataBegin restored).
Proof.
 intros INIT CTX RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE ERROR MASK reserved.
 destruct (recycled_writer_episode vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled boss plan result
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SAFE OBS]]].
 assert (CLEAN:Trace vi oi initial events (validate (writer_flash result)) view
  ((Logged (Ready (writer_flash result)) h a,OpenBoundary image root
    (preparation_error_state (writer_end result) reserved)),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))).
 { destruct ERROR as [E|E];unfold writer_exit_boundary in PATH;rewrite E in PATH |- *;exact PATH. }
 assert (PN:pending_preparation (preparation_error_state (writer_end result) reserved)=None).
 { destruct ERROR as [E|E];rewrite E;[destruct boss|];reflexivity. }
 destruct (normal_rollback_from_trace vi oi initial events (validate (writer_flash result)) view
   (writer_flash result) h a image root (preparation_error_state (writer_end result) reserved)
   (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) old resolved INIT CTX CLEAN PN HEAD MASK)
   as [d [FULL [FINAL [RECEIPTS NEXT]]]].
 exists previous,d;split;[exact FULL|]. split;[exact FINAL|]. split;[exact RECEIPTS|].
 intros restored EQ;exact (proj1 (NEXT restored EQ)).
Qed.

Theorem prepared_rejection_from_trace vi oi initial events valid view f h a id candidate s e old resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) ->
 hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists previous,
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)))) (e)) /\
 Safe valid view ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)))) (e)).
Proof.
 intros INIT CTX PREFIX HEAD MASK.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as CONTEXT.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [c [IN ID]].
 destruct c as [n previous];simpl in ID;subst n.
 assert (STEP:Step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) None valid view
   ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)))) (e))).
 { apply rollback_prepared_episode;assumption. }
 exists previous;split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil].
 - exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ SOURCE STEP)).
Qed.

(* Successful restoration uses the currently certified prestate. A failed
   mask resolver is fatal only when the real collection guard is enabled. *)
Definition rollback_collection_run view old s resolved :=
 if collection_enabled true (Some old) (Some old) s then
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
     (client_finish_contract view marker old []) collection_service_prefix)
     s resolved (client_collection_next old resolved s)
 else resolved=None.

Theorem freer_normal_rollback_from_trace vi oi initial events valid view f h a image root s e old
 rolled resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure DataAPI)
   data_contract (data_program [DataClose [] (physical_authority s) false])) s tt rolled ->
 rollback_collection_run view old rolled resolved ->
 data_caller (DataClose [] (physical_authority s) false) s /\
 collection_boundary view marker (Some old) (Some old) (object_extents (view old)) [] rolled /\
 exists d,Trace vi oi initial events valid view ((Logged (Ready f) h a,failure_phase old d resolved rolled),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved rolled))) (e)) /\
 Safe valid view ((Logged (Ready f) h a,failure_phase old d resolved rolled),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved rolled))) (e)).
Proof.
 intros INIT CTX PREFIX P HEAD CLOSE COLLECT.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as CONTEXT.
 assert (PH:physical_authority s=root_extents (view old)).
 { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 SOURCE))))) as LINK.
   unfold protection_history_link in LINK;simpl in LINK;rewrite HEAD in LINK;simpl in LINK;rewrite Nat2N.id in LINK;exact LINK. }
 assert (EQ:rolled=normal_external_rollback s).
 { apply data_program_post in CLOSE. exact CLOSE. }
 subst rolled.
 destruct (normal_rollback_callers view marker old s CONTEXT P PH) as [CALL BOUND].
 split;[exact CALL|]. split;[exact BOUND|].
 assert (MASK:forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []).
 { unfold rollback_collection_run in COLLECT;destruct collection_enabled.
   - eapply collection_service_prefix_mask;exact COLLECT.
   - intros mask EQ;congruence. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root s e old resolved
   INIT CTX PREFIX P HEAD MASK) as [d [FULL [FINAL REST]]]. exists d;auto.
Qed.

(* Operational witness schema: the second episode is an execution, not a
   renewed invariant. It may use the recycled producers at the same address. *)
Theorem rollback_then_next_success vi oi f0 h a0 old d0 ram0 e0 events valid view f a image root s e
 mask receipt vf of_ jf id df sf ef :
 Safe vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) ->
 Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) events valid view
   ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None ->
 mask=collect_ranges view marker (Some old) (object_extents (view old)) [] ->
 let restored:=preparation_collection old (Some mask) (normal_external_rollback s) in
 Trace valid view
   ((Logged (Ready f) h a,OpenBoundary (recovered_image d0) [recovered_boss d0] (data_next DataBegin restored)),e)
   [receipt] vf of_ ((jf,ClientBoundary id df sf),ef) ->
 Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) (receipt::events) vf of_
   ((jf,ClientBoundary id df sf),ef) /\
 Safe vf of_ ((jf,ClientBoundary id df sf),ef) /\
 boundary_receipts ((jf,ClientBoundary id df sf),ef)=receipt::events++client_receipts e0 /\
 data_caller DataBegin restored.
Proof.
 intros INIT PREFIX P MASK restored NEXT.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 destruct (normal_rollback_from_trace vi oi _ events valid view f h a image root s e old (Some mask)
   INIT I PREFIX P HEAD ltac:(intros m EQ;congruence))
   as [d [FULL [FINAL [OBS BEGIN]]]].
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 assert (SH:failure_phase old d (Some mask) (normal_external_rollback s)=IdleBoundary old d restored).
 { rewrite (normal_rollback_phase old d (Some mask) s (proj1 (proj2 (proj2 (proj1 SOURCE))))).
   unfold restored,preparation_collection;destruct collection_enabled;reflexivity. }
 rewrite SH in FULL,FINAL.
 assert (SEL:selected_live ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) (Certificate old d0)).
 { split;[exact (proj2 (proj2 INIT))|exact HEAD]. }
 destruct (episode_no_publication_transport g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ _ INIT SEL FULL eq_refl) as [LAST [SELECT BYTES]].
 pose proof (idle_selected_unique sector data_len valid view marker ranges decode pages
   f h a old d restored e (Certificate old d0) FINAL SELECT) as SAME.
 inversion SAME;subst d.
 destruct (BEGIN restored SH) as [CALL [OPEN OPEN_SAFE]].
 assert (WHOLE:Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0)
   (receipt::events) vf of_ ((jf,ClientBoundary id df sf),ef)).
 { change (receipt::events) with ([receipt]++events). eapply episodes_append;[exact OPEN|exact NEXT]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT WHOLE) as [END [RECEIPTS REST]].
 split;[exact WHOLE|]. split;[exact END|]. split;[exact RECEIPTS|exact CALL].
Qed.

Theorem rollback_reset_boot_from_trace vi oi initial events valid view f h a image root s e old resolved boot_final :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (Logged (Boot f) h a,Selecting) boot_final ->
 Trace vi oi initial events valid view ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence (e)) /\
 Safe valid view ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence (e)) /\
 boundary_receipts ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX P HEAD MASK BOOT.
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root s e old resolved
   INIT CTX PREFIX P HEAD MASK) as [d [FULL [SAFE REST]]].
 assert (CUT:Trace valid view ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))
   [] valid view ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence (e))).
 { eapply episodes_cons with (event:=None) (events:=[]).
   - apply reset_episode. apply record_step;apply reset_ready.
   - eapply episodes_cons with (event:=None) (events:=[]).
     + apply (boot_episode g sector data_len marker ranges decode topology pages
         valid view (Logged (Boot f) h a,Selecting) boot_final e);[intros;apply READERS|exact BOOT].
     + apply episodes_nil. }
 assert (ALL:Trace vi oi initial events valid view
   ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact FULL|exact CUT]. }
 split;[exact ALL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST']];auto.
Qed.

(* First segment supplied by the real recycling/writer producer, followed by
   an operational successful episode reusing that address. No second Safe. *)
Theorem recycled_error_then_reused_success vi oi f0 h a0 old d0 ram0 e0 events valid view f a image root s e
 recognize magic fuel req round alignment start r count recycled boss plan result mask
 receipt historical vf of_ jf fresh sf ef :
 Safe vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) ->
 raw_order sector 256 data_len (Logged (Ready f0) h a0) ->
 Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) events valid view
    ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) boss (neutral_flash recycled) plan result ->
 writer_end result=WriterLocalError -> writer_prefix result<>[] ->
 mask=collect_ranges view marker (Some old) (object_extents (view old)) [] ->
 let reused:=offset (block_pages (recycle_lo r) (useful_pages r)) in
 let cleaned:=preparation_error_state (writer_end result)
    (reservation_state boss (block_pages (recycle_lo r) (useful_pages r)) s) in
 let restored:=preparation_collection old (Some mask) (normal_external_rollback cleaned) in
 In historical (client_receipts e0) -> certificate_id (receipt_certificate historical)=reused ->
 image_dependencies ranges (recovered_image (certificate_decoded (receipt_certificate historical)))<>
 image_dependencies ranges (recovered_image fresh) ->
 Trace (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary (recovered_image d0) [recovered_boss d0]
      (data_next DataBegin restored)),selected_evidence old d0 (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))
   [receipt] vf of_ ((jf,ClientBoundary reused fresh sf),ef) ->
 Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) (receipt::events) vf of_
    ((jf,ClientBoundary reused fresh sf),ef) /\
 Safe vf of_ ((jf,ClientBoundary reused fresh sf),ef) /\
 In historical (client_receipts ef) /\
 data_caller DataBegin restored.
Proof.
 intros INIT RAW PREFIX P LOCAL SEARCH GEO RUN OK WRITE ERROR NONEMPTY MASK reused cleaned restored
   HIST AT DIFFERENT NEXT.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 destruct (recycled_writer_episode vi oi _ events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled boss plan result
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SOURCE OBS]]].
 assert (CLEAN:Trace vi oi ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) events
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary image root cleaned),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))).
 { unfold writer_exit_boundary in PATH;rewrite ERROR in PATH;unfold cleaned;rewrite ERROR;exact PATH. }
 assert (SEL:selected_live ((Logged (Ready f0) h a0,IdleBoundary old d0 ram0),e0) (Certificate old d0)).
 { split;[exact (proj2 (proj2 INIT))|exact HEAD]. }
 destruct (episode_no_publication_transport g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ _ INIT SEL CLEAN eq_refl) as [SAFE [[IN HEAD'] BYTES]].
 simpl in IN;destruct IN as [SAME|[]];inversion SAME;subst previous.
 assert (PN:pending_preparation cleaned=None).
 { unfold cleaned;rewrite ERROR;destruct boss;reflexivity. }
 destruct (rollback_then_next_success vi oi f0 h a0 old d0 ram0 e0 events (validate (writer_flash result)) view
   (writer_flash result) a image root cleaned (selected_evidence old d0 (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) mask receipt vf of_ jf reused fresh sf ef
   INIT CLEAN PN MASK NEXT) as [FULL [FINAL [RECEIPTS CALL]]].
 split;[exact FULL|]. split;[exact FINAL|]. split;[|exact CALL].
 change (In historical (boundary_receipts ((jf,ClientBoundary reused fresh sf),ef))).
 rewrite RECEIPTS;simpl;right;apply in_or_app;right;exact HIST.
Qed.

Theorem checked_recycling_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result boss word_max :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 offset span+RetentionCoverage.span span<=word_max -> page_limit span<=1024 ->
 exists previous,
 let destination:=(recycling_acquisition_boundary old image root s h a result span boss,phase_evidence (snd (recycling_acquisition_boundary old image root s h a result span boss)) (selected_evidence old previous (recycling_cursor_evidence result span e))) in
 Trace vi oi initial events (validate (neutral_flash result)) view destination /\
 Safe (validate (neutral_flash result)) view destination /\
 (neutral_end_ result=NeutralSuccess ->
   ram_reservation_check true word_max span s=None /\
   checked_reservation true word_max boss span s=(None,reservation_state boss span s) /\
   reservation_handoff sector (neutral_flash result) (reservation_state boss span s) (reservation_token boss span)).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN span BOUND CAP.
 destruct (recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count result boss INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH [SAFE [ORDER HANDOFF]]]].
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (recycling_physical_handoff g sector fuel recognize magic f (protection_table s) req round alignment pages start
   r count result (required_ranges s) LOCAL (proj1 (proj1 (proj1 (proj1 SOURCE))))
   (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 SOURCE)))))) SEARCH GEO RUN) as [V [KEEP [FRAME DONE]]].
 exists previous;split;[exact PATH|]. split;[exact SAFE|]. intro OK.
 assert (CHECK:ram_reservation_check true word_max span s=None).
 { apply free_admitted_reservation_cannot_fail;[exact BOUND|exact CAP|exact (proj1 (DONE OK))]. }
 split;[exact CHECK|]. split;[unfold checked_reservation;rewrite CHECK;reflexivity|exact (HANDOFF OK)].
Qed.

Theorem failed_restore_from_trace vi oi initial events valid view f h a image root s e old reader inspect valid_image outcome :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) -> root<>[boss_extent (view old)] ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector f) old) inspect valid_image) restore_probe) tt outcome tt ->
 (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed \/ outcome=RestorePanicked) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) /\
 Safe valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) /\
 boundary_receipts ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX P HEAD CHANGED RUN ERROR.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as SCOPE.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
   ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))).
 { destruct ERROR as [ER|[ER|ER]].
   - eapply restore_failed_episode;eauto.
   - eapply restore_failed_episode;eauto.
   - pose proof (restore_probe_outcome _ _ _ _ RUN) as OBS;rewrite ER in OBS.
     destruct (reader (object_flash sector f) old) as [bytes|] eqn:READ;[|discriminate].
     destruct (inspect bytes) eqn:INSPECT.
     + destruct (valid_image bytes);discriminate.
     + eapply restore_panic_episode;eauto. }
 assert (FULL:Trace vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS REST]];auto.
Qed.

Theorem failed_restore_boot_from_trace vi oi initial events valid view f h a image root s e old reader inspect valid_image outcome final :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) -> root<>[boss_extent (view old)] ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector f) old) inspect valid_image) restore_probe) tt outcome tt ->
 (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed \/ outcome=RestorePanicked) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
    (Logged (Boot f) h a,Selecting) final ->
 Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
 Safe valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
 boundary_receipts ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX P HEAD CHANGED RUN ERROR BOOT.
 destruct (failed_restore_from_trace vi oi initial events valid view f h a image root s e old reader inspect valid_image outcome
   INIT CTX PREFIX P HEAD CHANGED RUN ERROR) as [PATH [SAFE OBS]].
 assert (SUFFIX:Trace valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) [] valid view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))).
 { eapply episodes_cons with (event:=None) (events:=[]).
   - apply reset_episode;apply record_step;apply reset_ready.
   - eapply episodes_cons with (event:=None) (events:=[]).
     + apply (boot_episode g sector data_len marker ranges decode topology pages
         valid view (Logged (Boot f) h a,Selecting) final e);[intros;apply READERS|exact BOOT].
     + apply episodes_nil. }
 assert (ALL:Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PATH|exact SUFFIX]. }
 split;[exact ALL|]. destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [RECEIPTS REST]];auto.
Qed.

Theorem interrupted_restore_boot_from_trace vi oi initial events valid view f h a image root s e old reader inspect valid_image cut final :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) -> root<>[boss_extent (view old)] ->
 restore_cut_reached (reader (object_flash sector f) old) inspect valid_image cut ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (Logged (Boot f) h a,Selecting) final ->
 Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
 Safe valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
 boundary_receipts ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX P HEAD CHANGED CUT BOOT.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as SCOPE.
 assert (SUFFIX:Trace valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) [] valid view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))).
 { eapply episodes_cons with (event:=None) (events:=[]).
   - eapply restore_cut_episode;eauto.
   - eapply episodes_cons with (event:=None) (events:=[]).
     + apply (boot_episode g sector data_len marker ranges decode topology pages
         valid view (Logged (Boot f) h a,Selecting) final e);[intros;apply READERS|exact BOOT].
     + apply episodes_nil. }
 assert (ALL:Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|exact SUFFIX]. }
 split;[exact ALL|]. destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem recycling_cut_boot_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result final :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 neutral_end_ result=NeutralSuccess ->
 clos_refl_trans boot_state (boot_step g sector data_len (validate (neutral_flash result)) marker ranges decode topology pages)
   (Logged (Boot (neutral_flash result)) h a,Selecting) final ->
 exists previous,
 Trace vi oi initial events (validate (neutral_flash result)) view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (selected_evidence old previous e)) /\
 Safe (validate (neutral_flash result)) view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (selected_evidence old previous e)) /\
 boundary_receipts ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (selected_evidence old previous e))
   =events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK BOOT.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 assert (SUFFIX:Trace valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) []
   (validate (neutral_flash result)) view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (selected_evidence old previous e))).
 { eapply episodes_cons with (event:=None) (events:=[]).
   - eapply cut_recycled_before_reserve;eauto.
   - eapply episodes_cons with (event:=None) (events:=[]).
     + apply (boot_episode g sector data_len marker ranges decode topology pages
         (validate (neutral_flash result)) view (Logged (Boot (neutral_flash result)) h a,Selecting)
         final (selected_evidence old previous e));[intros;apply READERS|exact BOOT].
     + apply episodes_nil. }
 assert (ALL:Trace vi oi initial events (validate (neutral_flash result)) view
   ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (selected_evidence old previous e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|exact SUFFIX]. }
 exists previous;split;[exact ALL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem reconstructed_trace_opens vi oi initial events valid view j id d ram e :
 Safe vi oi initial -> Trace vi oi initial events valid view ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence (e)) ->
 Trace vi oi initial events valid view
   ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),recovered_page_evidence j id (forget_volatile_evidence e)) /\
 Safe valid view ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),recovered_page_evidence j id (forget_volatile_evidence e)) /\
 data_caller DataBegin ram.
Proof.
 intros INIT PREFIX.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (enriched_boot_usable sector data_len valid view marker ranges decode pages _ _ _ _ _ SOURCE)
   as [IDLE [CERT [CALL OPEN]]].
 split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply resume_episode|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply begin_episode|apply episodes_nil].
 - split;[apply recovered_page_evidence_invariant;exact OPEN|exact CALL].
Qed.

Theorem prepared_restore_failure_from_trace vi oi initial events valid view f h a id candidate s e old reader inspect valid_image outcome :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) ->
 hd_error h=Some (N.of_nat old) -> id<>old ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector f) old) inspect valid_image) restore_probe) tt outcome tt ->
 (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed \/ outcome=RestorePanicked) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) /\
 Safe valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) /\
 boundary_receipts ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX HEAD CHANGED RUN ERROR.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as SCOPE.
 assert (ALL:Trace vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply restore_prepared_failed_episode;eauto.
   - apply episodes_nil. }
 split;[exact ALL|]. destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem prepared_restore_cut_from_trace vi oi initial events valid view f h a id candidate s e old reader inspect valid_image cut :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) ->
 hd_error h=Some (N.of_nat old) -> id<>old ->
 restore_cut_reached (reader (object_flash sector f) old) inspect valid_image cut ->
 Trace vi oi initial events valid view ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e)) /\
 Safe valid view ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e)) /\
 boundary_receipts ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e))=events++boundary_receipts initial.
Proof.
 intros INIT CTX PREFIX HEAD CHANGED CUT.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as SCOPE.
 assert (ALL:Trace vi oi initial events valid view ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply restore_prepared_cut_episode;eauto.
   - apply episodes_nil. }
 split;[exact ALL|]. destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem fatal_trace_boot vi oi initial events valid view f h a e final :
 Safe vi oi initial -> Trace vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e)) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (Logged (Boot f) h a,Selecting) final ->
 Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
 Safe valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)).
Proof.
 intros INIT PREFIX BOOT.
 assert (ALL:Trace vi oi initial events valid view ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - apply reset_episode;apply record_step;apply reset_ready.
   - eapply episodes_cons with (event:=None) (events:=[]).
     + apply (boot_episode g sector data_len marker ranges decode topology pages
         valid view (Logged (Boot f) h a,Selecting) final e);[intros;apply READERS|exact BOOT].
     + apply episodes_nil. }
 split;[exact ALL|]. exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL)).
Qed.

Theorem checked_drop_from_trace vi oi initial events valid view j image root s e p initialized word_max :
 Safe vi oi initial -> Trace vi oi initial events valid view ((j,OpenBoundary image root s),e) ->
 pending_preparation s=Some p ->
 let phase:=if protection_frozen s then OpenBoundary image root (data_next DataDrop s)
   else match range_check initialized word_max (prep_range p) with
        | None=>OpenBoundary image root (data_next DataDrop s) | Some _=>FatalBoundary end in
 let destination:=((j,phase),phase_evidence phase e) in
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 boundary_receipts destination=events++boundary_receipts initial.
Proof.
 intros INIT PREFIX P phase destination.
 assert (STEP:Step valid view ((j,OpenBoundary image root s),e) None valid view destination).
 { unfold destination,phase;destruct (protection_frozen s) eqn:F;autorewrite with control_evidence.
   - eapply drop_unattached_episode;eauto.
   - destruct (range_check initialized word_max (prep_range p)) eqn:CHECK;autorewrite with control_evidence.
     + eapply drop_checked_failure;eauto.
     + eapply drop_unattached_episode;eauto. }
 assert (ALL:Trace vi oi initial events valid view destination).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 split;[exact ALL|]. destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem rejected_admission_from_trace vi oi initial events valid view f h a image root s e old provider which resolved :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) -> which<>CompareContents ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
   (check_contract provider) (check_program which)) tt false tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists d,
 Trace vi oi initial events valid view ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e)) /\
 Safe valid view ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e)) /\
 boundary_receipts ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))=events++boundary_receipts initial /\
 (forall restored,failure_phase old d resolved (normal_external_rollback s)=IdleBoundary old d restored -> data_caller DataBegin restored).
Proof.
 intros INIT CTX PREFIX P HEAD WHICH CHECK MASK.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as SCOPE.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id d] [IN ID]];simpl in ID;subst id.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
   ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))).
 { eapply admission_check_rejected;eauto. }
 assert (ALL:Trace vi oi initial events valid view ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]].
 exists d;split;[exact ALL|]. split;[exact END|]. split;[exact OBS|].
 intros restored EQ;rewrite EQ in END.
 exact (proj1 (common_begin sector data_len valid view marker ranges decode pages
    (Logged (Ready f) h a) old d restored (proj1 END))).
Qed.

Theorem recycled_rehome_failure_rollback vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result resolved initialized word_max roots err table_after :
 Safe vi oi initial -> external_rollback_context marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 let reserved:=reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s in
 checked_rehome initialized word_max (block_pages (recycle_lo r) (useful_pages r))
   (DeferredSnapshots.snapshot_owner roots) (protection_table reserved)=(Some err,table_after) ->
 table_after=protection_table reserved /\
 exists previous d,
 let cleaned:=snapshot_retain_error reserved in
 let destination:=((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)),phase_evidence (snd ((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)))) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall restored,snd (fst destination)=IdleBoundary old d restored -> data_caller DataBegin restored).
Proof.
 intros INIT CTX RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE MASK reserved CHECK.
 split;[eapply checked_rehome_failure;exact CHECK|].
 pose proof (completed_writer_retain_error _ _ _ _ _ _ WRITE COMPLETE) as FAIL.
 exact (recycled_writer_local_rollback vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled true plan
   (WriterObservation (writer_flash result) (writer_prefix result) WriterRetainError) resolved
   INIT CTX RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK FAIL (or_intror eq_refl) MASK).
Qed.

Theorem writer_drop_failure_from_trace vi oi initial events valid view f h a old image root s e p plan result initialized word_max err :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_writer_run g sector s p false f plan result ->
 prep_kind p=ObjectPreparation -> writer_end result=WriterLocalError ->
 range_check initialized word_max (prep_range p)=Some err ->
 exists previous,
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e)) /\
 Safe (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e)) /\
 boundary_receipts ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))
   =events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD RUN KIND ERROR CHECK.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 assert (ALL:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply writer_drop_checked_failure;eauto.
   - apply episodes_nil. }
 exists previous;split;[exact ALL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.

Theorem admitted_drop_from_trace vi oi initial events valid view j image root s e p initialized word_max source :
 Safe vi oi initial -> Trace vi oi initial events valid view ((j,OpenBoundary image root s),e) ->
 pending_preparation s=Some p -> protection_frozen s=false ->
 ram_reservation_check initialized word_max (prep_range p) source=None ->
 checked_release initialized word_max (prep_range p) (protection_table s)=
   (None,protection_table (data_next DataDrop s)) /\
 Trace vi oi initial events valid view ((j,OpenBoundary image root (data_next DataDrop s)),e) /\
 Safe valid view ((j,OpenBoundary image root (data_next DataDrop s)),e) /\
 boundary_receipts ((j,OpenBoundary image root (data_next DataDrop s)),e)=events++boundary_receipts initial.
Proof.
 intros INIT PREFIX P F ADMISSION.
 split;[eapply checked_release_matches_drop;eauto|].
 pose proof (checked_drop_from_trace vi oi initial events valid view j image root s e p initialized word_max
   INIT PREFIX P) as RESULT.
 rewrite F in RESULT;rewrite (range_check_from_reservation _ _ _ _ ADMISSION) in RESULT;cbn [fst snd] in RESULT;autorewrite with control_evidence in RESULT;exact RESULT.
Qed.

(* The pair's two concrete scopes are closed locally before this arbitrary
   operational suffix. NEXT is an execution, never an invariant of its result. *)
Theorem outer_pair_then_suffix valid view f h a old d s e ia ib ea eb ra rb pa pb wa wb same eq_a eq_b
 events vf of_ final :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 changed_pair same eq_a eq_b=[0;1] ->
 runtime_erased_admission sector pages e (outer_local_begin s) f ra ->
 writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges ea=[ra] ->
 runtime_erased_admission sector pages (advance_allocation_evidence ra e) (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) (writer_flash wa) rb ->
 writer_execution g sector rb false (writer_flash wa) pb wb -> writer_end wb=WriterComplete -> ranges eb=[rb] ->
 let accepted:=pair_accept ranges (recovered_image d) ia ib ea eb ra rb s in
 let image2:=image_replace (image_replace (recovered_image d) ia (Some ea)) ib (Some eb) in
 Trace (validate (writer_flash wb)) view
   ((Logged (Ready (writer_flash wb)) h a,OpenBoundary image2 [] accepted),selected_evidence old d (advance_allocation_evidence rb (advance_allocation_evidence ra e)))
   events vf of_ final ->
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) events vf of_ final /\
 Safe vf of_ final /\
 boundary_receipts final=events++client_receipts e /\
 protection_saved accepted=[protection_current s++attached_ranges s] /\
 collection_enabled true (Some old) (Some old) accepted=false.
Proof.
 intros INIT RAW PLAN HA WA OA RA HB WB OB RB accepted image2 NEXT.
 assert (PAIR:Step valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) None
   (validate (writer_flash wb)) view
   ((Logged (Ready (writer_flash wb)) h a,OpenBoundary image2 [] accepted),selected_evidence old d (advance_allocation_evidence rb (advance_allocation_evidence ra e)))).
 { eapply outer_pair_accepted;eauto. }
 assert (ALL:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) events vf of_ final).
 { replace events with (events++emitted_receipts None) by apply app_nil_r.
   eapply episodes_cons;[exact PAIR|exact NEXT]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]].
 split;[exact ALL|]. split;[exact END|]. split;[exact OBS|]. split;[reflexivity|].
 unfold accepted,pair_accept;apply local_accept_skips_collection.
Qed.

Theorem outer_pair_publication_callers valid view f h a old d s e ia ib ea eb ra rb pa pb wa wb same eq_a eq_b
 events vf of_ ready id fresh prepared ef kind :
 image_unique kind (recovered_image d) ->
 data_slot_for kind (recovered_image d) (entry_key kind ea)=Some ia ->
 data_slot_for kind (image_replace (recovered_image d) ia (Some ea)) (entry_key kind eb)=Some ib ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> changed_pair same eq_a eq_b=[0;1] ->
 runtime_erased_admission sector pages e (outer_local_begin s) f ra ->
 writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges ea=[ra] ->
 runtime_erased_admission sector pages (advance_allocation_evidence ra e) (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) (writer_flash wa) rb ->
 writer_execution g sector rb false (writer_flash wa) pb wb -> writer_end wb=WriterComplete -> ranges eb=[rb] ->
 Trace (validate (writer_flash wb)) view
   ((Logged (Ready (writer_flash wb)) h a,
     OpenBoundary (image_replace (image_replace (recovered_image d) ia (Some ea)) ib (Some eb)) []
       (pair_accept ranges (recovered_image d) ia ib ea eb ra rb s)),selected_evidence old d (advance_allocation_evidence rb (advance_allocation_evidence ra e)))
   events vf of_ ((ready,PublishingBoundary CandidatePrepared id fresh prepared),ef) ->
 (forall q, lookup_entry kind (image_replace (image_replace (recovered_image d) ia (Some ea)) ib (Some eb)) q =
   match object_key_eq_dec q (entry_key kind eb) with left _ => Some eb
   | right _ => match object_key_eq_dec q (entry_key kind ea) with left _ => Some ea
     | right _ => lookup_entry kind (recovered_image d) q end end) /\
 exit_calls marker (root_extents (of_ id)) (List.hd [] (protection_saved prepared))
   [SlotCompleted;DurableRamWritten;ExternalAccepted] prepared /\
 collection_boundary of_ marker (Some id) (Some id) (object_extents (of_ id)) []
   (successful_external_close marker (root_extents (of_ id)) (List.hd [] (protection_saved prepared)) prepared).
Proof.
 intros UNIQUE SELECT_A SELECT_B INIT RAW PLAN HA WA OA RA HB WB OB RB NEXT.
 destruct (outer_pair_then_suffix valid view f h a old d s e ia ib ea eb ra rb pa pb wa wb same eq_a eq_b
   events vf of_ _ INIT RAW PLAN HA WA OA RA HB WB OB RB NEXT) as [ALL REST].
 split;[eapply two_replacements_lookup;eauto|].
 exact (installed_exit_callers_from_trace valid view _ events vf of_ ready id fresh prepared ef INIT I ALL).
Qed.

(* OperationScope continuations consume the context produced by the trace,
   never an invariant supplied again by the failed writer's caller. *)
Theorem operation_writer_from_trace vi oi initial events valid view f h a image root s e old r plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 mapped_erased_admission sector pages s f r -> writer_execution g sector r false f plan result ->
 exists previous,
 Trace vi oi initial events (validate (writer_flash result)) view
  (operation_writer_exit old image root (reservation_state false r s) h a result,phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) (selected_evidence old previous (advance_allocation_evidence r e))) /\
 Safe (validate (writer_flash result)) view
  (operation_writer_exit old image root (reservation_state false r s) h a result,phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) (selected_evidence old previous (advance_allocation_evidence r e))) /\
 client_receipts (selected_evidence old previous (advance_allocation_evidence r e))=events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX P HEAD MAPPED WRITE.
 pose proof (mapped_erased_admission_forget _ _ _ _ _ MAPPED) as ADMIT.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]].
 simpl in ID;subst id.
 assert (ACQUIRE:Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
  ((Logged (Ready f) h a,OperationBoundary image root (reservation_state false r s)),advance_allocation_evidence r e)).
 { apply operation_reserve_episode;assumption. }
 assert (WRITE_STEP:Step valid view
  ((Logged (Ready f) h a,OperationBoundary image root (reservation_state false r s)),advance_allocation_evidence r e) None
  (validate (writer_flash result)) view
  (operation_writer_exit old image root (reservation_state false r s) h a result,phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) (selected_evidence old previous (advance_allocation_evidence r e)))).
 { eapply operation_writer_episode with (p:=reservation_token false r);eauto.
   split;[split;[reflexivity|exact (proj2 (erased_admission_guards _ _ _ _ ADMIT))]|exact WRITE]. }
 assert (ALL:Trace vi oi initial events (validate (writer_flash result)) view
  (operation_writer_exit old image root (reservation_state false r s) h a result,phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) (selected_evidence old previous (advance_allocation_evidence r e)))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact ACQUIRE|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact WRITE_STEP|apply episodes_nil]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [FINAL [OBS REST]].
 exists previous;split;[exact ALL|]. split;[exact FINAL|exact OBS].
Qed.

(* Miss is the executed probe; FoundErased is the actual fallback walk.
   The second acquisition observes the attached destination, not the source. *)
Theorem found_erased_then_next_acquisition vi oi initial events valid view f h a old image root s e
 word_max fuel recognize req round alignment start i n index entry plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) -> pages<=1024 -> pages*256<=word_max ->
 runtime_search_inputs sector pages word_max e s f req start ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundErased i n ->
 writer_execution g sector (block_pages i n) false f plan result -> writer_end result=WriterComplete ->
 ranges entry=[block_pages i n] ->
 exists previous,
 let attached:=exact_member ranges image index entry (block_pages i n) s in
 let reached:=selected_evidence old previous (advance_allocation_evidence (block_pages i n) e) in
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) [] attached),reached) /\
 forall next,
 runtime_erased_admission sector pages reached attached (writer_flash result) next ->
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) [] (reservation_state false next attached)),advance_allocation_evidence next reached) /\
 Safe (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) [] (reservation_state false next attached)),advance_allocation_evidence next reached) /\
 volatile_allocation (advance_allocation_evidence next reached)=
 option_map (fun source=>AllocationRuntime (extent_end next) (allocation_latest source)) (volatile_allocation e) /\
 extent_end next<=word_max /\ Nat.min word_max (extent_end next)=extent_end next.
Proof.
 intros INIT RAW PREFIX P HEAD CAP SIZE INPUTS SEARCH WRITE COMPLETE RANGE.
 assert (ADMIT:runtime_erased_admission sector pages e s f (block_pages i n)).
 { eapply runtime_search;eauto. }
 destruct (operation_writer_from_trace vi oi initial events valid view f h a image root s e old
   (block_pages i n) plan result INIT RAW PREFIX P HEAD
   (runtime_erased_admission_mapped _ _ _ _ _ _ ADMIT) WRITE) as [previous [PATH REST]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 exists previous;cbn zeta.
 assert (ATTACH:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) []
     (exact_member ranges image index entry (block_pages i n) s)),
    selected_evidence old previous (advance_allocation_evidence (block_pages i n) e))).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 split;[exact ATTACH|]. intros next NEXT.
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) []
     (reservation_state false next (exact_member ranges image index entry (block_pages i n) s))),
    advance_allocation_evidence next (selected_evidence old previous (advance_allocation_evidence (block_pages i n) e)))).
 { eapply episodes_append with (more:=[]);[exact ATTACH|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply operation_reserve_episode;[reflexivity|eapply runtime_erased_admission_forget;exact NEXT|eapply runtime_erased_admission_mapped;exact NEXT]|constructor]. }
 split;[exact FULL|]. split.
 - exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT FULL)).
 - split;[cbn;destruct (volatile_allocation e);reflexivity|].
   eapply runtime_erased_advance_bounded;[exact SIZE|exact NEXT].
Qed.

Theorem operation_cancel_from_trace vi oi initial events valid view f h a image root s e old read inspect check :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt RestoreValidated tt ->
 exists d,
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),e) /\
 Safe valid view ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),e) /\
 rollback_structure marker (operation_cancel s) /\
 collection_enabled true (Some old) (Some old) (operation_cancel s)=false.
Proof.
 intros INIT CTX PREFIX P HEAD RESTORE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as STRUCT.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id d] [IN ID]];simpl in ID;subst id.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
   ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),e)).
 { eapply operation_cancel_episode;eauto. }
 exists d;split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil].
 - exact (proj2 (certified_operation_cancel sector data_len valid view marker ranges decode pages
    f h a image root s e old d SOURCE STRUCT P HEAD IN)).
Qed.

Theorem outer_a_b_local_error_restart valid view f h a old d s e index entry ra rb pa pb wa wb
 read inspect check resolved :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 runtime_erased_admission sector pages e (outer_local_begin s) f ra ->
 writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges entry=[ra] ->
 let attached:=exact_member ranges (recovered_image d) index entry ra (outer_local_begin s) in
 runtime_erased_admission sector pages (advance_allocation_evidence ra e) attached (writer_flash wa) rb ->
 writer_execution g sector rb false (writer_flash wa) pb wb -> writer_end wb=WriterLocalError ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt RestoreValidated tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists previous restored,
 let destination:=((Logged (Ready (writer_flash wb)) h a,
   failure_phase old restored resolved
    (normal_external_rollback (operation_cancel (snapshot_error false (reservation_state false rb attached))))),phase_evidence (snd ((Logged (Ready (writer_flash wb)) h a,
   failure_phase old restored resolved
    (normal_external_rollback (operation_cancel (snapshot_error false (reservation_state false rb attached))))))) (selected_evidence old previous (advance_allocation_evidence rb (selected_evidence old d (advance_allocation_evidence ra e))))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash wb)) view destination /\
 Safe (validate (writer_flash wb)) view destination /\
 boundary_receipts destination=client_receipts e /\
 (forall ram,snd (fst destination)=IdleBoundary old restored ram ->
   data_caller DataBegin ram /\ recovered_image restored=recovered_image d /\
   volatile_allocation (snd destination)=option_map
     (fun source=>AllocationRuntime (extent_end rb) (allocation_latest source)) (volatile_allocation e)).
Proof.
 intros INIT RAW HA WA OA RA attached HB WB ERROR RESTORE MASK.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { pose proof (proj1 (proj2 (proj1 INIT))) as IDLE;exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
 assert (FIRST:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
  (validate (writer_flash wa)) view
  ((Logged (Ready (writer_flash wa)) h a,OperationBoundary
    (image_replace (recovered_image d) index (Some entry)) [] attached),selected_evidence old d (advance_allocation_evidence ra e))).
 { eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_first_episode;eauto|apply episodes_nil]. }
 destruct (operation_writer_from_trace valid view _ [] (validate (writer_flash wa)) view
   (writer_flash wa) h a (image_replace (recovered_image d) index (Some entry)) [] attached
   (selected_evidence old d (advance_allocation_evidence ra e)) old rb pb wb INIT RAW FIRST eq_refl HEAD (runtime_erased_admission_mapped _ _ _ _ _ _ HB) WB) as [previous [FAILED [SAFE OBS]]].
 unfold operation_writer_exit,writer_exit_boundary in FAILED,SAFE;rewrite ERROR in FAILED,SAFE;simpl in FAILED,SAFE.
 destruct (operation_cancel_from_trace valid view _ [] (validate (writer_flash wb)) view
   (writer_flash wb) h a (image_replace (recovered_image d) index (Some entry)) []
   (snapshot_error false (reservation_state false rb attached))
   (selected_evidence old previous (advance_allocation_evidence rb (selected_evidence old d (advance_allocation_evidence ra e)))) old read inspect check
   INIT I FAILED eq_refl HEAD RESTORE) as [local_decoded [CANCEL [CANCEL_SAFE STRUCT]]].
 destruct (normal_rollback_from_trace valid view _ [] (validate (writer_flash wb)) view
   (writer_flash wb) h a (recovered_image local_decoded) [recovered_boss local_decoded]
   (operation_cancel (snapshot_error false (reservation_state false rb attached)))
   (selected_evidence old previous (advance_allocation_evidence rb (selected_evidence old d (advance_allocation_evidence ra e)))) old resolved
   INIT I CANCEL eq_refl HEAD MASK) as [restored [FULL [FINAL [OBSERVED NEXT]]]].
 exists previous,restored;split;[exact FULL|]. split;[exact FINAL|]. split;[exact OBSERVED|].
 assert (SELECT0:selected_live ((Logged (Ready f) h a,IdleBoundary old d s),e) (Certificate old d))
   by (split;[exact (proj2 (proj2 INIT))|exact HEAD]).
 pose proof (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
   _ _ _ [] _ _ _ (Certificate old d) INIT SELECT0 FULL eq_refl) as [_ [SELECT KEEP]].
 intros ram EQ;split;[exact (proj1 (NEXT ram EQ))|]. split.
 -
 simpl in EQ;rewrite EQ in FINAL,SELECT.
 assert (SAME:Certificate old d=Certificate old restored).
 { eapply selected_live_unique;[exact FINAL|exact SELECT|].
   split;[exact (proj2 (proj2 FINAL))|exact HEAD]. }
 inversion SAME;reflexivity.
 - cbn in EQ;cbn [snd fst];unfold phase_evidence;rewrite EQ;cbn;
   destruct (volatile_allocation e);reflexivity.
Qed.

Theorem outer_a_b_writer_outcomes valid view f h a old d s e index entry ra rb pa pb wa wb :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 runtime_erased_admission sector pages e (outer_local_begin s) f ra ->
 writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges entry=[ra] ->
 let attached:=exact_member ranges (recovered_image d) index entry ra (outer_local_begin s) in
 runtime_erased_admission sector pages (advance_allocation_evidence ra e) attached (writer_flash wa) rb ->
 writer_execution g sector rb false (writer_flash wa) pb wb ->
 exists previous,
 let final:=(operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
    (reservation_state false rb attached) h a wb,phase_evidence (snd (operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
    (reservation_state false rb attached) h a wb)) (selected_evidence old previous (advance_allocation_evidence rb (selected_evidence old d (advance_allocation_evidence ra e))))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash wb)) view final /\
 Safe (validate (writer_flash wb)) view final /\
 boundary_receipts final=client_receipts e /\
 publications (boundary_journal final)=h /\
 selected_live final (Certificate old d) /\
 unchanged (certificate_ranges ranges (Certificate old d)) (object_flash sector f)
   (object_flash sector (writer_flash wb)).
Proof.
 intros INIT RAW HA WA OA RA attached HB WB.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { pose proof (proj1 (proj2 (proj1 INIT))) as IDLE;exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
 assert (FIRST:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
  (validate (writer_flash wa)) view
  ((Logged (Ready (writer_flash wa)) h a,OperationBoundary
    (image_replace (recovered_image d) index (Some entry)) [] attached),selected_evidence old d (advance_allocation_evidence ra e))).
 { eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_first_episode;eauto|apply episodes_nil]. }
 destruct (operation_writer_from_trace valid view _ [] (validate (writer_flash wa)) view
   (writer_flash wa) h a (image_replace (recovered_image d) index (Some entry)) [] attached
   (selected_evidence old d (advance_allocation_evidence ra e)) old rb pb wb INIT RAW FIRST eq_refl HEAD (runtime_erased_admission_mapped _ _ _ _ _ _ HB) WB) as [previous [FAILED [SAFE OBS]]].
 assert (HIST:publications (boundary_journal
   (operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
     (reservation_state false rb attached) h a wb,phase_evidence (snd (operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
     (reservation_state false rb attached) h a wb)) (selected_evidence old previous (advance_allocation_evidence rb (selected_evidence old d (advance_allocation_evidence ra e))))))=h).
 { unfold boundary_journal,operation_writer_exit,writer_exit_boundary;destruct (writer_end wb);reflexivity. }
 destruct (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
   _ _ _ [] _ _ _ (Certificate old d) INIT ltac:(split;[exact (proj2 (proj2 INIT))|exact HEAD]) FAILED HIST)
   as [_ [SELECT BYTES]].
 exists previous;split;[exact FAILED|]. split;[exact SAFE|].
 split;[exact OBS|]. split;[exact HIST|]. split;[exact SELECT|].
 unfold boundary_objects,boundary_journal,operation_writer_exit,writer_exit_boundary in BYTES;
   destruct (writer_end wb);exact BYTES.
Qed.

Theorem operation_frozen_cleanup_from_trace vi oi initial events valid view f h a image root s e old r plan result
 read1 inspect1 check1 read2 inspect2 check2 :
 Safe vi oi initial -> external_rollback_context marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 mapped_erased_admission sector pages s f r -> writer_execution g sector r false f plan result ->
 writer_end result=WriterPhysicalError ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read1 inspect1 check1) restore_probe) tt RestoreValidated tt ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read2 inspect2 check2) restore_probe) tt RestoreValidated tt ->
 let frozen:=snapshot_error true (reservation_state false r s) in
 let closed:=execute_data (operation_abort_commands (physical_authority frozen)) frozen in
 exists previous,
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) None closed),selected_evidence old previous (advance_allocation_evidence r e)) /\
 Safe (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) None closed),selected_evidence old previous (advance_allocation_evidence r e)) /\
 protection_table closed=protection_table frozen /\ protection_saved closed=[] /\
 ~ boundary_begin_caller (Logged (Ready (writer_flash result)) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) None closed).
Proof.
 intros INIT CTX RAW PREFIX P HEAD ADMIT WRITE ERROR LOCAL_RESTORE OUTER_RESTORE frozen closed.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as [STACK [BASE ACK]].
 destruct (operation_writer_from_trace vi oi initial events valid view f h a image root s e old r plan result
   INIT RAW PREFIX P HEAD ADMIT WRITE) as [previous [FAILED [SAFE OBS]]].
 unfold operation_writer_exit,writer_exit_boundary in FAILED,SAFE;rewrite ERROR in FAILED,SAFE;simpl in FAILED,SAFE.
 assert (CALL:data_calls (operation_abort_commands (physical_authority frozen)) frozen).
 { apply operation_abort_calls;[reflexivity|exact STACK]. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) None closed),selected_evidence old previous (advance_allocation_evidence r e))).
 { eapply episodes_append with (more:=[]);[exact FAILED|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply frozen_scope_close;[exact (proj1 CALL)|exact LOCAL_RESTORE].
   - eapply episodes_cons with (event:=None) (events:=[]).
     + eapply frozen_scope_close;[exact (proj1 (proj2 CALL))|exact OUTER_RESTORE].
     + apply episodes_nil. }
 exists previous;split;[exact FULL|]. split.
 - exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
     G DIV _ _ _ _ _ _ _ INIT FULL)).
 - destruct (operation_abort_frozen_table frozen eq_refl) as [TABLE [AUTH SAVED]].
   split;[exact TABLE|]. split;[exact SAVED|apply frozen_no_begin].
Qed.

Theorem operation_restore_stop_from_trace vi oi initial events valid view j image root s e read inspect check outcome :
 Safe vi oi initial ->
 Trace vi oi initial events valid view ((j,OperationBoundary image root s),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt -> outcome<>RestoreValidated ->
 Trace vi oi initial events valid view ((j,FatalBoundary),forget_volatile_evidence (e)) /\
 Safe valid view ((j,FatalBoundary),forget_volatile_evidence (e)) /\
 boundary_receipts ((j,FatalBoundary),forget_volatile_evidence (e))=events++boundary_receipts initial /\
 ~ boundary_begin_caller (j,FatalBoundary).
Proof.
 intros INIT PREFIX PROBE FAIL.
 assert (FULL:Trace vi oi initial events valid view ((j,FatalBoundary),forget_volatile_evidence (e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_restore_fatal;eauto|apply episodes_nil]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [FINAL [OBS REST]].
 split;[exact FULL|]. split;[exact FINAL|]. split;[exact OBS|apply fatal_no_begin].
Qed.

Theorem operation_drop_failure_from_trace vi oi initial events valid view f h a old image root s e p plan result initialized word_max err :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_writer_run g sector s p false f plan result ->
 prep_kind p=ObjectPreparation -> writer_end result=WriterLocalError ->
 range_check initialized word_max (prep_range p)=Some err ->
 exists previous,
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e)) /\
 Safe (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e)) /\
 boundary_receipts ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))
   =events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD RUN KIND ERROR CHECK.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 assert (ALL:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply operation_drop_checked_failure;eauto.
   - apply episodes_nil. }
 exists previous;split;[exact ALL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT ALL) as [END [OBS REST]];auto.
Qed.
Theorem operation_recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 exists previous,
 let final:=(operation_acquisition_boundary old image root s h a result span,phase_evidence (snd (operation_acquisition_boundary old image root s h a result span)) (selected_evidence old previous (recycling_cursor_evidence result span e))) in
 Trace vi oi initial events (validate (neutral_flash result)) view final /\
 Safe (validate (neutral_flash result)) view final /\
 raw_order sector 256 data_len (boundary_journal final) /\
 (neutral_end_ result=NeutralSuccess -> reservation_handoff sector (neutral_flash result)
   (reservation_state false span s) (reservation_token false span)).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN span.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 pose proof (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
   f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
   G DIV SOURCE ORDER HEAD IN (READERS _) LOCAL ACCEPT P SEARCH GEO RUN) as [LAST [KEEP [ORDER' HANDOFF]]].
 exists previous. split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|].

   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_acquire_recycled;eauto|apply episodes_nil].
 - split;[apply operation_phase_safe;exact LAST|]. split;[unfold boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary in *;destruct (neutral_end_ result);exact ORDER'|exact HANDOFF].
Qed.
Theorem operation_recycled_writer_episode vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) false (neutral_flash recycled) plan result ->
 let reserved:=reservation_state false (block_pages (recycle_lo r) (useful_pages r)) s in
 exists previous,
 let final:=(operation_writer_exit old image root reserved h a result,phase_evidence (snd (operation_writer_exit old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 boundary_receipts final=events++boundary_receipts initial.
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE reserved.
 destruct (operation_recycling_acquisition_from_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _
   recognize magic fuel req round alignment start r count recycled INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH [SOURCE [ORDER HANDOFF]]]].
 unfold recycling_cursor_evidence,operation_acquisition_boundary,recycling_acquisition_boundary in PATH,SOURCE,ORDER;rewrite OK in PATH,SOURCE,ORDER.
 assert (STEP:Step (validate (neutral_flash recycled)) view
    ((Logged (Ready (neutral_flash recycled)) h a,OperationBoundary image root reserved),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) None
    (validate (writer_flash result)) view
    (operation_writer_exit old image root reserved h a result,phase_evidence (snd (operation_writer_exit old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)))).
 { eapply operation_writer_episode with (e:=selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e));[exact ORDER|exact HEAD|simpl;auto|apply READERS|exact ACCEPT| |].
   - split;[exact (HANDOFF OK)|exact WRITE].
   - reflexivity. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   (operation_writer_exit old image root reserved h a result,phase_evidence (snd (operation_writer_exit old image root reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)))).
 { eapply episodes_append with (more:=[]);[exact PATH|].

   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|apply episodes_nil]. }
 exists previous. split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [LAST [OBS REST]]. auto.
Qed.
Theorem checked_operation_recycling_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result word_max :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 offset span+RetentionCoverage.span span<=word_max -> page_limit span<=1024 ->
 exists previous,
 let destination:=(operation_acquisition_boundary old image root s h a result span,phase_evidence (snd (operation_acquisition_boundary old image root s h a result span)) (selected_evidence old previous (recycling_cursor_evidence result span e))) in
 Trace vi oi initial events (validate (neutral_flash result)) view destination /\
 Safe (validate (neutral_flash result)) view destination /\
 (neutral_end_ result=NeutralSuccess ->
   ram_reservation_check true word_max span s=None /\
   checked_reservation true word_max false span s=(None,reservation_state false span s) /\
   reservation_handoff sector (neutral_flash result) (reservation_state false span s) (reservation_token false span)).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN span BOUND CAP.
 destruct (operation_recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count result INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH [SAFE [ORDER HANDOFF]]]].
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (recycling_physical_handoff g sector fuel recognize magic f (protection_table s) req round alignment pages start
   r count result (required_ranges s) LOCAL (proj1 (proj1 (proj1 (proj1 SOURCE))))
   (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 SOURCE)))))) SEARCH GEO RUN) as [V [KEEP [FRAME DONE]]].
 exists previous;split;[exact PATH|]. split;[exact SAFE|]. intro OK.
 assert (CHECK:ram_reservation_check true word_max span s=None).
 { apply free_admitted_reservation_cannot_fail;[exact BOUND|exact CAP|exact (proj1 (DONE OK))]. }
 split;[exact CHECK|]. split;[unfold checked_reservation;rewrite CHECK;reflexivity|exact (HANDOFF OK)].
Qed.
Theorem operation_recycled_member vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result index entry :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) false (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete -> ranges entry=[block_pages (recycle_lo r) (useful_pages r)] ->
 exists previous,
 let attached:=exact_member ranges image index entry (block_pages (recycle_lo r) (useful_pages r)) s in
 Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) [] attached),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) /\
 Safe (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) [] attached),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE DONE RANGE.
 destruct (operation_recycled_writer_episode vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled plan result
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SAFE OBS]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH,SAFE;rewrite DONE in PATH,SAFE;simpl in PATH,SAFE.
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary (image_replace image index (Some entry)) []
      (exact_member ranges image index entry (block_pages (recycle_lo r) (useful_pages r)) s)),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_attach_episode;try reflexivity;exact RANGE|apply episodes_nil]. }
 exists previous;split;[exact FULL|].
 exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL)).
Qed.

Theorem operation_accept_from_trace vi oi initial events valid view j image root s e :
 Safe vi oi initial -> external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((j,OperationBoundary image root s),e) -> pending_preparation s=None ->
 let accepted:=data_next (DataClose [physical_authority s] (physical_authority s) true) s in
 Trace vi oi initial events valid view ((j,OpenBoundary image root accepted),e) /\
 Safe valid view ((j,OpenBoundary image root accepted),e) /\
 collection_enabled true None None accepted=false.
Proof.
 intros INIT CTX PREFIX P accepted.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CTX PREFIX) as STRUCT.
 assert (FULL:Trace vi oi initial events valid view ((j,OpenBoundary image root accepted),e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply operation_accept_episode;assumption|apply episodes_nil]. }
 split;[exact FULL|]. split;[exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL))|reflexivity].
Qed.

(* Numeric admission of the actual recycling footprint follows from the
   initialized geometry; no vacancy or post-reservation check is inferred. *)
Lemma recycled_extent_numeric word_max r count :
 area_start g+area_length g<=2*sector+word_max ->
 area_start g+area_length g<=2*sector+1024*256 ->
 erase_geometry g sector r count ->
 range_numeric word_max (block_pages (recycle_lo r) (useful_pages r)).
Proof. exact (numeric_recycled_extent word_max g sector r count). Qed.

Theorem operation_recycled_pair valid view f h a old d s e ia ib ea eb
 recognize magic fuelA reqA roundA alignA startA rA countA recA planA writeA
 fuelB reqB roundB alignB startB rB countB recB planB writeB word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> recognizer_local sector recognize ->
 let local:=outer_local_begin s in
 let imageA:=image_replace (recovered_image d) ia (Some ea) in
 let attachedA:=exact_member ranges (recovered_image d) ia ea (block_pages (recycle_lo rA) (useful_pages rA)) local in
 let attachedB:=exact_member ranges imageA ib eb (block_pages (recycle_lo rB) (useful_pages rB)) attachedA in
 reusable_search sector fuelA recognize f (protection_table local) reqA roundA alignA pages startA=FoundRecyclable rA ->
 erase_geometry g sector rA countA -> recycling_run g sector recognize magic rA countA f recA -> neutral_end_ recA=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo rA) (useful_pages rA)) false (neutral_flash recA) planA writeA ->
 writer_end writeA=WriterComplete -> ranges ea=[block_pages (recycle_lo rA) (useful_pages rA)] ->
 reusable_search sector fuelB recognize (writer_flash writeA) (protection_table attachedA) reqB roundB alignB pages startB=FoundRecyclable rB ->
 erase_geometry g sector rB countB -> recycling_run g sector recognize magic rB countB (writer_flash writeA) recB -> neutral_end_ recB=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo rB) (useful_pages rB)) false (neutral_flash recB) planB writeB ->
 writer_end writeB=WriterComplete -> ranges eb=[block_pages (recycle_lo rB) (useful_pages rB)] ->
 exists previousA previousB,
 let accepted:=data_next (DataClose [physical_authority attachedB] (physical_authority attachedB) true) attachedB in
 let final:=((Logged (Ready (writer_flash writeB)) h a,OpenBoundary (image_replace imageA ib (Some eb)) [] accepted),
   selected_evidence old previousB (advance_allocation_evidence (block_pages (recycle_lo rB) (useful_pages rB)) (selected_evidence old previousA (advance_allocation_evidence (block_pages (recycle_lo rA) (useful_pages rA)) e)))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash writeB)) view final /\
 Safe (validate (writer_flash writeB)) view final /\ boundary_receipts final=client_receipts e /\
 state_numeric word_max accepted /\
 volatile_allocation (snd final)=
 option_map (fun allocation=>AllocationRuntime
   (extent_end (block_pages (recycle_lo rB) (useful_pages rB)))
   (allocation_latest allocation)) (volatile_allocation e).
Proof.
 intros MARK DEC WORD CAP INIT RAW LOCAL local imageA attachedA attachedB SA GA RA OA WA CA EA SB GB RB OB WB CB EB.
 pose proof (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC) as [NUM0 _].
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { pose proof (proj1 (proj2 (proj1 INIT))) as IDLE;exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
 assert (OPEN:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] local),e)).
 { eapply episodes_cons with (event:=None) (events:=[]);[apply operation_begin_episode|apply episodes_nil]. }
 destruct (operation_recycled_member valid view _ [] valid view f h a old (recovered_image d) [recovered_boss d] local e
   recognize magic fuelA reqA roundA alignA startA rA countA recA planA writeA ia ea
   INIT RAW OPEN HEAD eq_refl LOCAL SA GA RA OA WA CA EA) as [previousA [A SAFE_A]].
 destruct (operation_recycled_member valid view _ [] (validate (writer_flash writeA)) view (writer_flash writeA) h a old imageA [] attachedA
   (selected_evidence old previousA (advance_allocation_evidence (block_pages (recycle_lo rA) (useful_pages rA)) e)) recognize magic fuelB reqB roundB alignB startB rB countB recB planB writeB ib eb
   INIT RAW A HEAD eq_refl LOCAL SB GB RB OB WB CB EB) as [previousB [B SAFE_B]].
 destruct (operation_accept_from_trace valid view _ [] (validate (writer_flash writeB)) view
   (Logged (Ready (writer_flash writeB)) h a) (image_replace imageA ib (Some eb)) [] attachedB
   (selected_evidence old previousB (advance_allocation_evidence (block_pages (recycle_lo rB) (useful_pages rB)) (selected_evidence old previousA (advance_allocation_evidence (block_pages (recycle_lo rA) (useful_pages rA)) e)))) INIT I B eq_refl) as [FULL [SAFE COLLECT]].
 exists previousA,previousB;split;[exact FULL|]. split;[exact SAFE|]. split;[reflexivity|].
 split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] (validate (writer_flash writeB)) view _ MARK DEC WORD CAP INIT NUM0 FULL)).
 - cbn [snd selected_evidence evidence_with_live advance_allocation_evidence volatile_allocation].
   destruct (volatile_allocation e);reflexivity.
Qed.

Theorem operation_recycled_writer_numeric vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 writer_execution g sector span false (neutral_flash recycled) plan result ->
 exists previous,
 let final:=(operation_writer_exit old image root (reservation_state false span s) h a result,phase_evidence (snd (operation_writer_exit old image root (reservation_state false span s) h a result)) (selected_evidence old previous (advance_allocation_evidence span e))) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 boundary_receipts final=events++boundary_receipts initial /\
 (writer_end result<>WriterInterrupted ->
   token_numeric_certificate word_max (reservation_token false span) /\
   token_numeric_certificate word_max (set_phase (reservation_token false span) Written) /\
   (forall t,checked_release true word_max span t=(None,ScopeOwnership.release_extent 256 span t)) /\
   (forall depth t,depth<=6 -> checked_rehome true word_max span depth t=(None,rehome_extent span depth t))).
Proof.
 intros MARK DEC WORD CAP INIT NUM0 RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK span WRITE.
 destruct (operation_recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN) as [prior [ACQUIRED [SAFE_ACQUIRED FACTS]]].
 pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max vi oi initial events (validate (neutral_flash recycled)) view _ MARK DEC WORD CAP INIT NUM0 ACQUIRED)) as ACQUIRED_NUM.
 unfold operation_acquisition_boundary,recycling_acquisition_boundary in ACQUIRED_NUM.
 rewrite OK in ACQUIRED_NUM;cbn [fst snd operation_phase phase_numeric] in ACQUIRED_NUM.
 pose proof (numeric_pending word_max (reservation_state false span s) (reservation_token false span)
   ACQUIRED_NUM eq_refl) as NUMERIC.
 destruct (operation_recycled_writer_episode vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled plan result
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SAFE OBS]]].
 exists previous;split;[exact PATH|]. split;[exact SAFE|]. split;[exact OBS|]. intro NOT_RESET.
 split;[exact NUMERIC|]. split;[apply numeric_token_phase;exact NUMERIC|]. split.
 - intro t;exact (numeric_token_release word_max (reservation_token false span) t NUMERIC).
 - intros depth t DEPTH;exact (numeric_token_rehome word_max (reservation_token false span) depth t NUMERIC DEPTH).
Qed.

Theorem operation_recycled_local_error_restart vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count recycled plan result word_max read inspect check resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled -> neutral_end_ recycled=NeutralSuccess ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 writer_execution g sector span false (neutral_flash recycled) plan result -> writer_end result=WriterLocalError ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt RestoreValidated tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists previous restored,
 let failed:=snapshot_error false (reservation_state false span s) in
 let final:=((Logged (Ready (writer_flash result)) h a,
   failure_phase old restored resolved (normal_external_rollback (operation_cancel failed))),phase_evidence (snd ((Logged (Ready (writer_flash result)) h a,
   failure_phase old restored resolved (normal_external_rollback (operation_cancel failed))))) (selected_evidence old previous (advance_allocation_evidence span e))) in
 Trace vi oi initial events (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 boundary_receipts final=events++boundary_receipts initial /\
 checked_release true word_max span (protection_table (reservation_state false span s))=
   (None,protection_table failed) /\
 (forall ram,snd (fst final)=IdleBoundary old restored ram ->
   data_caller DataBegin ram /\ state_numeric word_max ram /\
   state_numeric word_max (data_next DataBegin ram) /\
   volatile_allocation (snd final)=volatile_allocation (advance_allocation_evidence span e)).
Proof.
 intros MARK DEC WORD CAPACITY INIT NUM0 CTX RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK span WRITE ERROR RESTORE MASK.
 destruct (operation_recycled_writer_numeric vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count recycled plan result word_max
   MARK DEC WORD CAPACITY INIT NUM0 RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH [SAFE [OBS NUMERIC]]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH,SAFE;rewrite ERROR in PATH,SAFE;simpl in PATH,SAFE.
 destruct (operation_cancel_from_trace vi oi initial events (validate (writer_flash result)) view
   (writer_flash result) h a image root (snapshot_error false (reservation_state false span s))
   (selected_evidence old previous (advance_allocation_evidence span e)) old read inspect check INIT CTX PATH eq_refl HEAD RESTORE)
   as [local_decoded [CANCEL [CANCEL_SAFE STRUCT]]].
 destruct (normal_rollback_from_trace vi oi initial events (validate (writer_flash result)) view
   (writer_flash result) h a (recovered_image local_decoded) [recovered_boss local_decoded]
   (operation_cancel (snapshot_error false (reservation_state false span s))) (selected_evidence old previous (advance_allocation_evidence span e)) old resolved
   INIT CTX CANCEL eq_refl HEAD MASK) as [restored [FULL [FINAL [RECEIPTS NEXT]]]].
 exists previous,restored;split;[exact FULL|]. split;[exact FINAL|]. split;[exact RECEIPTS|]. split.
 - destruct (NUMERIC ltac:(rewrite ERROR;discriminate)) as [C [W [RELEASE REHOME]]].
   exact (RELEASE (protection_table (reservation_state false span s))).
 - intros ram EQ.
   assert (IDLE:Trace vi oi initial events (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,IdleBoundary old restored ram),selected_evidence old previous (advance_allocation_evidence span e))).
   { cbn in EQ;rewrite EQ in FULL;exact FULL. }
   pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max vi oi initial events (validate (writer_flash result)) view _
     MARK DEC WORD CAPACITY INIT NUM0 IDLE)) as NUM.
   pose proof (proj1 (NEXT ram EQ)) as BEGIN.
   split;[exact BEGIN|]. split;[exact NUM|]. split.
   + eapply data_numeric_preserves;[exact NUM|exact BEGIN|exact I].
   + cbn in EQ; cbn [snd fst]; unfold phase_evidence; rewrite EQ; reflexivity.
Qed.

(* A12.g.16: the checker observes the SAME initialized table geometry and
   descriptor as the live reservation. No completion-of-plan premise. *)
Section CertifiedFailures.
Variable word_max:nat.
Hypothesis MARK:range_numeric word_max marker.
Hypothesis DEC:decoded_numeric_contract word_max ranges decode.
Hypothesis WORD:1024*256<=word_max.
Hypothesis GEOM:area_start g+area_length g<=2*sector+1024*256.

Theorem boss_local_cleanup_from_trace vi oi initial events valid view f h a old image root s e p plan result resolved :
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) ->
 pending_writer_run g sector s p true f plan result -> prep_kind p=BossPreparation ->
 writer_end result=WriterLocalError ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 checked_release true word_max (prep_range p) (protection_table s)=
   (None,ScopeOwnership.release_extent 256 (prep_range p) (protection_table s)) /\
 exists previous d,
 let cleaned:=preparation_error_state (writer_end result) s in
 let destination:=((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)),phase_evidence (snd ((Logged (Ready (writer_flash result)) h a,
    failure_phase old d resolved (normal_external_rollback cleaned)))) (selected_evidence old previous e)) in
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall restored,snd (fst destination)=IdleBoundary old d restored -> data_caller DataBegin restored).
Proof.
 intros INIT NUM CTX RAW PREFIX HEAD WRITE KIND ERROR MASK.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PREFIX) as [SOURCE NS].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 pose proof WRITE as [[P BLANK] RUN].
 pose proof (numeric_pending word_max s p NS P) as TOKEN.
 split;[exact (numeric_token_release word_max p (protection_table s) TOKEN)|].
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [_ ORDER].
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
   (validate (writer_flash result)) view
   (writer_exit_boundary old image root s h a result,phase_evidence (snd (writer_exit_boundary old image root s h a result)) (selected_evidence old previous e))).
 { eapply consume_pending;[exact ORDER|exact HEAD|exact IN|apply READERS|exact ACCEPT|exact WRITE|exact KIND]. }
 assert (CLEAN:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary image root (preparation_error_state (writer_end result) s)),selected_evidence old previous e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
   unfold writer_exit_boundary in STEP;rewrite ERROR in STEP |- *;exact STEP. }
 destruct (normal_rollback_from_trace vi oi initial events (validate (writer_flash result)) view
   (writer_flash result) h a image root (preparation_error_state (writer_end result) s)
   (selected_evidence old previous e) old resolved INIT CTX CLEAN
   ltac:(rewrite ERROR;reflexivity) HEAD MASK) as [d [FULL [SAFE [OBS NEXT]]]].
 exists previous,d;split;[exact FULL|]. split;[exact SAFE|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[exact OBS|]. intros restored EQ;exact (proj1 (NEXT restored EQ)).
Qed.

(* No independent BOUND/CAP premises at the late reserve call: the real
   selected geometry provides them; physical handoff supplies vacancy. *)
Theorem certified_late_reservation_from_trace vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result boss :
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 exists previous,
 let destination:=(recycling_acquisition_boundary old image root s h a result span boss,phase_evidence (snd (recycling_acquisition_boundary old image root s h a result span boss)) (selected_evidence old previous (recycling_cursor_evidence result span e))) in
 Trace vi oi initial events (validate (neutral_flash result)) view destination /\
 Safe (validate (neutral_flash result)) view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 (neutral_end_ result=NeutralSuccess ->
   ram_reservation_check true word_max span s=None /\
   checked_reservation true word_max boss span s=(None,reservation_state boss span s) /\
   reservation_handoff sector (neutral_flash result) (reservation_state boss span s) (reservation_token boss span)).
Proof.
 intros INIT NUM RAW PREFIX HEAD P LOCAL SEARCH GEO RUN span.
 pose proof (numeric_recycled_extent word_max g sector r count ltac:(lia) GEOM GEO) as RNUM.
 change (range_numeric word_max span) in RNUM.
 assert (BOUND:offset span+RetentionCoverage.span span<=word_max).
 { unfold range_numeric,range_check in RNUM.
   destruct (_ <=? word_max) eqn:B;[apply Nat.leb_le;exact B|discriminate]. }
 assert (CAP:page_limit span<=1024).
 { unfold range_numeric,range_check in RNUM.
   destruct (_ <=? word_max);[|discriminate].
   destruct (_ <=? 1024) eqn:B;[apply Nat.leb_le;exact B|discriminate]. }
 destruct (checked_recycling_from_trace vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count result boss word_max
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN BOUND CAP) as [previous [PATH [SAFE CHECK]]].
 exists previous;split;[exact PATH|]. split;[exact SAFE|]. split;[|exact CHECK].
 exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PATH)).
Qed.
End CertifiedFailures.

(* Original producer indices are retained, including the second-only branch. *)
Lemma prepass_dispatch_cases same eq_a eq_b :
 changed_pair same eq_a eq_b=[] \/ changed_pair same eq_a eq_b=[0] \/
 changed_pair same eq_a eq_b=[1] \/ changed_pair same eq_a eq_b=[0;1].
Proof. destruct same,eq_a,eq_b;cbn;auto. Qed.

Section FirstSelected.
Variable word_max:nat.
Hypothesis MARK:range_numeric word_max marker.
Hypothesis DEC:decoded_numeric_contract word_max ranges decode.
Hypothesis WORD:1024*256<=word_max.
Hypothesis GEOM:area_start g+area_length g<=2*sector+1024*256.

(* No successful-A premise: i is the first ORIGINAL index selected by the
   prepass. The plan function is evaluated at i, not at its position in changed. *)
Theorem prepass_first_writer_from_idle valid view f h a old d s e same eq_a eq_b i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 changed_pair same eq_a eq_b=i::remaining ->
 ( (acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
   exists recognize magic fuel req round alignment start r count recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r count /\ recycling_run g sector recognize magic r count f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled ) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 exists previous,
 let final:=(operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result,phase_evidence (snd (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result)) (selected_evidence old previous (advance_allocation_evidence (extent_at i) e))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\
 boundary_receipts final=client_receipts e /\
 publications (boundary_journal final)=h /\ acknowledgements (boundary_journal final)=a.
Proof.
 intros INIT RAW SELECT ACQUIRE WRITE.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation (outer_local_begin s)=None).
 { pose proof (proj1 (proj2 (proj1 INIT))) as IDLE.
   destruct IDLE as [[DI [F [STACK [P REST]]]] MORE].
   reflexivity. }
 assert (OPEN:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),e)).
 { eapply episodes_cons with (event:=None) (events:=[]);[apply operation_begin_episode|apply episodes_nil]. }
 assert (PATH:exists previous,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash result)) view
   (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result,phase_evidence (snd (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result)) (selected_evidence old previous (advance_allocation_evidence (extent_at i) e)))).
 { destruct ACQUIRE as [[EQ ADMIT]|[recognize [magic [fuel [req [round [alignment [start [r [count [recycled
      [LOCAL [SEARCH [GEO [RUN [OK [RANGE EQ]]]]]]]]]]]]]]]]].
   - subst acquired.
     destruct (operation_writer_from_trace valid view _ [] valid view f h a (recovered_image d) [recovered_boss d]
       (outer_local_begin s) e old (extent_at i) (plan_at i) result INIT RAW OPEN P HEAD ADMIT WRITE)
       as [previous [PATH REST]];eauto.
   - subst acquired;rewrite RANGE in WRITE |- *.
     destruct (operation_recycled_writer_episode valid view _ [] valid view f h a old (recovered_image d)
       [recovered_boss d] (outer_local_begin s) e recognize magic fuel req round alignment start r count recycled
       (plan_at i) result INIT RAW OPEN HEAD P LOCAL SEARCH GEO RUN OK WRITE)
       as [previous [PATH REST]];eauto. }
 destruct PATH as [previous PATH]. exists previous;split;[exact PATH|].
 pose proof (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC) as [NUM _].
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PATH) as [SAFE NUMERIC].
 split;[exact SAFE|]. split;[exact NUMERIC|]. split;[reflexivity|].
 unfold boundary_journal,operation_writer_exit,writer_exit_boundary;
 destruct (writer_end result);split;reflexivity.
Qed.

(* Includes acquisition errors, crypto stop and reset BEFORE the first writer.
   No success restriction and no fictitious writer/Drop after interruption. *)
Theorem prepass_first_recycling_from_idle valid view f h a old d s e same eq_a eq_b i remaining
 recognize magic fuel req round alignment start r count result :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 changed_pair same eq_a eq_b=i::remaining -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 exists previous,
 let final:=(operation_acquisition_boundary old (recovered_image d) [recovered_boss d] (outer_local_begin s) h a result
   (block_pages (recycle_lo r) (useful_pages r)),phase_evidence (snd (operation_acquisition_boundary old (recovered_image d) [recovered_boss d] (outer_local_begin s) h a result
   (block_pages (recycle_lo r) (useful_pages r)))) (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (neutral_flash result)) view final /\
 Safe (validate (neutral_flash result)) view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\ boundary_receipts final=client_receipts e.
Proof.
 intros INIT RAW SELECT LOCAL SEARCH GEO RUN.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation (outer_local_begin s)=None).
 { pose proof (proj1 (proj2 (proj1 INIT))) as IDLE.
   destruct IDLE as [[DI [F [STACK [P REST]]]] MORE].
   reflexivity. }
 assert (OPEN:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),e)).
 { eapply episodes_cons with (event:=None) (events:=[]);[apply operation_begin_episode|apply episodes_nil]. }
 destruct (operation_recycling_acquisition_from_trace valid view _ [] valid view f h a old (recovered_image d)
   [recovered_boss d] (outer_local_begin s) e recognize magic fuel req round alignment start r count result
   INIT RAW OPEN HEAD P LOCAL SEARCH GEO RUN) as [previous [PATH [SAFE REST]]].
 exists previous;split;[exact PATH|]. split;[exact SAFE|]. split;[|reflexivity].
 pose proof (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC) as [NUM _].
 exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PATH)).
Qed.
Theorem prepass_first_local_rollback valid view f h a old d s e same eq_a eq_b i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result resolved :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 changed_pair same eq_a eq_b=i::remaining ->
 ( (acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
   exists recognize magic fuel req round alignment start r count recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r count /\ recycling_run g sector recognize magic r count f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled ) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result -> writer_end result=WriterLocalError ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists previous restored,
 let failed:=snapshot_error false (reservation_state false (extent_at i) (outer_local_begin s)) in
 let final:=((Logged (Ready (writer_flash result)) h a,
   failure_phase old restored resolved (normal_external_rollback (operation_cancel failed))),phase_evidence (snd ((Logged (Ready (writer_flash result)) h a,
   failure_phase old restored resolved (normal_external_rollback (operation_cancel failed))))) (selected_evidence old previous (advance_allocation_evidence (extent_at i) e))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\
 boundary_receipts final=client_receipts e /\
 (forall ram,snd (fst final)=IdleBoundary old restored ram ->
   data_caller DataBegin ram /\ recovered_image restored=recovered_image d).
Proof.
 intros INIT RAW SELECT ACQUIRE WRITE ERROR MASK.
 destruct (prepass_first_writer_from_idle valid view f h a old d s e same eq_a eq_b i remaining
   extent_at plan_at acquired result INIT RAW SELECT ACQUIRE WRITE) as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite ERROR in PATH;cbn in PATH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (SEL0:selected_live ((Logged (Ready f) h a,IdleBoundary old d s),e) (Certificate old d))
   by (split;[exact (proj2 (proj2 INIT))|exact HEAD]).
 pose proof (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
   _ _ _ [] _ _ _ (Certificate old d) INIT SEL0 PATH eq_refl) as [SAFE_C [SEL_C KEEP_C]].
 destruct SEL_C as [IN_C HEAD_C];cbn in IN_C;destruct IN_C as [EQ_C|[]];inversion EQ_C;subst previous.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ [] _ _ _ INIT I PATH) as CTX.
 assert (CANCEL:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary (recovered_image d) [recovered_boss d]
    (operation_cancel (snapshot_error false (reservation_state false (extent_at i) (outer_local_begin s))))),
      selected_evidence old d (advance_allocation_evidence (extent_at i) e))).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
   eapply operation_clean_cancel_episode;[exact CTX|reflexivity|exact HEAD|simpl;auto|reflexivity|reflexivity]. }
 destruct (normal_rollback_from_trace valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (recovered_image d) [recovered_boss d]
   (operation_cancel (snapshot_error false (reservation_state false (extent_at i) (outer_local_begin s))))
   (selected_evidence old d (advance_allocation_evidence (extent_at i) e)) old resolved INIT I CANCEL eq_refl HEAD MASK)
   as [restored [FULL [FINAL [OBS NEXT]]]].
 exists d,restored;split;[exact FULL|]. split;[exact FINAL|]. split.
 - pose proof (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
     (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC) as [NUM _].
   exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[exact OBS|].
   assert (SEL:selected_live ((Logged (Ready f) h a,IdleBoundary old d s),e) (Certificate old d))
     by (split;[exact (proj2 (proj2 INIT))|exact HEAD]).
   pose proof (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
     _ _ _ [] _ _ _ (Certificate old d) INIT SEL FULL eq_refl) as [_ [SELECTED KEEP]].
   intros ram EQ;split;[exact (proj1 (NEXT ram EQ))|].
   cbn in EQ;rewrite EQ in FINAL,SELECTED.
   assert (SAME:Certificate old d=Certificate old restored).
   { eapply selected_live_unique;[exact FINAL|exact SELECTED|].
     split;[exact (proj2 (proj2 FINAL))|exact HEAD]. }
   inversion SAME;reflexivity.
Qed.

(* Ok with no changes is not a publication receipt. No scopes are opened. *)
Theorem prepass_unchanged_from_idle valid view j old d s e same eq_a eq_b :
 Safe valid view ((j,IdleBoundary old d s),e) -> changed_pair same eq_a eq_b=[] ->
 Trace valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e) /\
 Safe valid view ((j,IdleBoundary old d s),e) /\ state_numeric word_max s /\
 data_caller DataBegin s.
Proof.
 intros INIT EMPTY.
 assert (PATH:Trace valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e)).
 { eapply episodes_cons with (event:=None) (events:=[]);[eapply unchanged_pair_episode;exact EMPTY|apply episodes_nil]. }
 split;[exact PATH|]. split;[exact INIT|].
 destruct (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view j old d s e INIT PATH MARK DEC) as [NUM [CALL REST]].
 auto.
Qed.

End FirstSelected.

(* 87537f2: consume an already selected abort continuation. The provenance of
   the sticky latch across the WHOLE controller is not asserted here. *)
Definition aborted_observation {A E P} (value:A) (failure:E) (payload:list P)
 sw1 sw2 error1 error2 phase :=
 match phase with
 | IdleBoundary _ _ _ => Some (observe_retained_or_aborted true value failure AbortedResult,
     observe_apdu AbortedResult payload sw1 sw2 error1 error2)
 | _ => None
 end.

Theorem aborted_external_observation_from_trace vi oi initial events valid view f h a image root s e old resolved
 word_max A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists d,
 let destination:=((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e)) in
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=events++boundary_receipts initial /\
 publications (boundary_journal destination)=h /\
 (forall ram,snd (fst destination)=IdleBoundary old d ram ->
   data_caller DataBegin ram /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
     Some (OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)) /\
 (snd (fst destination)=FatalBoundary ->
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX PENDING HEAD MASK.
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root s e old resolved
   INIT CTX PREFIX PENDING HEAD MASK) as [d [FULL [SAFE [OBS NEXT]]]].
 exists d;split;[exact FULL|]. split;[exact SAFE|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[exact OBS|]. split;[reflexivity|]. split.
   + intros ram EQ;split;[exact (proj1 (NEXT ram EQ))|]. rewrite EQ;reflexivity.
   + intro EQ;rewrite EQ;reflexivity.
Qed.

(* Observing the corrected API cannot extend the durable receipt history.
   Payload suppression is independent of its bytes and the initial SW2. *)
Corollary aborted_external_apdu_failure A (payload:list A) sw1 sw2 error1 error2 :
 let result:=observe_apdu AbortedResult payload sw1 sw2 error1 error2 in
 fst (fst result)=[] /\ successful_status (snd (fst result))=false /\
 (successful_status sw1=false -> result=([],sw1,sw2)).
Proof. apply aborted_apdu_no_payload_or_success. Qed.

Theorem local_accept_aborted_observation_from_trace vi oi initial events valid view f h a image root s e old resolved
 word_max A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 let accepted:=data_next (DataClose [physical_authority s] (physical_authority s) true) s in
 exists d,
 let destination:=((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback accepted)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback accepted)))) (e)) in
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=events++boundary_receipts initial /\
 publications (boundary_journal destination)=h /\
 (forall ram,snd (fst destination)=IdleBoundary old d ram ->
   data_caller DataBegin ram /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
     Some (OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)) /\
 (snd (fst destination)=FatalBoundary ->
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX PENDING HEAD MASK accepted.
 destruct (operation_accept_from_trace vi oi initial events valid view (Logged (Ready f) h a) image root s e
   INIT CTX PREFIX PENDING) as [ACCEPTED REST].
 exact (aborted_external_observation_from_trace vi oi initial events valid view f h a image root accepted e old resolved
   word_max A E P value failure payload sw1 sw2 error1 error2
   MARK DEC WORD GEOM INIT NUM CTX ACCEPTED eq_refl HEAD MASK).
Qed.

(* Control effects are consumed by the SAME finite episode relation. *)
Lemma controller_from_trace vi oi initial events valid view j phase e action :
 Trace vi oi initial events valid view ((j,phase),e) ->
 controller_caller action phase (controller_read e) ->
 Trace vi oi initial events valid view ((j,phase),controller_evidence action phase e).
Proof.
 intros PREFIX CALL. eapply episodes_append with (more:=[]);[exact PREFIX|].
 eapply episodes_cons with (event:=None) (events:=[]);
 [apply controller_episode;exact CALL|apply episodes_nil].
Qed.


Theorem owned_local_control_from_idle valid view j old d s e :
 Trace valid view ((j,IdleBoundary old d s),e) [] valid view
 ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
   owned_local_evidence old d s e) /\
 controller_read (owned_local_evidence old d s e)=
   Control false true true true true None None.
Proof.
 split;[|reflexivity]. unfold owned_local_evidence.
 apply controller_from_trace;[|simpl;auto].
 eapply episodes_cons with (event:=None) (events:=[]).
 - apply controller_episode with (action:=ArmOwned);exact I.
 - eapply episodes_cons with (event:=None) (events:=[]);
   [apply operation_begin_episode|apply episodes_nil].
Qed.

(* The two concrete roots come from ArmOwned's Idle root and the two
   already-proved openings, not from an empty/nonempty dependency test. *)
Lemma owned_open_roots old d s e : protection_saved s=[] ->
 active_snapshot_roots
   (OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s))
   (owned_local_evidence old d s e)=Some [Some old;Some old].
Proof.
 intro STACK;unfold active_snapshot_roots,owned_local_evidence,outer_local_begin;
 cbn;rewrite STACK;reflexivity.
Qed.
Lemma owned_attached_roots old previous d s e index entry span : protection_saved s=[] ->
 active_snapshot_roots
   (OperationBoundary (image_replace (recovered_image d) index (Some entry)) []
    (exact_member ranges (recovered_image d) index entry span (outer_local_begin s)))
   (selected_evidence old previous (advance_allocation_evidence span (owned_local_evidence old d s e)))=Some [Some old;Some old].
Proof.
 intro STACK;unfold active_snapshot_roots,owned_local_evidence,exact_member,outer_local_begin;
 cbn;rewrite STACK;reflexivity.
Qed.
Theorem owned_open_roots_correspondence valid view j old d s e :
 Safe valid view ((j,IdleBoundary old d s),e) ->
 active_snapshot_roots
   (OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s))
   (owned_local_evidence old d s e)=Some [Some old;Some old] /\
 protection_saved (outer_local_begin s)=
   map (snapshot_dependencies (fun _=>recovered_boss d))
     [(Some old,image_dependencies ranges (recovered_image d));
      (Some old,image_dependencies ranges (recovered_image d))].
Proof.
 intro INIT.
 pose proof (proj1 (proj1 (proj2 (proj1 INIT)))) as [DI [F [STACK REST]]].
 pose proof (proj2 (proj2 (proj2 (proj1 INIT)))) as COR.
 split;[exact (owned_open_roots old d s e STACK)|].
 exact (proj2 (proj2 (proj2 (outer_local_materialized_roots
   (fun _=>recovered_boss d) old (image_dependencies ranges (recovered_image d)) s STACK COR)))).
Qed.
Theorem owned_first_before_change valid view j old d s e :
 Safe valid view ((j,IdleBoundary old d s),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e) false
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e).
Proof.
 intro INIT;destruct (owned_open_roots_correspondence valid view j old d s e INIT) as [ROOTS PROJECTION].
 exact (before_change_probe_known _ _ _ _ _ _ ROOTS).
Qed.
Theorem owned_second_before_change valid view j old previous d s e index entry span reached :
 Safe valid view ((j,IdleBoundary old d s),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((reached,OperationBoundary (image_replace (recovered_image d) index (Some entry)) []
    (exact_member ranges (recovered_image d) index entry span (outer_local_begin s))),
    selected_evidence old previous (advance_allocation_evidence span (owned_local_evidence old d s e))) false
   ((reached,OperationBoundary (image_replace (recovered_image d) index (Some entry)) []
    (exact_member ranges (recovered_image d) index entry span (outer_local_begin s))),
    selected_evidence old previous (advance_allocation_evidence span (owned_local_evidence old d s e))).
Proof.
 intro INIT;pose proof (proj1 (proj1 (proj2 (proj1 INIT)))) as [DI [F [STACK REST]]].
 exact (before_change_probe_known _ _ _ _ _ _ (owned_attached_roots old previous d s e index entry span STACK)).
Qed.
Theorem before_change_skip_from_trace vi oi initial events valid view j image root ram e :
 Safe vi oi initial ->
 Trace vi oi initial events valid view ((j,OperationBoundary image root ram),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((j,OperationBoundary image root ram),e) false ((j,OperationBoundary image root ram),e) ->
 controller_service_caller ((j,OperationBoundary image root ram),e) bool BeforeChangeProbe /\
 Trace vi oi initial events valid view ((j,OperationBoundary image root ram),e).
Proof.
 intros INIT PREFIX PROBE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
  _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (before_change_probe_result _ _ _ PROBE) as [rs [ROOTS REST]].
 split.
 - exists rs;split;[exact ROOTS|exact (proj1 (proj2 (proj2 (proj1 SOURCE))))].
 - eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply before_change_checked;exact PROBE|constructor].
Qed.

(* The branch is computed after request_abort and the successful local close;
   no Aborted continuation or selected finalization is an input. Storage/RAM
   rollback and mask failure are consumed from the previously proved service. *)
Theorem requested_abort_then_local_success vi oi initial events valid view f h a image root s e old resolved
 word_max A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=Control false true true true true None None ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 let accepted:=data_next (DataClose [physical_authority s] (physical_authority s) true) s in
 let op:=OperationBoundary image root s in
 let opened:=OpenBoundary image root accepted in
 let requested:=controller_evidence RequestAbort op e in
 let taken:=controller_evidence (TakeLocal true) op requested in
 let closed:=controller_evidence LocalClosed opened taken in
 let selected:=controller_evidence SelectFinish opened closed in
 let completing:=controller_evidence TakeOuter opened selected in
 finish_selected (controller_read selected)=Some FinishAbort /\
 abort_requested (controller_read closed)=true /\ local_live (controller_read closed)=false /\
 exists d,
 let destination:=((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback accepted)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback accepted)))) (completing)) in
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=events++boundary_receipts initial /\
 publications (boundary_journal destination)=h /\
 (forall ram,snd (fst destination)=IdleBoundary old d ram ->
   data_caller DataBegin ram /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
     Some (OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)) /\
 (snd (fst destination)=FatalBoundary ->
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX CTRL PENDING HEAD MASK
   accepted op opened requested taken closed selected completing.
 assert (REQ:Trace vi oi initial events valid view ((Logged (Ready f) h a,op),requested)).
 { apply controller_from_trace;[exact PREFIX|simpl;rewrite CTRL;reflexivity]. }
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,op),taken)).
 { apply controller_from_trace;[exact REQ|].
   change (local_live (controller_read e)=true /\ True);rewrite CTRL;simpl;repeat split;reflexivity. }
 destruct (operation_accept_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   image root s taken INIT CTX TAKE PENDING) as [ACCEPTED REST].
 assert (CLOSE:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),closed)).
 { apply controller_from_trace;[exact ACCEPTED|].
   split;[discriminate|exact I]. }
 assert (SELECT:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),selected)).
 { apply controller_from_trace;[exact CLOSE|].
   change (owns_outer (controller_read e)=true /\ owner_armed (controller_read e)=true /\ outer_live (controller_read e)=true /\ false=false /\ @None bool=None /\ body_error_pending (controller_read e)=false);rewrite CTRL;simpl;repeat split;reflexivity. }
 assert (OUTER:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),completing)).
 { apply controller_from_trace;[exact SELECT|].
   split;[discriminate|change (outer_live (controller_read e)=true);rewrite CTRL;reflexivity]. }
 assert (SELECTED:finish_selected (controller_read selected)=Some FinishAbort /\
   abort_requested (controller_read closed)=true /\ local_live (controller_read closed)=false).
 { repeat split;reflexivity. }
 destruct SELECTED as [BRANCH [STICKY CONSUMED]].
 split;[exact BRANCH|]. split;[exact STICKY|]. split;[exact CONSUMED|].
 exact (aborted_external_observation_from_trace vi oi initial events valid view f h a image root accepted completing old resolved
   word_max A E P value failure payload sw1 sw2 error1 error2 MARK DEC WORD GEOM INIT NUM CTX OUTER eq_refl HEAD MASK).
Qed.

(* Disarming is a separate step AFTER returned finalization, before observation. *)
Theorem controlled_aborted_return_from_trace vi oi initial events valid view j old d s e
 A E (value:A) (failure:E) :
 Trace vi oi initial events valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false ->
 finish_selected (controller_read e)=Some FinishAbort ->
 let returned:=controller_evidence DisarmOwner (IdleBoundary old d s) e in
 Trace vi oi initial events valid view ((j,IdleBoundary old d s),returned) /\
 owner_armed (controller_read returned)=false /\
 observe_retained_or_aborted true value failure AbortedResult=OperationInvalidState /\
 client_receipts returned=client_receipts e.
Proof.
 intros PREFIX CLOSED ROUTE returned. split.
 - apply controller_from_trace;[exact PREFIX|simpl;auto].
 - repeat split;reflexivity.
Qed.

Theorem controller_reset_from_trace vi oi initial events valid view j phase e :
 Trace vi oi initial events valid view ((j,phase),e) ->
 logged_step g sector 256 data_len valid j (logged_after_reset j) ->
 let after:=controller_evidence ForgetControl (RebuildingBoundary Selecting) e in
 Trace vi oi initial events valid view ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence (after)) /\
 volatile_control after=None /\ live_certificates after=live_certificates e /\
 client_receipts after=client_receipts e.
Proof.
 intros PREFIX RESET after. split;[|repeat split;reflexivity].
 eapply episodes_append with (more:=[]);[exact PREFIX|].
 eapply episodes_cons with (event:=None) (events:=[]);
 [apply reset_episode;exact RESET|apply episodes_nil].
Qed.

(* A concrete initial owner and both real scopes produce the controller used by
   the consumer. No invariant or abort choice is supplied at the join. *)
Lemma phase_evidence_outer_closed phase e :
 outer_live (controller_read e)=false ->
 outer_live (controller_read (phase_evidence phase e))=false.
Proof. destruct phase;cbn;auto. Qed.

Theorem owned_requested_abort_from_idle valid view f h a old d s e resolved word_max
 A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view destination /\
 Safe valid view destination /\ phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\ boundary_receipts destination=client_receipts e /\
 (forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
   finish_selected (controller_read (snd destination))=Some FinishAbort) /\
 outer_live (controller_read (snd destination))=false /\
 (forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
   data_caller DataBegin ram /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
   Some (OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)).
Proof.
 intros MARK DEC WORD GEOM INIT NUM MASK.
 destruct (owned_local_control_from_idle valid view (Logged (Ready f) h a) old d s e) as [PREFIX CTRL].
 assert (PENDING:pending_preparation (outer_local_begin s)=None).
 { reflexivity. }
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { pose proof (proj1 (proj2 (proj1 INIT))) as J;exact (proj1 (proj2 (proj2 (proj2 J)))). }
 destruct (requested_abort_then_local_success valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e) old resolved
   word_max A E P value failure payload sw1 sw2 error1 error2
   MARK DEC WORD GEOM INIT NUM I PREFIX CTRL PENDING HEAD MASK)
   as [ROUTE [LATCH [HANDLE [decoded [FULL [SAFE [NUMBER [RECEIPTS [HISTORY [OBS FATAL]]]]]]]]]].
 eexists;split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|].
 split;[exact HISTORY|]. split;[exact RECEIPTS|]. split.
 - intros id dd ram EQ;cbn [fst snd] in EQ |- *;rewrite EQ;cbn [fst snd];
   autorewrite with control_evidence;exact ROUTE.
 - split;[apply phase_evidence_outer_closed;reflexivity|].
 intros id dd ram EQ. pose proof EQ as ORIGINAL. unfold failure_phase in EQ.
 destruct resolved as [mask|];cbn in EQ;
 repeat match type of EQ with context[if ?b then _ else _]=>destruct b eqn:? end;
 try discriminate;inversion EQ;subst;apply OBS;exact ORIGINAL.
Qed.

Definition returned_control phase e := match phase with
 | IdleBoundary _ _ _ => controller_evidence DisarmOwner phase e
 | FatalBoundary => controller_evidence ForgetControl phase e
 | _ => e end.
Lemma finalize_control_from_trace vi oi initial events valid view j phase e :
 Trace vi oi initial events valid view ((j,phase),e) ->
 outer_live (controller_read e)=false ->
 Trace vi oi initial events valid view ((j,phase),returned_control phase e).
Proof.
 intros PREFIX CLOSED;destruct phase;simpl;try exact PREFIX.
 - apply controller_from_trace;[exact PREFIX|simpl;auto].
 - apply controller_from_trace;[exact PREFIX|exact I].
Qed.

Theorem owned_abort_client_from_idle valid view f h a old d s e resolved word_max
 A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (IdleBoundary old d s) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view destination /\
 Safe valid view destination /\ phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\ boundary_receipts destination=client_receipts e /\
 (forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
   data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false /\
   finish_selected (controller_read (snd destination))=Some FinishAbort /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
   Some (OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None /\
   aborted_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM MASK.
 destruct (owned_requested_abort_from_idle valid view f h a old d s e resolved word_max
   A E P value failure payload sw1 sw2 error1 error2 MARK DEC WORD GEOM INIT NUM MASK)
 as [[[j phase] evidence] [PREFIX [SAFE [NUMBER [HISTORY [RECEIPTS [ROUTE [CLOSED OBS]]]]]]]].
 pose proof (finalize_control_from_trace valid view _ [] valid view j phase evidence PREFIX CLOSED) as FULL.
 exists ((j,phase),returned_control phase evidence).
 split;[exact FULL|]. split.
 - exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT FULL)).
 - split;[exact NUMBER|]. split;[exact HISTORY|]. split.
   + destruct phase;exact RECEIPTS.
   + split.
     * intros id dd ram EQ;cbn in EQ;subst phase.
       destruct (OBS id dd ram eq_refl) as [CALL OBSERVED].
       split;[exact CALL|]. split;[reflexivity|]. split;[exact (ROUTE id dd ram eq_refl)|exact OBSERVED].
     * intro EQ;cbn in EQ;subst phase;split;reflexivity.
Qed.

(* Dispatch observes the latch and current-root invalidation, never image equality. *)
Theorem controlled_dispatch_from_trace vi oi initial events valid view j image root s e :
 Trace vi oi initial events valid view ((j,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 let selected:=controller_evidence SelectFinish (OpenBoundary image root s) e in
 Trace vi oi initial events valid view ((j,OpenBoundary image root s),selected) /\
 finish_selected (controller_read selected)=
   Some (choose_finish (controller_read e) (phase_dirty (OpenBoundary image root s))).
Proof. intros PREFIX CALL selected;split;[apply controller_from_trace;assumption|reflexivity]. Qed.

Definition retained_observation {A E P} (value:A) (failure:E) (payload:list P)
 sw1 sw2 error1 error2 phase := match phase with
 | IdleBoundary _ _ _ => Some (observe_retained_or_aborted true value failure RetainedResult,
     observe_apdu RetainedResult payload sw1 sw2 error1 error2)
 | _=>None end.

(* Result provenance retained until a distinct ordinary-delivery step. *)
Definition ordinary_return_ready route (x:execution_boundary) : Prop :=
 match snd (fst x) with
 | IdleBoundary _ _ _ | FrozenBoundary _ _ _ _ =>
     owner_armed (controller_read (snd x))=false /\
     outer_live (controller_read (snd x))=false /\
     finish_selected (controller_read (snd x))=Some route
 | FatalBoundary=>volatile_control (snd x)=None
 | _=>False end.
Lemma failure_phase_normal_shape old d resolved rolled :
 protection_frozen rolled=false ->
 failure_phase old d resolved rolled=FatalBoundary \/
 exists ram,failure_phase old d resolved rolled=IdleBoundary old d ram.
Proof.
 intro NF;unfold failure_phase;destruct collection_enabled eqn:E;[destruct resolved|].
 - unfold preparation_collection;rewrite E;cbn;rewrite NF;right;eexists;reflexivity.
 - left;reflexivity.
 - rewrite NF;right;eexists;reflexivity.
Qed.
Lemma returned_control_ready route j phase e :
 (phase=FatalBoundary \/ exists id d ram,phase=IdleBoundary id d ram) ->
 outer_live (controller_read e)=false -> finish_selected (controller_read e)=Some route ->
 ordinary_return_ready route ((j,phase),returned_control phase (phase_evidence phase e)).
Proof.
 intros [EQ|[id [d [ram EQ]]]] CLOSED ROUTE;subst phase;[reflexivity|].
 cbn [ordinary_return_ready fst snd returned_control];autorewrite with control_evidence.
 split;[reflexivity|]. split;[exact CLOSED|exact ROUTE].
Qed.
Lemma open_trace_not_frozen vi oi initial events valid view j image root s e :
 Safe vi oi initial -> Trace vi oi initial events valid view ((j,OpenBoundary image root s),e) ->
 protection_frozen s=false.
Proof.
 intros INIT RUN;pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
 _ _ _ _ _ _ _ INIT RUN)) as SOURCE.
 exact (proj1 (proj2 (proj2 (proj1 SOURCE)))).
Qed.

Theorem controlled_clean_from_trace_before_delivery vi oi initial events valid view f h a image root s e old resolved
 word_max A E P (value:A) (failure:E) (payload:list P) sw1 sw2 error1 error2 :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 abort_requested (controller_read e)=false -> phase_dirty (OpenBoundary image root s)=false ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination,
 ordinary_return_ready FinishClean destination /\
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
   data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false /\
   retained_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=
     Some (OperationValue value,(payload,sw1,sw2))) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None /\
   retained_observation value failure payload sw1 sw2 error1 error2 (snd (fst destination))=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL NOT_ABORT CLEAN PENDING HEAD MASK.
 pose proof (episode_trace_current_origin g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT ORIGIN PREFIX) as ROOT.
 destruct ROOT as [EMPTY|[id [d [H [IN [IMAGE ROOT]]]]]].
 { subst root;discriminate. }
 assert (ID:id=old) by (apply Nat2N.inj;cbn [boundary_journal fst snd publications] in H;congruence);subst id image root.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CTX PREFIX) as STRUCT.
 set (phase:=OpenBoundary (recovered_image d) [recovered_boss d] s).
 set (selected:=controller_evidence SelectFinish phase e).
 destruct (controlled_dispatch_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] s e PREFIX CALL) as [SELECT ROUTE].
 assert (ROUTE':finish_selected (controller_read selected)=Some FinishClean).
 { change (Some (choose_finish (controller_read e) false)=Some FinishClean).
   unfold choose_finish;rewrite NOT_ABORT;reflexivity. }
 set (taken:=controller_evidence TakeOuter phase selected).
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),taken)).
 { apply controller_from_trace;[exact SELECT|].
   split;[rewrite ROUTE';discriminate|exact (proj1 (proj2 (proj2 CALL)))]. }
 assert (CLOSE:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,failure_phase old d resolved (clean_external_close s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (clean_external_close s)))) (taken))).
 { eapply episodes_append with (more:=[]);[exact TAKE|].
   eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
   apply clean_retained_episode;try assumption;exact ROUTE'. }
 pose proof (finalize_control_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   _ (phase_evidence _ taken) CLOSE (phase_evidence_outer_closed _ taken eq_refl)) as FULL.
 eexists;split;[|].
 { apply (returned_control_ready FinishClean (Logged (Ready f) h a)
     (failure_phase old d resolved (clean_external_close s)) taken).
   + destruct (failure_phase_normal_shape old d resolved (clean_external_close s)
       (open_trace_not_frozen vi oi initial events valid view (Logged (Ready f) h a) _ _ s e INIT PREFIX))
       as [EQ|[ram EQ]];[left;exact EQ|right;exists old,d,ram;exact EQ].
   + reflexivity.
   + exact ROUTE'. }
 split;[exact FULL|].
 pose proof (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [FINAL [RECEIPTS REST]].
 split;[exact FINAL|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[reflexivity|]. split;[exact RECEIPTS|]. split.
   + intros id dd ram EQ;cbn [fst snd] in EQ.
     assert (CALL_NEXT:data_caller DataBegin ram).
     { rewrite EQ in FINAL;exact (proj1 (common_begin sector data_len valid view marker ranges decode pages
         (Logged (Ready f) h a) id dd ram (proj1 FINAL))). }
     split;[exact CALL_NEXT|]. split;[cbn in EQ;rewrite EQ;reflexivity|].
     rewrite EQ;reflexivity.
   + intro EQ;cbn [fst snd] in EQ;split;[rewrite EQ;reflexivity|rewrite EQ;reflexivity].
Qed.

Definition terminal_control phase e := match phase with
 | RebuildingBoundary _ | FatalBoundary => controller_evidence ForgetControl phase e
 | _=>e end.
Lemma terminal_control_from_trace vi oi initial events valid view j phase e :
 Trace vi oi initial events valid view ((j,phase),e) ->
 Trace vi oi initial events valid view ((j,phase),terminal_control phase e).
Proof.
 intro PREFIX;destruct phase;cbn [terminal_control];try exact PREFIX;
 apply controller_from_trace;[exact PREFIX|exact I|exact PREFIX|exact I].
Qed.
Lemma terminal_control_drops_ram_control pc e :
 volatile_control (terminal_control (RebuildingBoundary pc) e)=None /\
 live_certificates (terminal_control (RebuildingBoundary pc) e)=live_certificates e /\
 client_receipts (terminal_control (RebuildingBoundary pc) e)=client_receipts e.
Proof. repeat split;reflexivity. Qed.
Lemma actual_client_delivery_disarms j c e :
 match volatile_control (observe_client j c e) with
 | None=>True | Some control=>owner_armed control=false /\ outer_live control=false end.
Proof. unfold observe_client,deliver_published,synchronize_publication,install_runtime_counter,install_latest_range;cbn;destruct (volatile_control e);cbn;auto. Qed.

(* The supplied suffix is an operational execution of the existing services,
   not a promised post-invariant. Terminal evidence is projected immediately;
   no old volatile control is passed to a subsequent boot. *)
Theorem controlled_dirty_execution vi oi initial events valid view j image s e
 later vf of_ jf phase ef word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((j,OpenBoundary image [] s),e) ->
 controller_caller SelectFinish (OpenBoundary image [] s) (controller_read e) ->
 abort_requested (controller_read e)=false ->
 let selected:=controller_evidence SelectFinish (OpenBoundary image [] s) e in
 Trace valid view ((j,OpenBoundary image [] s),selected) later vf of_ ((jf,phase),ef) ->
 finish_selected (controller_read selected)=Some FinishPublish /\
 Trace vi oi initial (later++events) vf of_ ((jf,phase),terminal_control phase ef) /\
 Safe vf of_ ((jf,phase),terminal_control phase ef) /\
 phase_numeric word_max marker ranges phase /\
 boundary_receipts ((jf,phase),terminal_control phase ef)=later++events++boundary_receipts initial /\
 Forall (historical_delivery marker) (later++events).
Proof.
 intros MARK DEC WORD GEOM INIT NUM PREFIX CALL ABORT selected RUN.
 destruct (controlled_dispatch_from_trace vi oi initial events valid view j image [] s e PREFIX CALL) as [SELECT ROUTE].
 split;[change (Some (choose_finish (controller_read e) true)=Some FinishPublish);unfold choose_finish;rewrite ABORT;reflexivity|].
 assert (FULL:Trace vi oi initial (later++events) vf of_ ((jf,phase),terminal_control phase ef)).
 { apply terminal_control_from_trace;eapply episodes_append;[exact SELECT|exact RUN]. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS [VALID DELIVERY]]].
 split;[exact SAFE|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[rewrite <- app_assoc in OBS;exact OBS|exact DELIVERY].
Qed.

Theorem controlled_abort_from_trace_before_delivery vi oi initial events valid view f h a image root s e old resolved
 word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 abort_requested (controller_read e)=true -> pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination,
 ordinary_return_ready FinishAbort destination /\
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
   data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX CALL ABORT PENDING HEAD MASK.
 set (phase:=OpenBoundary image root s).
 set (selected:=controller_evidence SelectFinish phase e).
 destruct (controlled_dispatch_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   image root s e PREFIX CALL) as [SELECT ROUTE].
 assert (ROUTE':finish_selected (controller_read selected)=Some FinishAbort).
 { change (Some (choose_finish (controller_read e) (phase_dirty phase))=Some FinishAbort).
   unfold choose_finish;rewrite ABORT;reflexivity. }
 set (taken:=controller_evidence TakeOuter phase selected).
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),taken)).
 { apply controller_from_trace;[exact SELECT|].
   split;[rewrite ROUTE';discriminate|exact (proj1 (proj2 (proj2 CALL)))]. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root s taken old resolved
   INIT CTX TAKE PENDING HEAD MASK) as [d [CLOSE [SAFE [RECEIPTS NEXT]]]].
 pose proof (finalize_control_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   _ (phase_evidence _ taken) CLOSE (phase_evidence_outer_closed _ taken eq_refl)) as FULL.
 eexists;split;[|].
 { apply (returned_control_ready FinishAbort (Logged (Ready f) h a)
     (failure_phase old d resolved (normal_external_rollback s)) taken).
   + destruct (failure_phase_normal_shape old d resolved (normal_external_rollback s)
       (open_trace_not_frozen vi oi initial events valid view (Logged (Ready f) h a) _ _ s e INIT PREFIX))
       as [EQ|[ram EQ]];[left;exact EQ|right;exists old,d,ram;exact EQ].
   + reflexivity.
   + exact ROUTE'. }
 split;[exact FULL|].
 pose proof (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [FINAL [OBS REST]].
 split;[exact FINAL|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[reflexivity|]. split;[exact OBS|]. split.
   + intros id dd ram EQ;cbn [fst snd] in EQ.
     assert (CALL_NEXT:data_caller DataBegin ram).
     { rewrite EQ in FINAL;exact (proj1 (common_begin sector data_len valid view marker ranges decode pages
         (Logged (Ready f) h a) id dd ram (proj1 FINAL))). }
     split;[exact CALL_NEXT|]. rewrite EQ;reflexivity.
   + intro EQ;cbn [fst snd] in EQ;rewrite EQ;reflexivity.
Qed.



(* A single computed dispatch. The dirty argument is an operational suffix of
   episode_trace, supplied by the existing acquisition/writer/publication
   consumers. It contains no safe destination or certificate postcondition. *)
Theorem controller_dispatch_prefix_from_trace vi oi initial events valid view f h a image root s e old resolved
 later vf of_ dirty_destination word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 let route:=choose_finish (controller_read e) (phase_dirty (OpenBoundary image root s)) in
 let selected:=controller_evidence SelectFinish (OpenBoundary image root s) e in
 (route=FinishPublish ->
   Trace valid view ((Logged (Ready f) h a,OpenBoundary image root s),selected)
     later vf of_ dirty_destination) ->
 route=choose_finish (controller_read e)
   (rust_dirty_observer (outer_live (controller_read e)) (root_address root) (root_address (physical_authority s))) /\
 exists added final_valid final_view destination,
 (route=FinishPublish -> added=later /\ final_valid=vf /\ final_view=of_ /\
   destination=(fst dirty_destination,terminal_control (snd (fst dirty_destination)) (snd dirty_destination))) /\
 Trace vi oi initial (added++events) final_valid final_view destination /\
 Safe final_valid final_view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=added++events++boundary_receipts initial /\
 (route<>FinishPublish -> added=[] /\ publications (boundary_journal destination)=h /\
   forall id decoded ram,snd (fst destination)=IdleBoundary id decoded ram ->
     data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false) /\
 (forall pc,snd (fst destination)=RebuildingBoundary pc -> volatile_control (snd destination)=None) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL PENDING HEAD MASK route selected DIRTY.
 split.
 { pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
   pose proof (episode_trace_current_origin g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT ORIGIN PREFIX) as ROOT.
   unfold route;rewrite (proj1 (proj2 (proj2 CALL))).
   rewrite <- (phase_dirty_matches_roots sector data_len marker ranges decode pages
     valid view f h a image root s e old SOURCE ROOT HEAD);reflexivity. }
 destruct (abort_requested (controller_read e)) eqn:ABORT.
 - destruct (controlled_abort_from_trace_before_delivery vi oi initial events valid view f h a image root s e old resolved word_max
     MARK DEC WORD GEOM INIT NUM CTX PREFIX CALL ABORT PENDING HEAD MASK)
     as [[[j phase] evidence] [READY [PATH [SAFE [NUMBER [HISTORY [RECEIPTS [NEXT FATAL]]]]]]]].
   pose proof (terminal_control_from_trace vi oi initial events valid view j phase evidence PATH) as FULL.
   exists [],valid,view,((j,phase),terminal_control phase evidence).
   split;[intro EQ;unfold route,choose_finish in EQ;rewrite ABORT in EQ;discriminate|].
   split;[exact FULL|]. split.
   + exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ INIT FULL)).
   + split;[exact NUMBER|]. split;[destruct phase;exact RECEIPTS|]. split.
     * intro DIFFERENT;split;[reflexivity|]. split;[exact HISTORY|].
       intros id d ram EQ;cbn in EQ;subst phase;exact (NEXT id d ram eq_refl).
     * split;[intros pc EQ;cbn in EQ;subst phase;reflexivity|intro EQ;cbn in EQ;subst phase;reflexivity].
 - destruct root as [|boss rest].
   + destruct dirty_destination as [[j phase] evidence].
     assert (CHOSEN:route=FinishPublish) by (unfold route,choose_finish;rewrite ABORT;reflexivity).
     destruct (controlled_dirty_execution vi oi initial events valid view (Logged (Ready f) h a) image s e
       later vf of_ j phase evidence word_max MARK DEC WORD GEOM INIT NUM PREFIX CALL ABORT (DIRTY CHOSEN))
       as [ROUTE [FULL [SAFE [NUMBER [RECEIPTS DELIVERY]]]]].
     exists later,vf,of_,((j,phase),terminal_control phase evidence).
     split;[intros _;repeat split;reflexivity|].
     split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|]. split;[exact RECEIPTS|]. split.
     * intro BAD;contradiction.
     * split;[intros pc EQ;cbn in EQ;subst phase;reflexivity|intro EQ;cbn in EQ;subst phase;reflexivity].
   + destruct (controlled_clean_from_trace_before_delivery vi oi initial events valid view f h a image (boss::rest) s e old resolved
       word_max unit unit unit tt tt [] 144 0 105 0 MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL ABORT eq_refl PENDING HEAD MASK)
       as [[[j phase] evidence] [READY [PATH [SAFE [NUMBER [HISTORY [RECEIPTS [NEXT FATAL]]]]]]]].
     pose proof (terminal_control_from_trace vi oi initial events valid view j phase evidence PATH) as FULL.
     exists [],valid,view,((j,phase),terminal_control phase evidence).
     split;[intro EQ;unfold route,choose_finish in EQ;rewrite ABORT in EQ;discriminate|].
     split;[exact FULL|]. split.
     * exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
         _ _ _ _ _ _ _ INIT FULL)).
     * split;[exact NUMBER|]. split;[destruct phase;exact RECEIPTS|]. split.
       -- intro DIFFERENT;split;[reflexivity|]. split;[exact HISTORY|].
          intros id d ram EQ;cbn in EQ;subst phase;destruct (NEXT id d ram eq_refl) as [BEGIN [ARM OBS]];auto.
       -- split;[intros pc EQ;cbn in EQ;subst phase;reflexivity|intro EQ;cbn in EQ;subst phase;reflexivity].
Qed.

Theorem controller_recycled_publication vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result id fresh word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 phase_numeric word_max marker ranges (snd (fst initial)) ->
 Safe vi oi initial -> external_structure marker initial ->
 external_rollback_context marker initial -> current_root_origin initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 controller_caller SelectFinish (OpenBoundary image [] s) (controller_read e) ->
 abort_requested (controller_read e)=false ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 writer_end result=WriterComplete ->
 contains (block_pages (recycle_lo r) (useful_pages r)) id -> contains (boss_extent (view old)) old ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=block_pages (recycle_lo r) (useful_pages r) -> recovered_image fresh=image ->
 let selected:=controller_evidence SelectFinish (OpenBoundary image [] s) e in
 let prepared:=install_candidate (snapshot_written
   (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)) in
 let next_view:=install_decoded_view view ranges id fresh in
 finish_selected (controller_read selected)=Some FinishPublish /\
 exists previous,
 let candidate:=((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared id fresh prepared),
   evidence_with_live (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) selected) [Certificate old previous;Certificate id fresh]) in
 Trace vi oi initial events (validate (writer_flash result)) next_view candidate /\
 external_structure marker candidate /\
 exit_calls marker (root_extents (next_view id)) (List.hd [] (protection_saved prepared))
   [SlotCompleted;DurableRamWritten;ExternalAccepted] prepared /\
 collection_boundary next_view marker (Some id) (Some id) (object_extents (next_view id)) []
   (successful_external_close marker (root_extents (next_view id)) (List.hd [] (protection_saved prepared)) prepared) /\
 (forall middle,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len (validate (writer_flash result)) (N.of_nat id))
     (Logged (Ready (writer_flash result)) h a) middle ->
   logged_invariant sector 256 data_len (validate (writer_flash result)) middle /\
   persistent_evidence sector next_view ranges decode middle (snd candidate) /\
   (hd_error (publications middle)=hd_error h \/ hd_error (publications middle)=Some (N.of_nat id)) /\
   acknowledgements middle=a) /\
 (forall event vf of_ next,
   Step (validate (writer_flash result)) next_view candidate event vf of_ next ->
   let normalized:=(fst next,terminal_control (snd (fst next)) (snd next)) in
   Trace vi oi initial (emitted_receipts event++events) vf of_ normalized /\ Safe vf of_ normalized /\
   phase_numeric word_max marker ranges (snd (fst normalized)) /\
   boundary_receipts normalized=emitted_receipts event++events++boundary_receipts initial).
Proof.
 intros MARK DEC WORD GEOM NUM INIT STRUCT CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE selected prepared next_view.
 destruct (controlled_dispatch_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   image [] s e PREFIX CALL) as [SELECT ROUTE].
 assert (CHOSEN:choose_finish (controller_read e) true=FinishPublish).
 { unfold choose_finish;rewrite ABORT;reflexivity. }
 split;[exact (f_equal Some CHOSEN)|].
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT SELECT)) as SOURCE.
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT SELECT) as SOURCE_STRUCT.
 pose proof (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW SELECT) as SOURCE_RAW.
 destruct (recycled_publication_suffixes valid view _ [] valid view f h a old image s selected
   recognize magic fuel req round alignment start r count recycled plan result id fresh
   SOURCE SOURCE_STRUCT (proj2 SOURCE_RAW) (episodes_nil _ _ _ _ _ _ _ _ _ _ _)
   HEAD P LOCAL SEARCH GEO RUN OK WRITE COMPLETE AT OLDAT READ BOSS IMAGE)
   as [previous [PATH [SCOPE [CALLERS [COLLECT [UNCERTAIN NEXT]]]]]].
 exists previous;split.
 - eapply episodes_append with (more:=[]);[exact SELECT|exact PATH].
 - split;[exact SCOPE|]. split;[exact CALLERS|]. split;[exact COLLECT|]. split;[exact UNCERTAIN|].
   intros event vf of_ [[jf phase] ef] SUFFIX normalized.
   destruct (NEXT event vf of_ _ SUFFIX) as [LOCAL_RUN REST].
   rewrite app_nil_r in LOCAL_RUN.
   destruct (controller_dispatch_prefix_from_trace vi oi initial events valid view f h a image [] s e old None
      (emitted_receipts event) vf of_ ((jf,phase),ef) word_max
      MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL P HEAD
      ltac:(intros;discriminate) ltac:(intros _;exact LOCAL_RUN))
      as [DISPATCH [added [fv [fo [destination [MATCH [FULL [SAFE [NUMBER [OBS OTHER]]]]]]]]]].
   destruct (MATCH CHOSEN) as [ADDED [VALID [VIEW DESTINATION]]];subst added fv fo destination.
   split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|exact OBS].
Qed.

(* All BOSS writer outcomes remain prefixes of the selected dirty branch.
   A returned local error is NOT claimed finalized by this prefix theorem. *)
Theorem controller_recycled_boss_writer vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 controller_caller SelectFinish (OpenBoundary image [] s) (controller_read e) ->
 abort_requested (controller_read e)=false -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 let selected:=controller_evidence SelectFinish (OpenBoundary image [] s) e in
 let reserved:=reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s in
 exists previous,
 let raw:=(writer_exit_boundary old image [] reserved h a result,phase_evidence (snd (writer_exit_boundary old image [] reserved h a result)) (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) selected))) in
 let destination:=(fst raw,terminal_control (snd (fst raw)) (snd raw)) in
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (writer_end result=WriterInterrupted -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE selected reserved.
 destruct (controlled_dispatch_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   image [] s e PREFIX CALL) as [SELECT ROUTE].
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT SELECT)) as SOURCE.
 pose proof (proj2 (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW SELECT)) as SOURCE_RAW.
 destruct (recycled_writer_episode valid view _ [] valid view f h a old image [] s selected
   recognize magic fuel req round alignment start r count recycled true plan result
   SOURCE SOURCE_RAW (episodes_nil _ _ _ _ _ _ _ _ _ _ _) HEAD P LOCAL SEARCH GEO RUN OK WRITE)
   as [previous [LOCAL_RUN REST]].
 assert (CHOSEN:choose_finish (controller_read e) true=FinishPublish).
 { unfold choose_finish;rewrite ABORT;reflexivity. }
 destruct (controller_dispatch_prefix_from_trace vi oi initial events valid view f h a image [] s e old None
   [] (validate (writer_flash result)) view _ word_max MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL P HEAD
   ltac:(intros;discriminate) ltac:(intros _;exact LOCAL_RUN))
   as [DISPATCH [added [fv [fo [final [MATCH [FULL [SAFE [NUMBER [OBS OTHER]]]]]]]]]].
 destruct (MATCH CHOSEN) as [ADDED [VALID [VIEW DESTINATION]]];subst added fv fo final.
 exists previous;split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|]. split.
 - unfold boundary_journal,writer_exit_boundary;destruct (writer_end result);reflexivity.
 - split;[exact OBS|]. intro CUT;unfold writer_exit_boundary;rewrite CUT;reflexivity.
Qed.


(* A returned publisher error has already chosen FinishPublish. Rust takes
   outer before restoration, and the ? in run_operation leaves owner armed.
   Its subsequent Drop calls rollback again; with outer=None that call is inert. *)
Definition failed_owner_return phase e := match phase with
 | IdleBoundary _ _ _ => controller_evidence DropOwner phase e
 | FatalBoundary => controller_evidence ForgetControl phase e
 | _ => e end.

Theorem failed_owner_return_from_trace vi oi initial events valid view j phase e :
 Trace vi oi initial events valid view ((j,phase),e) ->
 (forall id d ram,phase=IdleBoundary id d ram ->
   owner_armed (controller_read e)=true /\ outer_live (controller_read e)=false) ->
 Trace vi oi initial events valid view ((j,phase),failed_owner_return phase e).
Proof.
 intros PREFIX CALL;destruct phase;try exact PREFIX;
 apply controller_from_trace;[exact PREFIX|exact (CALL _ _ _ eq_refl)|exact PREFIX|exact I].
Qed.

Theorem dirty_error_rollback_from_trace vi oi initial events valid view f h a image root s e old resolved word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists d,
 let taken:=controller_evidence TakeOuter (OpenBoundary image root s) e in
 let phase:=failure_phase old d resolved (normal_external_rollback s) in
 let destination:=((Logged (Ready f) h a,phase),failed_owner_return phase (phase_evidence phase taken)) in
 ordinary_return_ready FinishPublish destination /\
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges phase /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall id decoded ram,phase=IdleBoundary id decoded ram ->
   data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false /\
   outer_live (controller_read (snd destination))=false) /\
 (phase=FatalBoundary -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX ROUTE ARMED LIVE PENDING HEAD MASK.
 set (taken:=controller_evidence TakeOuter (OpenBoundary image root s) e).
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),taken)).
 { apply controller_from_trace;[exact PREFIX|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a image root s taken old resolved
   INIT CTX TAKE PENDING HEAD MASK) as [d [CLOSE [SAFE [RECEIPTS NEXT]]]].
 assert (ARM:owner_armed (controller_read taken)=true) by exact ARMED.
 assert (CONTROL:forall id dd ram,failure_phase old d resolved (normal_external_rollback s)=IdleBoundary id dd ram ->
   owner_armed (controller_read (phase_evidence (failure_phase old d resolved (normal_external_rollback s)) taken))=true /\
   outer_live (controller_read (phase_evidence (failure_phase old d resolved (normal_external_rollback s)) taken))=false).
 { intros id dd ram EQ;rewrite EQ;autorewrite with control_evidence;split;[exact ARM|reflexivity]. }
 pose proof (failed_owner_return_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   _ (phase_evidence _ taken) CLOSE CONTROL) as FULL.
 exists d;split.
 { pose proof (open_trace_not_frozen vi oi initial events valid view (Logged (Ready f) h a) image root s e INIT PREFIX) as NF.
   destruct (failure_phase_normal_shape old d resolved (normal_external_rollback s) NF) as [EQ|[ram EQ]];
   unfold ordinary_return_ready;cbn [fst snd];rewrite EQ;[reflexivity|].
   cbn [failed_owner_return];autorewrite with control_evidence.
   split;[reflexivity|]. split;[reflexivity|exact ROUTE]. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [FINAL [OBS REST]].
 split;[exact FINAL|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[exact OBS|]. split.
   + intros id dd ram EQ;split.
     * rewrite EQ in FINAL;exact (proj1 (common_begin sector data_len valid view marker ranges decode pages
         (Logged (Ready f) h a) id dd ram (proj1 FINAL))).
     * cbn [fst snd];rewrite EQ;split;reflexivity.
   + intro EQ;cbn [fst snd];rewrite EQ;reflexivity.
Qed.



Lemma RestoreObservation_eq_dec (x y:RestoreObservation) : {x=y}+{x<>y}.
Proof. decide equality. Qed.

(* The service supplies an observation, not a postulated successful restore.
   Failure stops before DataClose; a validated response uses the existing
   rollback producer, whose collection may itself stop fatally. *)
Theorem dirty_error_restore_outcome_from_trace vi oi initial events valid view f h a image s e old resolved word_max
 reader inspect check outcome :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector f) old) inspect check) restore_probe) tt outcome tt ->
 exists destination,
 ordinary_return_ready FinishPublish destination /\
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_journal destination=Logged (Ready f) h a /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (outcome<>RestoreValidated -> snd (fst destination)=FatalBoundary) /\
 (forall id d ram,snd (fst destination)=IdleBoundary id d ram ->
   data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX ROUTE ARMED LIVE P HEAD MASK RUN.
 destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|ERROR].
 - subst outcome.
   destruct (dirty_error_rollback_from_trace vi oi initial events valid view f h a image [] s e old resolved word_max
     MARK DEC WORD GEOM INIT NUM CTX PREFIX ROUTE ARMED LIVE P HEAD MASK)
     as [d [READY [FULL [SAFE [NUMBER [OBS [NEXT FATAL]]]]]]].
   lazymatch type of FULL with Trace _ _ _ _ _ _ ?target => exists target end;split;[exact READY|]. split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|].
   split;[reflexivity|]. split;[exact OBS|]. split;[contradiction|]. split;[|exact FATAL].
   intros id dd ram EQ;destruct (NEXT id dd ram EQ) as [BEGIN [ARM CLOSED]];auto.
 - set (taken:=controller_evidence TakeOuter (OpenBoundary image [] s) e).
   assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),taken)).
   { apply controller_from_trace;[exact PREFIX|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
   destruct (failed_restore_from_trace vi oi initial events valid view f h a image [] s taken old
     reader inspect check outcome INIT CTX TAKE P HEAD ltac:(discriminate) RUN
     ltac:(destruct outcome;auto;contradiction)) as [STOP REST].
   pose proof (terminal_control_from_trace vi oi initial events valid view (Logged (Ready f) h a)
     FatalBoundary (forget_volatile_evidence taken) STOP) as FULL.
   lazymatch type of FULL with Trace _ _ _ _ _ _ ?target => exists target end;split;[reflexivity|]. split;[exact FULL|].
   destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS OTHER]].
   split;[exact SAFE|]. split.
   + exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
   + split;[reflexivity|]. split;[exact OBS|]. split;[reflexivity|]. split.
     * intros id d ram EQ;discriminate.
     * reflexivity.
Qed.

Theorem controller_recycled_boss_error_return_before_delivery vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result resolved word_max reader inspect check outcome :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 controller_caller SelectFinish (OpenBoundary image [] s) (controller_read e) ->
 abort_requested (controller_read e)=false -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 (writer_end result=WriterLocalError \/ writer_end result=WriterRetainError) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector (writer_flash result)) old) inspect check) restore_probe) tt outcome tt ->
 exists destination,
 ordinary_return_ready FinishPublish destination /\
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (forall id d ram,snd (fst destination)=IdleBoundary id d ram ->
    data_caller DataBegin ram /\ owner_armed (controller_read (snd destination))=false) /\
 (snd (fst destination)=FatalBoundary -> volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE ERROR MASK RESTORE.
 destruct (controller_recycled_boss_writer vi oi initial events valid view f h a old image s e
   recognize magic fuel req round alignment start r count recycled plan result word_max
   MARK DEC WORD GEOM INIT NUM CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE)
   as [previous [PATH REST]].
 set (reserved:=reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s).
 set (selected:=controller_evidence SelectFinish (OpenBoundary image [] s) e).
 set (ev:=selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) selected)).
 set (cleaned:=preparation_error_state (writer_end result) reserved).
 assert (CLEAN:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OpenBoundary image [] cleaned),ev)).
 { destruct ERROR as [E|E];unfold writer_exit_boundary in PATH;rewrite E in PATH;
   unfold cleaned,preparation_error_state;rewrite E;exact PATH. }
 assert (PN:pending_preparation cleaned=None).
 { unfold cleaned;destruct ERROR as [E|E];rewrite E;reflexivity. }
 assert (ROUTE:finish_selected (controller_read ev)=Some FinishPublish).
 { change (Some (choose_finish (controller_read e) true)=Some FinishPublish).
   unfold choose_finish;rewrite ABORT;reflexivity. }
 assert (ARM:owner_armed (controller_read ev)=true) by exact (proj1 (proj2 CALL)).
 assert (LIVE:outer_live (controller_read ev)=true) by exact (proj1 (proj2 (proj2 CALL))).
 destruct (dirty_error_restore_outcome_from_trace vi oi initial events (validate (writer_flash result)) view
   (writer_flash result) h a image cleaned ev old resolved word_max reader inspect check outcome
   MARK DEC WORD GEOM INIT NUM CTX CLEAN ROUTE ARM LIVE PN HEAD MASK RESTORE)
   as [destination [READY [FULL [SAFE [NUMBER [JOURNAL [OBS [STOP [NEXT FATAL]]]]]]]]].
 exists destination;split;[exact READY|]. split;[exact FULL|]. split;[exact SAFE|]. split;[exact NUMBER|].
 split;[rewrite JOURNAL;reflexivity|]. split;[exact OBS|]. split;assumption.
Qed.


(* Returned append error followed by the actual outer restoration result.
   No DataClose runs on a failed restore and no Drop runs after Fatal. *)
Theorem controller_publication_error_return_before_delivery vi oi initial events valid view ready id d s e old error_j
 read inspect check outcome word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_structure marker initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 hd_error (publications ready)=Some old ->
 clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) ready error_j ->
 returned_error_control (journal_control error_j) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt ->
 exists destination,
 ordinary_return_ready FinishPublish destination /\
 Trace vi oi initial events valid view destination /\ Safe valid view destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_journal destination=error_j /\
 boundary_receipts destination=events++boundary_receipts initial /\
 (outcome=RestoreValidated -> exists ram,
    snd (fst destination)=FrozenBoundary old (N.of_nat id) None ram /\
    protection_table ram=protection_table s /\ protection_saved ram=[] /\
    owner_armed (controller_read (snd destination))=false /\
    ~boundary_begin_caller (error_j,FrozenBoundary old (N.of_nat id) None ram)) /\
 (outcome<>RestoreValidated -> snd (fst destination)=FatalBoundary /\ volatile_control (snd destination)=None).
Proof.
 intros MARK DEC WORD GEOM INIT NUM STRUCT PREFIX ROUTE ARMED LIVE LOCAL HEAD RUN ERROR RESTORE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [saved [STACK BASE]].
 assert (P:pending_preparation s=None) by exact (proj1 (proj2 (proj2 (proj2 (proj1 SOURCE))))).
 set (frozen:=uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s).
 set (phase:=FrozenBoundary old (N.of_nat id) (Some [recovered_boss d]) frozen).
 assert (FAILED:Trace vi oi initial events valid view ((error_j,phase),e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
   eapply fail_prepared with (commands:=[]);[exact LOCAL|exact HEAD|exact RUN|exact ERROR|exact I]. }
 set (taken:=controller_evidence TakeOuter phase e).
 assert (TAKE:Trace vi oi initial events valid view ((error_j,phase),taken)).
 { apply controller_from_trace;[exact FAILED|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
 destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|BAD].
 - subst outcome.
   set (closed:=data_next (DataClose [] saved false) frozen).
   assert (CLOSE:Trace vi oi initial events valid view ((error_j,FrozenBoundary old (N.of_nat id) None closed),taken)).
   { eapply episodes_append with (more:=[]);[exact TAKE|].
     eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
     apply frozen_scope_close with (read:=read) (inspect:=inspect) (check:=check);[|exact RESTORE].
     exact (proj1 (uncertain_rollback_caller _ s [] saved P STACK)). }
   set (done:=controller_evidence DropOwner (FrozenBoundary old (N.of_nat id) None closed) taken).
   assert (FULL:Trace vi oi initial events valid view ((error_j,FrozenBoundary old (N.of_nat id) None closed),done)).
   { apply controller_from_trace;[exact CLOSE|]. split;[exact ARMED|reflexivity]. }
   lazymatch type of FULL with Trace _ _ _ _ _ _ ?target => exists target end;split;[split;[reflexivity|];split;[reflexivity|exact ROUTE]|]. split;[exact FULL|].
   destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS OTHER]].
   split;[exact SAFE|]. split.
   + exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
   + split;[reflexivity|]. split;[exact OBS|]. split.
     * intros _;exists closed;split;[reflexivity|]. split;[reflexivity|].
       split;[reflexivity|]. split;[reflexivity|apply frozen_no_begin].
     * contradiction.
 - assert (STOP:Trace vi oi initial events valid view ((error_j,FatalBoundary),forget_volatile_evidence (taken))).
   { eapply episodes_append with (more:=[]);[exact TAKE|].
     eapply episodes_cons with (event:=None) (events:=[]);[|apply episodes_nil].
     eapply frozen_scope_stop;[exact RESTORE|exact BAD]. }
   pose proof (terminal_control_from_trace vi oi initial events valid view error_j FatalBoundary (forget_volatile_evidence taken) STOP) as FULL.
   lazymatch type of FULL with Trace _ _ _ _ _ _ ?target => exists target end;split;[reflexivity|]. split;[exact FULL|].
   destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS OTHER]].
   split;[exact SAFE|]. split.
   + exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
   + split;[reflexivity|]. split;[exact OBS|]. split;[contradiction|]. intros _;split;reflexivity.
Qed.


(* The public finalization consumer stops at its operational delivery edge.
   controller_dispatch_prefix_from_trace remains a prefix producer: a writer
   prefix is deliberately not called a completed finalization. *)
Theorem selected_finalization_from_trace vi oi initial events valid view j image root s e
 delivered vf of_ destination exit word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((j,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 operation_execution g sector data_len marker ranges decode topology pages
   valid view ((j,OpenBoundary image root s),controller_evidence SelectFinish (OpenBoundary image root s) e)
   delivered vf of_ destination exit ->
 Trace vi oi initial (delivered++events) vf of_ destination /\
 Safe vf of_ destination /\
 phase_numeric word_max marker ranges (snd (fst destination)) /\
 boundary_receipts destination=delivered++events++boundary_receipts initial /\
 delivered=match exit with ReturnedPublished receipt=>[receipt]|_=>[] end /\
 terminal_control_absent destination /\
 forall later vnext onext next,
 Trace vf of_ destination later vnext onext next ->
 Trace vi oi initial (later++delivered++events) vnext onext next /\
 forall history, append_operation_observation history exit=
   match exit_observation exit with Some result=>history++[result]|None=>history end.
Proof.
 intros MARK DEC WORD GEOM INIT NUM PREFIX CALL EXEC.
 assert (SELECTED:Trace vi oi initial events valid view
   ((j,OpenBoundary image root s),controller_evidence SelectFinish (OpenBoundary image root s) e)).
 { apply controller_from_trace;assumption. }
 assert (FULL:Trace vi oi initial (delivered++events) vf of_ destination).
 { eapply episodes_append;[exact SELECTED|eapply operation_execution_trace;exact EXEC]. }
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [SAFE [RECEIPTS REST]].
 split;[exact FULL|]. split;[exact SAFE|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[rewrite RECEIPTS;rewrite app_assoc;reflexivity|]. split.
   + eapply operation_execution_receipts;exact EXEC.
   + split.
     * pose proof (operation_execution_trace g sector data_len marker ranges decode topology pages
         _ _ _ _ _ _ _ _ EXEC) as PATH.
       exact (episode_trace_control g sector data_len marker ranges decode topology pages
         valid view ((j,OpenBoundary image root s),controller_evidence SelectFinish (OpenBoundary image root s) e)
         delivered vf of_ destination I PATH).
     * intros later vnext onext next CONT;split.
       -- exact (episodes_append g sector data_len marker ranges decode topology pages
            vi oi initial (delivered++events) vf of_ destination later vnext onext next FULL CONT).
       -- intro history;reflexivity.
Qed.


Lemma deliver_ready_execution route valid view before :
 ordinary_return_ready route before ->
 exists destination exit,
 operation_execution g sector data_len marker ranges decode topology pages
   valid view before [] valid view destination exit /\
 (exit=ReturnedOrdinary route \/ exit=InterruptedFatal) /\
 fst destination=fst before /\ boundary_receipts destination=boundary_receipts before.
Proof.
 destruct before as [[j phase] e];destruct phase as [id d ram|id d ram|image root ram|image root ram|stage id d ram|old candidate current ram|pc|];cbn [ordinary_return_ready fst snd];try contradiction.
 - intros [ARM [CLOSED ROUTE]].
   exists ((j,IdleBoundary id d ram),controller_evidence DeliverOwned (IdleBoundary id d ram) e),
     (ReturnedOrdinary route).
   split;[apply ordinary_delivery_execution;[split;[exact ARM|];split;[exact CLOSED|];split;[rewrite ROUTE;discriminate|exact I]|exact ROUTE]|].
   split;[left;reflexivity|]. split;reflexivity.
 - intros [ARM [CLOSED ROUTE]].
   exists ((j,FrozenBoundary old candidate current ram),controller_evidence DeliverOwned (FrozenBoundary old candidate current ram) e),
     (ReturnedOrdinary route).
   split;[apply ordinary_delivery_execution;[split;[exact ARM|];split;[exact CLOSED|];split;[rewrite ROUTE;discriminate|exact I]|exact ROUTE]|].
   split;[left;reflexivity|]. split;reflexivity.
 - intro EMPTY;exists ((j,FatalBoundary),e),InterruptedFatal.
   split;[apply operation_already_fatal;exact EMPTY|]. split;[right;reflexivity|]. split;reflexivity.
Qed.

(* Delivery is classified by the executed ready phase, not by a later
   continuation. Fatal has no returned observation. *)
Definition ready_delivery_exit route (before:execution_boundary) :=
 match snd (fst before) with
 | FatalBoundary=>InterruptedFatal | _=>ReturnedOrdinary route end.
Lemma deliver_ready_execution_observed route valid view before :
 ordinary_return_ready route before ->
 exists destination,
 operation_execution g sector data_len marker ranges decode topology pages
   valid view before [] valid view destination (ready_delivery_exit route before) /\
 fst destination=fst before /\ boundary_receipts destination=boundary_receipts before.
Proof.
 destruct before as [[j phase] e];destruct phase as [id d ram|id d ram|image root ram|image root ram|stage id d ram|old candidate current ram|pc|];
 cbn [ordinary_return_ready fst snd ready_delivery_exit];try contradiction.
 - intros [ARM [CLOSED ROUTE]].
   exists ((j,IdleBoundary id d ram),controller_evidence DeliverOwned (IdleBoundary id d ram) e).
   split;[apply ordinary_delivery_execution;[split;[exact ARM|];split;[exact CLOSED|];split;[rewrite ROUTE;discriminate|exact I]|exact ROUTE]|].
   split;reflexivity.
 - intros [ARM [CLOSED ROUTE]].
   exists ((j,FrozenBoundary old candidate current ram),controller_evidence DeliverOwned (FrozenBoundary old candidate current ram) e).
   split;[apply ordinary_delivery_execution;[split;[exact ARM|];split;[exact CLOSED|];split;[rewrite ROUTE;discriminate|exact I]|exact ROUTE]|].
   split;reflexivity.
 - intro EMPTY;exists ((j,FatalBoundary),e).
   split;[apply operation_already_fatal;exact EMPTY|]. split;reflexivity.
Qed.



Theorem controller_finalization_from_trace vi oi initial events valid view final exit word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view final exit ->
 controller_result_post word_max vi oi initial events valid view final.
Proof.
 intros MARK DEC WORD GEOM INIT NUM COMPLETE.
 pose proof (completed_operation_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ COMPLETE) as FULL.
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [SAFE [OBS OTHER]].
 split;[exact FULL|]. split;[exact SAFE|]. split.
 - exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM FULL)).
 - split;[exact OBS|]. split.
   + eapply completed_operation_control;exact COMPLETE.
   + destruct final as [[j phase] evidence];intros id d ram EQ;cbn in EQ;subst phase.
     exact (proj1 (common_begin sector data_len valid view marker ranges decode pages j id d ram (proj1 SAFE))).
Qed.



(* The four existing producers now supply delivery, not merely a closed RAM state. *)
Theorem controlled_clean_from_trace vi oi initial events valid view f h a image root s e old resolved
 word_max A E P (value:A) (failure:E) (payload:list P) (sw1 sw2 error1 error2:nat) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 abort_requested (controller_read e)=false -> phase_dirty (OpenBoundary image root s)=false ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishClean \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL NOT_ABORT CLEAN PENDING HEAD MASK.
 destruct (controlled_clean_from_trace_before_delivery vi oi initial events valid view f h a image root s e old resolved word_max A E P value failure payload sw1 sw2 error1 error2
   MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CALL NOT_ABORT CLEAN PENDING HEAD MASK) as [before [READY [PREFIX_RETURN REST]]].
 destruct (deliver_ready_execution FinishClean valid view before READY)
   as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PREFIX_RETURN|].
   split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - exact (controller_finalization_from_trace vi oi initial events valid view destination exit word_max
     MARK DEC WORD GEOM INIT NUM COMPLETE).
 - destruct REST as [_ [_ [HISTORY OTHER]]].
   assert (JOURNAL:boundary_journal destination=boundary_journal before).
   { unfold boundary_journal;rewrite SAME;reflexivity. }
   rewrite JOURNAL;exact HISTORY.
Qed.

Theorem controlled_abort_from_trace vi oi initial events valid view f h a image root s e old resolved
 word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 controller_caller SelectFinish (OpenBoundary image root s) (controller_read e) ->
 abort_requested (controller_read e)=true -> pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishAbort \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX CALL ABORT PENDING HEAD MASK.
 destruct (controlled_abort_from_trace_before_delivery vi oi initial events valid view f h a image root s e old resolved word_max
   MARK DEC WORD GEOM INIT NUM CTX PREFIX CALL ABORT PENDING HEAD MASK) as [before [READY [PREFIX_RETURN REST]]].
 destruct (deliver_ready_execution FinishAbort valid view before READY)
   as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PREFIX_RETURN|].
   split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - exact (controller_finalization_from_trace vi oi initial events valid view destination exit word_max
     MARK DEC WORD GEOM INIT NUM COMPLETE).
 - destruct REST as [_ [_ [HISTORY OTHER]]].
   assert (JOURNAL:boundary_journal destination=boundary_journal before).
   { unfold boundary_journal;rewrite SAME;reflexivity. }
   rewrite JOURNAL;exact HISTORY.
Qed.

Theorem controller_recycled_boss_error_return vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled plan result resolved word_max reader inspect check outcome :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 controller_caller SelectFinish (OpenBoundary image [] s) (controller_read e) ->
 abort_requested (controller_read e)=false -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) true (neutral_flash recycled) plan result ->
 (writer_end result=WriterLocalError \/ writer_end result=WriterRetainError) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector (writer_flash result)) old) inspect check) restore_probe) tt outcome tt ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE ERROR MASK RESTORE.
 destruct (controller_recycled_boss_error_return_before_delivery vi oi initial events valid view f h a old image s e recognize magic fuel req round alignment start r count recycled plan result resolved word_max reader inspect check outcome
   MARK DEC WORD GEOM INIT NUM CTX ORIGIN RAW PREFIX CALL ABORT HEAD P LOCAL SEARCH GEO RUN OK WRITE ERROR MASK RESTORE) as [before [READY [PREFIX_RETURN REST]]].
 destruct (deliver_ready_execution FinishPublish (validate (writer_flash result)) view before READY)
   as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (writer_flash result)) view destination exit).
 { exists (validate (writer_flash result)),view,before,events,[];split;[exact PREFIX_RETURN|].
   split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - exact (controller_finalization_from_trace vi oi initial events (validate (writer_flash result)) view destination exit word_max
     MARK DEC WORD GEOM INIT NUM COMPLETE).
 - destruct REST as [_ [_ [HISTORY OTHER]]].
   assert (JOURNAL:boundary_journal destination=boundary_journal before).
   { unfold boundary_journal;rewrite SAME;reflexivity. }
   rewrite JOURNAL;exact HISTORY.
Qed.

Theorem controller_publication_error_return vi oi initial events valid view ready id d s e old error_j
 read inspect check outcome word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_structure marker initial ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 hd_error (publications ready)=Some old ->
 clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) ready error_j ->
 returned_error_control (journal_control error_j) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=publications error_j /\
 exit=restoration_delivery_exit outcome.
Proof.
 intros MARK DEC WORD GEOM INIT NUM STRUCT PREFIX ROUTE ARMED LIVE LOCAL HEAD RUN ERROR RESTORE.
 destruct (controller_publication_error_return_before_delivery vi oi initial events valid view ready id d s e old error_j read inspect check outcome word_max
   MARK DEC WORD GEOM INIT NUM STRUCT PREFIX ROUTE ARMED LIVE LOCAL HEAD RUN ERROR RESTORE) as [before [READY [PREFIX_RETURN REST]]].
 destruct (deliver_ready_execution_observed FinishPublish valid view before READY)
   as [destination [DELIVERY [SAME RECEIPTS]]].
 set (exit:=ready_delivery_exit FinishPublish before).
 assert (EXACT:exit=restoration_delivery_exit outcome).
 { destruct REST as [_ [_ [_ [_ [OK BAD]]]]].
   destruct outcome;unfold exit,ready_delivery_exit.
   - rewrite (proj1 (BAD ltac:(discriminate)));reflexivity.
   - rewrite (proj1 (BAD ltac:(discriminate)));reflexivity.
   - rewrite (proj1 (BAD ltac:(discriminate)));reflexivity.
   - destruct (OK eq_refl) as [ram [PHASE _]];rewrite PHASE;reflexivity. }
 assert (KIND:exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal).
 { rewrite EXACT;destruct outcome;cbn;auto. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PREFIX_RETURN|].
   split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - exact (controller_finalization_from_trace vi oi initial events valid view destination exit word_max
     MARK DEC WORD GEOM INIT NUM COMPLETE).
 - split;[|exact EXACT].
   destruct REST as [_ [_ [HISTORY OTHER]]].
   assert (JOURNAL:boundary_journal destination=boundary_journal before).
   { unfold boundary_journal;rewrite SAME;reflexivity. }
   rewrite JOURNAL;rewrite HISTORY;reflexivity.
Qed.


(* A returned pre-append decode error follows the owner's selected publish
   route. This consumer is for the actual cache-hit path: there is no cache
   mutation to drop. Unlike fail_prepared, no journal command has run. *)
Theorem installed_validation_error_return vi oi initial events valid view f h a id candidate s e old
 observe reason after reader inspect check outcome resolved word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> id<>old ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (boss_check_program id true)) f (BossCheckFailed reason) after ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract (reader (object_flash sector after) old) inspect check) restore_probe) tt outcome tt ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 boundary_journal destination=Logged (Ready after) h a.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX PREFIX ROUTE ARMED LIVE HEAD DISTINCT CHECK MASK RESTORE.
 destruct (boss_check_program_post _ _ _ _ _ _ CHECK) as [FRAME OBS];subst after.
 set (phase:=PublishingBoundary CandidatePrepared id candidate s).
 set (taken:=controller_evidence TakeOuter phase e).
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),taken)).
 { apply controller_from_trace;[exact PREFIX|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
 assert (BEFORE:exists before,
   ordinary_return_ready FinishPublish before /\ Trace vi oi initial events valid view before /\
   boundary_journal before=Logged (Ready f) h a).
 { destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|BAD].
   - subst outcome.
     destruct (prepared_rejection_from_trace vi oi initial events valid view f h a id candidate s taken old resolved
       INIT CTX TAKE HEAD MASK) as [previous [CLOSE SAFE]].
     set (closed:=failure_phase old previous resolved (normal_external_rollback s)).
     assert (CONTROL:forall n dd ram,closed=IdleBoundary n dd ram ->
       owner_armed (controller_read (phase_evidence closed taken))=true /\
       outer_live (controller_read (phase_evidence closed taken))=false).
     { intros n dd ram EQ;rewrite EQ;autorewrite with control_evidence;split;[exact ARMED|reflexivity]. }
     pose proof (failed_owner_return_from_trace vi oi initial events valid view (Logged (Ready f) h a)
       closed (phase_evidence closed taken) CLOSE CONTROL) as FULL.
     exists ((Logged (Ready f) h a,closed),failed_owner_return closed (phase_evidence closed taken)).
     split;[|split;[exact FULL|reflexivity]].
     pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
     assert (NF:protection_frozen s=false) by exact (proj1 (proj2 (proj2 (proj1 SOURCE)))).
     destruct (failure_phase_normal_shape old previous resolved (normal_external_rollback s) NF)
       as [EQ|[ram EQ]];
       unfold closed,ordinary_return_ready;cbn [fst snd];rewrite EQ;[reflexivity|].
     cbn [failed_owner_return];autorewrite with control_evidence.
     split;[reflexivity|]. split;[reflexivity|exact ROUTE].
   - destruct (prepared_restore_failure_from_trace vi oi initial events valid view f h a id candidate s taken old
       reader inspect check outcome INIT CTX TAKE HEAD DISTINCT RESTORE
       ltac:(destruct outcome;auto;contradiction)) as [STOP REST].
     exists ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence taken).
     split;[reflexivity|]. split;[exact STOP|reflexivity]. }
 destruct BEFORE as [before [READY [PATH JOURNAL]]].
 destruct (deliver_ready_execution FinishPublish valid view before READY)
   as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - exact (controller_finalization_from_trace vi oi initial events valid view destination exit word_max
     MARK DEC WORD GEOM INIT NUM COMPLETE).
 - unfold boundary_journal;rewrite SAME;exact JOURNAL.
Qed.

Theorem controller_error_then_success vi oi initial first vm om middle second vf of_ final receipt word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial first vm om middle (ReturnedOrdinary FinishPublish) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vm om middle second vf of_ final (ReturnedPublished receipt) ->
 controller_result_post word_max vi oi initial (second++first) vf of_ final /\
 append_operation_observation
   (append_operation_observation [] (ReturnedOrdinary FinishPublish))
   (ReturnedPublished receipt)=[FinalizationError;RetainedResult].
Proof.
 intros MARK DEC WORD GEOM INIT NUM FIRST SECOND.
 destruct (controller_finalization_from_trace vi oi initial first vm om middle
   (ReturnedOrdinary FinishPublish) word_max MARK DEC WORD GEOM INIT NUM FIRST)
   as [PREFIX [MID [MIDNUM [OBS [CONTROL NEXT]]]]].
 destruct (controller_finalization_from_trace vm om middle second vf of_ final
   (ReturnedPublished receipt) word_max MARK DEC WORD GEOM MID MIDNUM SECOND)
   as [SUFFIX [LAST [LASTNUM [OBS' [CONTROL' NEXT']]]]].
 split;[|reflexivity]. split.
 - eapply episodes_append;[exact PREFIX|exact SUFFIX].
 - split;[exact LAST|]. split;[exact LASTNUM|]. split.
   + rewrite OBS';rewrite OBS;rewrite app_assoc;reflexivity.
   + split;assumption.
Qed.


(* A12.g.25: the prepass produces the early return. This is the actual
   write_registry_data_objects return BEFORE run_operation, not a fake clean
   transaction and not an independently chosen finish_route. *)
Theorem owned_pair_entry_return valid view j old d s e count same compare result success word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 pair_prepass_return result=Some success ->
 completed_operation g sector data_len marker ranges decode topology pages
  valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e)
  (ReturnedEntry success) /\
 controller_result_post word_max valid view ((j,IdleBoundary old d s),e) []
  valid view ((j,IdleBoundary old d s),e) /\
 result=pair_prepass_compute count same compare /\
 exit_observation (ReturnedEntry success)=Some (if success then RetainedResult else FinalizationError).
Proof.
 intros MARK DEC WORD GEOM INIT OUT ARM RUN RETURN.
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
  valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e)
  (ReturnedEntry success)).
 { exists valid,view,((j,IdleBoundary old d s),e),[],[];split;[constructor|].
   split;[eapply operation_entry_return;eauto|reflexivity]. }
 split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;try eassumption.
   exact (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
    word_max valid view _ [] valid view j old d s e INIT
    (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)).
 - split;[eapply pair_prepass_execution;exact RUN|reflexivity].
Qed.

(* Successive operations consume the existing numeric induction. The unchanged
   early return contributes an ordinary observation and zero durable receipts. *)
Theorem owned_pair_entry_then_operation valid view j old d s e count same compare result success
 events vf of_ final exit word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 pair_prepass_return result=Some success ->
 completed_operation g sector data_len marker ranges decode topology pages
  valid view ((j,IdleBoundary old d s),e) events vf of_ final exit ->
 controller_result_post word_max valid view ((j,IdleBoundary old d s),e) events vf of_ final /\
 append_operation_observation (append_operation_observation [] (ReturnedEntry success)) exit=
  (if success then [RetainedResult] else [FinalizationError]) ++
  match exit_observation exit with Some observed=>[observed]|None=>[] end.
Proof.
 intros MARK DEC WORD GEOM INIT OUT ARM RUN RETURN NEXT.
 destruct (owned_pair_entry_return valid view j old d s e count same compare result success word_max
   MARK DEC WORD GEOM INIT OUT ARM RUN RETURN) as [COMPLETE [POST REST]].
 destruct POST as [PATH [SAFE [NUM OTHER]]]. split.
 - eapply controller_finalization_from_trace;eauto.
 - unfold append_operation_observation;cbn;destruct success;destruct (exit_observation exit);reflexivity.
Qed.


(* A single dispatch consumer for the ENTRY prefix. A nonempty result opens
   owned/local control; it is not yet a proof of the complete body loop. *)
Theorem owned_pair_entry_dispatch valid view j old d s e count same compare result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 result=pair_prepass_compute count same compare /\
 match pair_prepass_return result with
 | Some success=>
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e)
     (ReturnedEntry success) /\
   controller_result_post word_max valid view ((j,IdleBoundary old d s),e) []
     valid view ((j,IdleBoundary old d s),e)
 | None=>
   exists i remaining,result=PairSelected (i::remaining) /\
   Trace valid view ((j,IdleBoundary old d s),e) [] valid view
    ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e) /\
   Safe valid view ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e) /\
   phase_numeric word_max marker ranges (OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)) /\
   controller_read (owned_local_evidence old d s e)=Control false true true true true None None
 end.
Proof.
 intros MARK DEC WORD GEOM INIT OUT ARM RUN.
 split;[eapply pair_prepass_execution;exact RUN|].
 destruct (pair_prepass_return result) as [success|] eqn:RETURN.
 - destruct (owned_pair_entry_return valid view j old d s e count same compare result success word_max
     MARK DEC WORD GEOM INIT OUT ARM RUN RETURN) as [COMPLETE [POST REST]];auto.
 - destruct result as [|i|[|i remaining]];try discriminate.
   exists i,remaining;split;[reflexivity|].
   destruct (owned_local_control_from_idle valid view j old d s e) as [OPEN CONTROL].
   split;[exact OPEN|].
   pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max valid view _ [] valid view j old d s e INIT
     (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
   destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM OPEN) as [SAFE NUMERIC].
   split;[exact SAFE|]. split;[exact NUMERIC|exact CONTROL].
Qed.

(* The first selected index is the result of the typed prepass. This producer
   includes actual owned/local control before the writer, unlike the historical
   RAM-only first-writer helper. All writer endings are retained. *)
Theorem owned_pair_first_writer valid view f h a old d s e count same compare i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 exists previous,
 let final:=(operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result,
    phase_evidence (snd (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result))
    (selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e)))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash result)) view final /\
 Safe (validate (writer_flash result)) view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\
 boundary_receipts final=client_receipts e /\
 publications (boundary_journal final)=h /\ acknowledgements (boundary_journal final)=a /\
 i::remaining=changed_pair (prepass_same count same) (prepass_equal_first compare)
    (prepass_equal_second count same compare).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE.
 assert (SELECT:i::remaining=changed_pair (prepass_same count same) (prepass_equal_first compare)
    (prepass_equal_second count same compare)).
 { apply pair_prepass_selected;symmetry;eapply pair_prepass_execution;exact PREPASS. }
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation (outer_local_begin s)=None) by reflexivity.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 assert (PATH:exists previous,
  Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (writer_flash result)) view
   (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result,
    phase_evidence (snd (operation_writer_exit old (recovered_image d) [recovered_boss d]
    (reservation_state false (extent_at i) (outer_local_begin s)) h a result))
    (selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))))).
 { destruct ACQUIRE as [[EQ ADMIT]|[recognize [magic [fuel [req [round [alignment [start [r [n [recycled
      [LOCAL [SEARCH [GEO [RUN [OK [RANGE EQ]]]]]]]]]]]]]]]]].
   - subst acquired.
     destruct (operation_writer_from_trace valid view _ [] valid view f h a (recovered_image d) [recovered_boss d]
       (outer_local_begin s) (owned_local_evidence old d s e) old (extent_at i) (plan_at i) result
       INIT RAW OPEN P HEAD ADMIT WRITE) as [previous [PATH REST]];eauto.
   - subst acquired;rewrite RANGE in WRITE |- *.
     destruct (operation_recycled_writer_episode valid view _ [] valid view f h a old (recovered_image d)
       [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
       recognize magic fuel req round alignment start r n recycled (plan_at i) result
       INIT RAW OPEN HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH REST]];eauto. }
 destruct PATH as [previous PATH]. exists previous;split;[exact PATH|].
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PATH) as [SAFE NUMERIC].
 split;[exact SAFE|]. split;[exact NUMERIC|]. split;[reflexivity|].
 split.
 - unfold boundary_journal,operation_writer_exit,writer_exit_boundary;destruct (writer_end result);reflexivity.
 - split;[unfold boundary_journal,operation_writer_exit,writer_exit_boundary;destruct (writer_end result);reflexivity|exact SELECT].
Qed.


(* Acquisition can terminate before any writer runs. The same prepass/owned
   control producer feeds these recycling prefixes; no synthetic cleanup is
   appended to Reset or crypto stop. *)
Theorem owned_pair_first_recycling valid view f h a old d s e count same compare i remaining
 recognize magic fuel req round alignment start r n result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r n -> recycling_run g sector recognize magic r n f result ->
 exists previous,
 let final:=(operation_acquisition_boundary old (recovered_image d) [recovered_boss d] (outer_local_begin s) h a result
   (block_pages (recycle_lo r) (useful_pages r)),phase_evidence (snd (operation_acquisition_boundary old (recovered_image d) [recovered_boss d] (outer_local_begin s) h a result
   (block_pages (recycle_lo r) (useful_pages r)))) (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) (owned_local_evidence old d s e)))) in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (neutral_flash result)) view final /\
 Safe (validate (neutral_flash result)) view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\
 boundary_receipts final=client_receipts e /\
 publications (boundary_journal final)=h /\ acknowledgements (boundary_journal final)=a.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS LOCAL SEARCH GEO RUN.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation (outer_local_begin s)=None) by reflexivity.
 destruct (operation_recycling_acquisition_from_trace valid view _ [] valid view f h a old
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   recognize magic fuel req round alignment start r n result INIT RAW OPEN HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH REST]].
 exists previous;split;[exact PATH|].
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PATH) as [SAFE NUMERIC].
 split;[exact SAFE|]. split;[exact NUMERIC|]. split;[reflexivity|].
 unfold boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result);split;reflexivity.
Qed.


Definition body_return_ready (x:execution_boundary) := match snd (fst x) with
 | IdleBoundary _ _ _ | FrozenBoundary _ _ _ _ =>
   controller_caller DeliverBodyError (snd (fst x)) (controller_read (snd x))
 | FatalBoundary=>volatile_control (snd x)=None
 | _=>False end.
Lemma deliver_body_ready valid view before : body_return_ready before ->
 exists destination exit,
 operation_execution g sector data_len marker ranges decode topology pages
   valid view before [] valid view destination exit /\
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 fst destination=fst before /\ boundary_receipts destination=boundary_receipts before.
Proof.
 destruct before as [[j phase] e];destruct phase;cbn [body_return_ready fst snd];try contradiction.
 - intro CALL;exists ((j,IdleBoundary id decoded ram),controller_evidence DeliverBodyError (IdleBoundary id decoded ram) e),ReturnedBodyError.
   split;[apply body_delivery_execution;exact CALL|]. split;[auto|split;reflexivity].
 - intro CALL;exists ((j,FrozenBoundary old candidate current ram),controller_evidence DeliverBodyError (FrozenBoundary old candidate current ram) e),ReturnedBodyError.
   split;[apply body_delivery_execution;exact CALL|]. split;[auto|split;reflexivity].
 - intro EMPTY;exists ((j,FatalBoundary),e),InterruptedFatal.
   split;[apply operation_already_fatal;exact EMPTY|]. split;[auto|split;reflexivity].
Qed.

(* The local restore service is executed, not assumed successful. An error here
   is fatal and does not deliver the initial body error. The outer root is already
   restored by the local rollback; its subsequent close uses the existing
   normal-rollback/collection producer. *)
Theorem body_error_finish_from_trace_flash vi oi initial events valid view f h a image root s e old
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=FullControl ab true true true true None None true ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P HEAD RESTORE_CASE MASK.
 set (taken:=controller_evidence (TakeLocal false) (OperationBoundary image root s) e).
 assert (TAKEN:Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken)).
 { apply controller_from_trace;[exact PREFIX|]. cbn [controller_caller];rewrite CTRL;split;reflexivity || exact I. }
 assert (SOURCE:Safe valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken)).
 { exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
    _ _ _ _ _ _ _ INIT TAKEN)). }
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CTX TAKEN) as SCOPE.
 pose proof (episode_trace_current_origin g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT ORIGIN TAKEN) as ORIG.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id d] [IN ID]];cbn in ID;subst id.
 assert (CANCEL_STEP:outcome=RestoreValidated ->
   Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken) None valid view
    ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),taken)).
 { intro OK;destruct RESTORE_CASE as [[SAME RESULT]|[DIFFERENT RESTORE]].
   - pose proof (current_origin_selected sector data_len marker ranges decode pages valid view
       (Logged (Ready f) h a) image root s taken old d SOURCE ORIG HEAD IN) as SHAPE.
     destruct SHAPE as [EMPTY|[IMAGE ROOT]];[rewrite EMPTY in SAME;discriminate|].
     eapply operation_clean_cancel_episode;eauto.
   - subst outcome;eapply operation_cancel_episode;eauto. }
 assert (FAILED:outcome<>RestoreValidated ->
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt).
 { intro BAD;destruct RESTORE_CASE as [[SAME OK]|[DIFF RUN]];[contradiction|exact RUN]. }
 destruct outcome.

 all: try solve [
   destruct (operation_restore_stop_from_trace vi oi initial events valid view (Logged (Ready f) h a)
     image root s taken read inspect check _ INIT TAKEN (FAILED ltac:(discriminate)) ltac:(discriminate)) as [STOP REST];
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence taken) InterruptedFatal)
     by (exists valid,view,((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence taken),events,[];
         split;[exact STOP|split;[apply operation_already_fatal;reflexivity|reflexivity]]);
   eexists;exists InterruptedFatal;split;[auto|];split;[exact COMPLETE|];split;
   [eapply controller_finalization_from_trace;eauto|split;reflexivity]].
 assert (CANCEL:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),taken)).
 { eapply episodes_append with (more:=[]);[exact TAKEN|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply CANCEL_STEP;reflexivity|constructor]. }
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CANCEL)) as CSAFE.
 set (opened:=OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)).
 set (closed:=controller_evidence LocalClosed opened taken).
 assert (CLOSED:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),closed)).
 { apply controller_from_trace;[exact CANCEL|]. change (Some false<>None /\ True);split;discriminate || exact I. }
 set (outer:=controller_evidence TakeBodyOuter opened closed).
 assert (CCTRL:controller_read closed=FullControl ab true true true false None None true).
 { change (control_close_local (control_take_local false (controller_read e))=FullControl ab true true true false None None true).
   rewrite CTRL;reflexivity. }
 assert (OCTRL:controller_read outer=FullControl ab false true true false None None true).
 { change (control_take_outer (controller_read closed)=FullControl ab false true true false None None true).
   rewrite CCTRL;reflexivity. }
 assert (OUTER:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),outer)).
 { apply controller_from_trace;[exact CLOSED|]. cbn [controller_caller];rewrite CCTRL;repeat split;reflexivity. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a (recovered_image d) [recovered_boss d]
   (operation_cancel s) outer old resolved INIT CTX OUTER eq_refl HEAD MASK)
   as [restored [ROLLED [RSAFE [RECEIPTS NEXT]]]].
 set (phase:=failure_phase old restored resolved (normal_external_rollback (operation_cancel s))).
 assert (ENDING:exists before, Trace vi oi initial events valid view before /\
    body_return_ready before /\ publications (boundary_journal before)=h /\
    control_image (journal_control (boundary_journal before))=f).
 { assert (CONTROL:forall id dd ram,phase=IdleBoundary id dd ram ->
     owner_armed (controller_read (phase_evidence phase outer))=true /\
     outer_live (controller_read (phase_evidence phase outer))=false).
   { intros id dd ram EQ;rewrite EQ;autorewrite with control_evidence;rewrite OCTRL;split;reflexivity. }
   pose proof (failed_owner_return_from_trace vi oi initial events valid view (Logged (Ready f) h a)
     phase (phase_evidence phase outer) ROLLED CONTROL) as FULL.
   exists ((Logged (Ready f) h a,phase),failed_owner_return phase (phase_evidence phase outer)).
   split;[exact FULL|]. split;[|split;reflexivity].
   assert (NF:protection_frozen (operation_cancel s)=false) by exact (proj1 (proj2 (proj2 (proj1 CSAFE)))).
   unfold phase;rewrite (normal_rollback_phase old restored resolved (operation_cancel s) NF).
   destruct collection_enabled;[destruct resolved|];unfold body_return_ready;cbn [fst snd];
     autorewrite with control_evidence;try reflexivity;
     change (body_error_pending (controller_read outer)=true /\ finish_selected (controller_read outer)=None /\ false=false /\ false=false /\ True);
     rewrite OCTRL;repeat split;reflexivity. }
 destruct ENDING as [before [PATH [READY [HISTORY FLASH]]]].
 destruct (deliver_body_ready valid view before READY) as [destination [exit [DELIVERY [KIND [SAME OBS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - split;unfold boundary_journal in *;rewrite SAME;assumption.
Qed.


Theorem body_error_cleanup_returned_from_trace vi oi initial events valid view f h a image root s e old
 read inspect check mask word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=FullControl ab true true true true None None true ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ RestoreValidated=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt RestoreValidated tt)) ->
 (forall candidate_mask,(Some mask)=Some candidate_mask -> candidate_mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination ReturnedBodyError /\
 controller_result_post word_max vi oi initial events valid view destination /\
 exists restored ram ev,
 destination=((Logged (Ready f) h a,IdleBoundary old restored ram),ev).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P HEAD RESTORE_CASE MASK.
 set (taken:=controller_evidence (TakeLocal false) (OperationBoundary image root s) e).
 assert (TAKEN:Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken)).
 { apply controller_from_trace;[exact PREFIX|]. cbn [controller_caller];rewrite CTRL;split;reflexivity || exact I. }
 assert (SOURCE:Safe valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken)).
 { exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
    _ _ _ _ _ _ _ INIT TAKEN)). }
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CTX TAKEN) as SCOPE.
 pose proof (episode_trace_current_origin g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT ORIGIN TAKEN) as ORIG.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id d] [IN ID]];cbn in ID;subst id.
 assert (CANCEL_STEP:RestoreValidated=RestoreValidated ->
   Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),taken) None valid view
    ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),taken)).
 { intro OK;destruct RESTORE_CASE as [[SAME RESULT]|[DIFFERENT RESTORE]].
   - pose proof (current_origin_selected sector data_len marker ranges decode pages valid view
       (Logged (Ready f) h a) image root s taken old d SOURCE ORIG HEAD IN) as SHAPE.
     destruct SHAPE as [EMPTY|[IMAGE ROOT]];[rewrite EMPTY in SAME;discriminate|].
     eapply operation_clean_cancel_episode;eauto.
   - eapply operation_cancel_episode;eauto. }
 assert (CANCEL:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),taken)).
 { eapply episodes_append with (more:=[]);[exact TAKEN|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply CANCEL_STEP;reflexivity|constructor]. }
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT CANCEL)) as CSAFE.
 set (opened:=OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)).
 set (closed:=controller_evidence LocalClosed opened taken).
 assert (CLOSED:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),closed)).
 { apply controller_from_trace;[exact CANCEL|]. change (Some false<>None /\ True);split;discriminate || exact I. }
 set (outer:=controller_evidence TakeBodyOuter opened closed).
 assert (CCTRL:controller_read closed=FullControl ab true true true false None None true).
 { change (control_close_local (control_take_local false (controller_read e))=FullControl ab true true true false None None true).
   rewrite CTRL;reflexivity. }
 assert (OCTRL:controller_read outer=FullControl ab false true true false None None true).
 { change (control_take_outer (controller_read closed)=FullControl ab false true true false None None true).
   rewrite CCTRL;reflexivity. }
 assert (OUTER:Trace vi oi initial events valid view ((Logged (Ready f) h a,opened),outer)).
 { apply controller_from_trace;[exact CLOSED|]. cbn [controller_caller];rewrite CCTRL;repeat split;reflexivity. }
 destruct (normal_rollback_from_trace vi oi initial events valid view f h a (recovered_image d) [recovered_boss d]
   (operation_cancel s) outer old (Some mask) INIT CTX OUTER eq_refl HEAD MASK)
   as [restored [ROLLED [RSAFE [RECEIPTS NEXT]]]].
 set (phase:=failure_phase old restored (Some mask) (normal_external_rollback (operation_cancel s))).
 assert (NF:protection_frozen (operation_cancel s)=false)
   by exact (proj1 (proj2 (proj2 (proj1 CSAFE)))).
 assert (IDLE:exists ram,phase=IdleBoundary old restored ram).
 { unfold phase;rewrite (normal_rollback_phase old restored (Some mask) (operation_cancel s) NF).
   destruct collection_enabled; eexists;reflexivity. }
 destruct IDLE as [ram IDLE].
 assert (CONTROL:forall id dd state,phase=IdleBoundary id dd state ->
   owner_armed (controller_read (phase_evidence phase outer))=true /\
   outer_live (controller_read (phase_evidence phase outer))=false).
 { intros id dd state EQ;rewrite EQ;autorewrite with control_evidence;rewrite OCTRL;split;reflexivity. }
 pose proof (failed_owner_return_from_trace vi oi initial events valid view (Logged (Ready f) h a)
   phase (phase_evidence phase outer) ROLLED CONTROL) as FULL.
 rewrite IDLE in FULL.
 set (before:=failed_owner_return (IdleBoundary old restored ram) (phase_evidence (IdleBoundary old restored ram) outer)).
 assert (CALL:controller_caller DeliverBodyError (IdleBoundary old restored ram) (controller_read before)).
 { unfold before;cbn [failed_owner_return];autorewrite with control_evidence.
   change (body_error_pending (controller_read outer)=true /\ finish_selected (controller_read outer)=None /\ false=false /\ false=false /\ True).
   rewrite OCTRL;repeat split;reflexivity. }
 set (ev:=controller_evidence DeliverBodyError (IdleBoundary old restored ram) before).
 assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view ((Logged (Ready f) h a,IdleBoundary old restored ram),ev) ReturnedBodyError).
 { exists valid,view,((Logged (Ready f) h a,IdleBoundary old restored ram),before),events,[];
   split;[exact FULL|]. split;[apply body_delivery_execution;exact CALL|reflexivity]. }
 eexists;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
 exists restored,ram,ev;reflexivity.
Qed.

Theorem body_error_finish_from_trace vi oi initial events valid view f h a image root s e old
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=FullControl ab true true true true None None true ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P HEAD RESTORE MASK.
 destruct (body_error_finish_from_trace_flash vi oi initial events valid view f h a image root s e old
   read inspect check outcome resolved word_max ab MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P HEAD RESTORE MASK)
   as [destination [exit [KIND [COMPLETE [POST [HISTORY FLASH]]]]]].
 exists destination,exit;auto.
Qed.

(* Checked rejection leaves the prepared token alive; its Drop is a SECOND
   transition. Numeric rejection of release is excluded by the global trace,
   not by another admission of the already reserved range. *)
Theorem prepared_rejection_return_from_trace vi oi initial events valid view f h a image root s e p kind key old
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=Control ab true true true true None None ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 prepared_local_rejection kind image key (prep_range p) -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 range_check true word_max (prep_range p)=None /\
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P KIND WRITTEN REJECT HEAD RESTORE MASK.
 pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM PREFIX)) as CURRENT_NUM.
 split;[exact (numeric_pending _ _ _ CURRENT_NUM P)|].
 assert (FAILED:Trace vi oi initial events valid view
  ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_prepared_rejected;eauto|constructor]. }
 assert (DROPPED:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OperationBoundary image root (data_next DataDrop s)),body_error_evidence e)).
 { eapply episodes_append with (more:=[]);[exact FAILED|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_rejected_token_drop;[exact P|reflexivity]|constructor]. }
 eapply body_error_finish_from_trace with (ab:=ab);try eassumption.
 - change (control_body_error (controller_read e)=FullControl ab true true true true None None true).
   rewrite CTRL;reflexivity.
 - reflexivity.
Qed.

Theorem attachment_rejection_return_from_trace vi oi initial events valid view f h a image root s e p kind key old
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=Control ab true true true true None None ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 data_slot_for kind image key=None -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 range_check true word_max (prep_range p)=None /\
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P KIND WRITTEN REJECT HEAD RESTORE MASK.
 eapply prepared_rejection_return_from_trace;try eassumption.
 apply missing_attachment_slot;exact REJECT.
Qed.

(* A nonempty key already present chooses that existing slot even when there
   are no holes; full capacity is a rejection only for an absent identity. *)
Lemma attachment_existing_identity_not_rejected kind image key index :
 find_identity kind image key=Some index -> data_slot_for kind image key=Some index.
Proof. intro FOUND;unfold data_slot_for;rewrite FOUND;reflexivity. Qed.
Lemma attachment_full_new_identity_rejected kind image key :
 find_identity kind image key=None -> find_hole image=None -> data_slot_for kind image key=None.
Proof. intros ABSENT FULL;unfold data_slot_for;rewrite ABSENT;exact FULL. Qed.

Theorem body_error_then_success vi oi initial first vm om middle second vf of_ final receipt word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial first vm om middle ReturnedBodyError ->
 completed_operation g sector data_len marker ranges decode topology pages
   vm om middle second vf of_ final (ReturnedPublished receipt) ->
 controller_result_post word_max vi oi initial (second++first) vf of_ final /\
 append_operation_observation (append_operation_observation [] ReturnedBodyError)
   (ReturnedPublished receipt)=[FinalizationError;RetainedResult].
Proof.
 intros MARK DEC WORD GEOM INIT NUM FIRST SECOND.
 destruct (controller_finalization_from_trace vi oi initial first vm om middle ReturnedBodyError word_max
   MARK DEC WORD GEOM INIT NUM FIRST) as [PREFIX [MID [MIDNUM [OBS [CONTROL NEXT]]]]].
 destruct (controller_finalization_from_trace vm om middle second vf of_ final (ReturnedPublished receipt) word_max
   MARK DEC WORD GEOM MID MIDNUM SECOND) as [SUFFIX [LAST [LASTNUM [OBS' [CONTROL' NEXT']]]]].
 split;[|reflexivity]. split;[eapply episodes_append;[exact PREFIX|exact SUFFIX]|].
 split;[exact LAST|]. split;[exact LASTNUM|]. split.
 - rewrite OBS';rewrite OBS;rewrite app_assoc;reflexivity.
 - split;assumption.
Qed.

Theorem owned_pair_first_attachment_rejection valid view f h a old d s e count same compare i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind key resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete ->
 data_slot_for kind (recovered_image d) key=None ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE REJECT MASK.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i remaining
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (BOSS:recovered_boss d=boss_extent (view old)).
 { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
 eapply (proj2 (attachment_rejection_return_from_trace valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (recovered_image d) [recovered_boss d]
   (snapshot_written (reservation_state false (extent_at i) (outer_local_begin s)))
   (selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e)))
   (set_phase (reservation_token false (extent_at i)) Written) kind key old
   None (fun _=>false) (fun _=>false) RestoreValidated resolved word_max false
   MARK DEC WORD GEOM INIT NUM I I PATH eq_refl eq_refl eq_refl eq_refl REJECT HEAD
   ltac:(left;split;[rewrite BOSS;reflexivity|reflexivity]) MASK)).
Qed.


Theorem local_writer_body_error_from_trace vi oi initial events valid view old image root s e p f h a plan result
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view (operation_writer_exit old image root s h a result,e) ->
 pending_preparation s=Some p ->
 writer_execution g sector (prep_range p) false f plan result -> writer_end result=WriterLocalError ->
 controller_read e=Control ab true true true true None None -> hd_error h=Some (N.of_nat old) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX P WRITE ERROR CTRL HEAD RESTORE MASK.
 assert (FAILED:Trace vi oi initial events valid view
  (operation_writer_exit old image root s h a result,
   phase_evidence (snd (operation_writer_exit old image root s h a result)) (body_error_evidence e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_writer_error_observed;[exact P|exact WRITE|auto|rewrite CTRL;repeat split;reflexivity]|constructor]. }
 unfold operation_writer_exit,writer_exit_boundary in FAILED;rewrite ERROR in FAILED;cbn [fst snd operation_phase] in FAILED;
 autorewrite with control_evidence in FAILED.
 eapply body_error_finish_from_trace with (ab:=ab);try eassumption.
 - change (control_body_error (controller_read e)=FullControl ab true true true true None None true).
   rewrite CTRL;reflexivity.
 - reflexivity.
Qed.

(* Dispatch on the executed writer result. The local-error branch does not
   attempt attachment; the complete branch consumes the actual slot rejection.
   Both use the same body delivery, not transaction finalization. *)
Theorem owned_pair_first_body_failure valid view f h a old d s e count same compare i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind key resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 (match writer_end result with
  | WriterComplete => data_slot_for kind (recovered_image d) key=None
  | WriterLocalError => True
  | _ => False end) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE FAILURE MASK.
 destruct (writer_end result) eqn:ENDING;try contradiction.
 - eapply owned_pair_first_attachment_rejection; eassumption.
 - destruct (owned_pair_first_writer valid view f h a old d s e count same compare i remaining
     extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
     as [previous [PATH [SAFE REST]]].
   pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
     (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
   assert (HEAD:hd_error h=Some (N.of_nat old)).
   { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
   assert (BOSS:recovered_boss d=boss_extent (view old)).
   { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
   assert (FAILED:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
     (validate (writer_flash result)) view
     (operation_writer_exit old (recovered_image d) [recovered_boss d]
       (reservation_state false (extent_at i) (outer_local_begin s)) h a result,
       selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e)))).
   { unfold operation_writer_exit,writer_exit_boundary in PATH |- *;rewrite ENDING in PATH |- *;exact PATH. }
   exact (local_writer_body_error_from_trace valid view _ [] (validate (writer_flash result)) view
     old (recovered_image d) [recovered_boss d]
     (reservation_state false (extent_at i) (outer_local_begin s))
     (selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e)))
     (reservation_token false (extent_at i)) acquired h a (plan_at i) result
     None (fun _=>false) (fun _=>false) RestoreValidated resolved word_max false
     MARK DEC WORD GEOM INIT NUM I I FAILED eq_refl WRITE ENDING eq_refl HEAD
     ltac:(left;split;[rewrite BOSS;reflexivity|reflexivity]) MASK).
Qed.

(* A direct reset at a rejected attachment abandons the still-live token and
   the owner. It does NOT run either Drop; existing boot episodes consume it. *)
Theorem rejected_attachment_reset_from_trace vi oi initial events valid view f h a image root s e p kind key word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 data_slot_for kind image key=None ->
 let destination:=((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (body_error_evidence e)) in
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination InterruptedReset /\
 controller_result_post word_max vi oi initial events valid view destination /\
 volatile_control (snd destination)=None /\ publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT NUM PREFIX P KIND WRITTEN REJECT destination.
 assert (FAILED:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_attach_rejected;eauto|constructor]. }
 assert (RESET:Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)
   None valid view destination).
 { apply reset_episode;apply record_step;apply reset_ready. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination InterruptedReset).
 { eapply completed_reset_from_trace;[exact FAILED|exact RESET]. }
 split;[exact COMPLETE|]. split;[eapply controller_finalization_from_trace;eauto|split;reflexivity].
Qed.

Theorem owned_pair_second_attachment_rejection valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry second_acquired second_result key read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 ((second_acquired=writer_flash result /\ mapped_erased_admission sector pages attached (writer_flash result) (extent_at second)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize (writer_flash result) (protection_table attached) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n (writer_flash result) recycled /\
    neutral_end_ recycled=NeutralSuccess /\ extent_at second=block_pages (recycle_lo r) (useful_pages r) /\
    second_acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at second) false second_acquired (plan_at second) second_result ->
 writer_end second_result=WriterComplete ->
 data_slot_for kind (image_replace (recovered_image d) index (Some entry)) key=None ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash second_result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash second_result)) view destination /\
 publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   ACQUIRE_B WRITE_B COMPLETE_B REJECT RESTORE MASK.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 pose proof (proj2 (before_change_skip_from_trace valid view _ []
   (validate (writer_flash result)) view (Logged (Ready (writer_flash result)) h a)
   (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   INIT ATTACH (owned_second_before_change valid view _ old previous d s e index entry
     (extent_at i) _ INIT))) as CHECKED.
 clear ATTACH;rename CHECKED into ATTACH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 assert (B:exists prior,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
    (validate (writer_flash second_result)) view
    (operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
     (reservation_state false (extent_at second) attached) h a second_result,
     phase_evidence (snd (operation_writer_exit old (image_replace (recovered_image d) index (Some entry)) []
     (reservation_state false (extent_at second) attached) h a second_result)) (selected_evidence old prior (advance_allocation_evidence (extent_at second) first_e)))).
 { destruct ACQUIRE_B as [[EQ ADMIT]|[recognize [magic [fuel [req [round [alignment [start [r [n [recycled
     [LOCAL [SEARCH [GEO [RUN [OK [SPAN EQ]]]]]]]]]]]]]]]]].
   - subst second_acquired.
     destruct (operation_writer_from_trace valid view _ [] (validate (writer_flash result)) view
       (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
       old (extent_at second) (plan_at second) second_result INIT RAW ATTACH P HEAD ADMIT WRITE_B)
       as [prior [PATH_B REST_B]];eauto.
   - subst second_acquired;rewrite SPAN in WRITE_B |- *.
     destruct (operation_recycled_writer_episode valid view _ [] (validate (writer_flash result)) view
       (writer_flash result) h a old (image_replace (recovered_image d) index (Some entry)) [] attached first_e
       recognize magic fuel req round alignment start r n recycled (plan_at second) second_result
       INIT RAW ATTACH HEAD P LOCAL SEARCH GEO RUN OK WRITE_B) as [prior [PATH_B REST_B]];eauto. }
 destruct B as [prior B]. unfold operation_writer_exit,writer_exit_boundary in B;rewrite COMPLETE_B in B;cbn in B.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 exact (proj2 (attachment_rejection_return_from_trace valid view _ [] (validate (writer_flash second_result)) view
   (writer_flash second_result) h a (image_replace (recovered_image d) index (Some entry)) []
   (snapshot_written (reservation_state false (extent_at second) attached)) (selected_evidence old prior (advance_allocation_evidence (extent_at second) first_e))
   (set_phase (reservation_token false (extent_at second)) Written) kind key old
   read inspect check outcome resolved word_max false MARK DEC WORD GEOM INIT NUM I I B
   eq_refl eq_refl eq_refl eq_refl REJECT HEAD ltac:(right;split;[discriminate|exact RESTORE]) MASK)).
Qed.


(* Consumes a DELIVERED body error. The residual flash need not equal the
   initial flash; only the still-selected certificate and its objects do. *)
Theorem delivered_body_error_prestate valid view f h a old d s e vf of_ jf chosen restored ram ef :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((jf,IdleBoundary chosen restored ram),ef) ReturnedBodyError ->
 publications jf=h ->
 chosen=old /\ restored=d /\ data_caller DataBegin ram /\
 client_receipts ef=client_receipts e /\
 unchanged (certificate_ranges ranges (Certificate old d))
   (object_flash sector f) (object_flash sector (control_image (journal_control jf))).
Proof.
 intros INIT COMPLETE HIST.
 pose proof (completed_operation_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ COMPLETE) as PATH.
 assert (SEL:selected_live ((Logged (Ready f) h a,IdleBoundary old d s),e) (Certificate old d)).
 { split;[exact (proj2 (proj2 INIT))|].
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 destruct (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ _ INIT SEL PATH HIST) as [FINAL [SELECT KEEP]].
 assert (ENDSEL:selected_live ((jf,IdleBoundary chosen restored ram),ef) (Certificate chosen restored)).
 { split;[exact (proj2 (proj2 FINAL))|].
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 FINAL))))))). }
 pose proof (selected_live_unique sector data_len marker ranges decode pages
   vf of_ _ _ _ FINAL SELECT ENDSEL) as SAME.
 inversion SAME;subst chosen restored;split;[reflexivity|]. split;[reflexivity|]. split.
 - exact (proj1 (common_begin sector data_len vf of_ marker ranges decode pages jf old d ram (proj1 FINAL))).
 - split.
   + exact (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ INIT PATH))).
   + exact KEEP.
Qed.

(* The two scope callers are a local interface. The public writer consumer
   below derives them from the source trace, before any freeze. *)
Theorem frozen_body_finish_from_trace vi oi initial events valid view f h a old candidate current s e
 read inspect check outcome word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,FrozenBoundary (N.of_nat old) candidate (Some current) s),e) ->
 controller_read e=FullControl ab true true true true None None true ->
 data_calls (operation_abort_commands (root_extents (view old))) s ->
 ((root_address current=root_address [boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root_address current<>root_address [boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f /\
 ~ boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT NUM PREFIX CTRL CALLS RESTORE.
 set (phase:=FrozenBoundary (N.of_nat old) candidate (Some current) s).
 set (taken:=controller_evidence (TakeLocal false) phase e).
 assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),taken)).
 { apply controller_from_trace;[exact PREFIX|].
   change (local_live (controller_read e)=true /\ false=false /\
     body_error_pending (controller_read e)=true /\ finish_selected (controller_read e)=None).
   rewrite CTRL;repeat split;reflexivity. }
 assert (ENDING:exists before,Trace vi oi initial events valid view before /\
   body_return_ready before /\ publications (boundary_journal before)=h /\
   control_image (journal_control (boundary_journal before))=f /\ ~boundary_begin_caller (fst before)).
 { destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|BAD].
   - subst outcome.
     set (saved:=root_extents (view old)).
     set (s1:=data_next (DataClose [saved] saved false) s).
     set (phase1:=FrozenBoundary (N.of_nat old) candidate (Some [boss_extent (view old)]) s1).
     assert (LOCAL:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase1),taken)).
     { eapply episodes_append with (more:=[]);[exact TAKE|].
       eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
       apply frozen_body_scope with (read:=read) (inspect:=inspect) (check:=check).
       - exact (proj1 CALLS).
       - destruct RESTORE as [[SAME _]|[DIFF RUN]];auto. }
     set (closed:=controller_evidence LocalClosed phase1 taken).
     assert (CLOSED:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase1),closed)).
     { apply controller_from_trace;[exact LOCAL|].
       change (Some false<>None /\ Some false=Some false /\ body_error_pending (controller_read e)=true /\ (None:option finish_route)=None).
       rewrite CTRL;repeat split;discriminate || reflexivity. }
     assert (CCTRL:controller_read closed=FullControl ab true true true false None None true).
     { change (control_close_local (control_take_local false (controller_read e))=FullControl ab true true true false None None true);rewrite CTRL;reflexivity. }
     set (outer:=controller_evidence TakeBodyOuter phase1 closed).
     assert (OUTER:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase1),outer)).
     { apply controller_from_trace;[exact CLOSED|]. cbn [controller_caller];rewrite CCTRL;repeat split;reflexivity. }
     set (s2:=data_next (DataClose [] saved false) s1).
     set (phase2:=FrozenBoundary (N.of_nat old) candidate (Some [boss_extent (view old)]) s2).
     assert (CLOSE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase2),outer)).
     { eapply episodes_append with (more:=[]);[exact OUTER|].
       eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
       apply frozen_body_scope with (read:=read) (inspect:=inspect) (check:=check).
       - exact (proj1 (proj2 CALLS)).
       - left;reflexivity. }
     assert (OCTRL:controller_read outer=FullControl ab false true true false None None true).
     { change (control_take_outer (controller_read closed)=FullControl ab false true true false None None true);rewrite CCTRL;reflexivity. }
     set (done:=controller_evidence DropOwner phase2 outer).
     assert (DONE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase2),done)).
     { apply controller_from_trace;[exact CLOSE|]. cbn [controller_caller];rewrite OCTRL;split;reflexivity. }
     exists ((Logged (Ready f) h a,phase2),done);split;[exact DONE|]. split;[|split;[reflexivity|split;[reflexivity|apply frozen_no_begin]]].
     change (body_error_pending (controller_read outer)=true /\ finish_selected (controller_read outer)=None /\ false=false /\ outer_live (controller_read outer)=false /\ ([]:list (list extent))=[]).
     rewrite OCTRL;repeat split;reflexivity.
   - assert (RUN:post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
       (restore_contract read inspect check) restore_probe) tt outcome tt).
     { destruct RESTORE as [[_ OK]|[_ RUN]];[contradiction|exact RUN]. }
     assert (STOP:Trace vi oi initial events valid view
       ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence taken)).
     { eapply episodes_append with (more:=[]);[exact TAKE|].
       eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
       eapply frozen_scope_stop;[exact RUN|exact BAD]. }
     exists ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence taken).
     split;[exact STOP|]. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|apply fatal_no_begin]. }
 destruct ENDING as [before [PATH [READY [HISTORY [FLASH BLOCK]]]]].
 destruct (deliver_body_ready valid view before READY) as [destination [exit [DELIVERY [KIND [SAME OBS]]]]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit).
 { exists valid,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
 exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - split;[unfold boundary_journal;rewrite SAME;exact HISTORY|]. split.
   + unfold boundary_journal in *;rewrite SAME;exact FLASH.
   + rewrite SAME;exact BLOCK.
Qed.

(* No post-freeze scope invariant is supplied here. The source Operation trace
   determines both saved roots and the current-root observer of the writer. *)
Theorem operation_physical_body_return vi oi initial events valid view f h a image root s e old r acquired plan result
 read inspect check outcome (cut:option RestoreCut) word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> controller_read e=Control ab true true true true None None ->
 hd_error h=Some (N.of_nat old) ->
 ((acquired=f /\ mapped_erased_admission sector pages s f r) \/
  exists recognize magic fuel req round alignment start chosen n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable chosen /\
    erase_geometry g sector chosen n /\ recycling_run g sector recognize magic chosen n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    r=block_pages (recycle_lo chosen) (useful_pages chosen) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector r false acquired plan result ->
 writer_end result=WriterPhysicalError ->
 (match cut with
  | Some point => root_address root<>root_address [boss_extent (view old)] /\ restore_cut_reached read inspect check point
  | None => (root_address root=root_address [boss_extent (view old)] /\ outcome=RestoreValidated) \/
    (root_address root<>root_address [boss_extent (view old)] /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect check) restore_probe) tt outcome tt) end) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash result /\
 ~ boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX RAW PREFIX P CTRL HEAD ACQUIRE WRITE ERROR RESTORE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as [STACK [BASE ACK]].
 assert (PH:physical_authority s=root_extents (view old)).
 { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 SOURCE))))) as LINK.
   unfold protection_history_link in LINK;cbn in LINK;rewrite HEAD in LINK;cbn in LINK;
   rewrite Nat2N.id in LINK;exact LINK. }
 assert (PRODUCED:exists previous,
   Trace vi oi initial events (validate (writer_flash result)) view
    (operation_writer_exit old image root (reservation_state false r s) h a result,
     phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result))
       (selected_evidence old previous (advance_allocation_evidence r e)))).
 { destruct ACQUIRE as [[EQ ADMIT]|[recognize [magic [fuel [req [round [alignment [start [chosen [n [recycled
      [LOCAL [SEARCH [GEO [RUN [OK [RANGE EQ]]]]]]]]]]]]]]]]].
   - subst acquired.
     destruct (operation_writer_from_trace vi oi initial events valid view f h a image root s e old r plan result
       INIT RAW PREFIX P HEAD ADMIT WRITE) as [previous [PATH REST]];eauto.
   - subst acquired;rewrite RANGE in WRITE |- *.
     destruct (operation_recycled_writer_episode vi oi initial events valid view f h a old image root s e
       recognize magic fuel req round alignment start chosen n recycled plan result
       INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK WRITE) as [previous [PATH REST]];eauto. }
 destruct PRODUCED as [previous PATH].
 set (kept:=selected_evidence old previous (advance_allocation_evidence r e)).
 set (frozen:=snapshot_error true (reservation_state false r s)).
 set (phase:=FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) frozen).
 assert (FAILED:Trace vi oi initial events (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,phase),body_error_evidence kept)).
 { assert (OBS:Step (validate (writer_flash result)) view
     (operation_writer_exit old image root (reservation_state false r s) h a result,
      phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) kept) None
     (validate (writer_flash result)) view
     (operation_writer_exit old image root (reservation_state false r s) h a result,
      phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result))
       (body_error_evidence (phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) kept)))).
   { apply operation_writer_error_observed with (p:=reservation_token false r) (f:=acquired) (plan:=plan).
     - reflexivity.
     - exact WRITE.
     - auto.
     - unfold operation_writer_exit,writer_exit_boundary;rewrite ERROR;cbn [fst snd operation_phase];
       autorewrite with control_evidence.
       change (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
         outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None).
       rewrite CTRL;repeat split;reflexivity. }
   assert (ALL:Trace vi oi initial events (validate (writer_flash result)) view
     (operation_writer_exit old image root (reservation_state false r s) h a result,
      phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result))
       (body_error_evidence (phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result)) kept)))).
   { eapply episodes_append with (more:=[]);[exact PATH|].
     eapply episodes_cons with (event:=None) (events:=[]);[exact OBS|constructor]. }
   unfold operation_writer_exit,writer_exit_boundary in ALL;rewrite ERROR in ALL;exact ALL. }
 assert (FCTRL:controller_read (body_error_evidence kept)=FullControl ab true true true true None None true).
 { change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity. }
 destruct cut as [point|].
 - set (taken:=controller_evidence (TakeLocal false) phase (body_error_evidence kept)).
   assert (TAKE:Trace vi oi initial events (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,phase),taken)).
   { apply controller_from_trace;[exact FAILED|]. cbn [controller_caller];rewrite FCTRL;repeat split;reflexivity. }
   set (destination:=((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
   assert (CUT:operation_execution g sector data_len marker ranges decode topology pages
     (validate (writer_flash result)) view ((Logged (Ready (writer_flash result)) h a,phase),taken) []
     (validate (writer_flash result)) view destination InterruptedReset).
   { apply operation_end with (event:=None);[apply reset_episode;apply record_step;apply reset_ready|reflexivity]. }
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (writer_flash result)) view destination InterruptedReset).
   { exists (validate (writer_flash result)),view,((Logged (Ready (writer_flash result)) h a,phase),taken),events,[];
     split;[exact TAKE|]. split;[exact CUT|reflexivity]. }
   exists destination,InterruptedReset;split;[auto|]. split;[exact COMPLETE|]. split;[|split;[reflexivity|split;[reflexivity|apply reconstruction_no_begin]]].
   eapply controller_finalization_from_trace;eauto.
 - assert (CALLS:data_calls (operation_abort_commands (root_extents (view old))) frozen).
   { replace (root_extents (view old)) with (physical_authority frozen) by exact PH.
     apply operation_abort_calls;[reflexivity|exact STACK]. }
   destruct (frozen_body_finish_from_trace vi oi initial events (validate (writer_flash result)) view
     (writer_flash result) h a old (N.of_nat old) root frozen (body_error_evidence kept)
     read inspect check outcome word_max ab MARK DEC WORD GEOM INIT NUM FAILED FCTRL CALLS RESTORE)
     as [destination [exit [KIND REST']]].
   exists destination,exit;split;[tauto|exact REST'].
Qed.

Theorem owned_pair_first_frozen_body_return valid view f h a old d s e count same compare i remaining
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterPhysicalError ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash result /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE ERROR.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (BOSS:recovered_boss d=boss_extent (view old)).
 { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
 exact (operation_physical_body_return valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   old (extent_at i) acquired (plan_at i) result
   None (fun _=>false) (fun _=>false) RestoreValidated None word_max false
   MARK DEC WORD GEOM INIT NUM I RAW OPEN eq_refl eq_refl HEAD ACQUIRE WRITE ERROR
   ltac:(left;split;[rewrite BOSS;reflexivity|reflexivity])).
Qed.

Theorem owned_pair_second_frozen_body_return valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry second_acquired second_result read inspect check outcome (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 ((second_acquired=writer_flash result /\ mapped_erased_admission sector pages attached (writer_flash result) (extent_at second)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize (writer_flash result) (protection_table attached) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n (writer_flash result) recycled /\
    neutral_end_ recycled=NeutralSuccess /\ extent_at second=block_pages (recycle_lo r) (useful_pages r) /\
    second_acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at second) false second_acquired (plan_at second) second_result ->
 writer_end second_result=WriterPhysicalError ->
 (match cut with Some point=>restore_cut_reached read inspect check point
  | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt end) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash second_result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash second_result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash second_result /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   ACQUIRE_B WRITE_B ERROR RESTORE.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 pose proof (proj2 (before_change_skip_from_trace valid view _ []
   (validate (writer_flash result)) view (Logged (Ready (writer_flash result)) h a)
   (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   INIT ATTACH (owned_second_before_change valid view _ old previous d s e index entry
     (extent_at i) _ INIT))) as CHECKED.
 clear ATTACH;rename CHECKED into ATTACH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 eapply (operation_physical_body_return valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   old (extent_at second) second_acquired (plan_at second) second_result
   read inspect check outcome cut word_max false
   MARK DEC WORD GEOM INIT NUM I RAW ATTACH P eq_refl HEAD ACQUIRE_B WRITE_B ERROR).
 destruct cut;[split;[discriminate|exact RESTORE]|right;split;[discriminate|exact RESTORE]].
Qed.

Theorem operation_acquisition_body_return vi oi initial events valid view f h a image root s e old recognize magic fuel req round alignment start r count result
 read inspect check outcome (cut:option RestoreCut) word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> controller_read e=Control ab true true true true None None ->
 hd_error h=Some (N.of_nat old) ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 neutral_end_ result<>NeutralSuccess ->
 (neutral_end_ result=NeutralError -> match cut with
  | Some point => root_address root<>root_address [boss_extent (view old)] /\ restore_cut_reached read inspect check point
  | None => (root_address root=root_address [boss_extent (view old)] /\ outcome=RestoreValidated) \/
    (root_address root<>root_address [boss_extent (view old)] /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect check) restore_probe) tt outcome tt) end) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash result)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (neutral_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash result /\
 ~ boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX RAW PREFIX P CTRL HEAD LOCAL SEARCH GEO RUN NOT_OK RESTORE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (episode_trace_rollback_context g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT CTX PREFIX) as [STACK [BASE ACK]].
 assert (PH:physical_authority s=root_extents (view old)).
 { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 SOURCE))))) as LINK.
   unfold protection_history_link in LINK;cbn in LINK;rewrite HEAD in LINK;cbn in LINK;
   rewrite Nat2N.id in LINK;exact LINK. }
 destruct (operation_recycling_acquisition_from_trace vi oi initial events valid view f h a old image root s e
   recognize magic fuel req round alignment start r count result INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN)
   as [previous [PATH REST]].
 set (kept:=selected_evidence old previous e).
 destruct (neutral_end_ result) eqn:END;[contradiction| | |];
 unfold recycling_cursor_evidence in PATH;rewrite END in PATH.
 - specialize (RESTORE eq_refl).
   set (frozen:=data_next DataFreeze s).
   set (phase:=FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) frozen).
   assert (FAILED:Trace vi oi initial events (validate (neutral_flash result)) view
     ((Logged (Ready (neutral_flash result)) h a,phase),body_error_evidence kept)).
   { eapply episodes_append with (more:=[]);[exact PATH|].
     eapply episodes_cons with (event:=None) (events:=[]).
     - apply operation_acquisition_error_observed with (f:=f) (recognize:=recognize) (magic:=magic)
         (r:=r) (count:=count);try assumption.
       unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite END;
       cbn [fst snd operation_phase];autorewrite with control_evidence.
       change (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
         outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None).
       rewrite CTRL;repeat split;reflexivity.
     - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite END;constructor. }
   assert (FCTRL:controller_read (body_error_evidence kept)=FullControl ab true true true true None None true).
   { change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity. }
   destruct cut as [point|].
   + set (taken:=controller_evidence (TakeLocal false) phase (body_error_evidence kept)).
     assert (TAKE:Trace vi oi initial events (validate (neutral_flash result)) view
       ((Logged (Ready (neutral_flash result)) h a,phase),taken)).
     { apply controller_from_trace;[exact FAILED|]. cbn [controller_caller];rewrite FCTRL;repeat split;reflexivity. }
     set (destination:=((Logged (Boot (neutral_flash result)) h a,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
     assert (CUT:operation_execution g sector data_len marker ranges decode topology pages
       (validate (neutral_flash result)) view ((Logged (Ready (neutral_flash result)) h a,phase),taken) []
       (validate (neutral_flash result)) view destination InterruptedReset).
     { apply operation_end with (event:=None);[apply reset_episode;apply record_step;apply reset_ready|reflexivity]. }
     assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
       vi oi initial events (validate (neutral_flash result)) view destination InterruptedReset).
     { exists (validate (neutral_flash result)),view,((Logged (Ready (neutral_flash result)) h a,phase),taken),events,[];
       split;[exact TAKE|]. split;[exact CUT|reflexivity]. }
     exists destination,InterruptedReset;split;[auto|]. split;[exact COMPLETE|]. split;[|split;[reflexivity|split;[reflexivity|apply reconstruction_no_begin]]].
     eapply controller_finalization_from_trace;eauto.
   + assert (CALLS:data_calls (operation_abort_commands (root_extents (view old))) frozen).
     { replace (root_extents (view old)) with (physical_authority frozen) by exact PH.
       apply operation_abort_calls;[exact P|exact STACK]. }
     destruct (frozen_body_finish_from_trace vi oi initial events (validate (neutral_flash result)) view
       (neutral_flash result) h a old (N.of_nat old) root frozen (body_error_evidence kept)
       read inspect check outcome word_max ab MARK DEC WORD GEOM INIT NUM FAILED FCTRL CALLS RESTORE)
       as [destination [exit [KIND REST']]].
     exists destination,exit;split;[tauto|exact REST'].
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary in PATH;rewrite END in PATH.
   set (destination:=((Logged (Boot (neutral_flash result)) h a,RebuildingBoundary Selecting),forget_volatile_evidence kept)).
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (neutral_flash result)) view destination InterruptedReset).
   { exists (validate (neutral_flash result)),view,destination,events,[];split;[exact PATH|].
     split;[apply operation_already_reset;reflexivity|reflexivity]. }
   exists destination,InterruptedReset;split;[auto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + split;[reflexivity|]. split;[reflexivity|apply reconstruction_no_begin].
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary in PATH;rewrite END in PATH.
   set (destination:=((Logged (Ready (neutral_flash result)) h a,FatalBoundary),forget_volatile_evidence kept)).
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (neutral_flash result)) view destination InterruptedFatal).
   { exists (validate (neutral_flash result)),view,destination,events,[];split;[exact PATH|].
     split;[apply operation_already_fatal;reflexivity|reflexivity]. }
   exists destination,InterruptedFatal;split;[auto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + split;[reflexivity|]. split;[reflexivity|apply fatal_no_begin].
Qed.

Theorem owned_pair_first_acquisition_return valid view f h a old d s e count same compare i remaining
 recognize magic fuel req round alignment start r n result word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r n -> recycling_run g sector recognize magic r n f result ->
 neutral_end_ result<>NeutralSuccess ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (neutral_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (neutral_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash result /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS LOCAL SEARCH GEO RUN NOT_OK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (BOSS:recovered_boss d=boss_extent (view old)).
 { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
 exact (operation_acquisition_body_return valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   old recognize magic fuel req round alignment start r n result
   None (fun _=>false) (fun _=>false) RestoreValidated None word_max false
   MARK DEC WORD GEOM INIT NUM I RAW OPEN eq_refl eq_refl HEAD LOCAL SEARCH GEO RUN NOT_OK
   ltac:(intro;left;split;[rewrite BOSS;reflexivity|reflexivity])).
Qed.

Theorem owned_pair_second_acquisition_return valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry recognize magic fuel req round alignment start r n second_result read inspect check outcome (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize (writer_flash result) (protection_table attached) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r n -> recycling_run g sector recognize magic r n (writer_flash result) second_result ->
 neutral_end_ second_result<>NeutralSuccess ->
 (neutral_end_ second_result=NeutralError -> match cut with Some point=>restore_cut_reached read inspect check point
  | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt end) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (neutral_flash second_result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (neutral_flash second_result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash second_result /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   LOCAL SEARCH GEO RUN NOT_OK RESTORE.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 pose proof (proj2 (before_change_skip_from_trace valid view _ []
   (validate (writer_flash result)) view (Logged (Ready (writer_flash result)) h a)
   (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   INIT ATTACH (owned_second_before_change valid view _ old previous d s e index entry
     (extent_at i) _ INIT))) as CHECKED.
 clear ATTACH;rename CHECKED into ATTACH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 eapply (operation_acquisition_body_return valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   old recognize magic fuel req round alignment start r n second_result
   read inspect check outcome cut word_max false
   MARK DEC WORD GEOM INIT NUM I RAW ATTACH P eq_refl HEAD LOCAL SEARCH GEO RUN NOT_OK).
 intro ERROR;specialize (RESTORE ERROR).
 destruct cut;[split;[discriminate|exact RESTORE]|right;split;[discriminate|exact RESTORE]].
Qed.

Theorem operation_search_body_return vi oi initial events valid view f h a image root s e old
 fuel recognize req round alignment start reply read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=Control ab true true true true None None ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEOM INIT NUM CTX ORIGIN PREFIX CTRL P HEAD SEARCH REJECT RESTORE MASK.
 assert (FAILED:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   eapply operation_search_rejected;[exact P|exact SEARCH|exact REJECT|].
   rewrite CTRL;repeat split;reflexivity. }
 eapply body_error_finish_from_trace_flash with (ab:=ab);try eassumption.
 change (control_body_error (controller_read e)=FullControl ab true true true true None None true).
 rewrite CTRL;reflexivity.
Qed.

Theorem owned_pair_first_search_return valid view f h a old d s e count same compare i remaining
 fuel recognize req round alignment start reply resolved word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS SEARCH REJECT MASK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (BOSS:recovered_boss d=boss_extent (view old)).
 { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
 exact (operation_search_body_return valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   old fuel recognize req round alignment start reply
   None (fun _=>false) (fun _=>false) RestoreValidated resolved word_max false
   MARK DEC WORD GEOM INIT NUM I I OPEN eq_refl eq_refl HEAD SEARCH REJECT
   ltac:(left;split;[rewrite BOSS;reflexivity|reflexivity]) MASK).
Qed.

Theorem owned_pair_second_search_return valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry fuel recognize req round alignment start reply read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 reusable_search sector fuel recognize (writer_flash result) (protection_table attached) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash result.
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   SEARCH REJECT RESTORE MASK.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 pose proof (proj2 (before_change_skip_from_trace valid view _ []
   (validate (writer_flash result)) view (Logged (Ready (writer_flash result)) h a)
   (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   INIT ATTACH (owned_second_before_change valid view _ old previous d s e index entry
     (extent_at i) _ INIT))) as CHECKED.
 clear ATTACH;rename CHECKED into ATTACH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 eapply (operation_search_body_return valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   old fuel recognize req round alignment start reply
   read inspect check outcome resolved word_max false
   MARK DEC WORD GEOM INIT NUM I I ATTACH eq_refl P HEAD SEARCH REJECT).
 - right;split;[discriminate|exact RESTORE].
 - exact MASK.
Qed.

Theorem operation_numeric_body_return vi oi initial events valid view f h a image root s e old
 read inspect check outcome resolved word_max ab :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> page_metadata_coherent initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial -> current_root_origin initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 controller_read e=Control ab true true true true None None ->
 pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((Logged (Ready f) h a,OperationBoundary image root s),e) false
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 local_admission_rejection sector s f ->
 ((root=[boss_extent (view old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (view old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEOM INIT META NUM CTX ORIGIN PREFIX CTRL P HEAD BEFORE LOCAL RESTORE MASK.
 assert (FAILED:Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   apply operation_numeric_rejected;[exact P| |].
   - apply payload_rejection_controlled.
     + exact (episode_trace_pages g sector data_len marker ranges decode topology pages
         _ _ _ _ _ _ _ META PREFIX).
     + exact BEFORE.
     + apply local_admission_error_classified;exact LOCAL.
   - rewrite CTRL;repeat split;reflexivity. }
 eapply body_error_finish_from_trace_flash with (ab:=ab);try eassumption.
 change (control_body_error (controller_read e)=FullControl ab true true true true None None true).
 rewrite CTRL;reflexivity.
Qed.

Theorem owned_pair_first_numeric_return valid view f h a old d s e count same compare i remaining
 resolved word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 local_admission_rejection sector (outer_local_begin s) f ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEOM INIT META RAW OUT ARM PREPASS LOCAL MASK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (BOSS:recovered_boss d=boss_extent (view old)).
 { exact (proj1 (proj1 (proj2 (proj2 (proj1 INIT))))). }
 exact (operation_numeric_body_return valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   old
   None (fun _=>false) (fun _=>false) RestoreValidated resolved word_max false
   MARK DEC WORD GEOM INIT META NUM I I OPEN eq_refl eq_refl HEAD
   (owned_first_before_change valid view _ old d s e INIT) LOCAL
   ltac:(left;split;[rewrite BOSS;reflexivity|reflexivity]) MASK).
Qed.

Theorem owned_pair_second_numeric_return valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 local_admission_rejection sector attached (writer_flash result) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect check) restore_probe) tt outcome tt ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash result.
Proof.
 intros MARK DEC WORD GEOM INIT META RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   LOCAL RESTORE MASK.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 eapply (operation_numeric_body_return valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   old
   read inspect check outcome resolved word_max false
   MARK DEC WORD GEOM INIT META NUM I I ATTACH eq_refl P HEAD
   (owned_second_before_change valid view _ old previous d s e index entry (extent_at i) _ INIT) LOCAL).
 - right;split;[discriminate|exact RESTORE].
 - exact MASK.
Qed.

Theorem operation_search_stop_from_trace vi oi initial events valid view f h a image root s e
 fuel shape verify req round alignment start target fatal word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table s) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 exists destination,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination (if fatal then InterruptedFatal else InterruptedReset) /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT NUM PREFIX P WALK STOP.
 set (destination:=if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
   else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e)).
 assert (EDGE:Step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view destination).
 { eapply operation_search_interrupted; eassumption. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination (if fatal then InterruptedFatal else InterruptedReset)).
 { exists valid,view,((Logged (Ready f) h a,OperationBoundary image root s),e),events,[];
   split;[exact PREFIX|]. split;[apply operation_end with (event:=None);[exact EDGE|destruct fatal;reflexivity]|reflexivity]. }
 exists destination;split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - destruct fatal;split;[reflexivity|split;[reflexivity|apply fatal_no_begin]|reflexivity|split;[reflexivity|apply reconstruction_no_begin]].
Qed.

Theorem owned_pair_first_search_stop valid view f h a old d s e count same compare i remaining
 fuel shape verify req round alignment start target fatal word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table (outer_local_begin s)) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 exists destination,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view destination
   (if fatal then InterruptedFatal else InterruptedReset) /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view destination /\
 publications (boundary_journal destination)=h /\ control_image (journal_control (boundary_journal destination))=f /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS WALK STOP.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [COMPUTED [first [rest [INDEX [OPEN OTHER]]]]].
 pose proof (proj2 (before_change_skip_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   INIT OPEN (owned_first_before_change valid view _ old d s e INIT))) as CHECKED.
 clear OPEN;rename CHECKED into OPEN.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 exact (operation_search_stop_from_trace valid view _ [] valid view f h a
   (recovered_image d) [recovered_boss d] (outer_local_begin s) (owned_local_evidence old d s e)
   fuel shape verify req round alignment start target fatal word_max
   MARK DEC WORD GEOM INIT NUM OPEN eq_refl WALK STOP).
Qed.

Theorem owned_pair_second_search_stop valid view f h a old d s e count same compare i second
 (extent_at:nat->extent) (plan_at:nat->list writer_command) acquired result word_max kind index entry fuel shape verify req round alignment start target fatal :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
  (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::second::[])) tt ->
 ((acquired=f /\ mapped_erased_admission sector pages (outer_local_begin s) f (extent_at i)) \/
  exists recognize magic fuel req round alignment start r n recycled,
    recognizer_local sector recognize /\
    reusable_search sector fuel recognize f (protection_table (outer_local_begin s)) req round alignment pages start=FoundRecyclable r /\
    erase_geometry g sector r n /\ recycling_run g sector recognize magic r n f recycled /\
    neutral_end_ recycled=NeutralSuccess /\
    extent_at i=block_pages (recycle_lo r) (useful_pages r) /\ acquired=neutral_flash recycled) ->
 writer_execution g sector (extent_at i) false acquired (plan_at i) result ->
 writer_end result=WriterComplete -> ranges entry=[extent_at i] ->
 data_slot_for kind (recovered_image d) (entry_key kind entry)=Some index ->
 let attached:=exact_member ranges (recovered_image d) index entry (extent_at i) (outer_local_begin s) in
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   (writer_flash result) (protection_table attached) req round alignment pages start target ->
 recognition_interruption shape verify (writer_flash result) target fatal ->
 exists destination,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination (if fatal then InterruptedFatal else InterruptedReset) /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=writer_flash result /\
 ~boundary_begin_caller (fst destination).
Proof.
 intros MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE COMPLETE RANGE SLOT attached
   WALK STOP.
 destruct (owned_pair_first_writer valid view f h a old d s e count same compare i [second]
   extent_at plan_at acquired result word_max MARK DEC WORD GEOM INIT RAW OUT ARM PREPASS ACQUIRE WRITE)
   as [previous [PATH [SAFE REST]]].
 unfold operation_writer_exit,writer_exit_boundary in PATH;rewrite COMPLETE in PATH;cbn in PATH.
 set (first_e:=selected_evidence old previous (advance_allocation_evidence (extent_at i) (owned_local_evidence old d s e))).
 assert (ATTACH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   (validate (writer_flash result)) view
   ((Logged (Ready (writer_flash result)) h a,OperationBoundary
      (image_replace (recovered_image d) index (Some entry)) [] attached),first_e)).
 { eapply episodes_append with (more:=[]);[exact PATH|].
   eapply episodes_cons with (event:=None) (events:=[]);
   [eapply operation_attach_episode;try reflexivity;exact RANGE|constructor]. }
 pose proof (proj2 (before_change_skip_from_trace valid view _ []
   (validate (writer_flash result)) view (Logged (Ready (writer_flash result)) h a)
   (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   INIT ATTACH (owned_second_before_change valid view _ old previous d s e index entry
     (extent_at i) _ INIT))) as CHECKED.
 clear ATTACH;rename CHECKED into ATTACH.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 assert (P:pending_preparation attached=None) by reflexivity.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 exact (operation_search_stop_from_trace valid view _ [] (validate (writer_flash result)) view
   (writer_flash result) h a (image_replace (recovered_image d) index (Some entry)) [] attached first_e
   fuel shape verify req round alignment start target fatal word_max
   MARK DEC WORD GEOM INIT NUM ATTACH P WALK STOP).
Qed.

(* A concrete, executable prepass selects only original producer index 1. *)
Example selected_second_prepass_exec :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract 2 (fun i=>Some (Nat.eqb i 0)))
   (pair_prepass_program 2 false)) tt (PairSelected [1]) tt.
Proof.
 cbn;exists (Some true),tt;split;[split;reflexivity|].
 cbn;exists (Some false),tt;repeat split;reflexivity.
Qed.

(* A12.g.32 coverage diagnostic, NOT an implementation of the pair loop.
   The existing trace permits accepting immediately after a NONEMPTY prepass.
   Thus a completed_operation parameter cannot stand in for that loop. *)
Theorem selected_body_not_enforced_by_trace valid view f h a old d s e
 count same compare i remaining word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt
   (PairSelected (i::remaining)) tt ->
 let local:=outer_local_begin s in
 let accepted:=data_next (DataClose [physical_authority local] (physical_authority local) true) local in
 let phase:=OpenBoundary (recovered_image d) [recovered_boss d] accepted in
 let taken:=controller_evidence (TakeLocal true)
   (OperationBoundary (recovered_image d) [recovered_boss d] local) (owned_local_evidence old d s e) in
 let closed:=controller_evidence LocalClosed phase taken in
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view
   ((Logged (Ready f) h a,phase),closed) /\
 Safe valid view ((Logged (Ready f) h a,phase),closed) /\
 phase_numeric word_max marker ranges phase /\
 page_metadata_coherent ((Logged (Ready f) h a,phase),closed) /\
 controller_caller SelectFinish phase (controller_read closed) /\
 choose_finish (controller_read closed) (phase_dirty phase)=FinishClean /\
 boundary_receipts ((Logged (Ready f) h a,phase),closed)=client_receipts e.
Proof.
 intros MARK DEC WORD GEOM INIT META OUT ARM PREPASS local accepted phase taken closed.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
   count same compare (PairSelected (i::remaining)) word_max
   MARK DEC WORD GEOM INIT OUT ARM PREPASS)
   as [_ [first [rest [INDEX [OPEN OTHER]]]]].
 assert (TAKE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view ((Logged (Ready f) h a,
   OperationBoundary (recovered_image d) [recovered_boss d] local),taken)).
 { apply controller_from_trace;[exact OPEN|split;reflexivity || exact I]. }
 destruct (operation_accept_from_trace valid view _ [] valid view (Logged (Ready f) h a)
   (recovered_image d) [recovered_boss d] local taken INIT I TAKE eq_refl) as [ACCEPTED_PATH REST].
 assert (CLOSE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view ((Logged (Ready f) h a,phase),closed)).
 { apply controller_from_trace;[exact ACCEPTED_PATH|split;[discriminate|exact I]]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEOM INIT NUM CLOSE) as [SAFE NUMERIC].
 split;[exact CLOSE|]. split;[exact SAFE|]. split;[exact NUMERIC|]. split.
 - eapply episode_trace_pages;[exact META|exact CLOSE].
 - split;[repeat split;reflexivity|]. split;reflexivity.
Qed.

(* The already-proved finalizer also accepts this unscheduled prefix. This
   records the missing CONTROL premise, rather than assuming a safe suffix. *)
Theorem selected_body_can_reach_clean_finalizer valid view f h a old d s e
 count same compare i remaining word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt
   (PairSelected (i::remaining)) tt ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishClean \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((Logged (Ready f) h a,IdleBoundary old d s),e) [] valid view destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
   valid view destination /\ publications (boundary_journal destination)=h.
Proof.
 intros MARK DEC WORD GEOM INIT META OUT ARM PREPASS.
 destruct (selected_body_not_enforced_by_trace valid view f h a old d s e
   count same compare i remaining word_max MARK DEC WORD GEOM INIT META OUT ARM PREPASS)
   as [PATH [SAFE [NUM [PAGES [CALL REST]]]]].
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 eapply (controlled_clean_from_trace valid view _ [] valid view f h a _ _ _ _ old
   (Some (collect_ranges view marker (Some old) (object_extents (view old)) []))
   word_max unit unit unit tt tt [] 0 0 0 0
   MARK DEC WORD GEOM INIT INITIAL_NUM I I PATH CALL).
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))).
 - intros mask E;inversion E;reflexivity.
Qed.


(* A12.g.33: an operational marking of the EXISTING episode relation.
   The marking carries only a program counter and the original indices. There
   is no second RAM/flash/table/history. In particular there is no constructor
   lifting an arbitrary episode_trace into a successful owned body. *)

Lemma image_replace_existing image index entry :
 nth_error image index=Some (Some entry) -> image_replace image index (Some entry)=image.
Proof.
 revert index;induction image as [|head rest IH];intros [|index] HIT;cbn in HIT |- *;try discriminate.
 - inversion HIT;reflexivity.
 - rewrite (IH index HIT);reflexivity.
Qed.

Section OrderedBody.
Variable runtime_kind : list N -> nat.
(* Local argument interpretation: parent, runtime Data kind, AID(tag).
   It is indexed by the ORIGINAL producer position, not the selected position. *)
Variable argument_key : nat -> object_key.
(* Address-dependent local writer plan for the original callback index. *)
Variable argument_plan : nat -> extent -> list writer_command.

Local Notation owned_body_edge := (owned_body_edge g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_start := (body_start g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_numeric_refused := (body_numeric_refused g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_search_refused := (body_search_refused g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_search_stopped := (body_search_stopped g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_erased := (body_erased g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_recycled := (body_recycled g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_written := (body_written g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_attached := (body_attached g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_identical := (body_identical g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_attach_rejected := (body_attach_rejected g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_reset_reserved := (body_reset_reserved g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_reset_prepared := (body_reset_prepared g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_request_abort := (body_request_abort g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_done := (body_done g sector data_len ranges pages validate runtime_kind argument_key argument_plan).

Lemma owned_body_edge_trace pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y -> Trace vi oi x [] vf of_ y.
Proof.
 intro RUN;destruct RUN.
 - apply episodes_nil.
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_numeric_rejected;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_search_rejected;eauto|apply episodes_nil].
 - destruct fatal;eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_search_interrupted;eauto|apply episodes_nil|eapply operation_search_interrupted;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_reserve_episode;eauto using runtime_erased_admission_mapped|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_acquire_recycled;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_writer_episode;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_attach_episode;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_identical_attachment;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply operation_prepared_rejected;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply reset_episode;eauto|apply episodes_nil].
 - eapply episodes_cons with (event:=None) (events:=[]);[eapply reset_episode;eauto|apply episodes_nil].
 - apply controller_from_trace;[apply episodes_nil|exact H].
 - apply episodes_nil.
Qed.

Lemma owned_body_edge_order pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 todo=map attachment_argument log++todo'.
Proof. intro RUN;destruct RUN;reflexivity. Qed.

(* This is a marked prefix, like operation_execution; all storage states are
   the original execution_boundary endpoints. The error/interrupted PCs have
   no successor here: cleanup belongs to the existing error suffix, not to a
   fictitious completion of the remaining members. *)
Local Notation owned_body_run := (owned_body_run g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_nil := (body_nil g sector data_len ranges pages validate runtime_kind argument_key argument_plan).
Local Notation body_cons := (body_cons g sector data_len ranges pages validate runtime_kind argument_key argument_plan).

Theorem owned_body_run_trace pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y -> Trace vi oi x [] vf of_ y.
Proof.
 intro RUN;induction RUN;[apply episodes_nil|].
 eapply episodes_append with (more:=[]);[eapply owned_body_edge_trace;exact H|exact IHRUN].
Qed.

Theorem owned_body_search_calculation word_max pc todo vi oi x log pc' todo' valid view j image root ram e req start :
 Safe vi oi x -> generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 decoded_allocation_geometry pages decode -> allocation_range_origin sector pages decode (snd x) ->
 pages*256<=word_max ->
 owned_body_run pc todo vi oi x log pc' todo' valid view ((j,OperationBoundary image root ram),e) ->
 runtime_search_inputs sector pages word_max e ram (control_image (journal_control j)) req start ->
 exists allocation,volatile_allocation e=Some allocation /\
 Nat.min word_max (extent_end (allocation_latest allocation))=extent_end (allocation_latest allocation) /\
 256*start=extent_end (allocation_latest allocation) /\ start<=pages.
Proof.
 intros INIT MATCH GEO ORIGIN CAP BODY SERVICE.
 eapply runtime_search_calculation;[|exact CAP|exact SERVICE].
 eapply (episode_trace_allocation_origin g sector data_len marker ranges decode topology pages G DIV
   vi oi x [] valid view ((j,OperationBoundary image root ram),e));
   [exact MATCH|exact GEO|exact ORIGIN|exact INIT|].
 apply owned_body_run_trace in BODY;exact BODY.
Qed.

(* Byte-level provenance of the marker follows the same marked execution.
   The arbitrary marker extent is tied to the concrete eight-byte header only
   at the read consumer, not assumed immutable by a reader contract. *)
Lemma owned_body_edge_marker pc todo vi oi x log pc' todo' vf of_ y :
 Safe vi oi x -> external_structure marker x ->
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 unchanged [marker] (boundary_objects sector x) (boundary_objects sector y).
Proof.
 intros INV STRUCT RUN;destruct RUN;try (intros ext addr IN AT;reflexivity).
 - destruct fatal;intros ext addr IN AT;reflexivity.
 - destruct STRUCT as [saved [STACK BASE]].
   pose proof (recycling_marker_frame g sector marker fuel recognize magic f s
     req round alignment pages start r count result H2
     (proj1 (proj1 (proj1 (proj1 INV))))
     (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 INV)))))) BASE H4 H5 H6) as KEEP.
   unfold boundary_objects,boundary_journal,operation_acquisition_boundary,
     recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result);exact KEEP.
 - destruct STRUCT as [saved [STACK BASE]].
   destruct H2 as [[P BLANK] WRITE].
   pose proof (pending_writer_marker_frame g sector marker s p false f plan result
     (proj1 (proj2 (proj1 INV))) BASE P
     (proj1 (proj1 (proj1 (proj1 INV)))) WRITE) as KEEP.
   unfold boundary_objects,boundary_journal,operation_writer_exit,writer_exit_boundary;
     destruct (writer_end result);exact KEEP.
 - destruct j as [ctrl pubs acks];destruct ctrl;intros ext addr IN AT;reflexivity.
 - destruct j as [ctrl pubs acks];destruct ctrl;intros ext addr IN AT;reflexivity.
Qed.
Theorem owned_body_run_marker pc todo vi oi x log pc' todo' vf of_ y :
 Safe vi oi x -> external_structure marker x ->
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 unchanged [marker] (boundary_objects sector x) (boundary_objects sector y).
Proof.
 intros INV STRUCT RUN;induction RUN;[intros ext addr IN AT;reflexivity|].
 pose proof (owned_body_edge_trace _ _ _ _ _ _ _ _ _ _ _ H) as PATH.
 pose proof (owned_body_edge_marker _ _ _ _ _ _ _ _ _ _ _ INV STRUCT H) as KEEP.
 assert (NEXT:Safe vm om y).
 { exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
     G DIV _ _ _ _ _ _ _ INV PATH)). }
 assert (SHAPE:external_structure marker y).
 { exact (episode_trace_external_structure g sector data_len marker ranges decode topology pages
     G DIV _ _ _ _ _ _ _ INV STRUCT PATH). }
 specialize (IHRUN NEXT SHAPE).
 intros ext addr IN AT;rewrite (IHRUN ext addr IN AT);exact (KEEP ext addr IN AT).
Qed.

Theorem owned_body_run_order pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 todo=map attachment_argument log++todo'.
Proof.
 intro RUN;induction RUN;[reflexivity|].
 rewrite (owned_body_edge_order _ _ _ _ _ _ _ _ _ _ _ H). rewrite IHRUN.
 rewrite map_app app_assoc;reflexivity.
Qed.

Lemma owned_finished_empty pc todo vi oi x log tail vf of_ y :
 owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y ->
 pc<>BodyFinished -> tail=[].
Proof.
 intro RUN;remember BodyFinished as last eqn:E;induction RUN;intro NE;[congruence|].
 subst last. destruct H;try (apply IHRUN;auto;discriminate).
 - destruct (neutral_end_ result);simpl in IHRUN;apply IHRUN;auto;discriminate.
 - destruct (writer_end result);simpl in IHRUN;apply IHRUN;auto;discriminate.
 - inversion RUN;subst;[reflexivity|inversion H].
Qed.

Theorem owned_body_success_order todo vi oi x log tail vf of_ y :
 owned_body_run BodyWaiting todo vi oi x log BodyFinished tail vf of_ y ->
 map attachment_argument log=todo /\ tail=[].
Proof.
 intro RUN;pose proof (owned_finished_empty _ _ _ _ _ _ _ _ _ _ RUN ltac:(discriminate)) as EMPTY.
 split;[pose proof (owned_body_run_order _ _ _ _ _ _ _ _ _ _ _ RUN) as ORDER;
 rewrite EMPTY app_nil_r in ORDER;symmetry;exact ORDER|exact EMPTY].
Qed.

Corollary owned_body_no_skipped_member i todo vi oi x tail vf of_ y :
 ~owned_body_run BodyWaiting (i::todo) vi oi x [] BodyFinished tail vf of_ y.
Proof. intro RUN;destruct (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN) as [BAD _];discriminate. Qed.

Theorem owned_body_prefix_numeric word_max pc todo vi oi x log pc' todo' vf of_ y :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi x -> phase_numeric word_max marker ranges (snd (fst x)) ->
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 Trace vi oi x [] vf of_ y /\ Safe vf of_ y /\ phase_numeric word_max marker ranges (snd (fst y)).
Proof.
 intros MARK DEC WORD GEO INIT NUM RUN.
 pose proof (owned_body_run_trace _ _ _ _ _ _ _ _ _ _ _ RUN) as PATH.
 split;[exact PATH|eapply episode_trace_numeric;eauto].
Qed.

Definition body_no_token pc (x:execution_boundary) := match pc with
 | BodyWaiting | BodyAcquiring | BodyFinished => match snd (fst x) with
   | OperationBoundary _ _ s => pending_preparation s=None | _=>True end
 | _=>True end.
Lemma owned_edge_no_token pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 body_no_token pc x -> body_no_token pc' y.
Proof.
 intro RUN;destruct RUN;cbn;auto.
 - destruct (neutral_end_ result);exact (fun _=>I).
 - destruct (writer_end result);exact (fun _=>I).
Qed.
Theorem owned_run_no_token pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 body_no_token pc x -> body_no_token pc' y.
Proof. intro RUN;induction RUN;intro TOKEN;[exact TOKEN|apply IHRUN;eapply owned_edge_no_token;eauto]. Qed.

Lemma owned_success_not_failed pc todo vi oi x log tail vf of_ y :
 owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y ->
 pc<>BodyFailed /\ pc<>BodyInterrupted.
Proof. intro RUN;inversion RUN;subst;[split;discriminate|inversion H;subst;split;discriminate]. Qed.

Definition body_image (x:execution_boundary) := match snd (fst x) with
 | OperationBoundary image _ _ => Some image | _=>None end.
Definition apply_attachment image item := image_replace image (attachment_slot item) (Some (attachment_entry item)).
Definition apply_attachments log image := fold_left apply_attachment log image.

Lemma owned_edge_image pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted ->
 body_image y=option_map (apply_attachments log) (body_image x).
Proof.
 intro RUN;destruct RUN;intros NF NI;try (destruct x as [[j ph] ev];destruct ph;reflexivity);
 try reflexivity;try contradiction.
 - unfold acquisition_pc in NF,NI;destruct (neutral_end_ result) eqn:END;try contradiction.
   unfold operation_acquisition_boundary, recycling_acquisition_boundary;rewrite END;reflexivity.
 - unfold preparation_pc in NF,NI;destruct (writer_end result) eqn:END;try contradiction.
   unfold operation_writer_exit, writer_exit_boundary;rewrite END;reflexivity.
 - change (Some image=Some (image_replace image index (Some entry))).
   rewrite (image_replace_existing image index entry H5);reflexivity.

Qed.

Theorem owned_success_exact_image pc todo vi oi x log tail vf of_ y :
 owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y ->
 body_image y=option_map (apply_attachments log) (body_image x).
Proof.
 intro RUN;remember BodyFinished as last eqn:E;induction RUN.
 - destruct x as [[j ph] ev];destruct ph;reflexivity.
 - subst last. destruct (owned_success_not_failed _ _ _ _ _ _ _ _ _ _ RUN) as [NF NI].
   rewrite (IHRUN eq_refl). rewrite (owned_edge_image _ _ _ _ _ _ _ _ _ _ _ H NF NI).
   destruct (body_image x);simpl;[|reflexivity].
   unfold apply_attachments;rewrite fold_left_app;reflexivity.
Qed.

Lemma owned_edge_keys pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 Forall (fun item=>entry_key runtime_kind (attachment_entry item)=argument_key (attachment_argument item)) log.
Proof. intro RUN;destruct RUN;repeat constructor;assumption. Qed.
Theorem owned_run_keys pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 Forall (fun item=>entry_key runtime_kind (attachment_entry item)=argument_key (attachment_argument item)) log.
Proof.
 intro RUN;induction RUN;[constructor|apply Forall_app;split;[eapply owned_edge_keys;exact H|exact IHRUN]].
Qed.

(* All successes, including original index 1 and repeated identities, use this
   same consumer. The only execution premise is the operational marked run;
   neither its trace, final invariant nor completion of indices is supplied. *)
Theorem owned_body_completion word_max todo vi oi initial events valid view x log tail vf of_ y :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view x ->
 body_no_token BodyWaiting x ->
 owned_body_run BodyWaiting todo valid view x log BodyFinished tail vf of_ y ->
 Trace vi oi initial events vf of_ y /\ Safe vf of_ y /\
 phase_numeric word_max marker ranges (snd (fst y)) /\
 map attachment_argument log=todo /\ tail=[] /\ body_no_token BodyFinished y /\
 body_image y=option_map (apply_attachments log) (body_image x) /\
 Forall (fun item=>entry_key runtime_kind (attachment_entry item)=argument_key (attachment_argument item)) log.
Proof.
 intros MARK DEC WORD GEO INIT NUM PREFIX TOKEN RUN.
 assert (PATH:Trace vi oi initial events vf of_ y).
 { eapply episodes_append with (more:=[]);[exact PREFIX|eapply owned_body_run_trace;exact RUN]. }
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT NUM PATH) as [SAFE NUMERIC].
 destruct (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN) as [ORDER EMPTY].
 split;[exact PATH|]. split;[exact SAFE|]. split;[exact NUMERIC|].
 split;[exact ORDER|]. split;[exact EMPTY|]. split;[eapply owned_run_no_token;eauto|].
 split;[eapply owned_success_exact_image;exact RUN|eapply owned_run_keys;exact RUN].
Qed.

Lemma owned_body_run_append pc todo vi oi x log mid rest vm om y logs last tail vf of_ z :
 owned_body_run pc todo vi oi x log mid rest vm om y ->
 owned_body_run mid rest vm om y logs last tail vf of_ z ->
 owned_body_run pc todo vi oi x (log++logs) last tail vf of_ z.
Proof.
 intros PREFIX SUFFIX;induction PREFIX;[exact SUFFIX|].
 rewrite -app_assoc. eapply body_cons;[exact H|apply IHPREFIX;exact SUFFIX].
Qed.

(* The actual existing acquisition/writer producers supply the marking.
   No invariant is a premise at the intermediate reservation. *)
Theorem owned_erased_writer_prefix vi oi initial events valid view f h a old image root s e
 i todo r plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 runtime_erased_admission sector pages e s f r -> writer_execution g sector r false f plan result ->
 plan=argument_plan i r ->
 exists previous,
 owned_body_run BodyWaiting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (preparation_pc (writer_end result)) (i::todo) (validate (writer_flash result)) view
   (operation_writer_exit old image root (reservation_state false r s) h a result,
    phase_evidence (snd (operation_writer_exit old image root (reservation_state false r s) h a result))
      (selected_evidence old previous (advance_allocation_evidence r e))).
Proof.
 intros INIT RAW PREFIX HEAD P ADMISSION WRITE PLAN.
 pose proof (runtime_erased_admission_forget _ _ _ _ _ _ ADMISSION) as ADMIT.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 exists previous.
 eapply body_cons with (log:=[]) (logs:=[]);[apply body_start|].
 eapply body_cons with (log:=[]) (logs:=[]);[eapply body_erased with (r:=r);[exact P|exact ADMISSION]|].
 eapply body_cons with (log:=[]) (logs:=[]);[|apply body_nil].
 eapply body_written with (p:=reservation_token false r);try eassumption.
 - split;[split;[reflexivity|exact (proj2 (erased_admission_guards _ _ _ _ ADMIT))]|exact WRITE].
 - reflexivity.
Qed.

Theorem owned_recycled_acquisition_prefix vi oi initial events valid view f h a old image root s e i todo
 recognize magic fuel req round alignment start r count result word_max :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 runtime_search_inputs sector pages word_max e s f req start ->
 exists previous,
 let final:=(operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)),
 phase_evidence (snd (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r))))
   (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e))) in
 owned_body_run BodyWaiting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (acquisition_pc (neutral_end_ result)) (i::todo) (validate (neutral_flash result)) view final /\
 Trace vi oi initial events (validate (neutral_flash result)) view final /\
 (neutral_end_ result=NeutralSuccess -> reservation_handoff sector (neutral_flash result)
   (reservation_state false (block_pages (recycle_lo r) (useful_pages r)) s)
   (reservation_token false (block_pages (recycle_lo r) (useful_pages r)))).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN INPUTS.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 exists previous.
 assert (MARKED:owned_body_run BodyWaiting (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (acquisition_pc (neutral_end_ result)) (i::todo) (validate (neutral_flash result)) view
   (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)),
    phase_evidence (snd (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r))))
      (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e)))).
 { eapply body_cons with (log:=[]) (logs:=[]);[apply body_start|].
   eapply body_cons with (log:=[]) (logs:=[]);[eapply body_recycled;eauto|apply body_nil]. }
 split;[exact MARKED|]. split.
 - eapply episodes_append with (more:=[]);[exact PREFIX|eapply owned_body_run_trace;exact MARKED].
 - exact (proj2 (proj2 (proj2 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV SOURCE ORDER HEAD IN (READERS _) LOCAL ACCEPT P SEARCH GEO RUN)))).
Qed.

(* Appending this edge is the ONLY means to consume a selected index. The
   descriptor is tied to the original argument; the slot is selected on the
   reached image, not on the initial one. *)
Theorem owned_attach_member pc selected vi oi x prefix valid view j image root s e i todo p index entry :
 owned_body_run pc selected vi oi x prefix BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 nth_error image index<>Some (Some entry) ->
 owned_body_run pc selected vi oi x (prefix++[OwnedAttachment i index entry]) BodyWaiting todo valid view
   ((j,OperationBoundary (image_replace image index (Some entry)) []
     (exact_attach ranges image index entry (data_next DataWritten s))),e).
Proof.
 intros PREFIX P KIND WRITTEN RANGE KEY SLOT DIFFERENT.
 eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[OwnedAttachment i index entry]) (logs:=[]);
 [eapply body_attached;eauto|apply body_nil].
Qed.

Corollary owned_two_success_original_order vi oi x log tail vf of_ y :
 owned_body_run BodyWaiting [0;1] vi oi x log BodyFinished tail vf of_ y ->
 map attachment_argument log=[0;1].
Proof. intro RUN;exact (proj1 (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN)). Qed.
Corollary owned_second_only_original_index vi oi x log tail vf of_ y :
 owned_body_run BodyWaiting [1] vi oi x log BodyFinished tail vf of_ y ->
 map attachment_argument log=[1].
Proof. intro RUN;exact (proj1 (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN)). Qed.
Corollary owned_error_after_first_keeps_second vi oi x log vf of_ y :
 owned_body_run BodyWaiting [0;1] vi oi x log BodyFailed [1] vf of_ y ->
 map attachment_argument log=[0].
Proof.
 intro RUN;pose proof (owned_body_run_order _ _ _ _ _ _ _ _ _ _ _ RUN) as ORDER.
 destruct (map attachment_argument log) as [|i [|j rest]];simpl in ORDER;try discriminate.
 - inversion ORDER;reflexivity.
 - inversion ORDER. destruct rest;discriminate.
Qed.


Theorem owned_pending_writer_prefix vi oi initial events valid view f h a old image root s e
 i todo p plan result :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_writer_run g sector s p false f plan result -> prep_kind p=ObjectPreparation ->
 plan=argument_plan i (prep_range p) ->
 exists previous,
 owned_body_run BodyWriting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (preparation_pc (writer_end result)) (i::todo) (validate (writer_flash result)) view
   (operation_writer_exit old image root s h a result,
    phase_evidence (snd (operation_writer_exit old image root s h a result)) (selected_evidence old previous e)).
Proof.
 intros INIT RAW PREFIX HEAD WRITE KIND PLAN.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];simpl in ID;subst id.
 exists previous. eapply body_cons with (log:=[]) (logs:=[]);[eapply body_written;eauto|apply body_nil].
Qed.

(* The body [] itself is a no-effect program. Its public entry still uses the
   existing early return, not OperationScope or an artificial accept. *)
Lemma owned_empty_body valid view x :
 owned_body_run BodyWaiting [] valid view x [] BodyFinished [] valid view x.
Proof. eapply body_cons with (log:=[]) (logs:=[]);[apply body_done|apply body_nil]. Qed.

Theorem owned_empty_prepass_return valid view j old d s e count same compare word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected []) tt ->
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e) (ReturnedEntry true) /\
 controller_result_post word_max valid view ((j,IdleBoundary old d s),e) [] valid view ((j,IdleBoundary old d s),e).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM RUN.
 exact (proj2 (owned_pair_entry_dispatch valid view j old d s e count same compare (PairSelected [])
   word_max MARK DEC WORD GEO INIT OUT ARM RUN)).
Qed.

Theorem owned_single_prepared vi oi x valid view j image root s e i p index entry :
 owned_body_run BodyWaiting [i] vi oi x [] BodyPrepared [i] valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 nth_error image index<>Some (Some entry) ->
 owned_body_run BodyWaiting [i] vi oi x [OwnedAttachment i index entry] BodyFinished [] valid view
   ((j,OperationBoundary (image_replace image index (Some entry)) []
     (exact_attach ranges image index entry (data_next DataWritten s))),e).
Proof.
 intros PREFIX P KIND WRITTEN RANGE KEY SLOT DIFFERENT.
 eapply owned_body_run_append with (log:=[OwnedAttachment i index entry]) (logs:=[]).
 - exact (owned_attach_member _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PREFIX P KIND WRITTEN RANGE KEY SLOT DIFFERENT).
 - apply owned_empty_body.
Qed.

Theorem owned_two_prepared vi oi x va oa ja imageA rootA sA eA i k pA slotA entryA
 vb ob jb imageB rootB sB eB pB slotB entryB :
 owned_body_run BodyWaiting [i;k] vi oi x [] BodyPrepared [i;k] va oa ((ja,OperationBoundary imageA rootA sA),eA) ->
 pending_preparation sA=Some pA -> prep_kind pA=ObjectPreparation -> prep_phase pA=Written ->
 ranges entryA=[prep_range pA] -> entry_key runtime_kind entryA=argument_key i ->
 data_slot_for runtime_kind imageA (argument_key i)=Some slotA ->
 nth_error imageA slotA<>Some (Some entryA) ->
 owned_body_run BodyWaiting [k] va oa
   ((ja,OperationBoundary (image_replace imageA slotA (Some entryA)) []
     (exact_attach ranges imageA slotA entryA (data_next DataWritten sA))),eA) []
   BodyPrepared [k] vb ob ((jb,OperationBoundary imageB rootB sB),eB) ->
 pending_preparation sB=Some pB -> prep_kind pB=ObjectPreparation -> prep_phase pB=Written ->
 ranges entryB=[prep_range pB] -> entry_key runtime_kind entryB=argument_key k ->
 data_slot_for runtime_kind imageB (argument_key k)=Some slotB ->
 nth_error imageB slotB<>Some (Some entryB) ->
 owned_body_run BodyWaiting [i;k] vi oi x
   [OwnedAttachment i slotA entryA;OwnedAttachment k slotB entryB] BodyFinished [] vb ob
   ((jb,OperationBoundary (image_replace imageB slotB (Some entryB)) []
     (exact_attach ranges imageB slotB entryB (data_next DataWritten sB))),eB).
Proof.
 intros FIRST PA KA WA RA EA SA DA SECOND PB KB WB RB EB SB DB.
 eapply owned_body_run_append with (log:=[OwnedAttachment i slotA entryA])
   (logs:=[OwnedAttachment k slotB entryB]).
 - exact (owned_attach_member _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIRST PA KA WA RA EA SA DA).
 - eapply owned_single_prepared;eauto.
Qed.

(* Reuse the exact replacement theorem: equal keys do NOT remove the second
   argument. Both actual slot selections are needed, on their respective images. *)
Theorem owned_repeated_tag_last image a b slotA slotB i k :
 image_unique runtime_kind image -> argument_key i=argument_key k ->
 entry_key runtime_kind a=argument_key i -> entry_key runtime_kind b=argument_key k ->
 data_slot_for runtime_kind image (argument_key i)=Some slotA ->
 data_slot_for runtime_kind (image_replace image slotA (Some a)) (argument_key k)=Some slotB ->
 lookup_entry runtime_kind
   (apply_attachments [OwnedAttachment i slotA a;OwnedAttachment k slotB b] image) (argument_key i)=Some b.
Proof.
 intros UNIQUE SAME KA KB SA SB.
 change (lookup_entry runtime_kind (image_replace (image_replace image slotA (Some a)) slotB (Some b))
   (argument_key i)=Some b).
 rewrite -KA in SA. rewrite -KB in SB.
 rewrite (two_replacements_lookup runtime_kind image a b slotA slotB UNIQUE SA SB).
 destruct (object_key_eq_dec (argument_key i) (entry_key runtime_kind b));[reflexivity|congruence].
Qed.

Lemma owned_failure_has_no_body_success pc todo vi oi x log tail vf of_ y :
 pc=BodyFailed \/ pc=BodyInterrupted ->
 ~owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y.
Proof. intros BAD RUN;destruct (owned_success_not_failed _ _ _ _ _ _ _ _ _ _ RUN);tauto. Qed.


Fixpoint attachment_checks image log := match log with
 | []=>True
 | item::tail=>data_slot_for runtime_kind image (argument_key (attachment_argument item))=Some (attachment_slot item) /\
   attachment_checks (apply_attachment image item) tail end.
Lemma attachment_checks_app image first second :
 attachment_checks image (first++second) <->
 attachment_checks image first /\ attachment_checks (apply_attachments first image) second.
Proof.
 revert image;induction first as [|a rest IH];intro image;cbn;[tauto|].
 rewrite IH;tauto.
Qed.
Lemma owned_edge_slots pc todo vi oi x log pc' todo' vf of_ y image :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 body_image x=Some image -> attachment_checks image log.
Proof. intro RUN;destruct RUN;cbn;intro IMAGE;try exact I;inversion IMAGE;subst;split;auto. Qed.
Theorem owned_success_slots pc todo vi oi x log tail vf of_ y image :
 owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y ->
 body_image x=Some image -> attachment_checks image log.
Proof.
 intro RUN;remember BodyFinished as last eqn:E;revert image;induction RUN;intros image IMAGE;[exact I|].
 subst last. apply attachment_checks_app;split;[eapply owned_edge_slots;eauto|].
 apply IHRUN;[reflexivity|].
 destruct (owned_success_not_failed _ _ _ _ _ _ _ _ _ _ RUN) as [NF NI].
 rewrite (owned_edge_image _ _ _ _ _ _ _ _ _ _ _ H NF NI) IMAGE;reflexivity.
Qed.

Theorem owned_success_repeated_tag vi oi x vf of_ y tail image a b slotA slotB i k :
 owned_body_run BodyWaiting [i;k] vi oi x
   [OwnedAttachment i slotA a;OwnedAttachment k slotB b] BodyFinished tail vf of_ y ->
 body_image x=Some image -> image_unique runtime_kind image -> argument_key i=argument_key k ->
 exists final_image, body_image y=Some final_image /\
 lookup_entry runtime_kind final_image (argument_key i)=Some b.
Proof.
 intros RUN IMAGE UNIQUE SAME.
 pose proof (owned_success_slots _ _ _ _ _ _ _ _ _ _ _ RUN IMAGE) as SLOTS.
 pose proof (owned_run_keys _ _ _ _ _ _ _ _ _ _ _ RUN) as KEYS.
 inversion KEYS as [|aa aa_tail KA REST];subst.
 inversion REST as [|bb bb_tail KB NIL];subst.
 exists (apply_attachments [OwnedAttachment i slotA a;OwnedAttachment k slotB b] image).
 split.
 - rewrite (owned_success_exact_image _ _ _ _ _ _ _ _ _ _ RUN) IMAGE;reflexivity.
 - apply owned_repeated_tag_last;[exact UNIQUE|exact SAME|exact KA|exact KB|exact (proj1 SLOTS)|exact (proj1 (proj2 SLOTS))].
Qed.

Definition live_body_progress pc (todo:list nat) := match pc with
 | BodyInterrupted=>None | _=>Some (pc,todo) end.
Lemma body_reset_has_no_live_progress todo : live_body_progress BodyInterrupted todo=None.
Proof. reflexivity. Qed.

Theorem owned_prepared_rejection pc selected vi oi x prefix valid view j image root s e i todo p :
 owned_body_run pc selected vi oi x prefix BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 data_slot_for runtime_kind image (argument_key i)=None ->
 owned_body_run pc selected vi oi x prefix BodyFailed (i::todo) valid view
   ((j,OperationBoundary image root s),body_error_evidence e).
Proof.
 intros PREFIX P KIND WRITTEN SLOT.
 rewrite -(app_nil_r prefix).
 eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[eapply body_attach_rejected;try eassumption;apply missing_attachment_slot;exact SLOT|apply body_nil].
Qed.


(* The request changes only the sticky bit; storage and progress are shared. *)
Definition owned_control_sticky before after :=
 after=before \/ after=control_abort before.
Lemma owned_control_sticky_refl c : owned_control_sticky c c.
Proof. left;reflexivity. Qed.
Lemma owned_control_sticky_trans a b c :
 owned_control_sticky a b -> owned_control_sticky b c -> owned_control_sticky a c.
Proof.
 intros [B|B] [C|C];subst;try (left;reflexivity);try (right;reflexivity).
Qed.
Lemma owned_control_sticky_bit a b :
 owned_control_sticky a b -> abort_requested a=true -> abort_requested b=true.
Proof. intros [E|E] AB;rewrite E;[exact AB|reflexivity]. Qed.
Lemma owned_control_sticky_shape ab before after :
 owned_control_sticky before after -> before=Control ab true true true true None None ->
 after=Control (abort_requested after) true true true true None None.
Proof. intros [E|E] C;rewrite E C;reflexivity. Qed.

Lemma owned_edge_control pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted ->
 owned_control_sticky (controller_read (snd x)) (controller_read (snd y)).
Proof.
 intro RUN;destruct RUN;intros NF NI;try (apply owned_control_sticky_refl);try contradiction.
 - unfold acquisition_pc in NF,NI;destruct (neutral_end_ result) eqn:END;try contradiction.
   unfold operation_acquisition_boundary,recycling_acquisition_boundary;rewrite END;left;reflexivity.
 - unfold preparation_pc in NF,NI;destruct (writer_end result) eqn:END;try contradiction.
   unfold operation_writer_exit,writer_exit_boundary;rewrite END;left;reflexivity.
 - right;reflexivity.
Qed.
Lemma owned_success_control pc todo vi oi x log tail vf of_ y :
 owned_body_run pc todo vi oi x log BodyFinished tail vf of_ y ->
 owned_control_sticky (controller_read (snd x)) (controller_read (snd y)).
Proof.
 intro RUN;remember BodyFinished as last eqn:E;induction RUN;[left;reflexivity|].
 subst last. destruct (owned_success_not_failed _ _ _ _ _ _ _ _ _ _ RUN) as [NF NI].
 eapply owned_control_sticky_trans;[eapply owned_edge_control;eauto|apply IHRUN;reflexivity].
Qed.

Theorem owned_controller_body_accept valid view j old d s e count same compare i remaining word_max
 log tail vf of_ j' image root s' e' :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 owned_body_run BodyWaiting (i::remaining) valid view
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((j',OperationBoundary image root s'),e') ->
 let accepted:=data_next (DataClose [physical_authority s'] (physical_authority s') true) s' in
 let taken:=controller_evidence (TakeLocal true) (OperationBoundary image root s') e' in
 let closed:=controller_evidence LocalClosed (OpenBoundary image root accepted) taken in
 map attachment_argument log=i::remaining /\
 image=apply_attachments log (recovered_image d) /\
 attachment_checks (recovered_image d) log /\
 Trace valid view ((j,IdleBoundary old d s),e) [] vf of_ ((j',OpenBoundary image root accepted),closed) /\
 Safe vf of_ ((j',OpenBoundary image root accepted),closed) /\
 phase_numeric word_max marker ranges (OpenBoundary image root accepted) /\
 local_live (controller_read closed)=false /\ local_taken (controller_read closed)=None /\
 collection_enabled true None None accepted=false.
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN accepted taken closed.
 destruct (owned_pair_entry_dispatch valid view j old d s e count same compare (PairSelected (i::remaining))
   word_max MARK DEC WORD GEO INIT OUT ARM PREPASS) as [_ [first [rest [_ [OPEN [SAFEOPEN [NUMOPEN CTRLOPEN]]]]]]].
 assert (PREFIX:Trace valid view ((j,IdleBoundary old d s),e) [] vf of_
   ((j',OperationBoundary image root s'),e')).
 { eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact RUN]. }
 pose proof (owned_success_control _ _ _ _ _ _ _ _ _ _ RUN) as CTRL.
 pose proof (owned_control_sticky_shape _ _ _ CTRL CTRLOPEN) as SHAPE.
 clear CTRL;rename SHAPE into CTRL.
 assert (TAKE:Trace valid view ((j,IdleBoundary old d s),e) [] vf of_
   ((j',OperationBoundary image root s'),taken)).
 { apply controller_from_trace;[exact PREFIX|cbn;rewrite CTRL;split;reflexivity || exact I]. }
 assert (TOKEN:pending_preparation s'=None).
 { exact (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ RUN eq_refl). }
 destruct (operation_accept_from_trace _ _ _ _ _ _ _ _ _ _ _ INIT I TAKE TOKEN)
   as [ACCEPTED [SAFE NOCOLLECT]].
 assert (CLOSE:Trace valid view ((j,IdleBoundary old d s),e) [] vf of_
   ((j',OpenBoundary image root accepted),closed)).
 { apply controller_from_trace;[exact ACCEPTED|].
   change (local_taken (control_take_local true (controller_read e'))<>None /\ True).
   rewrite CTRL;split;[discriminate|exact I]. }
 destruct (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN) as [ORDER EMPTY].
 pose proof (owned_success_exact_image _ _ _ _ _ _ _ _ _ _ RUN) as IMAGE.
 change (Some image=Some (apply_attachments log (recovered_image d))) in IMAGE.
 assert (IMGEQ:image=apply_attachments log (recovered_image d)) by congruence.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view j old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT NUM CLOSE) as [ENDSAFE ENDNUM].
 split;[exact ORDER|]. split;[congruence|]. split;[eapply owned_success_slots;[exact RUN|reflexivity]|].
 split;[exact CLOSE|]. split;[exact ENDSAFE|]. split;[exact ENDNUM|].
 split;[reflexivity|]. split;[reflexivity|exact NOCOLLECT].
Qed.


Lemma owned_edge_history pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 publications (boundary_journal y)=publications (boundary_journal x) /\
 boundary_receipts y=boundary_receipts x.
Proof.
 intro RUN;destruct RUN;try (split;reflexivity).
 - destruct fatal;split;reflexivity.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);split;reflexivity.
 - unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);split;reflexivity.
Qed.
Theorem owned_body_history pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_run pc todo vi oi x log pc' todo' vf of_ y ->
 publications (boundary_journal y)=publications (boundary_journal x) /\
 boundary_receipts y=boundary_receipts x.
Proof.
 intro RUN;induction RUN;[split;reflexivity|].
 destruct (owned_edge_history _ _ _ _ _ _ _ _ _ _ _ H) as [HIST OBS].
 destruct IHRUN as [HIST' OBS'];split;congruence.
Qed.


Theorem owned_recycled_writer_prefix vi oi initial events valid view f h a old image root s e i todo
 recognize magic fuel req round alignment start r count recycled plan result word_max :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 runtime_search_inputs sector pages word_max e s f req start ->
 neutral_end_ recycled=NeutralSuccess ->
 writer_execution g sector (block_pages (recycle_lo r) (useful_pages r)) false (neutral_flash recycled) plan result ->
 plan=argument_plan i (block_pages (recycle_lo r) (useful_pages r)) ->
 exists previous previous',
 let reserved:=reservation_state false (block_pages (recycle_lo r) (useful_pages r)) s in
 owned_body_run BodyWaiting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   (preparation_pc (writer_end result)) (i::todo) (validate (writer_flash result)) view
   (operation_writer_exit old image root reserved h a result,
    phase_evidence (snd (operation_writer_exit old image root reserved h a result))
      (selected_evidence old previous' (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)))).
Proof.
 intros INIT RAW PREFIX HEAD P LOCAL SEARCH GEO REC INPUTS OK WRITE PLAN.
 destruct (owned_recycled_acquisition_prefix vi oi initial events valid view f h a old image root s e i todo
   recognize magic fuel req round alignment start r count recycled word_max INIT RAW PREFIX HEAD P LOCAL SEARCH GEO REC INPUTS)
   as [previous [ACQUIRED [PATH HANDOFF]]].
 unfold recycling_cursor_evidence,operation_acquisition_boundary,recycling_acquisition_boundary in ACQUIRED,PATH;
 rewrite OK in ACQUIRED,PATH;cbn [operation_phase fst snd] in ACQUIRED,PATH.
 change (owned_body_run BodyWaiting (i::todo) valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) []
   BodyWriting (i::todo) (validate (neutral_flash recycled)) view
   ((Logged (Ready (neutral_flash recycled)) h a,OperationBoundary image root
     (reservation_state false (block_pages (recycle_lo r) (useful_pages r)) s)),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in ACQUIRED.
 change (Trace vi oi initial events (validate (neutral_flash recycled)) view
   ((Logged (Ready (neutral_flash recycled)) h a,OperationBoundary image root
     (reservation_state false (block_pages (recycle_lo r) (useful_pages r)) s)),selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e))) in PATH.
 destruct (owned_pending_writer_prefix vi oi initial events (validate (neutral_flash recycled)) view
   (neutral_flash recycled) h a old image root _ (selected_evidence old previous (advance_allocation_evidence (block_pages (recycle_lo r) (useful_pages r)) e)) i todo
   (reservation_token false (block_pages (recycle_lo r) (useful_pages r))) plan result
   INIT RAW PATH HEAD (conj (HANDOFF OK) WRITE) eq_refl PLAN) as [previous' WRITTEN].
 exists previous,previous'. eapply owned_body_run_append with (log:=[]) (logs:=[]);eassumption.
Qed.


Lemma owned_nonfailed_origin pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted -> pc<>BodyFailed /\ pc<>BodyInterrupted.
Proof. intros RUN NF NI;inversion RUN;subst;[auto|inversion H;subst;split;discriminate]. Qed.
Lemma owned_live_control pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted ->
 owned_control_sticky (controller_read (snd x)) (controller_read (snd y)).
Proof.
 intro RUN;induction RUN;intros NF NI;[left;reflexivity|].
 destruct (owned_nonfailed_origin _ _ _ _ _ _ _ _ _ _ _ RUN NF NI) as [MF MI].
 eapply owned_control_sticky_trans;[eapply owned_edge_control;eauto|apply IHRUN;assumption].
Qed.

Theorem owned_numeric_refusal pc selected vi oi x prefix valid view f h a image root s e i todo ab :
 owned_body_run pc selected vi oi x prefix BodyAcquiring (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 body_no_token pc x -> controller_read (snd x)=Control ab true true true true None None ->
 operation_payload_rejection sector f h a image root s e ->
 owned_body_run pc selected vi oi x prefix BodyFailed (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e).
Proof.
 intros PREFIX TOKEN CTRL REJECT.
 pose proof (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ PREFIX TOKEN) as P.
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ PREFIX ltac:(discriminate) ltac:(discriminate)) as C.
 pose proof (owned_control_sticky_shape _ _ _ C CTRL) as SHAPE.
 clear C;rename SHAPE into C.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[|apply body_nil].
 apply body_numeric_refused;[exact P|exact REJECT|rewrite C;repeat split;reflexivity].
Qed.

Theorem owned_search_refusal pc selected vi oi x prefix valid view f h a image root s e i todo ab
 fuel recognize req round alignment start reply word_max :
 owned_body_run pc selected vi oi x prefix BodyAcquiring (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 body_no_token pc x -> controller_read (snd x)=Control ab true true true true None None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 runtime_search_inputs sector pages word_max e s f req start ->
 owned_body_run pc selected vi oi x prefix BodyFailed (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e).
Proof.
 intros PREFIX TOKEN CTRL SEARCH REJECT INPUTS.
 pose proof (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ PREFIX TOKEN) as P.
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ PREFIX ltac:(discriminate) ltac:(discriminate)) as C.
 pose proof (owned_control_sticky_shape _ _ _ C CTRL) as SHAPE.
 clear C;rename SHAPE into C.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[|apply body_nil].
 eapply body_search_refused;[exact P|exact SEARCH|exact REJECT|rewrite C;repeat split;reflexivity|exact INPUTS].
Qed.

Theorem owned_search_interruption pc selected vi oi x prefix valid view f h a image root s e i todo
 fuel shape verify req round alignment start target fatal word_max :
 owned_body_run pc selected vi oi x prefix BodyAcquiring (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 body_no_token pc x ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table s) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 runtime_search_inputs sector pages word_max e s f req start ->
 owned_body_run pc selected vi oi x prefix BodyInterrupted (i::todo) valid view
   (if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
    else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e)).
Proof.
 intros PREFIX TOKEN WALK STOP INPUTS.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[|apply body_nil].
 eapply body_search_stopped;[exact (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ PREFIX TOKEN)|exact WALK|exact STOP|exact INPUTS].
Qed.

Theorem owned_prepared_local_error pc selected vi oi x prefix valid view j image root s e i todo p :
 owned_body_run pc selected vi oi x prefix BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 prepared_local_rejection runtime_kind image (argument_key i) (prep_range p) ->
 owned_body_run pc selected vi oi x prefix BodyFailed (i::todo) valid view
   ((j,OperationBoundary image root s),body_error_evidence e).
Proof.
 intros PREFIX P KIND WRITTEN REJECT.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[eapply body_attach_rejected;eauto|apply body_nil].
Qed.

(* Both positions share this consumer; the queue head i is obtained from the
   actual marked run. Cleanup is the old checked release/rollback consumer. *)
(* This is the controller guard used in the error route, not a claim that an
   arbitrary later operation can never select a finalization. *)
Lemma body_error_cannot_select_finish phase c :
 body_error_pending c=true -> ~controller_caller SelectFinish phase c.
Proof. intros ERROR CALL;unfold controller_caller in CALL.
 destruct CALL as [_ [_ [_ [_ [_ LAST]]]]].
 destruct phase;try contradiction;congruence.
Qed.


Theorem owned_marked_prepared_error_return valid view f h a old d s e count same compare first selected word_max
 log v' o' f' h' a' image root s' e' i todo p read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyPrepared (i::todo) v' o' ((Logged (Ready f') h' a',OperationBoundary image root s'),e') ->
 pending_preparation s'=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 prepared_local_rejection runtime_kind image (argument_key i) (prep_range p) ->
 ((root=[boss_extent (o' old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (o' old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges o' marker (Some old) (object_extents (o' old)) []) ->
 (first::selected)=map attachment_argument log++i::todo /\
 ~controller_caller SelectFinish (OperationBoundary image root s') (control_body_error (controller_read e')) /\
 range_check true word_max (prep_range p)=None /\
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o' destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o' destination /\
 publications (boundary_journal destination)=h'.
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN P KIND WRITTEN REJECT RESTORE MASK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e count same compare
   (PairSelected (first::selected)) word_max MARK DEC WORD GEO INIT OUT ARM PREPASS)
   as [_ [k [rest [_ [OPEN [SAFE [NUM CTRL]]]]]]].
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(discriminate) ltac:(discriminate)) as C.
 pose proof (owned_control_sticky_shape _ _ _ C CTRL) as SHAPE.
 clear C;rename SHAPE into C.
 assert (PATH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o'
   ((Logged (Ready f') h' a',OperationBoundary image root s'),e')).
 { eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact RUN]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 split;[eapply owned_body_run_order;exact RUN|].
 split;[apply body_error_cannot_select_finish;reflexivity|].
 eapply prepared_rejection_return_from_trace;try eassumption;exact I.
Qed.


Definition compact_entry_dec (a b:compact_entry) : {a=b}+{a<>b}.
Proof. repeat decide equality. Defined.
Definition entry_identical image index entry := match nth_error image index with
 | Some (Some old)=>match compact_entry_dec old entry with left _=>true | right _=>false end
 | _=>false end.
Lemma entry_identical_spec image index entry :
 entry_identical image index entry=true <-> nth_error image index=Some (Some entry).
Proof.
 unfold entry_identical;destruct (nth_error image index) as [[old|]|] eqn:SLOT;
 try (split;discriminate).
 destruct (compact_entry_dec old entry) as [EQ|NE];[subst old;tauto|split;[discriminate|intro EQ;inversion EQ;contradiction]].
Qed.
Definition checked_attachment_boundary (j:logged_state) image root s (e:boundary_evidence) index entry : execution_boundary :=
 if entry_identical image index entry then
   ((j,OperationBoundary image root (identical_attach_state s)),e)
 else ((j,OperationBoundary (image_replace image index (Some entry)) []
   (exact_attach ranges image index entry (data_next DataWritten s))),e).

Theorem owned_attach_dispatch pc selected vi oi x prefix valid view j image root s e i todo p index entry :
 owned_body_run pc selected vi oi x prefix BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 owned_body_run pc selected vi oi x (prefix++[OwnedAttachment i index entry]) BodyWaiting todo valid view
   (checked_attachment_boundary j image root s e index entry).
Proof.
 intros PREFIX P KIND WRITTEN RANGE KEY SLOT.
 eapply owned_body_run_append;[exact PREFIX|].
 unfold checked_attachment_boundary;destruct (entry_identical image index entry) eqn:SAME.
 - eapply body_cons with (log:=[OwnedAttachment i index entry]) (logs:=[]);[|apply body_nil].
   eapply body_identical;try eassumption;apply entry_identical_spec;exact SAME.
 - eapply body_cons with (log:=[OwnedAttachment i index entry]) (logs:=[]);[|apply body_nil].
   eapply body_attached;try eassumption.
   intro EQ;apply entry_identical_spec in EQ;congruence.
Qed.

Theorem owned_single_checked vi oi x valid view j image root s e i p index entry :
 owned_body_run BodyWaiting [i] vi oi x [] BodyPrepared [i] valid view ((j,OperationBoundary image root s),e) ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 owned_body_run BodyWaiting [i] vi oi x [OwnedAttachment i index entry] BodyFinished [] valid view
   (checked_attachment_boundary j image root s e index entry).
Proof.
 intros PREFIX P KIND WRITTEN RANGE KEY SLOT.
 eapply owned_body_run_append with (log:=[OwnedAttachment i index entry]) (logs:=[]).
 - exact (owned_attach_dispatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PREFIX P KIND WRITTEN RANGE KEY SLOT).
 - apply owned_empty_body.
Qed.


Theorem owned_two_checked vi oi x va oa ja imageA rootA sA eA i k pA slotA entryA
 vb ob jb imageB rootB sB eB pB slotB entryB :
 owned_body_run BodyWaiting [i;k] vi oi x [] BodyPrepared [i;k] va oa ((ja,OperationBoundary imageA rootA sA),eA) ->
 pending_preparation sA=Some pA -> prep_kind pA=ObjectPreparation -> prep_phase pA=Written ->
 ranges entryA=[prep_range pA] -> entry_key runtime_kind entryA=argument_key i ->
 data_slot_for runtime_kind imageA (argument_key i)=Some slotA ->
 owned_body_run BodyWaiting [k] va oa
   (checked_attachment_boundary ja imageA rootA sA eA slotA entryA) []
   BodyPrepared [k] vb ob ((jb,OperationBoundary imageB rootB sB),eB) ->
 pending_preparation sB=Some pB -> prep_kind pB=ObjectPreparation -> prep_phase pB=Written ->
 ranges entryB=[prep_range pB] -> entry_key runtime_kind entryB=argument_key k ->
 data_slot_for runtime_kind imageB (argument_key k)=Some slotB ->
 owned_body_run BodyWaiting [i;k] vi oi x
   [OwnedAttachment i slotA entryA;OwnedAttachment k slotB entryB] BodyFinished [] vb ob
   (checked_attachment_boundary jb imageB rootB sB eB slotB entryB).
Proof.
 intros FIRST PA KA WA RA EA SA SECOND PB KB WB RB EB SB.
 eapply owned_body_run_append with (log:=[OwnedAttachment i slotA entryA])
   (logs:=[OwnedAttachment k slotB entryB]).
 - exact (owned_attach_dispatch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FIRST PA KA WA RA EA SA).
 - eapply owned_single_checked;eauto.
Qed.

Theorem identical_attachment_effect valid view j image root s e i todo p index entry :
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 ranges entry=[prep_range p] -> entry_key runtime_kind entry=argument_key i ->
 data_slot_for runtime_kind image (argument_key i)=Some index ->
 nth_error image index=Some (Some entry) ->
 owned_body_edge BodyPrepared (i::todo) valid view ((j,OperationBoundary image root s),e)
   [OwnedAttachment i index entry] BodyWaiting todo valid view
   ((j,OperationBoundary image root (identical_attach_state s)),e) /\
 protection_table (identical_attach_state s)=protection_table s /\
 protection_dirty (identical_attach_state s)=protection_dirty s /\
 protection_frozen (identical_attach_state s)=protection_frozen s /\
 pending_preparation (identical_attach_state s)=None.
Proof. intros P KIND WRITTEN RANGE KEY SLOT SAME;split;[eapply body_identical;eauto|repeat split;reflexivity]. Qed.

(* This demonstrates why no positivity exclusion was inferred from the generic
   admission interface. It is NOT a trace of the Rust Data length formatter. *)
Example abstract_zero_probe area_len table f :
 cursor_probe sector area_len (fun _=>Some 0) 0 table f=Some {| offset:=0;span:=0 |}.
Proof. reflexivity. Qed.


Lemma owned_edge_roots pc todo vi oi x log pc' todo' vf of_ y :
 owned_body_edge pc todo vi oi x log pc' todo' vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted ->
 active_snapshot_roots (snd (fst y)) (snd y)=active_snapshot_roots (snd (fst x)) (snd x).
Proof.
 intro RUN;destruct RUN;intros NF NI;try reflexivity;try contradiction.
 - unfold acquisition_pc in NF,NI;destruct (neutral_end_ result) eqn:END;try contradiction.
   unfold operation_acquisition_boundary,recycling_acquisition_boundary;rewrite END;reflexivity.
 - unfold preparation_pc in NF,NI;destruct (writer_end result) eqn:END;try contradiction.
   destruct H2 as [[P BLANK] WRITE].
   unfold operation_writer_exit,writer_exit_boundary;rewrite END.
   unfold active_snapshot_roots,snapshot_written;rewrite P;reflexivity.
 - unfold active_snapshot_roots,exact_attach,data_next;rewrite H;reflexivity.
Qed.
Theorem owned_live_roots pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 pc'<>BodyFailed -> pc'<>BodyInterrupted ->
 active_snapshot_roots (snd (fst y)) (snd y)=active_snapshot_roots (snd (fst x)) (snd x).
Proof.
 intro RUN;induction RUN;intros NF NI;[reflexivity|].
 destruct (owned_nonfailed_origin _ _ _ _ _ _ _ _ _ _ _ RUN NF NI) as [MF MI].
 rewrite (IHRUN NF NI);eapply owned_edge_roots;eauto.
Qed.
Theorem owned_marked_before_change valid view j old d s e selected log pc todo vf of_ j' image root ram e' :
 Safe valid view ((j,IdleBoundary old d s),e) ->
 owned_body_run BodyWaiting selected valid view
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log pc todo vf of_ ((j',OperationBoundary image root ram),e') ->
 pc<>BodyFailed -> pc<>BodyInterrupted ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((j',OperationBoundary image root ram),e') false ((j',OperationBoundary image root ram),e').
Proof.
 intros INIT RUN NF NI.
 pose proof (owned_live_roots _ _ _ _ _ _ _ _ _ _ _ RUN NF NI) as ROOTS.
 change (active_snapshot_roots (OperationBoundary image root ram) e'=
   active_snapshot_roots (OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s))
     (owned_local_evidence old d s e)) in ROOTS.
 rewrite (proj1 (owned_open_roots_correspondence valid view j old d s e INIT)) in ROOTS.
 exact (before_change_probe_known _ _ _ _ _ _ ROOTS).
Qed.


Inductive owned_local_refusal e f s : Prop :=
| owned_payload_refused : local_admission_rejection sector s f ->
 owned_local_refusal e f s
| owned_search_refused fuel recognize req round alignment start reply word_max :
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 runtime_search_inputs sector pages word_max e s f req start -> owned_local_refusal e f s.

Theorem owned_marked_local_error_return valid view f h a old d s e count same compare first selected word_max
 log v' o' f' h' a' image root s' e' i todo read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyAcquiring (i::todo) v' o' ((Logged (Ready f') h' a',OperationBoundary image root s'),e') ->
 owned_local_refusal e' f' s' ->
 ((root=[boss_extent (o' old)] /\ outcome=RestoreValidated) \/
  (root<>[boss_extent (o' old)] /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
    (restore_contract read inspect check) restore_probe) tt outcome tt)) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges o' marker (Some old) (object_extents (o' old)) []) ->
 (first::selected)=map attachment_argument log++i::todo /\
 ~controller_caller SelectFinish (OperationBoundary image root s') (control_body_error (controller_read e')) /\
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o' destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o' destination /\
 publications (boundary_journal destination)=h' /\
 control_image (journal_control (boundary_journal destination))=f'.
Proof.
 intros MARK DEC WORD GEO INIT META OUT ARM PREPASS RUN REJECT RESTORE MASK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e count same compare
   (PairSelected (first::selected)) word_max MARK DEC WORD GEO INIT OUT ARM PREPASS)
   as [_ [k [rest [_ [OPEN [SAFE [NUM CTRL]]]]]]].
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(discriminate) ltac:(discriminate)) as C.
 pose proof (owned_control_sticky_shape _ _ _ C CTRL) as SHAPE.
 clear C;rename SHAPE into C.
 pose proof (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ RUN eq_refl) as P.
 assert (FAILED:owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFailed (i::todo) v' o' ((Logged (Ready f') h' a',OperationBoundary image root s'),body_error_evidence e')).
 { destruct REJECT.

   - eapply owned_numeric_refusal;[exact RUN|reflexivity|exact CTRL|].
     apply payload_rejection_controlled.
     + change (page_metadata_coherent ((Logged (Ready f') h' a',OperationBoundary image root s'),e')).
       eapply episode_trace_pages;[exact META|].
       eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact RUN].
     + eapply owned_marked_before_change;[exact INIT|exact RUN|discriminate|discriminate].
     + apply local_admission_error_classified;exact H.
   - eapply owned_search_refusal;[exact RUN|reflexivity|exact CTRL|exact H|exact H0|exact H1]. }
 assert (PATH:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] v' o'
   ((Logged (Ready f') h' a',OperationBoundary image root s'),body_error_evidence e')).
 { eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact FAILED]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 split;[eapply owned_body_run_order;exact RUN|].
 split;[apply body_error_cannot_select_finish;reflexivity|].
 eapply body_error_finish_from_trace_flash with (ab:=abort_requested (controller_read e'));try eassumption;try exact I.
 change (control_body_error (controller_read e')=FullControl (abort_requested (controller_read e')) true true true true None None true).
 rewrite C;reflexivity.
Qed.



(* The success gate consumes the marked body, not an arbitrary A11 prefix.
   No prepared BOSS or final invariant occurs in this interface. *)
Theorem owned_marked_success_finish valid view f h a old d s e count same compare i remaining word_max
 log tail vf of_ f' h' a' image root s' e' resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 owned_body_run BodyWaiting (i::remaining) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((Logged (Ready f') h' a',OperationBoundary image root s'),e') ->
 (forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []) ->
 let accepted:=data_next (DataClose [physical_authority s'] (physical_authority s') true) s' in
 let taken:=controller_evidence (TakeLocal true) (OperationBoundary image root s') e' in
 let closed:=controller_evidence LocalClosed (OpenBoundary image root accepted) taken in
 let selected:=controller_evidence SelectFinish (OpenBoundary image root accepted) closed in
 map attachment_argument log=i::remaining /\
 image=apply_attachments log (recovered_image d) /\
 (if abort_requested (controller_read e') then
    exists destination exit,
     (exit=ReturnedOrdinary FinishAbort \/ exit=InterruptedFatal) /\
     completed_operation g sector data_len marker ranges decode topology pages valid view
       ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination exit /\
     controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
     publications (boundary_journal destination)=h'
  else if phase_dirty (OpenBoundary image root accepted) then
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
     ((Logged (Ready f') h' a',OpenBoundary image root accepted),selected) /\
   Safe vf of_ ((Logged (Ready f') h' a',OpenBoundary image root accepted),selected) /\
   phase_numeric word_max marker ranges (OpenBoundary image root accepted) /\
   root=[] /\ pending_preparation accepted=None /\
   finish_selected (controller_read selected)=Some FinishPublish /\
   owner_armed (controller_read selected)=true /\
   outer_live (controller_read selected)=true /\
   (forall r,free_range 256 (protection_table accepted) r ->
      snapshot_api_caller accepted unit (SnapshotReserve r)) /\
   unchanged [marker] (object_flash sector f) (object_flash sector f') /\
   active_snapshot_roots (OpenBoundary image root accepted) selected=Some [Some old]
  else exists destination exit,
   (exit=ReturnedOrdinary FinishClean \/ exit=InterruptedFatal) /\
   completed_operation g sector data_len marker ranges decode topology pages valid view
     ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination exit /\
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
   publications (boundary_journal destination)=h').
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN MASK accepted taken closed selected.
 destruct (owned_controller_body_accept valid view (Logged (Ready f) h a) old d s e
   count same compare i remaining word_max log tail vf of_ (Logged (Ready f') h' a') image root s' e'
   MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [ORDER [IMAGE [CHECKS [CLOSE [SAFE [NUM [LOCAL [TAKEN NOCOLLECT]]]]]]]].
 pose proof (owned_success_control _ _ _ _ _ _ _ _ _ _ RUN) as CTRL.
 pose proof (owned_control_sticky_shape false _ _ CTRL eq_refl) as SHAPE.
 clear CTRL;rename SHAPE into CTRL.
 assert (CC:controller_read closed=Control (abort_requested (controller_read e')) true true true false None None).
 { unfold closed,taken;change (control_close_local (control_take_local true (controller_read e'))=
      Control (abort_requested (controller_read e')) true true true false None None).
   rewrite CTRL;reflexivity. }
 assert (CALL:controller_caller SelectFinish (OpenBoundary image root accepted) (controller_read closed)).
 { rewrite CC;repeat split;reflexivity. }
 assert (P:pending_preparation accepted=None).
 { pose proof (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ RUN eq_refl) as EMPTY.
   reflexivity. }
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 split;[exact ORDER|]. split;[exact IMAGE|].
 destruct (abort_requested (controller_read e')) eqn:ABORT.
 - eapply (controlled_abort_from_trace valid view _ [] vf of_ f' h' a' image root accepted closed old resolved word_max);
     try eassumption;try exact I;try reflexivity;rewrite CC ?ABORT;repeat split;reflexivity.
 - destruct (phase_dirty (OpenBoundary image root accepted)) eqn:DIRTY.
 + destruct (controlled_dispatch_from_trace valid view _ [] vf of_ (Logged (Ready f') h' a')
     image root accepted closed CLOSE CALL) as [SELECT CHOSEN].
   split;[exact SELECT|]. split.
   * exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ INIT SELECT)).
   * split;[exact NUM|]. split;[destruct root;[reflexivity|discriminate]|].
     split;[exact P|]. split.
     -- change (Some (choose_finish (controller_read closed) (phase_dirty (OpenBoundary image root accepted)))=Some FinishPublish).
       rewrite CC ?ABORT ?DIRTY;reflexivity.
     -- split;[change (owner_armed (controller_read closed)=true);rewrite CC;reflexivity|].
        split;[change (outer_live (controller_read closed)=true);rewrite CC;reflexivity|].
        split.
        ** intros r FREE;split;[exact (proj1 (proj2 (proj2 (proj1 SAFE))))|]. split;assumption.
        ** split.
           2: { apply accepted_outer_root.
                pose proof (owned_live_roots _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(discriminate) ltac:(discriminate)) as ROOTS.
                rewrite ROOTS;exact (proj1 (owned_open_roots_correspondence valid view (Logged (Ready f) h a) old d s e INIT)). }
           destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e
             count same compare (PairSelected (i::remaining)) word_max
             MARK DEC WORD GEO INIT OUT ARM PREPASS)
             as [_ [first [rest [_ [OPEN [SAFEOPEN OTHER]]]]]].
           exact (owned_body_run_marker _ _ _ _ _ _ _ _ _ _ _ SAFEOPEN
             (episode_trace_external_structure g sector data_len marker ranges decode topology pages
              G DIV _ _ _ _ _ _ _ INIT I OPEN) RUN).
 + eapply (controlled_clean_from_trace valid view _ [] vf of_ f' h' a' image root accepted closed old resolved
     word_max unit unit unit tt tt [] 0 0 0 0);try eassumption;try exact I.
Qed.

Corollary marked_success_gate_no_skip i remaining vi oi x tail vf of_ y :
 ~owned_body_run BodyWaiting (i::remaining) vi oi x [] BodyFinished tail vf of_ y.
Proof. apply owned_body_no_skipped_member. Qed.


(* Explicit operational RequestAbort after the marked body, before consuming
   its local handle. It is not a supplied choice of FinishAbort. *)
Theorem owned_marked_abort_finish valid view f h a old d s e count same compare i remaining word_max
 log tail vf of_ f' h' a' image root s' e' resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 owned_body_run BodyWaiting (i::remaining) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((Logged (Ready f') h' a',OperationBoundary image root s'),e') ->
 (forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []) ->
 map attachment_argument log=i::remaining /\
 exists destination exit,
 (exit=ReturnedOrdinary FinishAbort \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
 publications (boundary_journal destination)=h'.
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN MASK.
 destruct (owned_pair_entry_dispatch valid view (Logged (Ready f) h a) old d s e count same compare
   (PairSelected (i::remaining)) word_max MARK DEC WORD GEO INIT OUT ARM PREPASS)
   as [_ [k [rest [_ [OPEN [SAFEOPEN [NUMOPEN CTRLOPEN]]]]]]].
 assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',OperationBoundary image root s'),e')).
 { eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact RUN]. }
 pose proof (owned_success_control _ _ _ _ _ _ _ _ _ _ RUN) as CTRL.
 pose proof (owned_control_sticky_shape _ _ _ CTRL CTRLOPEN) as SHAPE.
 clear CTRL;rename SHAPE into CTRL.
 set (requested:=controller_evidence RequestAbort (OperationBoundary image root s') e').
 assert (REQ:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',OperationBoundary image root s'),requested)).
 { apply controller_from_trace;[exact PREFIX|cbn;rewrite CTRL;reflexivity]. }
 set (taken:=controller_evidence (TakeLocal true) (OperationBoundary image root s') requested).
 assert (TAKE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',OperationBoundary image root s'),taken)).
 { apply controller_from_trace;[exact REQ|].
   change (local_live (control_abort (controller_read e'))=true /\ True);rewrite CTRL;split;reflexivity || exact I. }
 assert (P:pending_preparation s'=None) by exact (owned_run_no_token _ _ _ _ _ _ _ _ _ _ _ RUN eq_refl).
 destruct (operation_accept_from_trace _ _ _ _ _ _ _ _ _ _ _ INIT I TAKE P) as [CLOSE REST].
 set (accepted:=data_next (DataClose [physical_authority s'] (physical_authority s') true) s').
 set (closed:=controller_evidence LocalClosed (OpenBoundary image root accepted) taken).
 assert (CLOSED:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',OpenBoundary image root accepted),closed)).
 { apply controller_from_trace;[exact CLOSE|split;[discriminate|exact I]]. }
 assert (CC:controller_read closed=Control true true true true false None None).
 { change (control_close_local (control_take_local true (control_abort (controller_read e')))=Control true true true true false None None).
   rewrite CTRL;reflexivity. }
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 split;[exact (proj1 (owned_body_success_order _ _ _ _ _ _ _ _ _ RUN))|].
 eapply (controlled_abort_from_trace valid view _ [] vf of_ f' h' a' image root accepted closed old resolved word_max);
 try eassumption;try exact I;try reflexivity;rewrite CC;repeat split;reflexivity.
Qed.


Definition owned_interrupted_boundary (x:execution_boundary) :=
 match snd (fst x) with FatalBoundary | RebuildingBoundary _=>True | _=>False end.
Lemma owned_edge_interrupted pc todo vi oi x log pc' tail vf of_ y :
 owned_body_edge pc todo vi oi x log pc' tail vf of_ y ->
 pc'=BodyInterrupted -> owned_interrupted_boundary y.
Proof.
 intro RUN;destruct RUN;intro END;try discriminate;try exact I.
 - destruct fatal;exact I.
 - unfold acquisition_pc in END;destruct (neutral_end_ result) eqn:E;try discriminate;
   unfold owned_interrupted_boundary,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite E;exact I.
 - unfold preparation_pc in END;destruct (writer_end result) eqn:E;try discriminate;
   unfold owned_interrupted_boundary,operation_writer_exit,writer_exit_boundary;rewrite E;exact I.
Qed.
Theorem owned_interrupted_shape pc todo vi oi x log tail vf of_ y :
 owned_body_run pc todo vi oi x log BodyInterrupted tail vf of_ y ->
 pc<>BodyInterrupted -> owned_interrupted_boundary y.
Proof.
 intro RUN;remember BodyInterrupted as last eqn:E;induction RUN;intro NE;[congruence|].
 subst last;destruct mid;try (apply IHRUN;auto;discriminate).
 inversion RUN;subst;[eapply owned_edge_interrupted;[exact H|reflexivity]|inversion H0].
Qed.


Theorem owned_marked_interruption_return valid view j old d s e count same compare i remaining word_max
 log tail vf of_ final :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 owned_body_run BodyWaiting (i::remaining) valid view
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyInterrupted tail vf of_ final ->
 exists exit,(exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((j,IdleBoundary old d s),e) [] vf of_ final exit /\
 controller_result_post word_max valid view ((j,IdleBoundary old d s),e) [] vf of_ final /\
 publications (boundary_journal final)=publications j /\
 boundary_receipts final=client_receipts e.
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN.
 destruct (owned_pair_entry_dispatch valid view j old d s e count same compare
   (PairSelected (i::remaining)) word_max MARK DEC WORD GEO INIT OUT ARM PREPASS)
   as [_ [k [rest [_ [OPEN OTHER]]]]].
 assert (PATH:Trace valid view ((j,IdleBoundary old d s),e) [] vf of_ final).
 { eapply episodes_append with (more:=[]);[exact OPEN|eapply owned_body_run_trace;exact RUN]. }
 pose proof (owned_interrupted_shape _ _ _ _ _ _ _ _ _ _ RUN ltac:(discriminate)) as SHAPE.
 pose proof (episode_trace_control g sector data_len marker ranges decode topology pages
   valid view ((j,IdleBoundary old d s),e) [] vf of_ final I PATH) as CONTROL.
 pose proof (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN) as HIST.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view j old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 assert (ENDING:exists exit,(exit=InterruptedFatal \/ exit=InterruptedReset) /\
   operation_execution g sector data_len marker ranges decode topology pages vf of_ final [] vf of_ final exit).
 { destruct final as [[jj ph] ev];destruct ph;try contradiction.
   - exists InterruptedReset;split;[right;reflexivity|apply operation_already_reset;exact CONTROL].
   - exists InterruptedFatal;split;[left;reflexivity|apply operation_already_fatal;exact CONTROL]. }
 destruct ENDING as [exit [KIND LAST]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
    valid view ((j,IdleBoundary old d s),e) [] vf of_ final exit).
 { exists vf,of_,final,[],[];repeat split;assumption || reflexivity. }
 exists exit;split;[exact KIND|]. split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - exact HIST.
Qed.


(* A Failed boundary carries the actual last failing command, not a caller
   selected cleanup. There is no outgoing body command from Failed. *)
Lemma owned_failed_no_edge todo vi oi x log pc' tail vf of_ y :
 ~owned_body_edge BodyFailed todo vi oi x log pc' tail vf of_ y.
Proof. intro EDGE;inversion EDGE. Qed.
Theorem owned_failed_last pc selected vi oi x log tail vf of_ y :
 owned_body_run pc selected vi oi x log BodyFailed tail vf of_ y ->
 pc<>BodyFailed ->
 exists before_pc before_todo vb ob before prefix,
 owned_body_run pc selected vi oi x prefix before_pc before_todo vb ob before /\
 owned_body_edge before_pc before_todo vb ob before [] BodyFailed tail vf of_ y /\
 log=prefix.
Proof.
 intro RUN;remember BodyFailed as last eqn:END;induction RUN;intro NOTFAILED;[congruence|].
 subst last;destruct mid.
 all: try (destruct (IHRUN eq_refl ltac:(discriminate)) as [bp [bt [bv [bo [b [pre [PREFIX [EDGE LOG]]]]]]]];
   exists bp,bt,bv,bo,b,(log++pre);split;[eapply body_cons;eassumption|];split;[exact EDGE|congruence]).
 inversion RUN;subst.
 - exists pc,todo,vi,oi,x,[];split;[constructor|].
   assert (EMPTY:log=[]) by (inversion H;reflexivity).
   subst log;split;[exact H|reflexivity].
 - exfalso;eapply owned_failed_no_edge;exact H0.
Qed.

Lemma writer_retain_requires_boss r boss f plan result :
 writer_execution g sector r boss f plan result ->
 writer_end result=WriterRetainError -> boss=true.
Proof. intro RUN;induction RUN;cbn;intro END;try discriminate;auto. Qed.
Lemma data_writer_failed_result s p f plan result :
 pending_writer_run g sector s p false f plan result ->
 preparation_pc (writer_end result)=BodyFailed ->
 writer_end result=WriterLocalError \/ writer_end result=WriterPhysicalError.
Proof.
 intros [[P BLANK] WRITE] FAILED.
 pose proof (writer_retain_requires_boss _ _ _ _ _ WRITE) as BOSS.
 destruct (writer_end result);cbn in FAILED;try discriminate;auto.
 exfalso;specialize (BOSS eq_refl);discriminate.
Qed.

Inductive owned_failure_site :=
 | FailurePayloadAdmission | FailureReusableSearch | FailureRecycling
 | FailureWriter | FailurePreparedCheck.

(* Classification of the actual failing edge. The witnesses retain the
   search/command execution and the reached flash from that constructor. *)
Definition owned_failure_at site before after : Prop :=
 match site with
 | FailurePayloadAdmission => exists f h a image root s e,
   before=((Logged (Ready f) h a,OperationBoundary image root s),e) /\
   after=((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e) /\
   pending_preparation s=None /\ operation_payload_rejection sector f h a image root s e
 | FailureReusableSearch => exists f h a image root s e fuel recognize req round alignment start reply,
   before=((Logged (Ready f) h a,OperationBoundary image root s),e) /\
   after=((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e) /\
   pending_preparation s=None /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply /\
   (reply=SearchMiss \/ reply=SearchError)
 | FailureRecycling => exists f h a old previous image root s e recognize magic fuel req round alignment start r count result,
   before=((Logged (Ready f) h a,OperationBoundary image root s),e) /\
   after=(operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)),
     phase_evidence (snd (operation_acquisition_boundary old image root s h a result
       (block_pages (recycle_lo r) (useful_pages r)))) (selected_evidence old previous e)) /\
   pending_preparation s=None /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r /\
   recycling_run g sector recognize magic r count f result /\ neutral_end_ result=NeutralError
 | FailureWriter => exists f h a old previous image root s e p plan result,
   before=((Logged (Ready f) h a,OperationBoundary image root s),e) /\
   after=(operation_writer_exit old image root s h a result,
     phase_evidence (snd (operation_writer_exit old image root s h a result)) (selected_evidence old previous e)) /\
   pending_writer_run g sector s p false f plan result /\
   (writer_end result=WriterLocalError \/ writer_end result=WriterPhysicalError)
 | FailurePreparedCheck => exists j image root s e p key,
   before=((j,OperationBoundary image root s),e) /\
   after=((j,OperationBoundary image root s),body_error_evidence e) /\
   pending_preparation s=Some p /\ prep_kind p=ObjectPreparation /\ prep_phase p=Written /\
   prepared_local_rejection runtime_kind image key (prep_range p)
 end.
Lemma owned_failed_edge_site pc todo vi oi x tail vf of_ y :
 owned_body_edge pc todo vi oi x [] BodyFailed tail vf of_ y ->
 exists site,owned_failure_at site x y.
Proof.
 intro EDGE;inversion EDGE;subst.
 - exists FailurePayloadAdmission;cbn;exists f,h,a,image,root,s,e;repeat split;assumption || reflexivity.
 - exists FailureReusableSearch;cbn;exists f,h,a,image,root,s,e,fuel,recognize,req,round,alignment,start,
   (reusable_search sector fuel recognize f (protection_table s) req round alignment pages start);repeat split;assumption || reflexivity.
 - assert (END:neutral_end_ result=NeutralError).
   { unfold acquisition_pc in *;destruct (neutral_end_ result);congruence. }
   exists FailureRecycling;cbn.
   exists f,h,a,old,previous,image,root,s,e,recognize,magic,fuel,req,round,alignment,start,r,count,result.
   unfold recycling_cursor_evidence;rewrite END.
   repeat split;assumption || reflexivity.
 - exists FailureWriter;unfold owned_failure_at.
   exists f,h,a,old,previous,image,root,s,e,p,(argument_plan i (prep_range p)),result.
   split;[reflexivity|]. split;[reflexivity|]. split;[assumption|eapply data_writer_failed_result;eassumption].
 - exists FailurePreparedCheck;cbn;exists j,image,root,s,e,p,(argument_key i);repeat split;assumption || reflexivity.
Qed.

Theorem owned_failed_provenance pc selected vi oi x log tail vf of_ y :
 owned_body_run pc selected vi oi x log BodyFailed tail vf of_ y -> pc<>BodyFailed ->
 exists before_pc before_todo vb ob before site,
 owned_body_run pc selected vi oi x log before_pc before_todo vb ob before /\
 owned_body_edge before_pc before_todo vb ob before [] BodyFailed tail vf of_ y /\
 owned_failure_at site before y.
Proof.
 intros RUN NE;destruct (owned_failed_last _ _ _ _ _ _ _ _ _ _ RUN NE)
   as [pc0 [todo0 [v0 [o0 [b [pre [PREFIX [EDGE EQ]]]]]]]].
 subst pre;destruct (owned_failed_edge_site _ _ _ _ _ _ _ _ _ EDGE) as [site CALL].
 exists pc0,todo0,v0,o0,b,site;auto.
Qed.


Definition owned_scope_context (x:execution_boundary) :=
 match snd (fst x) with
 | OperationBoundary _ _ s => operation_rollback_structure marker s
 | FrozenBoundary old candidate _ s =>
     operation_rollback_structure marker s /\ old=candidate /\ hd_error (publications (boundary_journal x))=Some old
 | _=>True end.
Lemma owned_edge_scope_context pc todo vi oi x log pc' tail vf of_ y :
 owned_body_edge pc todo vi oi x log pc' tail vf of_ y ->
 owned_scope_context x -> owned_scope_context y.
Proof.
 intro EDGE;destruct EDGE;intro CTX;try exact CTX;try exact I.
 - destruct fatal;exact I.
 - unfold owned_scope_context,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);try exact CTX;try exact I.
   split;[exact CTX|split;[reflexivity|assumption]].
 - unfold owned_scope_context,operation_writer_exit,writer_exit_boundary;
   destruct (writer_end result);try exact I;
   destruct H2 as [[P BLANK] WRITE];
   unfold snapshot_written,snapshot_error,snapshot_retain_error,
          operation_rollback_structure in *;
   rewrite ?P;try exact CTX.
   split;[exact CTX|split;[reflexivity|assumption]].
 - unfold owned_scope_context,operation_rollback_structure,exact_attach,data_next in *;
   rewrite H;exact CTX.
Qed.
Theorem owned_run_scope_context pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 owned_scope_context x -> owned_scope_context y.
Proof. intro RUN;induction RUN;intro CTX;[exact CTX|apply IHRUN;eapply owned_edge_scope_context;eauto]. Qed.



Definition owned_journal_ready pc (x:execution_boundary) :=
 match pc with BodyInterrupted=>True
 | _=>exists f,journal_control (boundary_journal x)=Ready f end.
Lemma owned_edge_ready pc todo vi oi x log pc' tail vf of_ y :
 owned_body_edge pc todo vi oi x log pc' tail vf of_ y ->
 owned_journal_ready pc x -> owned_journal_ready pc' y.
Proof.
 intro EDGE;destruct EDGE;intro READY;try exact READY;try exact I.
 - unfold owned_journal_ready,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,acquisition_pc;
   destruct (neutral_end_ result);try exact I;exists (neutral_flash result);reflexivity.
 - unfold owned_journal_ready,operation_writer_exit,writer_exit_boundary,preparation_pc;
   destruct (writer_end result);try exact I;exists (writer_flash result);reflexivity.
Qed.
Lemma owned_run_ready pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 owned_journal_ready pc x -> owned_journal_ready pc' y.
Proof. intro RUN;induction RUN;intro READY;[exact READY|apply IHRUN;eapply owned_edge_ready;eauto]. Qed.


Definition owned_error_ready ab (x:execution_boundary) :=
 controller_read (snd x)=FullControl ab true true true true None None true /\
 match snd (fst x) with
 | OperationBoundary _ _ s => pending_preparation s=None
 | FrozenBoundary _ _ (Some _) s => pending_preparation s=None /\ protection_frozen s=true
 | _=>False end.

Lemma owned_failed_edge_observe pc todo vi oi x tail vf of_ y ab :
 owned_body_edge pc todo vi oi x [] BodyFailed tail vf of_ y ->
 controller_read (snd x)=Control ab true true true true None None ->
 exists observed,
 Trace vf of_ y [] vf of_ observed /\ owned_error_ready ab observed /\
 boundary_journal observed=boundary_journal y /\
 owned_error_observation observed=owned_error_observation y /\
 (owned_scope_context y -> owned_scope_context observed).
Proof.
 intros EDGE CTRL;inversion EDGE;subst;cbn [snd] in CTRL.
 - eexists;split;[apply episodes_nil|]. split.
   + split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|exact H].
   + exact (conj eq_refl (conj eq_refl (fun H=>H))).
 - eexists;split;[apply episodes_nil|]. split.
   + split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|exact H].
   + exact (conj eq_refl (conj eq_refl (fun H=>H))).
 - assert (END:neutral_end_ result=NeutralError).
   { unfold acquisition_pc in *;destruct (neutral_end_ result);congruence. }
   set (kept:=selected_evidence old previous e).
   exists ((Logged (Ready (neutral_flash result)) h a,
     FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) (data_next DataFreeze s)),body_error_evidence kept).
   split.
   + assert (OBS:Step (validate (neutral_flash result)) of_
       (operation_acquisition_boundary old image root s h a result
         (block_pages (recycle_lo r) (useful_pages r)),kept) None
       (validate (neutral_flash result)) of_
       (operation_acquisition_boundary old image root s h a result
         (block_pages (recycle_lo r) (useful_pages r)),body_error_evidence kept)).
     { eapply operation_acquisition_error_observed with (f:=f) (recognize:=recognize)
         (magic:=magic) (r:=r) (count:=count);try eassumption.
       change (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\ outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None).
       rewrite CTRL;repeat split;reflexivity. }
     unfold recycling_cursor_evidence,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary in OBS |- *;rewrite END in OBS |- *.
     cbn [fst snd operation_phase phase_evidence] in *.
     eapply episodes_cons with (event:=None) (events:=[]);[exact OBS|constructor].
   + split.
     * split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|].
       split;[exact H4|reflexivity].
     * unfold recycling_cursor_evidence,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite END;exact (conj eq_refl (conj eq_refl (fun H=>H))).
 - assert (ERROR:writer_end result=WriterLocalError \/ writer_end result=WriterPhysicalError).
   { eapply data_writer_failed_result;eassumption. }
   match goal with W : pending_writer_run _ _ _ _ _ _ _ _ |- _ => destruct W as [[P BLANK] WRITE] end.
   set (kept:=selected_evidence old previous e).
   exists (operation_writer_exit old image root s h a result,
     phase_evidence (snd (operation_writer_exit old image root s h a result)) (body_error_evidence kept)).
   split.
   + eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
     assert (OBS:Step (validate (writer_flash result)) of_
       (operation_writer_exit old image root s h a result,kept) None (validate (writer_flash result)) of_
       (operation_writer_exit old image root s h a result,
         phase_evidence (snd (operation_writer_exit old image root s h a result)) (body_error_evidence kept))).
     { eapply operation_writer_error_observed;[exact P|exact WRITE|tauto|].
       change (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\ outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None).
       rewrite CTRL;repeat split;reflexivity. }
     destruct ERROR as [END|END];unfold operation_writer_exit,writer_exit_boundary in OBS |- *;rewrite END in OBS |- *;exact OBS.
   + destruct ERROR as [END|END];unfold operation_writer_exit,writer_exit_boundary;rewrite END;
     split;[split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|reflexivity]|
       exact (conj eq_refl (conj eq_refl (fun H=>H)))|split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|split;reflexivity]|
       exact (conj eq_refl (conj eq_refl (fun H=>H)))].
 - exists ((j,OperationBoundary image root (data_next DataDrop s)),body_error_evidence e).
   split.
   + eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
     eapply operation_rejected_token_drop;[exact H|reflexivity].
   + split;[split;[change (control_body_error (controller_read e)=FullControl ab true true true true None None true);rewrite CTRL;reflexivity|reflexivity]|].
     exact (conj eq_refl (conj eq_refl (fun H=>H))).
Qed.

Theorem owned_failed_observed pc selected vi oi x log tail vf of_ y ab :
 owned_body_run pc selected vi oi x log BodyFailed tail vf of_ y -> pc<>BodyFailed ->
 controller_read (snd x)=Control ab true true true true None None ->
 exists site before observed reached_abort,
 owned_failure_at site before y /\ Trace vi oi x [] vf of_ observed /\
 owned_error_ready reached_abort observed /\
 boundary_journal observed=boundary_journal y /\
 owned_error_observation observed=owned_error_observation y /\
 (owned_scope_context x -> owned_scope_context observed).
Proof.
 intros RUN NOTFAILED CTRL.
 destruct (owned_failed_provenance _ _ _ _ _ _ _ _ _ _ RUN NOTFAILED)
   as [bp [bt [bv [bo [before [site [PREFIX [EDGE SITE]]]]]]]].
 assert (NOTFAIL:bp<>BodyFailed) by (intro E;subst bp;eapply owned_failed_no_edge;exact EDGE).
 assert (NOTSTOP:bp<>BodyInterrupted) by (intro E;subst bp;inversion EDGE).
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ PREFIX NOTFAIL NOTSTOP) as CONTROL.
 pose proof (owned_control_sticky_shape _ _ _ CONTROL CTRL) as SHAPE.
 clear CONTROL;rename SHAPE into CONTROL.
 destruct (owned_failed_edge_observe _ _ _ _ _ _ _ _ _ (abort_requested (controller_read (snd before))) EDGE CONTROL)
   as [observed [SUFFIX [READY [HISTORY [FLASH CTX]]]]].
 exists site,before,observed,(abort_requested (controller_read (snd before)));split;[exact SITE|]. split.
 - eapply episodes_append with (more:=[]);[eapply owned_body_run_trace;exact RUN|exact SUFFIX].
 - split;[exact READY|]. split;[exact HISTORY|]. split;[exact FLASH|].
   intro S;apply CTX;eapply owned_run_scope_context;[exact RUN|exact S].
Qed.

(* The last failed edge determines token cleanup and the ordinary/frozen
   boundary. This consumes the executed prepass and the marked body, then the
   existing A11 numeric induction. It stops BEFORE restoration/delivery. *)
Theorem owned_marked_failed_boundary valid view j old d s e count same compare first selected
 word_max log tail vf of_ failed :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((j,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFailed tail vf of_ failed ->
 exists site before observed reached_abort,
 owned_failure_at site before failed /\
 Trace valid view ((j,IdleBoundary old d s),e) [] vf of_ observed /\
 Safe vf of_ observed /\ phase_numeric word_max marker ranges (snd (fst observed)) /\
 owned_error_ready reached_abort observed /\ owned_scope_context observed /\
 boundary_journal observed=boundary_journal failed /\
 owned_error_observation observed=owned_error_observation failed /\
 ~controller_caller SelectFinish (snd (fst observed)) (controller_read (snd observed)).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN.
 destruct (owned_pair_entry_dispatch valid view j old d s e count same compare
   (PairSelected (first::selected)) word_max MARK DEC WORD GEO INIT OUT ARM PREPASS)
   as [_ [k [rest [_ [OPEN [SAFEOPEN [NUMOPEN CTRL]]]]]]].
 destruct (owned_failed_observed _ _ _ _ _ _ _ _ _ _ false RUN ltac:(discriminate) CTRL)
   as [site [before [observed [reached_abort [SITE [SUFFIX [READY [JOURNAL [ROOT SCOPE]]]]]]]]].
 assert (PATH:Trace valid view ((j,IdleBoundary old d s),e) [] vf of_ observed).
 { eapply episodes_append with (more:=[]);[exact OPEN|exact SUFFIX]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view j old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT NUM PATH) as [SAFE NUMERIC].
 assert (SCOPED:owned_scope_context observed).
 { apply SCOPE.
   exact (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT I OPEN). }
 exists site,before,observed,reached_abort;split;[exact SITE|]. split;[exact PATH|].
 split;[exact SAFE|]. split;[exact NUMERIC|]. split;[exact READY|].
 split;[exact SCOPED|]. split;[exact JOURNAL|]. split;[exact ROOT|].
 apply body_error_cannot_select_finish;rewrite (proj1 READY);reflexivity.
Qed.

(* An executed RequestAbort between members changes neither the original
   queue nor the attachment log. Subsequent successful members cannot clear it. *)
Theorem owned_abort_interleaved pc selected vi oi x prefix vm om j image root s e todo
 suffix last tail vf of_ final :
 owned_body_run pc selected vi oi x prefix BodyWaiting todo vm om
   ((j,OperationBoundary image root s),e) ->
 controller_caller RequestAbort (OperationBoundary image root s) (controller_read e) ->
 owned_body_run BodyWaiting todo vm om
   ((j,OperationBoundary image root s),controller_evidence RequestAbort (OperationBoundary image root s) e)
   suffix last tail vf of_ final ->
 owned_body_run pc selected vi oi x (prefix++suffix) last tail vf of_ final /\
 (last<>BodyFailed -> last<>BodyInterrupted ->
   abort_requested (controller_read (snd final))=true).
Proof.
 intros PREFIX CALL SUFFIX;split.
 - eapply owned_body_run_append;[exact PREFIX|].
   change (owned_body_run BodyWaiting todo vm om
     ((j,OperationBoundary image root s),e) ([]++suffix) last tail vf of_ final).
   eapply body_cons;[apply body_request_abort;exact CALL|exact SUFFIX].
 - intros NF NI;apply (owned_control_sticky_bit _ _
     (owned_live_control _ _ _ _ _ _ _ _ _ _ _ SUFFIX NF NI));reflexivity.
Qed.

(* This consumer uses the request at its actual marked position. It does not
   insert a second RequestAbort after the body. *)
Theorem owned_interleaved_abort_finish valid view f h a old d s e count same compare i remaining
 word_max prefix vm om jm image_m root_m sm em todo suffix tail vf of_ f' h' a' image root s' e' resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (i::remaining)) tt ->
 owned_body_run BodyWaiting (i::remaining) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   prefix BodyWaiting todo vm om ((jm,OperationBoundary image_m root_m sm),em) ->
 owned_body_run BodyWaiting todo vm om
   ((jm,OperationBoundary image_m root_m sm),controller_evidence RequestAbort (OperationBoundary image_m root_m sm) em)
   suffix BodyFinished tail vf of_ ((Logged (Ready f') h' a',OperationBoundary image root s'),e') ->
 (forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []) ->
 map attachment_argument (prefix++suffix)=i::remaining /\
 exists destination exit,
 (exit=ReturnedOrdinary FinishAbort \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages valid view
   ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
 publications (boundary_journal destination)=h'.
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS PREFIX SUFFIX MASK.
 pose proof (owned_live_control _ _ _ _ _ _ _ _ _ _ _ PREFIX
   ltac:(discriminate) ltac:(discriminate)) as LIVE.
 pose proof (owned_control_sticky_shape false _ _ LIVE eq_refl) as CONTROL.
 assert (CALL:controller_caller RequestAbort (OperationBoundary image_m root_m sm) (controller_read em)).
 { change (outer_live (controller_read em)=true);rewrite CONTROL;reflexivity. }
 destruct (owned_abort_interleaved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PREFIX CALL SUFFIX)
   as [RUN STICKY].
 specialize (STICKY ltac:(discriminate) ltac:(discriminate)).
 change (abort_requested (controller_read e')=true) in STICKY.
 destruct (owned_marked_success_finish valid view f h a old d s e count same compare i remaining word_max
   (prefix++suffix) tail vf of_ f' h' a' image root s' e' resolved
   MARK DEC WORD GEO INIT OUT ARM PREPASS RUN MASK) as [ORDER [IMAGE FINISH]].
 rewrite STICKY in FINISH;split;assumption.
Qed.

(* Local restore replies are indexed by the root observer of the FAILED
   execution, not by a separately supplied root or a chosen safe suffix. *)

Theorem owned_marked_failed_return valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ failed read inspect check outcome resolved :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFailed tail vf of_ failed ->
 owned_restore_reply old of_ failed read inspect check outcome ->
 (forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []) ->
 exists destination exit,
 (exit=ReturnedBodyError \/ exit=InterruptedFatal) /\
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=
   control_image (journal_control (boundary_journal failed)).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN RESTORE MASK.
 destruct (owned_marked_failed_boundary valid view (Logged (Ready f) h a) old d s e count same compare first selected
   word_max log tail vf of_ failed MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [site [before [observed [ab [SITE [PATH [SAFE [NUMERIC [ERROR [SCOPE [JOURNAL [ROOT NOFINISH]]]]]]]]]]]].
 pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
 change (exists ff,journal_control (boundary_journal failed)=Ready ff) in READY.
 destruct READY as [ff READY];rewrite -JOURNAL in READY.
 assert (PUB:publications (boundary_journal observed)=h).
 { rewrite JOURNAL;exact (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)). }
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 unfold owned_restore_reply in RESTORE;rewrite -ROOT in RESTORE.
 rewrite -JOURNAL.
 destruct observed as [[[jc pubs acks] phase] ev];cbn in READY,PUB;subst jc pubs.
 destruct ERROR as [CTRL ERROR].
 destruct phase;cbn [owned_error_ready fst snd] in ERROR;try contradiction.
 - cbn [owned_error_observation fst snd] in RESTORE.
   eapply body_error_finish_from_trace_flash;try eassumption;exact I.
 - destruct current as [current|];[|contradiction].
   cbn [owned_error_observation fst snd] in RESTORE.
   destruct ERROR as [P FROZEN].
   destruct SCOPE as [STACK [IDS HEADOLD]].
   cbn in HEADOLD;assert (OLD:old0=N.of_nat old) by congruence.
   subst candidate old0.
   assert (PH:physical_authority ram=root_extents (of_ old)).
   { pose proof (proj1 (proj2 (proj2 (proj2 (proj1 SAFE))))) as LINK.
     unfold protection_history_link in LINK;cbn in LINK;rewrite HEAD in LINK;cbn in LINK;
     rewrite Nat2N.id in LINK;exact LINK. }
   assert (CALLS:data_calls (operation_abort_commands (root_extents (of_ old))) ram).
   { rewrite -PH;apply operation_abort_calls;[exact P|exact (proj1 STACK)]. }
   destruct (frozen_body_finish_from_trace valid view _ [] vf of_ ff h acks old (N.of_nat old) current ram ev
     read inspect check outcome word_max ab MARK DEC WORD GEO INIT INITIAL_NUM PATH CTRL CALLS RESTORE)
     as [destination [exit [KIND [COMPLETE [POST [HIST [FLASH NOBEGIN]]]]]]].
   exists destination,exit;split;[exact KIND|]. split;[exact COMPLETE|].
   split;[exact POST|]. split;[exact HIST|exact FLASH].
Qed.

Theorem owned_marked_local_cleanup_returned valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ failed read inspect check mask current :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFailed tail vf of_ failed ->
 owned_restore_reply old of_ failed read inspect check RestoreValidated ->
 (forall candidate_mask,Some mask=Some candidate_mask -> candidate_mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []) ->
 owned_error_observation failed=Some(false,current) ->
 exists destination,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination ReturnedBodyError /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination /\
 control_image (journal_control (boundary_journal destination))=
   control_image (journal_control (boundary_journal failed)) /\
 exists ff hh aa restored ram ev,
   destination=((Logged (Ready ff) hh aa,IdleBoundary old restored ram),ev).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN RESTORE MASK ORDINARY.
 destruct (owned_marked_failed_boundary valid view (Logged (Ready f) h a) old d s e count same compare first selected
   word_max log tail vf of_ failed MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [site [before [observed [ab [SITE [PATH [SAFE [NUMERIC [ERROR [SCOPE [JOURNAL [ROOT NOFINISH]]]]]]]]]]]].
 pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
 change (exists ff,journal_control (boundary_journal failed)=Ready ff) in READY.
 destruct READY as [ff READY];rewrite -JOURNAL in READY.
 assert (PUB:publications (boundary_journal observed)=h).
 { rewrite JOURNAL;exact (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)). }
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 unfold owned_restore_reply in RESTORE;rewrite -ROOT in RESTORE.
 assert (OBS:owned_error_observation observed=Some(false,current)) by (rewrite ROOT;exact ORDINARY).
 destruct observed as [[[jc pubs acks] phase] ev];cbn in READY,PUB;subst jc pubs.
 destruct ERROR as [CTRL ERROR].
 destruct phase;cbn [owned_error_observation fst snd] in OBS;try discriminate;
 try (match goal with opt:option (list extent) |- _=>destruct opt;discriminate end).
 destruct (body_error_cleanup_returned_from_trace valid view _ [] vf of_ ff h acks
   image root ram ev old read inspect check mask word_max ab
   MARK DEC WORD GEO INIT INITIAL_NUM I I PATH CTRL ERROR HEAD RESTORE MASK)
   as [destination [DONE [POST [restored [state [eout DEST]]]]]].
 exists destination;split;[exact DONE|]. split;[exact POST|]. split.
 - rewrite DEST;change (ff=control_image (journal_control (boundary_journal failed))).
   rewrite -JOURNAL;reflexivity.
 - exists ff,h,acks,restored,state,eout;exact DEST.
Qed.

Definition owned_live_phase pc (x:execution_boundary) :=
 match pc with BodyFailed | BodyInterrupted=>True
 | _=>exists image root s,snd (fst x)=OperationBoundary image root s end.
Lemma owned_edge_live_phase pc todo vi oi x log pc' tail vf of_ y :
 owned_body_edge pc todo vi oi x log pc' tail vf of_ y ->
 owned_live_phase pc x -> owned_live_phase pc' y.
Proof.
 intro EDGE;destruct EDGE;intro PHASE;try exact PHASE;try exact I;
 try solve [repeat eexists;reflexivity].
 - unfold owned_live_phase,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,acquisition_pc;
   destruct (neutral_end_ result);try exact I;repeat eexists;reflexivity.
 - unfold owned_live_phase,operation_writer_exit,writer_exit_boundary,preparation_pc;
   destruct (writer_end result);try exact I;repeat eexists;reflexivity.
Qed.
Lemma owned_run_live_phase pc todo vi oi x log pc' tail vf of_ y :
 owned_body_run pc todo vi oi x log pc' tail vf of_ y ->
 owned_live_phase pc x -> owned_live_phase pc' y.
Proof. intro RUN;induction RUN;intro PHASE;[exact PHASE|apply IHRUN;eapply owned_edge_live_phase;eauto]. Qed.

(* Result predicate only: executions below prove it; no edge assumes it.
   The right disjunct is a CALL boundary, not a prepared or published BOSS. *)
Definition owned_controller_result word_max vi oi initial vf of_ destination :=
 (exists exit,
   (exit=ReturnedEntry true \/ exit=ReturnedEntry false \/ exit=ReturnedBodyError \/
    exit=ReturnedOrdinary FinishClean \/ exit=ReturnedOrdinary FinishAbort \/
    exit=InterruptedFatal \/ exit=InterruptedReset) /\
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial [] vf of_ destination exit /\
   controller_result_post word_max vi oi initial [] vf of_ destination) \/
 (exists j image root s e,
   destination=((j,OpenBoundary image root s),e) /\
   Trace vi oi initial [] vf of_ destination /\ Safe vf of_ destination /\
   phase_numeric word_max marker ranges (OpenBoundary image root s) /\
   root=[] /\ pending_preparation s=None /\
   finish_selected (controller_read e)=Some FinishPublish /\
   owner_armed (controller_read e)=true /\
   outer_live (controller_read e)=true /\
   (forall r,free_range 256 (protection_table s) r ->
     snapshot_api_caller s unit (SnapshotReserve r)) /\
   unchanged [marker] (boundary_objects sector initial) (boundary_objects sector destination) /\
   (exists old,active_snapshot_roots (OpenBoundary image root s) e=Some [Some old]) /\
   (exists ff,journal_control j=Ready ff)).


(* A cut is an abandoned service execution, not a RestoreObservation response.
   A skipped read has no admissible RestoreCut. *)

Lemma owned_skipped_restore_no_cut old view x read inspect check point frozen current :
 owned_error_observation x=Some(frozen,current) ->
 (if frozen then root_address current=root_address [boss_extent (view old)]
  else current=[boss_extent (view old)]) ->
 ~owned_restore_cut_guard old view x read inspect check point.
Proof. intros OBS SAME;unfold owned_restore_cut_guard;rewrite OBS.
 destruct frozen;intros [DIFF _];contradiction. Qed.

(* The local restore cut loses the whole RAM, including the consumed handle.
   The read/validation/copy prefix itself writes no flash. *)
Theorem owned_reset_after_prefix vi oi initial events valid view f h a phase e word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),e) ->
 let destination:=((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e) in
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination InterruptedReset /\
 controller_result_post word_max vi oi initial events valid view destination.
Proof.
 intros MARK DEC WORD GEO INIT NUM PATH destination.
 assert (STOP:operation_execution g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,phase),e) [] valid view destination InterruptedReset).
 { apply operation_end with (event:=None);[apply reset_episode;apply record_step;apply reset_ready|reflexivity]. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination InterruptedReset).
 { exists valid,view,((Logged (Ready f) h a,phase),e),events,[];split;[exact PATH|].
   split;[exact STOP|reflexivity]. }
 split;[exact COMPLETE|eapply controller_finalization_from_trace;eauto].
Qed.

Theorem owned_marked_failed_cut valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ failed read inspect check point :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFailed tail vf of_ failed ->
 owned_restore_cut_guard old of_ failed read inspect check point ->
 exists ff acks abandoned,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Boot ff) h acks,RebuildingBoundary Selecting),forget_volatile_evidence abandoned) InterruptedReset /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Boot ff) h acks,RebuildingBoundary Selecting),forget_volatile_evidence abandoned) /\
 ff=control_image (journal_control (boundary_journal failed)).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN CUT.
 destruct (owned_marked_failed_boundary valid view (Logged (Ready f) h a) old d s e count same compare first selected
   word_max log tail vf of_ failed MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [site [before [observed [ab [SITE [PATH [SAFE [NUMERIC [ERROR [SCOPE [JOURNAL [ROOT NOFINISH]]]]]]]]]]]].
 pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
 change (exists ff,journal_control (boundary_journal failed)=Ready ff) in READY.
 destruct READY as [ff READY];rewrite -JOURNAL in READY.
 assert (PUB:publications (boundary_journal observed)=h).
 { rewrite JOURNAL;exact (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)). }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 unfold owned_restore_cut_guard in CUT;rewrite -ROOT in CUT.
 destruct observed as [[[jc pubs acks] phase] ev];cbn in READY,PUB;subst jc pubs.
 destruct ERROR as [CTRL ERROR].
 assert (CALL:controller_caller (TakeLocal false) phase (controller_read ev)).
 { rewrite CTRL;destruct phase;cbn [owned_error_ready fst snd] in ERROR;try contradiction.
   - split;reflexivity || exact I.
   - destruct current;[repeat split;reflexivity|contradiction]. }
 set (taken:=controller_evidence (TakeLocal false) phase ev).
 assert (TAKE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready ff) h acks,phase),taken)).
 { apply controller_from_trace;assumption. }
 destruct (owned_reset_after_prefix valid view _ [] vf of_ ff h acks phase taken word_max
   MARK DEC WORD GEO INIT NUM TAKE) as [COMPLETE POST].
 exists ff,acks,taken;split;[exact COMPLETE|]. split;[exact POST|].
 rewrite -JOURNAL;reflexivity.
Qed.


Theorem owned_marked_abort_cut valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ f' h' a' image root ram ev read inspect check point :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((Logged (Ready f') h' a',OperationBoundary image root ram),ev) ->
 abort_requested (controller_read ev)=true ->
 owned_restore_cut_guard old of_ ((Logged (Ready f') h' a',OperationBoundary image root ram),ev) read inspect check point ->
 exists abandoned,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Boot f') h' a',RebuildingBoundary Selecting),forget_volatile_evidence abandoned) InterruptedReset /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Boot f') h' a',RebuildingBoundary Selecting),forget_volatile_evidence abandoned).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN AB CUT.
 destruct (owned_controller_body_accept valid view (Logged (Ready f) h a) old d s e
   count same compare first selected word_max log tail vf of_ (Logged (Ready f') h' a') image root ram ev
   MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [ORDER [IMAGE [CHECKS [CLOSE [SAFE [NUM [LOCAL [TAKEN NOCOLLECT]]]]]]]].
 set (accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram).
 set (phase:=OpenBoundary image root accepted).
 set (closed:=controller_evidence LocalClosed phase
   (controller_evidence (TakeLocal true) (OperationBoundary image root ram) ev)).
 pose proof (owned_success_control _ _ _ _ _ _ _ _ _ _ RUN) as STICKY.
 pose proof (owned_control_sticky_shape false _ _ STICKY eq_refl) as CONTROL.
 assert (CC:controller_read closed=Control true true true true false None None).
 { change (control_close_local (control_take_local true (controller_read ev))=Control true true true true false None None).
   rewrite CONTROL;cbn;rewrite AB;reflexivity. }
 assert (CALL:controller_caller SelectFinish phase (controller_read closed)).
 { rewrite CC;repeat split;reflexivity. }
 set (selected_e:=controller_evidence SelectFinish phase closed).
 assert (SELECT:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',phase),selected_e)).
 { apply controller_from_trace;assumption. }
 set (taken:=controller_evidence TakeOuter phase selected_e).
 assert (TAKE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',phase),taken)).
 { apply controller_from_trace;[exact SELECT|].
   change (finish_selected (control_select (phase_dirty phase) (controller_read closed))<>None /\
     outer_live (control_select (phase_dirty phase) (controller_read closed))=true).
   rewrite CC;split;[discriminate|reflexivity]. }
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT I TAKE) as SCOPE.
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 destruct CUT as [CHANGED REACHED].
 set (destination:=((Logged (Boot f') h' a',RebuildingBoundary Selecting),forget_volatile_evidence taken)).
 assert (STOP:operation_execution g sector data_len marker ranges decode topology pages vf of_
   ((Logged (Ready f') h' a',phase),taken) [] vf of_ destination InterruptedReset).
 { apply operation_end with (event:=None);[|reflexivity].
   eapply restore_cut_episode with (old:=old) (read:=fun _ _=>read) (inspect:=inspect) (validate:=check) (cut:=point);
   try eassumption;reflexivity. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination InterruptedReset).
 { exists vf,of_,((Logged (Ready f') h' a',phase),taken),[],[];split;[exact TAKE|]. split;[exact STOP|reflexivity]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 exists taken;split;[exact COMPLETE|eapply controller_finalization_from_trace;eauto].
Qed.

Theorem owned_marked_abort_restore_failure valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ f' h' a' image root ram ev read inspect check outcome :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((Logged (Ready f') h' a',OperationBoundary image root ram),ev) ->
 abort_requested (controller_read ev)=true ->
 owned_restore_reply old of_ ((Logged (Ready f') h' a',OperationBoundary image root ram),ev) read inspect check outcome ->
 (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed \/ outcome=RestorePanicked) ->
 exists abandoned,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',FatalBoundary),forget_volatile_evidence abandoned) InterruptedFatal /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',FatalBoundary),forget_volatile_evidence abandoned).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN AB REPLY ERROR.
 destruct (owned_controller_body_accept valid view (Logged (Ready f) h a) old d s e
   count same compare first selected word_max log tail vf of_ (Logged (Ready f') h' a') image root ram ev
   MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
   as [ORDER [IMAGE [CHECKS [CLOSE [SAFE [NUM [LOCAL [TAKEN NOCOLLECT]]]]]]]].
 set (accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram).
 set (phase:=OpenBoundary image root accepted).
 set (closed:=controller_evidence LocalClosed phase
   (controller_evidence (TakeLocal true) (OperationBoundary image root ram) ev)).
 pose proof (owned_success_control _ _ _ _ _ _ _ _ _ _ RUN) as STICKY.
 pose proof (owned_control_sticky_shape false _ _ STICKY eq_refl) as CONTROL.
 assert (CC:controller_read closed=Control true true true true false None None).
 { change (control_close_local (control_take_local true (controller_read ev))=Control true true true true false None None).
   rewrite CONTROL;cbn;rewrite AB;reflexivity. }
 assert (CALL:controller_caller SelectFinish phase (controller_read closed)).
 { rewrite CC;repeat split;reflexivity. }
 set (selected_e:=controller_evidence SelectFinish phase closed).
 assert (SELECT:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',phase),selected_e)).
 { apply controller_from_trace;assumption. }
 set (taken:=controller_evidence TakeOuter phase selected_e).
 assert (TAKE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Ready f') h' a',phase),taken)).
 { apply controller_from_trace;[exact SELECT|].
   change (finish_selected (control_select (phase_dirty phase) (controller_read closed))<>None /\
     outer_live (control_select (phase_dirty phase) (controller_read closed))=true).
   rewrite CC;split;[discriminate|reflexivity]. }
 pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT I TAKE) as SCOPE.
 assert (HEAD:hd_error h'=Some (N.of_nat old)).
 { pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as HIST.
   change (h'=h) in HIST;rewrite HIST.
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }

 cbn [owned_restore_reply owned_error_observation fst snd] in REPLY.
 destruct REPLY as [[SAME OK]|[CHANGED RESTORE]].
 { subst outcome;destruct ERROR as [BAD|[BAD|BAD]];discriminate. }
 set (destination:=((Logged (Ready f') h' a',FatalBoundary),forget_volatile_evidence taken)).
 assert (STOP:operation_execution g sector data_len marker ranges decode topology pages vf of_
   ((Logged (Ready f') h' a',phase),taken) [] vf of_ destination InterruptedFatal).
 { apply operation_end with (event:=None);[|reflexivity].
   destruct ERROR as [ERR|[ERR|ERR]].
   - eapply restore_failed_episode with (old:=old) (read:=fun _ _=>read)
       (inspect:=inspect) (validate:=check) (outcome:=outcome);try eassumption;try reflexivity;tauto.
   - eapply restore_failed_episode with (old:=old) (read:=fun _ _=>read)
       (inspect:=inspect) (validate:=check) (outcome:=outcome);try eassumption;try reflexivity;tauto.
   - pose proof (restore_probe_outcome _ _ _ _ RESTORE) as OBS;rewrite ERR in OBS.
     destruct read as [bytes|] eqn:READ;[|discriminate].
     destruct (inspect bytes) eqn:INSPECT.
     + destruct (check bytes);discriminate.
     + eapply restore_panic_episode with (old:=old) (read:=fun _ _=>Some bytes)
         (diagnostics:=inspect) (bytes:=bytes);try eassumption;reflexivity. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ destination InterruptedFatal).
 { exists vf,of_,((Logged (Ready f') h' a',phase),taken),[],[];split;[exact TAKE|]. split;[exact STOP|reflexivity]. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 exists taken;split;[exact COMPLETE|eapply controller_finalization_from_trace;eauto].
Qed.

(* One dispatch from the actual prepass and terminal marked result.
   No successful suffix, final invariant or finalization decision is an input. *)
Theorem owned_marked_controller valid view f h a old d s e count same compare selected
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected selected) tt ->
 (match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 exists vo oo destination,
 owned_controller_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   vo oo destination /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=client_receipts e.
Proof.
 intros MARK DEC WORD GEO INIT META OUT ARM PREPASS BODY RESTORE MASK.
 destruct selected as [|first selected].
 - destruct (owned_empty_prepass_return valid view (Logged (Ready f) h a) old d s e
     count same compare word_max MARK DEC WORD GEO INIT OUT ARM PREPASS) as [COMPLETE POST].
   exists valid,view,((Logged (Ready f) h a,IdleBoundary old d s),e).
   split;[left;exists (ReturnedEntry true);split;[tauto|split;assumption]|split;reflexivity].
 - destruct cut as [point|].
   + destruct BODY as [RUN TERMINAL].
     destruct RESTORE as [[DONE|FAILED] [AB CUT]];subst pc.
     * pose proof (owned_run_live_phase _ _ _ _ _ _ _ _ _ _ _ RUN
         ltac:(repeat eexists;reflexivity)) as SHAPE.
       pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
       destruct final as [[[jc pubs acks] phase] ev].
       destruct SHAPE as [image [root [ram EQ]]];cbn in EQ;subst phase.
       destruct READY as [ff READY];cbn in READY;subst jc.
       pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as PUB.
       change (pubs=h) in PUB;subst pubs.
       destruct (owned_marked_abort_cut valid view f h a old d s e count same compare first selected
         word_max log tail vf of_ ff h acks image root ram ev read inspect check point
         MARK DEC WORD GEO INIT OUT ARM PREPASS RUN (AB eq_refl) CUT)
         as [abandoned [COMPLETE POST]].
       exists vf,of_,((Logged (Boot ff) h acks,RebuildingBoundary Selecting),forget_volatile_evidence abandoned).
       split;[left;exists InterruptedReset;split;[tauto|split;assumption]|].
       split;[reflexivity|exact (proj1 (proj2 (proj2 (proj2 POST))))].
     * destruct (owned_marked_failed_cut valid view f h a old d s e count same compare first selected
         word_max log tail vf of_ final read inspect check point
         MARK DEC WORD GEO INIT OUT ARM PREPASS RUN CUT)
         as [ff [acks [abandoned [COMPLETE [POST FLASH]]]]].
       exists vf,of_,((Logged (Boot ff) h acks,RebuildingBoundary Selecting),forget_volatile_evidence abandoned).
       split;[left;exists InterruptedReset;split;[tauto|split;assumption]|].
       split;[reflexivity|exact (proj1 (proj2 (proj2 (proj2 POST))))].
   + { destruct BODY as [RUN [DONE|[FAILED|INTERRUPTED]]];subst pc.
   + pose proof (owned_run_live_phase _ _ _ _ _ _ _ _ _ _ _ RUN
       ltac:(repeat eexists;reflexivity)) as SHAPE.
     pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
     destruct final as [[[jc pubs acks] phase] ev].
     destruct SHAPE as [image [root [ram EQ]]];cbn in EQ;subst phase.
     destruct READY as [ff READY];cbn in READY;subst jc.
     pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as PUB.
     change (pubs=h) in PUB;subst pubs.
     assert (NORMAL_RESULT: exists vo oo destination,
       owned_controller_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
         vo oo destination /\
       publications (boundary_journal destination)=h /\
       boundary_receipts destination=client_receipts e).
     {
     destruct (owned_marked_success_finish valid view f h a old d s e count same compare first selected
       word_max log tail vf of_ ff h acks image root ram ev resolved
       MARK DEC WORD GEO INIT OUT ARM PREPASS RUN MASK) as [ORDER [IMAGE FINISH]].
     destruct (abort_requested (controller_read ev)) eqn:AB.
     * destruct FINISH as [destination [exit [KIND [COMPLETE [POST PUB]]]]].
       exists vf,of_,destination;split.
       -- left;exists exit;split;[tauto|split;assumption].
       -- split;[exact PUB|exact (proj1 (proj2 (proj2 (proj2 POST))))].
     * destruct (phase_dirty (OpenBoundary image root
         (data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram))) eqn:DIRTY.
       -- pose proof (proj1 FINISH) as PATH.
          eexists vf,of_,_;split.
          ++ right;do 5 eexists;split;[reflexivity|].
             destruct FINISH as [T [S [N [R [P [F [A [L [C [M ROOTS]]]]]]]]]].
             exact (conj T (conj S (conj N (conj R (conj P (conj F (conj A (conj L (conj C (conj M (conj (ex_intro _ old ROOTS) (ex_intro _ ff eq_refl)))))))))))).
          ++ split;[reflexivity|].
             exact (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
               _ _ _ _ _ _ _ INIT PATH))).
       -- destruct FINISH as [destination [exit [KIND [COMPLETE [POST PUB]]]]].
          exists vf,of_,destination;split.
          ++ left;exists exit;split;[tauto|split;assumption].
          ++ split;[exact PUB|exact (proj1 (proj2 (proj2 (proj2 POST))))].
     }
     destruct (abort_requested (controller_read ev)) eqn:ABORT.
     * destruct outcome.
       -- destruct (owned_marked_abort_restore_failure valid view f h a old d s e count same compare first selected
            word_max log tail vf of_ ff h acks image root ram ev read inspect check RestoreReadFailed
            MARK DEC WORD GEO INIT OUT ARM PREPASS RUN ABORT
            (RESTORE (or_intror (conj eq_refl ABORT))) (or_introl eq_refl))
            as [abandoned [COMPLETE POST]].
          exists vf,of_,((Logged (Ready ff) h acks,FatalBoundary),forget_volatile_evidence abandoned).
          split;[left;exists InterruptedFatal;split;[tauto|split;assumption]|].
          split;[reflexivity|exact (proj1 (proj2 (proj2 (proj2 POST))))].
       -- destruct (owned_marked_abort_restore_failure valid view f h a old d s e count same compare first selected
            word_max log tail vf of_ ff h acks image root ram ev read inspect check RestorePanicked
            MARK DEC WORD GEO INIT OUT ARM PREPASS RUN ABORT
            (RESTORE (or_intror (conj eq_refl ABORT))) (or_intror (or_intror eq_refl)))
            as [abandoned [COMPLETE POST]].
          exists vf,of_,((Logged (Ready ff) h acks,FatalBoundary),forget_volatile_evidence abandoned).
          split;[left;exists InterruptedFatal;split;[tauto|split;assumption]|].
          split;[reflexivity|exact (proj1 (proj2 (proj2 (proj2 POST))))].
       -- destruct (owned_marked_abort_restore_failure valid view f h a old d s e count same compare first selected
            word_max log tail vf of_ ff h acks image root ram ev read inspect check RestoreValidationFailed
            MARK DEC WORD GEO INIT OUT ARM PREPASS RUN ABORT
            (RESTORE (or_intror (conj eq_refl ABORT))) (or_intror (or_introl eq_refl)))
            as [abandoned [COMPLETE POST]].
          exists vf,of_,((Logged (Ready ff) h acks,FatalBoundary),forget_volatile_evidence abandoned).
          split;[left;exists InterruptedFatal;split;[tauto|split;assumption]|].
          split;[reflexivity|exact (proj1 (proj2 (proj2 (proj2 POST))))].
       -- exact NORMAL_RESULT.
     * exact NORMAL_RESULT.
   + destruct (owned_marked_failed_return valid view f h a old d s e count same compare first selected
       word_max log tail vf of_ final read inspect check outcome resolved
       MARK DEC WORD GEO INIT OUT ARM PREPASS RUN (RESTORE (or_introl eq_refl)) MASK)
       as [destination [exit [KIND [COMPLETE [POST [PUB FLASH]]]]]].
     exists vf,of_,destination;split.
     * left;exists exit;split;[tauto|split;assumption].
     * split;[exact PUB|exact (proj1 (proj2 (proj2 (proj2 POST))))].
   + destruct (owned_marked_interruption_return valid view (Logged (Ready f) h a) old d s e count same compare first selected
       word_max log tail vf of_ final MARK DEC WORD GEO INIT OUT ARM PREPASS RUN)
       as [exit [KIND [COMPLETE [POST [PUB RECEIPTS]]]]].
     exists vf,of_,final;split.
     * left;exists exit;split;[tauto|split;assumption].
     * split;assumption.
   }
Qed.

(* Entry errors are delivered before any scope; selected bodies retain their
   marked execution and the same interrupted cleanup interface. *)
Theorem owned_entry_marked_controller valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 exists vo oo destination,
 owned_controller_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   vo oo destination /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=client_receipts e.
Proof.
 intros MARK DEC WORD GEO INIT META OUT ARM ENTRY BODY RESTORE MASK.
 pose proof (owned_pair_entry_dispatch valid view (Logged (Ready f) h a)
   old d s e count same compare result word_max
   MARK DEC WORD GEO INIT OUT ARM ENTRY) as DISPATCH.
 destruct result as [|index|selected].
 - destruct DISPATCH as [COMPUTE [COMPLETE POST]].
   exists valid,view,((Logged (Ready f) h a,IdleBoundary old d s),e).
   split;[left;exists (ReturnedEntry false);split;[tauto|split;assumption]|split;reflexivity].
 - destruct DISPATCH as [COMPUTE [COMPLETE POST]].
   exists valid,view,((Logged (Ready f) h a,IdleBoundary old d s),e).
   split;[left;exists (ReturnedEntry false);split;[tauto|split;assumption]|split;reflexivity].
 - eapply owned_marked_controller;try eassumption.
   + exact (BODY selected eq_refl).
   + exact (RESTORE selected eq_refl).
   + exact (MASK selected eq_refl).
Qed.

Definition open_destination (destination:execution_boundary) :=
 exists j image root ram ev,destination=((j,OpenBoundary image root ram),ev).

Theorem owned_entry_marked_controller_indexed valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 exists vo oo destination,
 owned_controller_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   vo oo destination /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=client_receipts e /\
 (marked_boss_requested result pc final=true -> open_destination destination /\
   vo=vf /\ oo=of_ /\ destination=marked_selected_boundary final).
Proof.
 intros MARK DEC WORD GEO INIT META OUT ARM ENTRY BODY RESTORE MASK.
 destruct (marked_boss_requested result pc final) eqn:REQUEST.
 - assert (WANT:=REQUEST).
   unfold marked_boss_requested in WANT.
   destruct result as [|idx|[|first remaining]];try discriminate.
   destruct pc;try discriminate.
   destruct final as [[[jc pubs acks] phase] ev];destruct phase;try discriminate.
   cbn in WANT;apply Bool.andb_true_iff in WANT;destruct WANT as [AB DIRTY].
   apply Bool.negb_true_iff in AB.
   change (phase_dirty (OpenBoundary image root (data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram))=true) in DIRTY.
   destruct (BODY (first::remaining) eq_refl) as [RUN _].
   pose proof (owned_run_ready _ _ _ _ _ _ _ _ _ _ _ RUN ltac:(exists f;reflexivity)) as READY.
   destruct READY as [ff READY];cbn in READY;subst jc.
   pose proof (proj1 (owned_body_history _ _ _ _ _ _ _ _ _ _ _ RUN)) as PUB.
   change (pubs=h) in PUB;subst pubs.
   destruct (owned_marked_success_finish valid view f h a old d s e count same compare first remaining
     word_max log tail vf of_ ff h acks image root ram ev None
     MARK DEC WORD GEO INIT OUT ARM ENTRY RUN ltac:(intros;discriminate)) as [_ [_ FINISH]].
   rewrite AB in FINISH;rewrite DIRTY in FINISH.
   pose proof (proj1 FINISH) as PATH.
   eexists vf,of_,_;split.
   + right;do 5 eexists;split;[reflexivity|].
     destruct FINISH as [T [S [N [R [P [F [A [L [C [M ROOTS]]]]]]]]]].
     exact (conj T (conj S (conj N (conj R (conj P (conj F (conj A (conj L (conj C (conj M (conj (ex_intro _ old ROOTS) (ex_intro _ ff eq_refl)))))))))))).
   + split;[reflexivity|]. split.
     * exact (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ INIT PATH))).
     * intros;split;[repeat eexists;reflexivity|]. repeat split;reflexivity.
 - destruct (owned_entry_marked_controller valid view f h a old d s e count same compare result
     word_max log pc tail vf of_ final read inspect check outcome resolved cut
     MARK DEC WORD GEO INIT META OUT ARM ENTRY BODY RESTORE MASK) as [vo [oo [destination [RESULT [PUB RECEIPTS]]]]].
   exists vo,oo,destination;split;[exact RESULT|]. split;[exact PUB|]. split;[exact RECEIPTS|].
   discriminate.
Qed.


(* Returned physical acquisition errors start AFTER SelectFinish, with no token.
   A cut abandons the read/copy continuation; it is not a normal restore reply. *)
Theorem selected_recycling_error_return vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled
 word_max read inspect check outcome (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_structure marker initial ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralError ->
 (match cut with
 | Some point=>restore_cut_reached read inspect check point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt end) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash recycled)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (neutral_flash recycled)) view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash recycled.
Proof.
 intros MARK DEC WORD GEO INIT NUM STRUCT RAW PREFIX ROUTE ARMED LIVE HEAD P LOCAL SEARCH GEOM RUN ERROR RESTORE.
 destruct (recycling_acquisition_from_trace vi oi initial events valid view f h a old image [] s e
   recognize magic fuel req round alignment start r count recycled true
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEOM RUN) as [previous [ACQUIRE OTHER]].
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [saved [STACK BASE]].
 set (vf:=validate (neutral_flash recycled)).
 set (j:=Logged (Ready (neutral_flash recycled)) h a).
 set (ram:=data_next DataFreeze s).
 set (phase:=FrozenBoundary (N.of_nat old) (N.of_nat old) (Some []) ram).
 set (ev:=phase_evidence phase (selected_evidence old previous e)).
 assert (FAILED:Trace vi oi initial events vf view ((j,phase),ev)).
 { unfold recycling_cursor_evidence,recycling_acquisition_boundary in ACQUIRE;rewrite ERROR in ACQUIRE.
   unfold neutral_open_boundary in ACQUIRE;rewrite ERROR in ACQUIRE;exact ACQUIRE. }
 set (taken:=controller_evidence TakeOuter phase ev).
 assert (TAKE:Trace vi oi initial events vf view ((j,phase),taken)).
 { apply controller_from_trace;[exact FAILED|].
   split;unfold ev;autorewrite with control_evidence;[rewrite ROUTE;discriminate|exact LIVE]. }
 assert (ARM:owner_armed (controller_read taken)=true).
 { unfold taken,ev;autorewrite with control_evidence;exact ARMED. }
 assert (SELECTED:finish_selected (controller_read taken)=Some FinishPublish).
 { unfold taken,ev;autorewrite with control_evidence;exact ROUTE. }
 destruct cut as [point|].
 - destruct (owned_reset_after_prefix vi oi initial events vf view (neutral_flash recycled) h a phase taken word_max
     MARK DEC WORD GEO INIT NUM TAKE) as [COMPLETE POST].
   eexists _,InterruptedReset;split;[tauto|]. split;[exact COMPLETE|].
   split;[exact POST|]. split;reflexivity.
 - assert (ENDING:exists before,
     Trace vi oi initial events vf view before /\
     ordinary_return_ready FinishPublish before /\
     boundary_journal before=j).
   { destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|BAD].
     - subst outcome.
       set (closed:=data_next (DataClose [] saved false) ram).
       set (last:=FrozenBoundary (N.of_nat old) (N.of_nat old) None closed).
       assert (CLOSE:Trace vi oi initial events vf view ((j,last),taken)).
       { eapply episodes_append with (more:=[]);[exact TAKE|].
         eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
         eapply frozen_scope_close;[|exact RESTORE].
         change (pending_preparation s=None /\ protection_saved s=[]++[saved]);auto. }
       set (done:=controller_evidence DropOwner last taken).
       assert (DROP:Trace vi oi initial events vf view ((j,last),done)).
       { apply controller_from_trace;[exact CLOSE|].
         split;[exact ARM|reflexivity]. }
       exists ((j,last),done);split;[exact DROP|].
       split;[|reflexivity].
       change (owner_armed (controller_read done)=false /\ outer_live (controller_read done)=false /\
         finish_selected (controller_read done)=Some FinishPublish).
       unfold done;autorewrite with control_evidence;auto.
     - assert (STOP:Trace vi oi initial events vf view ((j,FatalBoundary),forget_volatile_evidence taken)).
       { eapply episodes_append with (more:=[]);[exact TAKE|].
         eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
         eapply frozen_scope_stop;eassumption. }
       exists ((j,FatalBoundary),forget_volatile_evidence taken);split;[exact STOP|].
       split;reflexivity. }
   destruct ENDING as [before [PATH [READY JOURNAL]]].
   destruct (deliver_ready_execution FinishPublish vf view before READY)
     as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events vf view destination exit).
   { exists vf,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
   exists destination,exit;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + assert (J:boundary_journal destination=j).
     { unfold boundary_journal in *;rewrite SAME;exact JOURNAL. }
     rewrite J;split;reflexivity.
Qed.

Theorem selected_recycling_interruption vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 (neutral_end_ recycled=NeutralFatal \/ neutral_end_ recycled=NeutralReset) ->
 exists destination exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash recycled)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (neutral_flash recycled)) view destination /\
 exit_observation exit=None /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash recycled.
Proof.
 intros MARK DEC WORD GEO INIT NUM RAW PREFIX HEAD P LOCAL SEARCH GEOM RUN END.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];cbn in ID;subst id.
 set (dest:=(recycling_acquisition_boundary old image [] s h a recycled
   (block_pages (recycle_lo r) (useful_pages r)) true,
   phase_evidence (snd (recycling_acquisition_boundary old image [] s h a recycled
   (block_pages (recycle_lo r) (useful_pages r)) true)) (selected_evidence old previous (recycling_cursor_evidence recycled (block_pages (recycle_lo r) (useful_pages r)) e)))).
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None
   (validate (neutral_flash recycled)) view dest).
 { eapply acquire_recycled;eauto. }
 destruct dest as [[jj phase] ee] eqn:DEST.
 assert (STOP:phase=FatalBoundary \/ exists pc,phase=RebuildingBoundary pc).
 { unfold dest,recycling_acquisition_boundary,neutral_open_boundary in DEST.
   destruct END as [END|END];rewrite END in DEST;inversion DEST;subst;auto.
   right;exists Selecting;reflexivity. }
 destruct (stopped_operation_execution g sector data_len marker ranges decode topology pages
   _ _ _ _ _ jj phase ee STEP STOP) as [exit [EXEC OBS]].
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash recycled)) view ((jj,phase),ee) exit).
 { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),e),events,[];
     split;[exact PREFIX|]. split;[exact EXEC|reflexivity]. }
 exists ((jj,phase),ee),exit;split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - split;[exact OBS|].
   unfold dest,recycling_acquisition_boundary,neutral_open_boundary in DEST.
   destruct END as [END|END];rewrite END in DEST;inversion DEST;subst;split;reflexivity.
Qed.

Theorem selected_recycling_before_reserve_reset vi oi initial events valid view f h a old image s e
 recognize magic fuel req round alignment start r count recycled word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f recycled ->
 neutral_end_ recycled=NeutralSuccess ->
 exists destination exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash recycled)) view destination exit /\
 controller_result_post word_max vi oi initial events (validate (neutral_flash recycled)) view destination /\
 exit_observation exit=None /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=neutral_flash recycled.
Proof.
 intros MARK DEC WORD GEO INIT NUM RAW PREFIX HEAD P LOCAL SEARCH GEOM RUN END.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX) as [SOURCE ORDER].
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [IN ID]];cbn in ID;subst id.
 set (dest:=((Logged (Boot (neutral_flash recycled)) h a,RebuildingBoundary Selecting),
   forget_volatile_evidence (selected_evidence old previous e))).
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None
   (validate (neutral_flash recycled)) view dest).
 { eapply cut_recycled_before_reserve;eauto. }
 assert (EXEC:operation_execution g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) []
   (validate (neutral_flash recycled)) view dest InterruptedReset).
 { apply operation_end with (event:=None);[exact STEP|reflexivity]. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events (validate (neutral_flash recycled)) view dest InterruptedReset).
 { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),e),events,[];
     split;[exact PREFIX|]. split;[exact EXEC|reflexivity]. }
 exists dest,InterruptedReset;split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - split;[reflexivity|]. split;reflexivity.
Qed.

Theorem selected_search_error_return vi oi initial events valid view f h a old image s e
 fuel recognize req round alignment start reply word_max rd ins chk observed resolved
 (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
 (reply=SearchMiss \/ reply=SearchError) ->
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE HEAD P SEARCH ERROR RESTORE MASK.
 destruct cut as [point|].
 - set (taken:=controller_evidence TakeOuter (OpenBoundary image [] s) e).
   assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),taken)).
   { apply controller_from_trace;[exact PREFIX|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
   pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT CTX TAKE) as SCOPE.
   set (dest:=((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
   assert (STOP:operation_execution g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,OpenBoundary image [] s),taken) [] valid view dest InterruptedReset).
   { apply operation_end with (event:=None);[|reflexivity].
     eapply restore_cut_episode with (old:=old) (read:=fun _ _=>rd) (inspect:=ins) (validate:=chk) (cut:=point);
       try eassumption;discriminate. }
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view dest InterruptedReset).
   { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),taken),events,[];
     split;[exact TAKE|]. split;[exact STOP|reflexivity]. }
   exists dest,InterruptedReset;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + split;reflexivity.
 - destruct (dirty_error_restore_outcome_from_trace vi oi initial events valid view f h a image s e old resolved word_max
     (fun _ _=>rd) ins chk observed MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE P HEAD MASK RESTORE)
     as [before [READY [PATH [SAFE [NUMBER [JOURNAL REST]]]]]].
   destruct (deliver_ready_execution FinishPublish valid view before READY)
     as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view destination exit).
   { exists valid,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
   exists destination,exit;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + assert (J:boundary_journal destination=Logged (Ready f) h a).
     { unfold boundary_journal in *;rewrite SAME;exact JOURNAL. }
     rewrite J;split;reflexivity.
Qed.

(* Shared finalization-error continuation after FinishPublish: no acquisition,
   token or additional SelectFinish is fabricated by this suffix. *)
Theorem selected_preallocation_error_return vi oi initial events valid view f h a old image s e
 word_max rd ins chk observed resolved
 (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE HEAD P RESTORE MASK.
 destruct cut as [point|].
 - set (taken:=controller_evidence TakeOuter (OpenBoundary image [] s) e).
   assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),taken)).
   { apply controller_from_trace;[exact PREFIX|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
   pose proof (episode_trace_rollback_context g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT CTX TAKE) as SCOPE.
   set (dest:=((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
   assert (STOP:operation_execution g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,OpenBoundary image [] s),taken) [] valid view dest InterruptedReset).
   { apply operation_end with (event:=None);[|reflexivity].
     eapply restore_cut_episode with (old:=old) (read:=fun _ _=>rd) (inspect:=ins) (validate:=chk) (cut:=point);
       try eassumption;discriminate. }
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view dest InterruptedReset).
   { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),taken),events,[];
     split;[exact TAKE|]. split;[exact STOP|reflexivity]. }
   exists dest,InterruptedReset;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + split;reflexivity.
 - destruct (dirty_error_restore_outcome_from_trace vi oi initial events valid view f h a image s e old resolved word_max
     (fun _ _=>rd) ins chk observed MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE P HEAD MASK RESTORE)
     as [before [READY [PATH [SAFE [NUMBER [JOURNAL REST]]]]]].
   destruct (deliver_ready_execution FinishPublish valid view before READY)
     as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view destination exit).
   { exists valid,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
   exists destination,exit;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + assert (J:boundary_journal destination=Logged (Ready f) h a).
     { unfold boundary_journal in *;rewrite SAME;exact JOURNAL. }
     rewrite J;split;reflexivity.
Qed.

Theorem selected_probe_error_return vi oi initial events valid view f h a old image s e
 area_len req cursor probe_final word_max rd ins chk observed resolved
 (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector area_len req cursor f) (probe_cursor_checked word_max)) s ProbeRejected probe_final ->
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 probe_final=s /\
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE HEAD P PROBE RESTORE MASK.
 split;[exact (proj1 (checked_probe_execution _ _ _ _ _ _ _ _ _ PROBE))|].
 eapply selected_preallocation_error_return;eassumption.
Qed.

(* Conditional adapter only: the existing runtime/decoded records do not yet
   supply counter from a trace. Do not mistake this local arithmetic premise
   for the missing generation provenance producer. *)
Theorem selected_generation_overflow_return vi oi initial events valid view f h a old image s e
 counter word_max rd ins chk observed resolved
 (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 owner_armed (controller_read e)=true -> outer_live (controller_read e)=true ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None ->
 boss_checked_generation counter=None ->
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM CTX PREFIX ROUTE ARMED LIVE HEAD P OVERFLOW RESTORE MASK.
 eapply selected_preallocation_error_return;eassumption.
Qed.

Theorem selected_search_interruption vi oi initial events valid view f h a image s e
 fuel shape verify req round alignment start target fatal word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 pending_preparation s=None ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table s) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 let dest:=if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
   else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e) in
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view dest (if fatal then InterruptedFatal else InterruptedReset) /\
 controller_result_post word_max vi oi initial events valid view dest /\
 publications (boundary_journal dest)=h /\
 control_image (journal_control (boundary_journal dest))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM PREFIX P SEARCH STOP dest.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None valid view dest).
 { eapply acquisition_search_interrupted;try eassumption;right;reflexivity. }
 assert (EXEC:operation_execution g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) [] valid view dest
     (if fatal then InterruptedFatal else InterruptedReset)).
 { apply operation_end with (event:=None);[exact STEP|destruct fatal;reflexivity]. }
 assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view dest (if fatal then InterruptedFatal else InterruptedReset)).
 { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),e),events,[];
   split;[exact PREFIX|]. split;[exact EXEC|reflexivity]. }
 split;[exact COMPLETE|]. split.
 - eapply controller_finalization_from_trace;eauto.
 - destruct fatal;split;reflexivity.
Qed.


Lemma active_single_outer_depth image root s e id :
 active_snapshot_roots (OpenBoundary image root s) e=Some [Some id] ->
 length (protection_saved s)=1.
Proof.
 unfold active_snapshot_roots;cbn.
 destruct (volatile_scope_roots e) as [|old|roots];try discriminate.
 destruct (length (protection_saved s)<=?length roots) eqn:BOUND;try discriminate.
 intro EQ;inversion EQ as [PREFIX];apply Nat.leb_le in BOUND.
 apply (f_equal (@length (option nat))) in PREFIX.
 rewrite firstn_length in PREFIX. rewrite (Nat.min_l _ _ BOUND) in PREFIX;exact PREFIX.
Qed.

(* The target is computed from the concrete surviving scope roots. This is a
   call contract for the existing checked_rehome service, not its execution. *)
Definition boss_rehome_call word_max image s e r :=
 exists roots,
 active_snapshot_roots (OpenBoundary image [] s) e=Some roots /\
 DeferredSnapshots.snapshot_owner roots=length (protection_saved s) /\
 forall table,
 checked_rehome true word_max r (DeferredSnapshots.snapshot_owner roots) table=
   (None,IncarnationBoundary.rehome_extent r (DeferredSnapshots.snapshot_owner roots) table).

Lemma boss_rehome_from_roots_numeric word_max image s e r id :
 state_numeric word_max s ->
 pending_preparation s=Some (reservation_token true r) ->
 active_snapshot_roots (OpenBoundary image [] s) e=Some [Some id] ->
 boss_rehome_call word_max image s e r.
Proof.
 intros NUM P ROOTS.
 pose proof (active_single_outer_depth image [] s e id ROOTS) as DEPTH.
 pose proof (numeric_pending word_max s (reservation_token true r) NUM P) as CERT.
 exists [Some id];split;[exact ROOTS|]. split;[cbn;lia|].
 intro table;apply (numeric_token_rehome word_max (reservation_token true r));[exact CERT|cbn;lia].
Qed.

Lemma boss_rehome_refusal_excluded word_max image s e r roots error table table' :
 boss_rehome_call word_max image s e r ->
 active_snapshot_roots (OpenBoundary image [] s) e=Some roots ->
 checked_rehome true word_max r (DeferredSnapshots.snapshot_owner roots) table=(Some error,table') -> False.
Proof.
 intros [actual [ROOTS [OWNER CHECK]]] EQ REFUSED.
 assert (roots=actual) by congruence;subst roots.
 rewrite CHECK in REFUSED;discriminate.
Qed.

(* Executed RAM prefix, using the same table and the existing snapshot API. *)
Definition rehome_cache_post word_max image s e r :=
 exists roots,
 active_snapshot_roots (OpenBoundary image [] s) e=Some roots /\
 let target:=DeferredSnapshots.snapshot_owner roots in
 let written:=snapshot_written s in
 let cached:=remember_recovered_boss pages r (snapshot_rehome target written) in
 snapshot_calls [SnapshotRehome target;SnapshotRemember pages] written /\
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
   snapshot_contract (snapshot_program [SnapshotRehome target;SnapshotRemember pages])) written tt cached /\
 data_invariant cached /\ state_numeric word_max cached /\
 pending_preparation cached=Some (set_phase (reservation_token true r) Detached) /\
 physical_authority cached=physical_authority s /\
 acknowledged_authority cached=acknowledged_authority s /\
 (forall q,owner (protection_table cached q)=
   if touches 256 r q then S target else owner (protection_table s q)) /\
 (forall q,validated (protection_table cached q)=
   validated (protection_table s q) ||
     ((offset r mod 256 =? 0) && (q =? offset r / 256) && (q <? pages) &&
       negb ((if touches 256 r q then S target else owner (protection_table s q)) =? 0))).

Lemma execute_written_rehome_cache word_max image s e r :
 data_invariant s -> state_numeric word_max s -> protection_frozen s=false ->
 pending_preparation s=Some (reservation_token true r) ->
 boss_rehome_call word_max image s e r ->
 rehome_cache_post word_max image s e r.
Proof.
 intros INV NUM FREE P [roots [ROOTS [OWNER CHECK]]].
 exists roots;split;[exact ROOTS|]. cbn zeta.
 assert (CALLS:snapshot_calls
   [SnapshotRehome (DeferredSnapshots.snapshot_owner roots);SnapshotRemember pages]
   (snapshot_written s)).
 { cbn [snapshot_calls snapshot_api_caller snapshot_api_update].
   unfold snapshot_written,snapshot_rehome;rewrite P;cbn.
   split.
   - split;[reflexivity|]. eexists;repeat split;try reflexivity;lia.
   - split;[|exact I]. split;[reflexivity|]. eexists;repeat split;reflexivity. }
 assert (RUN:post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
   snapshot_contract (snapshot_program [SnapshotRehome (DeferredSnapshots.snapshot_owner roots);SnapshotRemember pages]))
   (snapshot_written s) tt
   (remember_recovered_boss pages r (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))).
 { pose proof (snapshot_program_executes [SnapshotRehome (DeferredSnapshots.snapshot_owner roots);SnapshotRemember pages]
      (snapshot_written s)) as EXEC.
   cbn [snapshot_execute snapshot_api_update] in EXEC.
   unfold snapshot_written,snapshot_rehome in EXEC |- *. rewrite P in EXEC. rewrite P. exact EXEC. }
 split;[exact CALLS|]. split;[exact RUN|]. split.
 - eapply composed_snapshot_data_preserves;[|exact CALLS|exact RUN].
   eapply snapshot_written_preserves;[exact INV|exact FREE|exact P].
 - assert (NUMBER:state_numeric word_max
     (remember_recovered_boss pages r (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))).
   { unfold remember_recovered_boss,update_validation,snapshot_rehome,snapshot_written.
     rewrite P;cbn.
     unfold state_numeric,pending_ranges in NUM |- *;rewrite P in NUM;exact NUM. }
   split;[exact NUMBER|].
   unfold remember_recovered_boss,update_validation,snapshot_rehome,snapshot_written.
   rewrite P;cbn. repeat split;try reflexivity.
   + intro q;unfold ScopeOwnership.rehome_extent;destruct (touches 256 r q);reflexivity.
   + intro q;unfold ScopeOwnership.rehome_extent;destruct (touches 256 r q);reflexivity.
Qed.

Theorem installed_validation_cut_from_trace vi oi initial events valid view f h a id candidate s e
 cached observation prefix :
 Safe vi oi initial ->
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) ->
 boss_check_cut cached observation prefix ->
 Trace vi oi initial events valid view
   ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e) /\
 Safe valid view
   ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e) /\
 boundary_receipts ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e)=
   events++boundary_receipts initial.
Proof.
 intros INIT PREFIX CUT.
 assert (FULL:Trace vi oi initial events valid view
   ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   apply reset_episode;apply record_step;apply reset_ready. }
 split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT FULL) as [SAFE [RECEIPTS OTHER]].
 split;assumption.
Qed.

(* Local format service. The generated continuation below now derives its
   concrete cache argument and the preceding read_area/offset/latest guards;
   the provider still describes only format and crypto results. *)
Definition installed_boss_validation read f id encoded cached :=
 forall observe reply after,
 boss_check_provider read observe ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (boss_check_program id cached)) f reply after ->
 after=f /\
 (reply=BossCheckReady (counter_value encoded) \/
  reply=BossCheckFailed GenerationError \/
  (cached=false /\ reply=BossCheckFailed AuthenticationError)) /\
 (forall n,reply=BossCheckReady n ->
    n=counter_value encoded /\ validate after (N.of_nat id)=true).

Theorem installed_boss_validation_from_writer read f id decoded encoded cached :
 generation_decoding_matches sector decode read ->
 read f id=Some (decoded,encoded) ->
 installed_boss_validation read f id encoded cached.
Proof.
 intros MATCH READ observe reply after PROVIDER RUN.
 destruct (composed_boss_check read observe f id decoded encoded cached reply after
   PROVIDER READ RUN) as [FRAME OUTCOME].
 split;[exact FRAME|]. split;[exact OUTCOME|].
 intros n SUCCESS;split.
 - destruct OUTCOME as [YES|[NO|[_ NO]]];congruence.
 - rewrite FRAME. apply (ACCEPT f id decoded).
   rewrite <-MATCH,READ;reflexivity.
Qed.

(* The caller continues from FinishPublish already selected.  A restoration
   cut is a separate execution, never a normal reply to restore_probe. *)
Definition installed_validation_owner vi oi initial events valid view f h (a:list N) id
 (candidate:recovery_decoding) (ram:protection_state) (e:boundary_evidence) old word_max :=
 forall observe reason after reader inspect check outcome resolved (cut:option RestoreCut),
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (boss_check_program id true)) f (BossCheckFailed reason) after ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 (match cut with
  | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract (reader (object_flash sector after) old) inspect check) restore_probe) tt outcome tt
  | Some point=>restore_cut_reached (reader (object_flash sector after) old) inspect check point end) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view destination exit /\
 controller_result_post word_max vi oi initial events valid view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=after.

Lemma installed_validation_owner_from_trace vi oi initial events valid view f h a id candidate ram e old word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_rollback_context marker initial ->
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate ram),e) ->
 finish_selected (controller_read e)=Some FinishPublish -> owner_armed (controller_read e)=true ->
 outer_live (controller_read e)=true -> hd_error h=Some (N.of_nat old) -> id<>old ->
 installed_validation_owner vi oi initial events valid view f h a id candidate ram e old word_max.
Proof.
 intros MARK DEC WORD GEO INIT NUM CTX PATH ROUTE ARMED LIVE HEAD DISTINCT
   observe reason after reader inspect check outcome resolved cut CHECK MASK RESTORE.
 destruct cut as [point|].
 - destruct (boss_check_program_post _ _ _ _ _ _ CHECK) as [FRAME OBS];subst after.
   set (phase:=PublishingBoundary CandidatePrepared id candidate ram).
   set (taken:=controller_evidence TakeOuter phase e).
   assert (TAKE:Trace vi oi initial events valid view ((Logged (Ready f) h a,phase),taken)).
   { apply controller_from_trace;[exact PATH|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
   destruct (prepared_restore_cut_from_trace vi oi initial events valid view f h a id candidate ram taken old
     reader inspect check point INIT CTX TAKE HEAD DISTINCT RESTORE) as [CUT REST].
   set (last:=((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
   assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view last InterruptedReset).
   { exists valid,view,last,events,[];split;[exact CUT|].
     split;[apply operation_already_reset;reflexivity|reflexivity]. }
   exists last,InterruptedReset;split;[auto|]. split;[exact DONE|]. split.
   + exact (controller_finalization_from_trace vi oi initial events valid view last InterruptedReset word_max
       MARK DEC WORD GEO INIT NUM DONE).
   + split;reflexivity.
 - destruct (installed_validation_error_return vi oi initial events valid view f h a id candidate ram e old
     observe reason after reader inspect check outcome resolved word_max
     MARK DEC WORD GEO INIT NUM CTX PATH ROUTE ARMED LIVE HEAD DISTINCT CHECK MASK RESTORE)
     as [last [exit [KIND [DONE [POST JOURNAL]]]]].
   exists last,exit;split;[tauto|]. split;[exact DONE|]. split;[exact POST|].
   rewrite JOURNAL;split;reflexivity.
Qed.

(* The current address is the installed candidate even when the physical
   journal authority has changed.  The cut occurs after TakeOuter, before
   any close, collect, Drop or delivery. *)
Theorem controller_publication_restore_cut vi oi initial events valid view ready id d s e old error_j
 read inspect check point word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 finish_selected (controller_read e)=Some FinishPublish ->
 outer_live (controller_read e)=true ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 hd_error (publications ready)=Some (N.of_nat old) -> id<>old ->
 offset (recovered_boss d)=id ->
 clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) ready error_j ->
 returned_error_control (journal_control error_j) ->
 restore_cut_reached read inspect check point ->
 exists dest,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view dest InterruptedReset /\
 controller_result_post word_max vi oi initial events valid view dest /\
 boundary_journal dest=logged_after_reset error_j /\
 volatile_control (snd dest)=None /\
 (* The compared current/prestate addresses differ, so this is not the
    no-read path. Unknown legacy Frozen roots are not used here. *)
 root_address [recovered_boss d]<>Some old.
Proof.
 intros MARK DEC WORD GEO INIT NUM PREFIX ROUTE LIVE LOCAL HEAD DISTINCT CURRENT RUN ERROR CUT.
 set (ram:=uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s).
 set (phase:=FrozenBoundary (N.of_nat old) (N.of_nat id) (Some [recovered_boss d]) ram).
 assert (FAILED:Trace vi oi initial events valid view ((error_j,phase),e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   eapply fail_prepared with (commands:=[]);[exact LOCAL|exact HEAD|exact RUN|exact ERROR|exact I]. }
 set (taken:=controller_evidence TakeOuter phase e).
 assert (TAKE:Trace vi oi initial events valid view ((error_j,phase),taken)).
 { apply controller_from_trace;[exact FAILED|]. split;[rewrite ROUTE;discriminate|exact LIVE]. }
 set (dest:=((logged_after_reset error_j,RebuildingBoundary Selecting),forget_volatile_evidence taken)).
 assert (STEP:Step valid view ((error_j,phase),taken) None valid view dest).
 { apply reset_episode;apply returned_error_reset_step;exact ERROR. }
 pose proof (proj1 (completed_reset_from_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ _ _ _ _ TAKE STEP)) as DONE.
 exists dest;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
 split;[reflexivity|]. split;[reflexivity|]. unfold root_address;cbn;rewrite CURRENT;congruence.
Qed.

(* This continuation is enabled only by a successful executed local check.
   Journal and client services still supply their actual executions. *)
Definition validated_append_suffixes vi oi initial events valid view f h a id d s e (old:nat) word_max :=
 logged_invariant sector 256 data_len valid (Logged (Ready f) h a) /\
 (exists next,validated_append_entry sector data_len valid f (N.of_nat id)=Some next /\
   logged_step g sector 256 data_len valid (Logged (Ready f) h a) (Logged next h a)) /\
 exit_calls marker (root_extents (view id)) (List.hd [] (protection_saved s))
   [SlotCompleted;DurableRamWritten;ExternalAccepted] s /\
 collection_boundary view marker (Some id) (Some id) (object_extents (view id)) []
   (successful_external_close marker (root_extents (view id)) (List.hd [] (protection_saved s)) s) /\
 (forall out slot pubs acks,
   clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
   logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
     (Logged (Ready out) pubs (N.of_nat id::acks)) ->
   let synced_ram:=durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s) in
   let synced_evidence:=synchronize_publication (Logged (Ready out) pubs (N.of_nat id::acks))
     (Certificate id d) e in
   Safe valid view ((Logged (Ready out) pubs (N.of_nat id::acks),
     PublishingBoundary DurableSynchronized id d synced_ram),synced_evidence) /\
   volatile_latest_registry synced_evidence=Some id /\
   volatile_counter synced_evidence=read_counter (counter_decoder e) out id /\
   volatile_allocation synced_evidence=option_map (fun allocation=>AllocationRuntime (allocation_append allocation)
     (recovered_boss d)) (volatile_allocation e) /\
   client_receipts synced_evidence=client_receipts e /\
   (forall point,
     let reached:=runtime_sync_prefix point (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id d) e in
     let reset:=((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence reached) in
     completed_operation g sector data_len marker ranges decode topology pages
       vi oi initial events valid view reset InterruptedReset /\
     controller_result_post word_max vi oi initial events valid view reset /\
     boundary_receipts reset=events++boundary_receipts initial) /\
   (forall final (delivered:bool),
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
     (client_finish_contract view marker id (List.hd [] (protection_saved s)))
     (client_finish_program id (recovered_image d) [ExternalAccepted]))
     synced_ram (if delivered then ClientReturned (DataClientSuccess id (recovered_image d)) else ClientStopped) final ->
   let receipt:=Receipt (pred (length pubs)) (Certificate id d) in
   let dest:=if delivered then
     ((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id d final),
       deliver_published (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id d) (evidence_with_live synced_evidence [Certificate id d]))
     else ((Logged (Ready out) pubs (N.of_nat id::acks),FatalBoundary),forget_volatile_evidence e) in
   let observations:=if delivered then receipt::events else events in
   let exit:=if delivered then ReturnedPublished receipt else InterruptedFatal in
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial observations valid view dest exit /\
   controller_result_post word_max vi oi initial observations valid view dest)) /\
 (forall error_j read inspect check outcome,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j -> returned_error_control (journal_control error_j) ->
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt ->
   exists dest exit,(exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal) /\
   completed_operation g sector data_len marker ranges decode topology pages vi oi initial events valid view dest exit /\
   controller_result_post word_max vi oi initial events valid view dest /\
   publications (boundary_journal dest)=publications error_j /\
   exit=restoration_delivery_exit outcome) /\
 (forall cut,
   publication_reset_prefix g sector data_len valid (N.of_nat id) (Logged (Ready f) h a) cut ->
   let dest:=((cut,RebuildingBoundary Selecting),forget_volatile_evidence e) in
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view dest InterruptedReset /\
   controller_result_post word_max vi oi initial events valid view dest) /\
 (forall middle,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) middle ->
   logged_invariant sector 256 data_len valid middle /\ persistent_evidence sector view ranges decode middle e /\
   (hd_error (publications middle)=hd_error h \/ hd_error (publications middle)=Some (N.of_nat id)) /\
   acknowledgements middle=a) /\
 (forall out slot pubs acks,
   clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
   logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
     (Logged (Ready out) pubs (N.of_nat id::acks)) ->
   ((exists phases suffix partial,phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program phases)) s tt partial) \/
    (exists closed resolved partial,
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) s tt closed /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
       (client_finish_contract view marker id (List.hd [] (protection_saved s)))
       collection_service_prefix) closed resolved partial)) ->
   let dest:=((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence e) in
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view dest InterruptedReset /\
   controller_result_post word_max vi oi initial events valid view dest) /\
 (forall error_j read inspect check point,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j -> returned_error_control (journal_control error_j) ->
   restore_cut_reached read inspect check point ->
   exists dest,
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events valid view dest InterruptedReset /\
   controller_result_post word_max vi oi initial events valid view dest /\
   boundary_journal dest=logged_after_reset error_j /\ volatile_control (snd dest)=None).

Lemma validated_append_suffixes_from_trace vi oi initial events valid view f h a id d s e old word_max :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 external_structure marker initial ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id d s),e) ->
 finish_selected (controller_read e)=Some FinishPublish -> owner_armed (controller_read e)=true ->
 outer_live (controller_read e)=true -> hd_error h=Some (N.of_nat old) ->
 id<>old -> offset (recovered_boss d)=id -> candidate_valid 256 data_len valid (N.of_nat id) ->
 validated_append_suffixes vi oi initial events valid view f h a id d s e old word_max.
Proof.
 intros MARK DEC WORD GEO INIT NUM STRUCT PATH ROUTE ARM LIVE HEAD DISTINCT CURRENT CANDIDATE.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT PATH)) as SOURCE.
 pose proof (proj1 (proj1 SOURCE)) as JOURNAL.
 destruct (installed_exit_callers_from_trace _ _ _ _ _ _ _ _ _ _ _ INIT STRUCT PATH) as [CALL COLLECT].
 pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT STRUCT PATH) as [saved [STACK BASE]].
 split;[exact JOURNAL|]. split.
 - eapply validated_append_entry_step;eassumption.
 - split;[exact CALL|]. split;[exact COLLECT|]. split.
   + intros out slot pubs acks RUN ACK synced_ram synced_evidence.
     split.
     { eapply certified_runtime_sync;try eassumption;intros;apply READERS. }
     split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
     split.
     { intros point reached reset.
       destruct (append_runtime_cut_from_trace g sector data_len marker ranges decode topology pages G DIV
         vi oi initial events valid view (Logged (Ready f) h a) id d s e saved out slot pubs acks point
         INIT PATH ltac:(intros;apply READERS) STACK BASE RUN ACK)
         as [CUT [SAFE_CUT [HEAD_CUT [RECEIPTS_CUT REST]]]].
       assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
         vi oi initial events valid view reset InterruptedReset).
       { exists valid,view,reset,events,[];split;[exact CUT|].
         split;[apply operation_already_reset;reflexivity|reflexivity]. }
       split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|exact RECEIPTS_CUT]. }
     intros final delivered SUFFIX receipt dest observations exit.
     pose proof (client_finish_from_runtime view marker id (recovered_image d)
       (List.hd [] (protection_saved s)) s _ final CALL SUFFIX) as FINISH.
     assert (STEP:Step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id d s),e)
       (if delivered then Some receipt else None) valid view dest).
     { destruct delivered;cbn [dest].
       - eapply return_prepared with (saved:=saved);try eassumption;
           try (intros;apply READERS);try (rewrite STACK in FINISH;cbn in FINISH;exact FINISH).
       - eapply stop_prepared with (saved:=saved);try eassumption;
           try (intros;apply READERS);try (rewrite STACK in FINISH;cbn in FINISH;exact FINISH). }
     assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
       vi oi initial observations valid view dest exit).
     { exists valid,view,((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id d s),e),events,
         (if delivered then [receipt] else []).
       split;[exact PATH|]. split.
       - destruct delivered.
         + eapply operation_end with (event:=Some receipt);[exact STEP|reflexivity].
         + eapply operation_end with (event:=None);[exact STEP|reflexivity].
       - destruct delivered;reflexivity. }
     split;[exact DONE|]. eapply controller_finalization_from_trace;eassumption.
   + split.
     * intros error_j read inspect check outcome RUN ERROR RESTORE.
       eapply controller_publication_error_return;try eassumption;intros;apply READERS.
     * split.
       -- intros cut CUT dest.
          assert (STEP:Step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id d s),e)
            None valid view dest).
          { apply cut_prepared;[intros;apply READERS|exact CUT]. }
          pose proof (proj1 (completed_reset_from_trace g sector data_len marker ranges decode topology pages
            _ _ _ _ _ _ _ _ _ _ _ _ PATH STEP)) as DONE.
          split;[exact DONE|]. eapply controller_finalization_from_trace;eassumption.
       -- split.
          ++ intros middle RUN;exact (installed_publication_prefix_from_trace vi oi initial events valid view
               (Logged (Ready f) h a) id d s e middle INIT PATH RUN).
          ++ split.
             ** intros out slot pubs acks RUN ACK CUT dest.
             assert (STEP:Step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id d s),e)
               None valid view dest).
             { destruct CUT as [[phases [suffix [partial [PREFIX FINISH]]]]|[closed [resolved [partial [CLOSE COLLECT_RUN]]]]].
               - eapply cut_exit_prepared with (saved:=saved) (phases:=phases) (suffix:=suffix) (partial:=partial);
                   try eassumption;try (intros;apply READERS);
                   try (rewrite STACK in FINISH;cbn in FINISH;exact FINISH).
               - eapply cut_collection_prepared with (saved:=saved) (closed:=closed) (resolved:=resolved) (partial:=partial);
                   try eassumption;try (intros;apply READERS);
                   try (rewrite STACK in CLOSE;cbn in CLOSE;exact CLOSE);
                   try (rewrite STACK in COLLECT_RUN;cbn in COLLECT_RUN;exact COLLECT_RUN). }
             pose proof (proj1 (completed_reset_from_trace g sector data_len marker ranges decode topology pages
               _ _ _ _ _ _ _ _ _ _ _ _ PATH STEP)) as DONE.
             split;[exact DONE|]. eapply controller_finalization_from_trace;eassumption.

             ** intros error_j read inspect check point RUN ERROR CUT.
                destruct (controller_publication_restore_cut vi oi initial events valid view
                  (Logged (Ready f) h a) id d s e old error_j read inspect check point word_max
                  MARK DEC WORD GEO INIT NUM PATH ROUTE LIVE ltac:(intros;apply READERS)
                  HEAD DISTINCT CURRENT RUN ERROR CUT) as [dest [DONE [POST [RESET_JOURNAL [CONTROL GUARD]]]]].
                exists dest;split;[exact DONE|]. split;[exact POST|]. split;assumption.
Qed.

(* Finalization already selected: the frozen writer has dropped its handle,
   but its pages remain retained. This is not the body-error route. *)
Theorem selected_frozen_writer_return vi oi initial events vf view f h a old ram ev
 word_max read inspect check outcome (cut:option RestoreCut) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 (exists saved,protection_saved ram=[saved]) ->
 Trace vi oi initial events vf view
   ((Logged (Ready f) h a,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some []) ram),ev) ->
 finish_selected (controller_read ev)=Some FinishPublish ->
 owner_armed (controller_read ev)=true -> outer_live (controller_read ev)=true ->
 pending_preparation ram=None ->
 (match cut with Some point=>restore_cut_reached read inspect check point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt end) ->
 exists destination exit,
 (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events vf view destination exit /\
 controller_result_post word_max vi oi initial events vf view destination /\
 publications (boundary_journal destination)=h /\
 control_image (journal_control (boundary_journal destination))=f.
Proof.
 intros MARK DEC WORD GEO INIT NUM STRUCT FAILED ROUTE ARMED LIVE P RESTORE.
 destruct STRUCT as [saved STACK].
 set (j:=Logged (Ready f) h a).
 set (phase:=FrozenBoundary (N.of_nat old) (N.of_nat old) (Some []) ram).
 set (taken:=controller_evidence TakeOuter phase ev).
 assert (TAKE:Trace vi oi initial events vf view ((j,phase),taken)).
 { apply controller_from_trace;[exact FAILED|].
   split;autorewrite with control_evidence;[rewrite ROUTE;discriminate|exact LIVE]. }
 assert (ARM:owner_armed (controller_read taken)=true).
 { unfold taken;autorewrite with control_evidence;exact ARMED. }
 assert (SELECTED:finish_selected (controller_read taken)=Some FinishPublish).
 { unfold taken;autorewrite with control_evidence;exact ROUTE. }
 destruct cut as [point|].
 - destruct (owned_reset_after_prefix vi oi initial events vf view (f) h a phase taken word_max
     MARK DEC WORD GEO INIT NUM TAKE) as [COMPLETE POST].
   eexists _,InterruptedReset;split;[tauto|]. split;[exact COMPLETE|].
   split;[exact POST|]. split;reflexivity.
 - assert (ENDING:exists before,
     Trace vi oi initial events vf view before /\
     ordinary_return_ready FinishPublish before /\
     boundary_journal before=j).
   { destruct (RestoreObservation_eq_dec outcome RestoreValidated) as [OK|BAD].
     - subst outcome.
       set (closed:=data_next (DataClose [] saved false) ram).
       set (last:=FrozenBoundary (N.of_nat old) (N.of_nat old) None closed).
       assert (CLOSE:Trace vi oi initial events vf view ((j,last),taken)).
       { eapply episodes_append with (more:=[]);[exact TAKE|].
         eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
         eapply frozen_scope_close;[|exact RESTORE].
         change (pending_preparation ram=None /\ protection_saved ram=[]++[saved]);auto. }
       set (done:=controller_evidence DropOwner last taken).
       assert (DROP:Trace vi oi initial events vf view ((j,last),done)).
       { apply controller_from_trace;[exact CLOSE|].
         split;[exact ARM|reflexivity]. }
       exists ((j,last),done);split;[exact DROP|].
       split;[|reflexivity].
       change (owner_armed (controller_read done)=false /\ outer_live (controller_read done)=false /\
         finish_selected (controller_read done)=Some FinishPublish).
       unfold done;autorewrite with control_evidence;auto.
     - assert (STOP:Trace vi oi initial events vf view ((j,FatalBoundary),forget_volatile_evidence taken)).
       { eapply episodes_append with (more:=[]);[exact TAKE|].
         eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
         eapply frozen_scope_stop;eassumption. }
       exists ((j,FatalBoundary),forget_volatile_evidence taken);split;[exact STOP|].
       split;reflexivity. }
   destruct ENDING as [before [PATH [READY JOURNAL]]].
   destruct (deliver_ready_execution FinishPublish vf view before READY)
     as [destination [exit [DELIVERY [KIND [SAME RECEIPTS]]]]].
   assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events vf view destination exit).
   { exists vf,view,before,events,[];split;[exact PATH|]. split;[exact DELIVERY|reflexivity]. }
   exists destination,exit;split;[tauto|]. split;[exact COMPLETE|]. split.
   + eapply controller_finalization_from_trace;eauto.
   + assert (J:boundary_journal destination=j).
     { unfold boundary_journal in *;rewrite SAME;exact JOURNAL. }
     rewrite J;split;reflexivity.
Qed.

(* The plan argument is selected by checked_add, not by a writer caller. The
   same pending token from either acquisition origin is consumed exactly once. *)
Definition generated_writer_continuation vi oi initial events (valid:N->bool) view f h a old image s e counter r word_max :=
 forall encode plan result,
 boss_generation_format g sector encode (counter_decoder e) ->
 checked_boss_plan encode image counter r=Some plan ->
 writer_execution g sector r true f plan result ->
 exists previous,
 let destination:=(writer_exit_boundary old image [] s h a result,
   phase_evidence (snd (writer_exit_boundary old image [] s h a result)) (selected_evidence old previous e)) in
 Trace vi oi initial events (validate (writer_flash result)) view destination /\
 Safe (validate (writer_flash result)) view destination /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=events++boundary_receipts initial /\
 volatile_counter (snd destination)=
   (match writer_end result with WriterInterrupted=>None | _=>Some counter end) /\
 (writer_end result=WriterInterrupted ->
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (writer_flash result)) view destination InterruptedReset /\
   controller_result_post word_max vi oi initial events (validate (writer_flash result)) view destination /\
   exit_observation InterruptedReset=None) /\
 (* A returned local writer error is already after FinishPublish.  Its
    cleanup consumed the pending token; restoration is executed on reached
    flash, without selecting finalization or acquiring again. *)
 ((writer_end result=WriterLocalError \/ writer_end result=WriterRetainError) ->
   forall rd ins chk observed resolved (cut:option RestoreCut),
   (match cut with Some point=>restore_cut_reached rd ins chk point
    | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
   (forall mask,resolved=Some mask ->
      mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
   exists returned exit,
   (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (writer_flash result)) view returned exit /\
   controller_result_post word_max vi oi initial events (validate (writer_flash result)) view returned /\
   publications (boundary_journal returned)=h /\
   control_image (journal_control (boundary_journal returned))=writer_flash result) /\
 (writer_end result=WriterPhysicalError ->
   forall rd ins chk observed (cut:option RestoreCut),
   (match cut with Some point=>restore_cut_reached rd ins chk point
    | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
   exists returned exit,
   (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
   completed_operation g sector data_len marker ranges decode topology pages
     vi oi initial events (validate (writer_flash result)) view returned exit /\
   controller_result_post word_max vi oi initial events (validate (writer_flash result)) view returned /\
   publications (boundary_journal returned)=h /\
   control_image (journal_control (boundary_journal returned))=writer_flash result) /\
 exists next,
 boss_checked_generation (counter_value counter)=Some next /\
 next=N.succ (counter_value counter) /\ plan=encode image next r /\
 (exists suffix,plan=map fst (writer_prefix result)++suffix) /\
 terminal_prefix (writer_prefix result) /\
 (writer_end result=WriterComplete -> exists decoded n,
   counter_decoder e (writer_flash result) (offset r)=Some (decoded,n) /\
   recovered_boss decoded=r /\ recovered_image decoded=image /\ counter_value n=next) /\
 (writer_end result=WriterComplete ->
   rehome_cache_post word_max image s e r /\
   exists target,
   target=length (protection_saved s) /\
   Trace vi oi initial events (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,
       OpenBoundary image []
         (remember_recovered_boss pages r (snapshot_rehome target (snapshot_written s)))),
       selected_evidence old previous e) /\
   Safe (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,
       OpenBoundary image []
         (remember_recovered_boss pages r (snapshot_rehome target (snapshot_written s)))),
       selected_evidence old previous e) /\
   let after_setter := image_generation_set next
     (remember_recovered_boss pages r (snapshot_rehome target (snapshot_written s))) in
   Trace vi oi initial events (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,OpenBoundary image [] after_setter),
       selected_evidence old previous e) /\
   Safe (validate (writer_flash result)) view
     ((Logged (Ready (writer_flash result)) h a,OpenBoundary image [] after_setter),
       selected_evidence old previous e) /\
   protection_image_generation after_setter=Some next /\
   Trace vi oi initial events (validate (writer_flash result)) view
     ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
       forget_volatile_evidence (selected_evidence old previous e)) /\
   forall base checked, mapped_registry_base base ->
   exists decoded raw encoded,
     rust_absolute_address checked base (offset r)=Some (Some raw) /\
     (raw-base=N.of_nat (offset r))%N /\
     let installed:=((Logged (Ready (writer_flash result)) h a,
       PublishingBoundary CandidatePrepared (offset r) decoded
         (install_candidate_observed after_setter)),
       evidence_with_live (selected_evidence old previous e)
         [Certificate old previous;Certificate (offset r) decoded]) in
     Trace vi oi initial events (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded) installed /\
     Safe (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded) installed /\
     counter_decoder e (writer_flash result) (offset r)=Some (decoded,encoded) /\
     counter_value encoded=next /\
     recovered_boss decoded=r /\ recovered_image decoded=image /\
     protection_image_generation (install_candidate_observed after_setter)=Some next /\
     volatile_counter (snd installed)=Some counter /\
     publications (boundary_journal installed)=h /\
     boundary_receipts installed=boundary_receipts destination /\
     pending_preparation (install_candidate_observed after_setter)=None /\
     In r (protection_current (install_candidate_observed after_setter)) /\
     offset r<>old /\
     Trace vi oi initial events (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded)
       ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
         forget_volatile_evidence (snd installed)) /\
     volatile_latest_registry (snd installed)=Some old /\
     preappend_gate base pages raw (volatile_latest_registry (snd installed))=
       EnterBossCheck (N.of_nat (offset r)) /\
     xip_authenticated base pages (offset r) raw
       (protection_table (install_candidate_observed after_setter))=true /\
     installed_boss_validation (counter_decoder e) (writer_flash result) (offset r) encoded
       (xip_authenticated base pages (offset r) raw
         (protection_table (install_candidate_observed after_setter))) /\
     installed_validation_owner vi oi initial events (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded) (writer_flash result) h a
       (offset r) decoded (install_candidate_observed after_setter) (snd installed) old word_max /\
     (forall observe n after,
       boss_check_provider (counter_decoder e) observe ->
       post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
         (boss_check_contract observe) (boss_check_program (offset r)
           (xip_authenticated base pages (offset r) raw
             (protection_table (install_candidate_observed after_setter)))))
         (writer_flash result) (BossCheckReady n) after ->
       after=writer_flash result /\ n=next /\
       candidate_valid 256 data_len (validate after) (N.of_nat (offset r)) /\
       validated_append_suffixes vi oi initial events (validate after)
         (install_decoded_view view ranges (offset r) decoded) after h a (offset r) decoded
         (install_candidate_observed after_setter) (snd installed) old word_max) /\
     (forall observe prefix, boss_check_cut true (observe (writer_flash result) (offset r)) prefix ->
       Trace vi oi initial events (validate (writer_flash result))
         (install_decoded_view view ranges (offset r) decoded)
         ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
           forget_volatile_evidence (snd installed)) /\
       Safe (validate (writer_flash result)) (install_decoded_view view ranges (offset r) decoded)
         ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
           forget_volatile_evidence (snd installed)) /\
       boundary_receipts ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
           forget_volatile_evidence (snd installed))=events++boundary_receipts initial)).

Theorem generated_pending_writer_from_trace vi oi initial events valid view f h a old image s e counter r word_max :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 external_structure marker initial ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 phase_numeric word_max marker ranges (snd (fst initial)) -> external_rollback_context marker initial ->
 finish_selected (controller_read e)=Some FinishPublish -> owner_armed (controller_read e)=true ->
 outer_live (controller_read e)=true ->
 generation_decoding_matches sector decode (counter_decoder e) ->
 decoding_address_contract decode ->
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) ->
 hd_error h=Some (N.of_nat old) ->
 reservation_handoff sector f s (reservation_token true r) ->
 volatile_counter e=Some counter ->
 state_numeric word_max s -> boss_rehome_call word_max image s e r ->
 volatile_latest_registry e=Some old -> mapped_pages pages ->
 offset r mod 256=0 -> span r mod 256=0 -> offset r+span r<=pages*256 ->
 generated_writer_continuation vi oi initial events valid view f h a old image s e counter r word_max.
Proof.
 intros MARKER_HEADER OBJECT_MAPPING STRUCT MARK DEC WORD GEO INITIAL_NUM CTX ROUTE ARMED OUTERLIVE MATCH ADDRESS INIT RAW PREFIX HEAD HANDOFF VALUE NUM REHOME LATEST PAGES ALIGNED SPAN_ALIGNED MAPPED encode plan result FORMAT PLAN RUN.
 pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 pose proof (proj2 (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT RAW PREFIX)) as ORDER.
 destruct ((proj1 (proj2 (proj1 (proj2 SOURCE)))) old HEAD) as [[id previous] [LIVE ID]].
 cbn in ID;subst id.
 assert (STEP:Step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None
   (validate (writer_flash result)) view
   (writer_exit_boundary old image [] s h a result,
    phase_evidence (snd (writer_exit_boundary old image [] s h a result)) (selected_evidence old previous e))).
 { eapply consume_pending with (p:=reservation_token true r) (boss:=true);
     [exact ORDER|exact HEAD|exact LIVE|apply READERS|exact ACCEPT| |reflexivity].
   split;[exact HANDOFF|exact RUN]. }
 assert (FULL:Trace vi oi initial events (validate (writer_flash result)) view
   (writer_exit_boundary old image [] s h a result,
    phase_evidence (snd (writer_exit_boundary old image [] s h a result)) (selected_evidence old previous e))).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[exact STEP|constructor]. }
 exists previous;split;[exact FULL|].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
   G DIV _ _ _ _ _ _ _ INIT FULL) as [SAFE [RECEIPTS REST]].
 split;[exact SAFE|]. split.
 - unfold boundary_journal,writer_exit_boundary;destruct (writer_end result);reflexivity.
 - split;[exact RECEIPTS|]. split.
   + unfold writer_exit_boundary;destruct (writer_end result);cbn;try exact VALUE;reflexivity.
   + split.
     { intro CUT.
       assert (STOP:operation_execution g sector data_len marker ranges decode topology pages
         valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) []
         (validate (writer_flash result)) view
         (writer_exit_boundary old image [] s h a result,
          phase_evidence (snd (writer_exit_boundary old image [] s h a result))
            (selected_evidence old previous e)) InterruptedReset).
       { apply operation_end with (event:=None);[exact STEP|].
         unfold writer_exit_boundary;rewrite CUT;reflexivity. }
       assert (COMPLETE:completed_operation g sector data_len marker ranges decode topology pages
         vi oi initial events (validate (writer_flash result)) view
         (writer_exit_boundary old image [] s h a result,
          phase_evidence (snd (writer_exit_boundary old image [] s h a result))
            (selected_evidence old previous e)) InterruptedReset).
       { exists valid,view,((Logged (Ready f) h a,OpenBoundary image [] s),e),events,[];
         split;[exact PREFIX|]. split;[exact STOP|reflexivity]. }
       split;[exact COMPLETE|]. split;[|reflexivity].
       eapply controller_finalization_from_trace;eassumption. }
     split.
     { intros ERROR rd ins chk observed resolved cut RESTORE MASK.
       set (cleaned:=preparation_error_state (writer_end result) s).
       assert (CLEAN:Trace vi oi initial events (validate (writer_flash result)) view
         ((Logged (Ready (writer_flash result)) h a,OpenBoundary image [] cleaned),
           selected_evidence old previous e)).
       { destruct ERROR as [E|E];unfold writer_exit_boundary in FULL;rewrite E in FULL;
         unfold cleaned,preparation_error_state;rewrite E;exact FULL. }
       assert (PN:pending_preparation cleaned=None).
       { unfold cleaned;destruct ERROR as [E|E];rewrite E;reflexivity. }
       eapply selected_preallocation_error_return;try eassumption;
         autorewrite with control_evidence;assumption. }
     split.
     { intros ERROR rd ins chk observed cut RESTORE.
       assert (FAILED:Trace vi oi initial events (validate (writer_flash result)) view
         ((Logged (Ready (writer_flash result)) h a,
           FrozenBoundary (N.of_nat old) (N.of_nat old) (Some []) (snapshot_error true s)),
           selected_evidence old previous e)).
       { unfold writer_exit_boundary in FULL;rewrite ERROR in FULL;exact FULL. }
       assert (STACK:exists saved,protection_saved (snapshot_error true s)=[saved]).
       { destruct (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
           _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [saved [SAVED BASE]].
         exists saved;change (protection_saved s=[saved]);exact SAVED. }
       eapply selected_frozen_writer_return;try eassumption;
         try (autorewrite with control_evidence;assumption).
       reflexivity. }
     destruct (checked_boss_plan_writer g sector encode (counter_decoder e) image counter r f plan result
       FORMAT PLAN (proj2 HANDOFF) RUN) as [next [N [SUCCESS [ENCODE [COMMANDS [PREFIX_OK DECODED]]]]]].
     exists next;split;[exact N|]. split;[exact SUCCESS|]. split;[exact ENCODE|].
     split;[exact COMMANDS|]. split;[exact PREFIX_OK|]. split;[exact DECODED|].
     intro COMPLETE.
     assert (LOCAL:rehome_cache_post word_max image s e r).
     { apply execute_written_rehome_cache;try assumption.
       - exact (proj1 (proj2 (proj1 SOURCE))).
       - exact (proj1 (proj2 (proj2 (proj1 SOURCE)))).
       - exact (proj1 HANDOFF). }
     split;[exact LOCAL|].
     destruct REHOME as [roots [ROOTS [OWNER CHECK]]].
     exists (DeferredSnapshots.snapshot_owner roots);split;[exact OWNER|].
     unfold writer_exit_boundary in FULL;rewrite COMPLETE in FULL;cbn in FULL.
     assert (CACHE_STEP:Step (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image [] (snapshot_written s)),
          selected_evidence old previous e) None (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))),
          selected_evidence old previous e)).
     { apply prepared_rehome_cache_post with
       (p:=set_phase (reservation_token true r) Written)
       (lifetime:=DeferredSnapshots.snapshot_owner roots).
     * unfold snapshot_written;rewrite (proj1 HANDOFF);reflexivity.
     * reflexivity.
     * reflexivity.
     * unfold snapshot_written;rewrite (proj1 HANDOFF);cbn;rewrite OWNER;lia.
     * destruct LOCAL as [rs [RS [CALLS [EXEC CACHE_FACTS]]]].
       assert (EQ:rs=roots) by congruence;subst rs;exact EXEC. }
     assert (CACHED:Trace vi oi initial events (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))),
          selected_evidence old previous e)).
     { eapply episodes_append with (more:=[]);[exact FULL|].
       eapply episodes_cons with (event:=None) (events:=[]);[exact CACHE_STEP|constructor]. }
     unfold writer_exit_boundary in SAFE;rewrite COMPLETE in SAFE.
     pose proof (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
         G DIV _ _ _ _ _ _ _ SAFE CACHE_STEP)) as CACHE_SAFE.
     split;[exact CACHED|]. split;[exact CACHE_SAFE|].
     cbn zeta.
     destruct (DECODED COMPLETE) as [decoded [encoded [READ [BOSS [IMAGE GENERATION]]]]].
     assert (SETTER:Step (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))),
          selected_evidence old previous e) None (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (image_generation_set next (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s))))),
          selected_evidence old previous e)).
     { eapply prepared_image_setter with (p:=set_phase (reservation_token true r) Detached)
         (counter:=counter) (decoded:=decoded) (encoded:=encoded);try eassumption;try reflexivity.
       - unfold remember_recovered_boss,update_validation,snapshot_rehome,snapshot_written.
         rewrite (proj1 HANDOFF);reflexivity. }
     assert (SET_PATH:Trace vi oi initial events (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (image_generation_set next (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s))))),
          selected_evidence old previous e)).
     { eapply episodes_append with (more:=[]);[exact CACHED|].
       eapply episodes_cons with (event:=None) (events:=[]);[exact SETTER|constructor]. }
     split;[exact SET_PATH|].
     split;[exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
         G DIV _ _ _ _ _ _ _ CACHE_SAFE SETTER))|].
     split;[reflexivity|].
     split.
     { eapply episodes_append with (more:=[]);[exact SET_PATH|].
       eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
       apply reset_episode;apply record_step;apply reset_ready. }
     intros base checked CONFIG.
     assert (RANGE:range_numeric word_max r).
     { unfold state_numeric in NUM.
       destruct NUM as [_ [_ [_ [_ [_ [_ PENDING]]]]]].
       unfold pending_ranges in PENDING;rewrite (proj1 HANDOFF) in PENDING.
       exact (Forall_inv PENDING). }
     destruct (rust_absolute_address_success checked base (offset r) CONFIG
       (range_numeric_offset word_max r RANGE)) as [ABS RELATIVE].
     exists decoded,(base+N.of_nat (offset r))%N,encoded.
     split;[exact ABS|]. split;[exact RELATIVE|]. cbn zeta.
     assert (DECODE:decode (object_flash sector (writer_flash result)) (offset r)=Some decoded).
     { rewrite <-MATCH,READ;reflexivity. }
     assert (INSTALL:Step (validate (writer_flash result)) view
       ((Logged (Ready (writer_flash result)) h a,OpenBoundary image []
         (image_generation_set next (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s))))),
          selected_evidence old previous e) None (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded)
       ((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared (offset r) decoded
         (install_candidate_observed (image_generation_set next (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))))),
         evidence_with_live (selected_evidence old previous e)
           [Certificate old previous;Certificate (offset r) decoded])).
     { eapply install_detached_address with (p:=set_phase (reservation_token true r) Detached)
         (base:=base) (checked:=checked) (raw:=(base+N.of_nat (offset r))%N);
         try eassumption;try reflexivity.
       - simpl;auto.
       - unfold image_generation_set,image_generation_observe;cbn [pending_preparation].
         unfold remember_recovered_boss,update_validation,snapshot_rehome,snapshot_written.
         rewrite (proj1 HANDOFF);reflexivity. }
     assert (SET_SAFE:=proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
       G DIV _ _ _ _ _ _ _ CACHE_SAFE SETTER)).
     assert (INSTALLED_PATH:Trace vi oi initial events (validate (writer_flash result))
       (install_decoded_view view ranges (offset r) decoded)
       ((Logged (Ready (writer_flash result)) h a,PublishingBoundary CandidatePrepared (offset r) decoded
         (install_candidate_observed (image_generation_set next (remember_recovered_boss pages r
           (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s)))))),
         evidence_with_live (selected_evidence old previous e)
           [Certificate old previous;Certificate (offset r) decoded])).
     { eapply episodes_append with (more:=[]);[exact SET_PATH|].
       eapply episodes_cons with (event:=None) (events:=[]);[exact INSTALL|constructor]. }
     split;[exact INSTALLED_PATH|].
     split;[exact (proj1 (episode_step_safe g sector data_len marker ranges decode topology pages
       G DIV _ _ _ _ _ _ _ SET_SAFE INSTALL))|].
     split;[exact READ|]. split;[exact GENERATION|].
     split;[exact BOSS|]. split;[exact IMAGE|].
     split;[reflexivity|]. split;[exact VALUE|]. split;[reflexivity|].
     split.
     { unfold boundary_receipts,phase_evidence,writer_exit_boundary;rewrite COMPLETE;reflexivity. }
     assert (PENDING:pending_preparation
       (image_generation_set next (remember_recovered_boss pages r
         (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s))))=
       Some (set_phase (reservation_token true r) Detached)).
     { unfold image_generation_set,image_generation_observe;cbn [pending_preparation].
       unfold remember_recovered_boss,update_validation,snapshot_rehome,snapshot_written.
       rewrite (proj1 HANDOFF);reflexivity. }
     destruct (detached_installation_transfer _ _ PENDING) as [EMPTY [ROOT TRANSFER_FRAME]].
     split;[exact EMPTY|]. split;[exact ROOT|].
     assert (DISTINCT:offset r<>old).
     { eapply reserved_decoded_candidate_distinct;try exact SET_SAFE;try eassumption.
       simpl;auto. }
     split;[exact DISTINCT|].
     split.
     - eapply episodes_append with (more:=[]);[exact INSTALLED_PATH|].
       eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
       apply reset_episode;apply record_step;apply reset_ready.
     - split;[exact LATEST|].
       assert (POS:0<span r).
       { pose proof (ADDRESS _ _ _ DECODE) as CONTAINS.
         rewrite BOSS in CONTAINS;unfold contains in CONTAINS;lia. }
       assert (HEADER:offset r+32<=pages*256).
       { pose proof (Nat.div_mod (span r) 256 ltac:(lia)) as SIZE.
         rewrite SPAN_ALIGNED in SIZE;nia. }
       split.
       { cbn [snd evidence_with_live selected_evidence volatile_latest_registry].
         rewrite LATEST;apply prepared_preappend_gate;assumption. }
       assert (HIT:xip_authenticated base pages (offset r) (base+N.of_nat (offset r))
         (protection_table (install_candidate_observed (image_generation_set next
           (remember_recovered_boss pages r
             (snapshot_rehome (DeferredSnapshots.snapshot_owner roots) (snapshot_written s))))))=true).
       { eapply remembered_installed_cache_hit with
           (p:=set_phase (reservation_token true r) Written).
         - exact CONFIG.
         - exact PAGES.
         - unfold snapshot_written;rewrite (proj1 HANDOFF);reflexivity.
         - reflexivity.
         - exact ALIGNED.
         - exact POS.
         - apply Nat.div_lt_upper_bound;lia. }
       split;[exact HIT|].
       split;[exact (installed_boss_validation_from_writer _ _ _ _ _ _ MATCH READ)|].
       split.
       + eapply installed_validation_owner_from_trace;try eassumption;
           autorewrite with control_evidence;assumption.
       + split.
         * intros observe n after PROVIDER CHECK_RUN.
           pose proof (installed_boss_validation_from_writer _ _ _ _ _ _ MATCH READ
             observe (BossCheckReady n) after PROVIDER CHECK_RUN) as [FRAME [OUTCOME RESULT]].
           destruct (RESULT n eq_refl) as [GEN VALIDATE].
           split;[exact FRAME|]. split;[congruence|].
           assert (LOW:256<=offset r).
           { pose proof (episode_trace_external_structure g sector data_len marker ranges decode topology pages
               G DIV _ _ _ _ _ _ _ INIT STRUCT PREFIX) as [scope [STACK BASE]].
             eapply (reserved_boss_after_marker marker s (reservation_token true r));
               try exact (proj1 (proj2 (proj1 SOURCE)));try exact BASE;try exact MARKER_HEADER;
               try exact (proj1 HANDOFF);assumption. }
           assert (CANDIDATE:candidate_valid 256 data_len (validate after) (N.of_nat (offset r))).
           { eapply acquired_validated_candidate;eassumption. }
           split;[exact CANDIDATE|]. subst after.
           eapply validated_append_suffixes_from_trace;try eassumption;
             autorewrite with control_evidence;try assumption;rewrite BOSS;reflexivity.
         * intros observe prefix CUT;eapply installed_validation_cut_from_trace;eassumption.

Qed.

(* Uniform weak simulation of the RAM-only interval, consumed by both BOSS
   acquisitions below. ReservationDone is an abstract representative only;
   the concrete point is retained in the reset projection. *)
Lemma boss_acquisition_ram_cut vi oi initial events valid view f h a image s e r boss word_max point :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial events valid view
   ((Logged (Ready f) h a,OpenBoundary image [] (reservation_state boss r s)),advance_allocation_evidence r e) ->
 let dest:=acquisition_ram_reset point boss r s e (Logged (Ready f) h a) in
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial events valid view dest InterruptedReset /\
 controller_result_post word_max vi oi initial events valid view dest /\
 boundary_receipts dest=events++boundary_receipts initial.
Proof.
 intros MARK DEC WORD GEO INIT NUM PREFIX dest.
 assert (STEP:Step valid view
   ((Logged (Ready f) h a,OpenBoundary image [] (reservation_state boss r s)),advance_allocation_evidence r e)
   None valid view dest).
 { unfold dest;rewrite acquisition_ram_reset_same.
   eapply reset_episode with (e:=advance_allocation_evidence r e);apply record_step;apply reset_ready. }
 pose proof (proj1 (completed_reset_from_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ _ _ _ _ PREFIX STEP)) as DONE.
 split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
 exact (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT (completed_operation_trace g sector data_len marker ranges decode topology pages
     _ _ _ _ _ _ _ _ DONE)))).
Qed.

(* Acquisition and owner continuations from the marked BOSS entry. Runtime
   search arguments and their geometry come from the initial decoded range
   and the single global trace, including historical producers. *)
(* Size-indexed executions of the existing acquisition services. These expose
   their actual arguments; no destination invariant is part of admission. *)
Local Notation boss_search_inputs := (boss_search_inputs sector pages).
Lemma boss_search_inputs_runtime word_max total e s f req start :
 boss_search_inputs word_max total e s f req start ->
 runtime_search_inputs sector pages word_max e s f req start.
Proof. intros [a [OBS [PROBE [REQ START]]]];exists a,(fun _=>Some total);auto. Qed.
Local Notation boss_erased_admission := (boss_erased_admission sector pages).
Lemma boss_erased_admission_runtime word_max total e s f r :
 boss_erased_admission word_max total e s f r ->
 runtime_erased_admission sector pages e s f r.
Proof.
 intros [[a [final [OBS [PROBE SIZE]]]]|[fuel [recognize [req [round [alignment [start [i [n [INPUT [SEARCH [R SIZE]]]]]]]]]]]].
 - eapply runtime_cursor;eassumption.
 - eapply runtime_search;try eassumption;eapply boss_search_inputs_runtime;exact INPUT.
Qed.

(* Only executions of existing local services are packaged here. No final
   boundary, invariant, selected observation or safe continuation is an input. *)
Lemma completed_no_receipts vi oi initial valid view final exit :
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial [] valid view final exit -> delivered_receipts exit=[].
Proof.
 intros [vm [om [before [previous [returned [PREFIX [RUN EQ]]]]]]].
 symmetry in EQ;apply app_eq_nil in EQ;destruct EQ as [EMPTY _].
 pose proof (operation_execution_receipts g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ RUN) as RECEIPTS.
 unfold delivered_receipts;rewrite <-RECEIPTS;exact EMPTY.
Qed.
Definition owner_terminal_erased word_max vi oi initial before :=
 exists receipts vf of_ final exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts vf of_ final exit /\
 controller_result_post word_max vi oi initial receipts vf of_ final /\
 receipts=delivered_receipts exit++before.

Definition append_exit_matches kind exit :=
 match kind with
 | AppendClient true=>exists receipt,exit=ReturnedPublished receipt
 | AppendClient false=>exit=InterruptedFatal
 | AppendError=>exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal
 | AppendReset=>exit=InterruptedReset
 end.
Definition legacy_append_services valid view f h a id d s kind :=
 (exists out slot pubs acks,
   clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) /\
   logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
     (Logged (Ready out) pubs (N.of_nat id::acks)) /\
   ((exists final delivered,kind=AppendClient delivered /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
       (client_finish_contract view marker id (List.hd [] (protection_saved s)))
       (client_finish_program id (recovered_image d) [ExternalAccepted]))
       (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s))
       (if delivered then ClientReturned (DataClientSuccess id (recovered_image d)) else ClientStopped) final) \/
    (kind=AppendReset /\ exists point:runtime_sync_point, True) \/
    (kind=AppendReset /\ exists phases suffix partial,phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program phases)) s tt partial) \/
    (kind=AppendReset /\ exists closed resolved partial,
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
       (exit_contract marker (root_extents (view id)) (List.hd [] (protection_saved s)))
       (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) s tt closed /\
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
       (client_finish_contract view marker id (List.hd [] (protection_saved s)))
       collection_service_prefix) closed resolved partial))) \/
 (kind=AppendError /\ exists error_j read inspect check outcome,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j /\ returned_error_control (journal_control error_j) /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract read inspect check) restore_probe) tt outcome tt) \/
 (kind=AppendReset /\ exists cut,publication_reset_prefix g sector data_len valid (N.of_nat id) (Logged (Ready f) h a) cut) \/
 (kind=AppendReset /\ exists error_j read inspect check point,
   clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id))
     (Logged (Ready f) h a) error_j /\ returned_error_control (journal_control error_j) /\
   restore_cut_reached read inspect check point).

(* Indices record replies/cut locations of the actual services. The stamp is
   computed from the reached append history, not chosen as a client result. *)
Local Notation append_services := (append_services g sector data_len marker).

(* Forgetting reply indices recovers precisely the historical interface. *)
Lemma append_services_erase valid view f h a id d s reply :
 append_services valid view f h a id d s reply ->
 legacy_append_services valid view f h a id d s (append_reply_kind reply).
Proof.
 intros [[out [slot [pubs [acks [RUN [ACK LAST]]]]]]|
   [[error_j [rd [ins [chk [observed [EQ [RUN [ERR REST]]]]]]]]|
   [[EQ [cut RUN]]|[error_j [rd [ins [chk [point [EQ [RUN [ERR CUT]]]]]]]]]]].
 - left;exists out,slot,pubs,acks;split;[exact RUN|]. split;[exact ACK|].
   destruct LAST as [[final [delivered [EQ FINISH]]]|[[point EQ]|[[phases [suffix [partial [EQ CUT]]]]|[closed [resolved [partial [EQ CUT]]]]]]];subst reply;cbn [append_reply_kind].
   + left;exists final,delivered;split;[reflexivity|exact FINISH].
   + right;left;split;[reflexivity|exists point;exact I].
   + right;right;left;split;[reflexivity|exists phases,suffix,partial;exact CUT].
   + right;right;right;split;[reflexivity|exists closed,resolved,partial;exact CUT].
 - subst reply;right;left;split;[reflexivity|]. exists error_j,rd,ins,chk,observed;auto.
 - subst reply;right;right;left;split;[reflexivity|exists cut;exact RUN].
 - subst reply;right;right;right;split;[reflexivity|]. exists error_j,rd,ins,chk,point;auto.
Qed.
Lemma append_services_refine valid view f h a id d s kind :
 legacy_append_services valid view f h a id d s kind ->
 exists reply, append_reply_kind reply=kind /\ append_services valid view f h a id d s reply.
Proof.
 intros [[out [slot [pubs [acks [RUN [ACK LAST]]]]]]|
   [[EQ [error_j [rd [ins [chk [observed [RUN [ERR REST]]]]]]]]|
   [[EQ [cut RUN]]|[EQ [error_j [rd [ins [chk [point [RUN [ERR CUT]]]]]]]]]]].
 - destruct LAST as [[final [delivered [EQ FINISH]]]|[[EQ [point _]]|[[EQ [phases [suffix [partial CUT]]]]|[EQ [closed [resolved [partial CUT]]]]]]];subst kind.
   + exists (AppendFinishReply delivered (pred (length pubs)));split;[reflexivity|].
     left;exists out,slot,pubs,acks;split;[exact RUN|]. split;[exact ACK|].
     left;exists final,delivered;auto.
   + exists (AppendSyncCutReply point);split;[reflexivity|].
     left;exists out,slot,pubs,acks;split;[exact RUN|]. split;[exact ACK|].
     right;left;exists point;reflexivity.
   + exists (AppendExitCutReply phases);split;[reflexivity|].
     left;exists out,slot,pubs,acks;split;[exact RUN|]. split;[exact ACK|].
     right;right;left;exists phases,suffix,partial;auto.
   + exists (AppendCollectionCutReply resolved);split;[reflexivity|].
     left;exists out,slot,pubs,acks;split;[exact RUN|]. split;[exact ACK|].
     right;right;right;exists closed,resolved,partial;auto.
 - subst kind;exists (AppendRestoreReply observed);split;[reflexivity|].
   right;left;exists error_j,rd,ins,chk,observed;auto.
 - subst kind;exists AppendPhysicalCutReply;split;[reflexivity|].
   right;right;left;split;[reflexivity|exists cut;exact RUN].
 - subst kind;exists (AppendRestoreCutReply point);split;[reflexivity|].
   right;right;right;exists error_j,rd,ins,chk,point;auto.
Qed.

Lemma append_services_terminal vi oi initial events valid view f h a id d s e old word_max reply :
 validated_append_suffixes vi oi initial events valid view f h a id d s e old word_max ->
 append_services valid view f h a id d s reply ->
 exists receipts final exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts valid view final exit /\
 controller_result_post word_max vi oi initial receipts valid view final /\
 append_exit_matches (append_reply_kind reply) exit /\
 receipts=delivered_receipts exit++events /\ exit=append_reply_exit id d reply.
Proof.
 intros [INV [ENTRY [CALLS [COLLECT [SUCCESS [FAIL [RESET [PREFIX [CUT RESTORE_CUT]]]]]]]]] RUN.
 destruct RUN as [[out [slot [pubs [acks [APPEND [ACK LAST]]]]]]|
   [[error_j [read [inspect [check [outcome [K [APPEND [ERROR RESTORE]]]]]]]]|
   [[K [cut STOP]]|[error_j [read [inspect [check [point [K [APPEND [ERROR INTERRUPT]]]]]]]]]]].
 - destruct (SUCCESS out slot pubs acks APPEND ACK) as
     [SAFE [LATEST [COUNTER [ALLOCATION [RECEIPTS [SYNC FINISH]]]]]].
   destruct LAST as [[final [delivered [K RUN]]]|[[point K]|[[phases [suffix [partial [K RAM]]]]|[closed [resolved [partial [K COLLECTION]]]]]]];subst reply.
   + specialize (FINISH final delivered RUN).
     destruct delivered.
     * cbn zeta in FINISH;destruct FINISH as [DONE POST].
       do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[cbn [append_reply_kind append_exit_matches];eauto|]. split;reflexivity.
     * cbn zeta in FINISH;destruct FINISH as [DONE POST].
       do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
   + specialize (SYNC point);cbn zeta in SYNC.
     destruct SYNC as [DONE [POST RECEIPTS_]].
     do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
   + specialize (CUT out slot pubs acks APPEND ACK (or_introl (ex_intro _ phases (ex_intro _ suffix (ex_intro _ partial RAM))))).
     cbn zeta in CUT;destruct CUT as [DONE POST].
     do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
   + specialize (CUT out slot pubs acks APPEND ACK (or_intror (ex_intro _ closed (ex_intro _ resolved (ex_intro _ partial COLLECTION))))).
     cbn zeta in CUT;destruct CUT as [DONE POST].
     do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
 - subst reply;destruct (FAIL error_j read inspect check outcome APPEND ERROR RESTORE)
     as [destination [exit [KIND [DONE [POST [HISTORY EXACT]]]]]].
   do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[exact KIND|].
   split;[destruct KIND as [K|K];subst;reflexivity|exact EXACT].
 - subst reply;specialize (RESET cut STOP);cbn zeta in RESET;destruct RESET as [DONE POST].
   do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
 - subst reply;destruct (RESTORE_CUT error_j read inspect check point APPEND ERROR INTERRUPT)
     as [dest [DONE [POST [JOURNAL CONTROL]]]].
   do 3 eexists;split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|]. split;reflexivity.
Qed.

Definition append_reply_observation reply :=
 match reply with
 | AppendFinishReply true _=>Some RetainedResult
 | AppendRestoreReply RestoreValidated=>Some FinalizationError
 | _=>None end.
Lemma append_reply_observation_exact id d reply :
 exit_observation (append_reply_exit id d reply)=append_reply_observation reply.
Proof. destruct reply;try destruct delivered;try destruct observed;reflexivity. Qed.

(* The writer caller consumes the precise response, not merely a disjunction
   saying that either a return or a fatal stop would be safe. *)
Lemma append_services_observed_terminal vi oi initial events valid view f h a id d s e old word_max reply :
 validated_append_suffixes vi oi initial events valid view f h a id d s e old word_max ->
 append_services valid view f h a id d s reply ->
 exists final,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial (delivered_receipts (append_reply_exit id d reply)++events)
   valid view final (append_reply_exit id d reply) /\
 controller_result_post word_max vi oi initial
   (delivered_receipts (append_reply_exit id d reply)++events) valid view final /\
 exit_observation (append_reply_exit id d reply)=append_reply_observation reply.
Proof.
 intros SUFFIX RUN.
 destruct (append_services_terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SUFFIX RUN)
   as [receipts [final [exit [DONE [POST [MATCH [RECEIPTS EXACT]]]]]]].
 subst exit;subst receipts;exists final;split;[exact DONE|]. split;[exact POST|].
 apply append_reply_observation_exact.
Qed.

Definition restoration_services view old :=
 exists rd ins chk observed resolved (cut:option RestoreCut),
 (match cut with Some point=>restore_cut_reached rd ins chk point
 | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
     (restore_contract rd ins chk) restore_probe) tt observed tt end) /\
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []).

Local Notation restoration_services_at := (restoration_services_at marker).
Lemma restoration_services_refine view old :
 restoration_services view old <-> exists response,restoration_services_at view old response.
Proof.
 split.
 - intros [rd [ins [chk [observed [resolved [cut [RUN MASK]]]]]]].
   exists (cleanup_response observed resolved cut),rd,ins,chk,observed,resolved,cut;auto.
 - intros [response [rd [ins [chk [observed [resolved [cut [EQ [RUN MASK]]]]]]]]].
   exists rd,ins,chk,observed,resolved,cut;auto.
Qed.

Local Notation generated_candidate_ram := (generated_candidate_ram pages).

Definition legacy_validation_services read view f h a id d s old :=
 (exists observe reply after,
   boss_check_provider read observe /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
     (boss_check_contract observe) (boss_check_program id true)) f reply after /\
   match reply with
   | BossCheckReady _=>exists kind,append_services (validate after) view after h a id d s kind
   | BossCheckFailed _=>restoration_services view old
   end) \/
 (exists observe prefix,boss_check_cut true (observe f id) prefix).

Local Notation validation_services_at := (validation_services_at g sector data_len marker validate).
Definition validation_services read view f h a id d s old :=
 exists response,validation_services_at read view f h a id d s old response.
Lemma validation_services_erase read view f h a id d s old :
 validation_services read view f h a id d s old ->
 legacy_validation_services read view f h a id d s old.
Proof.
 intros [response RUN];destruct response as [reason cleanup|generation reply|prefix].
 - destruct RUN as [observe [after [PROVIDER [RUN CLEANUP]]]].
   left;exists observe,(BossCheckFailed reason),after;split;[exact PROVIDER|]. split;[exact RUN|].
   apply (proj2 (restoration_services_refine view old));exists cleanup;exact CLEANUP.
 - destruct RUN as [observe [after [PROVIDER [RUN APPEND]]]].
   left;exists observe,(BossCheckReady generation),after;split;[exact PROVIDER|]. split;[exact RUN|]. exists reply;exact APPEND.
 - destruct RUN as [observe RUN];right;exists observe,prefix;exact RUN.
Qed.
Lemma validation_services_refine read view f h a id d s old :
 legacy_validation_services read view f h a id d s old ->
 validation_services read view f h a id d s old.
Proof.
 intros [[observe [reply [after [PROVIDER [RUN LAST]]]]]|[observe [prefix CUT]]].
 - destruct reply as [reason|generation].
   + destruct (proj1 (restoration_services_refine view old) LAST) as [cleanup CLEANUP].
     exists (ValidationRejectedReply reason cleanup);exists observe,after;auto.
   + destruct LAST as [reply APPEND].
     exists (ValidationAcceptedReply generation reply);exists observe,after;auto.
 - exists (ValidationInterruptedReply prefix),observe;exact CUT.
Qed.

(* A cut is an executed interruption at the named RAM boundary, not a
   request to run the remaining preparation steps before resetting. *)

Definition writer_tail_services view h a old s read counter r result :=
 match writer_end result with
 | WriterComplete=>(exists point:preparation_ram_cut, True) \/ (forall decoded encoded,
     read (writer_flash result) (offset r)=Some (decoded,encoded) ->
     validation_services (read)
       (install_decoded_view view ranges (offset r) decoded) (writer_flash result) h a
       (offset r) decoded (generated_candidate_ram s r counter) old)
 | WriterLocalError | WriterRetainError | WriterPhysicalError=>restoration_services view old
 | WriterInterrupted=>True
 end.

(* A report is produced while consuming local replies; it is not a second
   controller or an additional persistent log. Non-append reports never
   manufacture an append response. *)

Lemma local_cleanup_mask_spec pc final outcome resolved cut mask :
 local_cleanup_mask pc final outcome resolved cut=Some mask ->
 pc=BodyFailed /\ outcome=RestoreValidated /\ resolved=Some mask /\ cut=None /\
 exists root,owned_error_observation final=Some(false,root).
Proof.
 unfold local_cleanup_mask;destruct pc;try discriminate.
 destruct (owned_error_observation final) as [[frozen root]|] eqn:ROOT;try discriminate.
 destruct frozen;try discriminate;destruct outcome;try discriminate;
 destruct resolved;try discriminate;destruct cut;try discriminate.
 intro EQ;inversion EQ;subst;repeat split;try reflexivity;exists root;reflexivity.
Qed.


Lemma owner_local_response_projects response exit :
 owner_response_matches response exit -> owner_response_matches (erase_local_response response) exit.
Proof.
 destruct response;try (intro MATCH;exact MATCH).
 intro EQ;cbn [owner_response_matches] in EQ;subst exit;reflexivity.
Qed.

Definition owner_terminal word_max vi oi initial before :=
 exists receipts vf of_ final exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts vf of_ final exit /\
 controller_result_post word_max vi oi initial receipts vf of_ final /\
 receipts=delivered_receipts exit++before /\
 exists response,owner_response_matches response exit.

Lemma owner_terminal_forget word_max vi oi initial before :
 owner_terminal word_max vi oi initial before ->
 owner_terminal_erased word_max vi oi initial before.
Proof.
 intros [receipts [vf [of_ [final [exit [DONE [POST [EXACT REPORT]]]]]]]].
 exists receipts,vf,of_,final,exit;auto.
Qed.

Local Notation restoration_services_for := (restoration_services_for marker).
Local Notation writer_tail_services_for := (writer_tail_services_for g sector data_len marker ranges pages validate).
Definition owner_terminal_for (Q:owner_service_response->Prop) word_max vi oi initial before :=
 exists receipts vf of_ final exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts vf of_ final exit /\
 controller_result_post word_max vi oi initial receipts vf of_ final /\
 receipts=delivered_receipts exit++before /\
 exists response,owner_response_matches response exit /\ Q response /\ owner_reply_ready response final.
Lemma owner_terminal_forget_index Q word_max vi oi initial before :
 owner_terminal_for Q word_max vi oi initial before -> owner_terminal word_max vi oi initial before.
Proof.
 intros [receipts [vf [of_ [final [exit [DONE [POST [EQ [response [MATCH [INDEX READY]]]]]]]]]]].
 exists receipts,vf,of_,final,exit;split;[exact DONE|]. split;[exact POST|]. split;[exact EQ|].
 exists (erase_local_response response);apply owner_local_response_projects;exact MATCH.
Qed.
Lemma writer_tail_services_unindexed view h a old s read counter r result :
 writer_tail_services view h a old s read counter r result <->
 writer_tail_services_for (fun _=>True) view h a old s read counter r result.
Proof.
 unfold writer_tail_services,writer_tail_services_for;destruct (writer_end result).
 - split;intros [[point _]|RUN];[left;exists point;exact I|right|left;exists point;exact I|right].
   + intros decoded encoded READ;destruct (RUN decoded encoded READ) as [reply EXEC];exists reply;auto.
   + intros decoded encoded READ;destruct (RUN decoded encoded READ) as [reply [EXEC _]];exists reply;exact EXEC.
 - unfold restoration_services_for;rewrite restoration_services_refine;
   split;[intros [reply RUN];exists reply;split;[exact RUN|exact I]|
     intros [reply [RUN _]];exists reply;exact RUN].
 - unfold restoration_services_for;rewrite restoration_services_refine;
   split;[intros [reply RUN];exists reply;split;[exact RUN|exact I]|
     intros [reply [RUN _]];exists reply;exact RUN].
 - unfold restoration_services_for;rewrite restoration_services_refine;
   split;[intros [reply RUN];exists reply;split;[exact RUN|exact I]|
     intros [reply [RUN _]];exists reply;exact RUN].
 - tauto.
Qed.

Theorem generated_writer_services_terminal_for (Q:owner_service_response->Prop) vi oi initial events valid view f h a old image s e counter r word_max
 encode plan result base (checked:bool) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 mapped_registry_base base ->
 generated_writer_continuation vi oi initial events valid view f h a old image s e counter r word_max ->
 boss_generation_format g sector encode (counter_decoder e) ->
 checked_boss_plan encode image counter r=Some plan ->
 writer_execution g sector r true f plan result ->
 writer_tail_services_for Q view h a old s (counter_decoder e) counter r result ->
 owner_terminal_for Q word_max vi oi initial events.
Proof.
 intros MARK DEC WORD GEO INIT NUM BASE CONT FORMAT PLAN WRITE SERVICES.
 destruct (CONT encode plan result FORMAT PLAN WRITE) as [previous
   [PATH [SAFE [HISTORY [RECEIPTS [COUNTER [CUT [LOCAL [PHYSICAL [next
     [NEXT [SUCCESSOR [ENCODE [COMMANDS [TERMINAL [DECODED COMPLETE]]]]]]]]]]]]]]]].
 unfold writer_tail_services_for in SERVICES.
 destruct (writer_end result) eqn:END.
 - destruct (COMPLETE eq_refl) as [REHOME [target [TARGET [CACHED [CACHE_SAFE [SETTER [SETTER_SAFE [GEN [RESET INSTALL]]]]]]]]].
   destruct SERVICES as [[point INDEX]|SERVICES].
   + destruct point.
     * assert (RESET_CACHE:Trace vi oi initial events (validate (writer_flash result)) view
         ((Logged (Boot (writer_flash result)) h a,RebuildingBoundary Selecting),
          forget_volatile_evidence (selected_evidence old previous e))).
       { eapply episodes_append with (more:=[]);[exact CACHED|].
         eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
         eapply reset_episode;apply record_step;apply reset_ready. }
       lazymatch type of RESET_CACHE with Trace _ _ _ _ ?v ?o ?dest =>
         assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
           vi oi initial events v o dest InterruptedReset) by
         (exists v,o,dest,events,[];split;[exact RESET_CACHE|];
          split;[apply operation_already_reset;reflexivity|reflexivity]) end.
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
       split;[reflexivity|exists (PreparationCutResponse PreparationAfterRehomeCache);split;[reflexivity|(split;[exact INDEX|exact I])]].
     * lazymatch type of RESET with Trace _ _ _ _ ?v ?o ?dest =>
         assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
           vi oi initial events v o dest InterruptedReset) by
         (exists v,o,dest,events,[];split;[exact RESET|];
          split;[apply operation_already_reset;reflexivity|reflexivity]) end.
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
       split;[reflexivity|exists (PreparationCutResponse PreparationAfterSetter);split;[reflexivity|(split;[exact INDEX|exact I])]].
     * destruct (INSTALL base checked BASE) as [decoded [raw [encoded INSTALLED]]].
       destruct INSTALLED as [ABS [REL [READY [READY_SAFE [READ [GENERATION [RANGE [IMAGE [IMAGE_GEN [COUNTER_ [HIST [RECEIPT [TOKEN [PROTECTED [DISTINCT [RESET_INSTALLED REST]]]]]]]]]]]]]]]].
       lazymatch type of RESET_INSTALLED with Trace _ _ _ _ ?v ?o ?dest =>
         assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
           vi oi initial events v o dest InterruptedReset) by
         (exists v,o,dest,events,[];split;[exact RESET_INSTALLED|];
          split;[apply operation_already_reset;reflexivity|reflexivity]) end.
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
       split;[reflexivity|exists (PreparationCutResponse PreparationAfterInstallation);split;[reflexivity|(split;[exact INDEX|exact I])]].
   + { destruct (INSTALL base checked BASE) as [decoded [raw [encoded INSTALLED]]].
   destruct INSTALLED as [ABS [REL [READY [READY_SAFE [READ [GENERATION [RANGE [IMAGE [IMAGE_GEN [COUNTER_ [HIST [RECEIPT [TOKEN [PROTECTED [DISTINCT [RESET_INSTALLED [LATEST [GATE [HIT [CHECK [FAILED [VALIDATED VALIDATION_CUT]]]]]]]]]]]]]]]]]]]]]].
   specialize (SERVICES decoded encoded READ).
   unfold generated_candidate_ram in SERVICES;rewrite <- SUCCESSOR,<-TARGET in SERVICES.
   destruct SERVICES as [response [SERVICES INDEX]].
   destruct response as [reason cleanup|n kind|prefix].
   + destruct SERVICES as [observe [after [PROVIDER [RUN TAIL]]]].
     destruct TAIL as [rd [ins [chk [observed [resolved [cut [CLEANUP [RESTORE MASK]]]]]]]];subst cleanup.
       destruct (FAILED observe reason after (fun _ _=>rd) ins chk observed resolved cut RUN MASK RESTORE)
         as [last [exit [KIND [DONE [POST REST]]]]].
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[destruct exit;cbn in KIND |- *;intuition discriminate|].
       exists (ValidationFailureResponse reason (cleanup_response observed resolved cut));split;[|(split;[exact INDEX|exact I])];destruct exit;cbn in KIND |- *;intuition discriminate.
   + destruct SERVICES as [observe [after [PROVIDER [RUN APPEND_RUN]]]].
       rewrite HIT in VALIDATED.
       destruct (VALIDATED observe n after PROVIDER RUN) as [FLASH [NUMBER [CANDIDATE APPEND]]].
       destruct (append_services_observed_terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ APPEND APPEND_RUN)
         as [last [DONE [POST OBSERVED]]].
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[reflexivity|exists (AppendResponse (offset r) decoded kind);split;[reflexivity|(split;[exact INDEX|exact I])]].
   + destruct SERVICES as [observe INTERRUPTED].
     destruct (VALIDATION_CUT observe prefix INTERRUPTED) as [RESET_RUN [RESET_SAFE RESET_RECEIPTS]].
     lazymatch type of RESET_RUN with
     | Trace _ _ _ _ ?v ?o ?dest =>
       assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
         vi oi initial events v o dest InterruptedReset) by
       (exists v,o,dest,events,[];split;[exact RESET_RUN|];
        split;[apply operation_already_reset;reflexivity|reflexivity])
     end.
     unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[eapply controller_finalization_from_trace;eassumption|].
       split;[reflexivity|exists (ValidationCutResponse prefix);split;[reflexivity|(split;[exact INDEX|exact I])]]. }
 - destruct SERVICES as [cleanup [SERVICES INDEX]].
   destruct SERVICES as [rd [ins [chk [observed [resolved [cut [EQ [RESTORE MASK]]]]]]]];subst cleanup.
   destruct (LOCAL (or_introl eq_refl) rd ins chk observed resolved cut RESTORE MASK)
     as [last [exit [KIND [DONE [POST REST]]]]];unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[destruct exit;cbn in KIND |- *;intuition discriminate|].
       exists (WriterFailureResponse WriterLocalError (cleanup_response observed resolved cut));split;[|(split;[exact INDEX|exact I])];destruct exit;cbn in KIND |- *;intuition discriminate.
 - destruct SERVICES as [cleanup [SERVICES INDEX]].
   destruct SERVICES as [rd [ins [chk [observed [resolved [cut [EQ [RESTORE MASK]]]]]]]];subst cleanup.
   destruct (LOCAL (or_intror eq_refl) rd ins chk observed resolved cut RESTORE MASK)
     as [last [exit [KIND [DONE [POST REST]]]]];unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[destruct exit;cbn in KIND |- *;intuition discriminate|].
       exists (WriterFailureResponse WriterRetainError (cleanup_response observed resolved cut));split;[|(split;[exact INDEX|exact I])];destruct exit;cbn in KIND |- *;intuition discriminate.
 - destruct SERVICES as [cleanup [SERVICES INDEX]].
   destruct SERVICES as [rd [ins [chk [observed [resolved [cut [EQ [RESTORE MASK]]]]]]]];subst cleanup.
   destruct (PHYSICAL eq_refl rd ins chk observed cut RESTORE)
     as [last [exit [KIND [DONE [POST REST]]]]];unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[destruct exit;cbn in KIND |- *;intuition discriminate|].
       exists (WriterFailureResponse WriterPhysicalError (cleanup_response observed resolved cut));split;[|(split;[exact INDEX|exact I])];destruct exit;cbn in KIND |- *;intuition discriminate.
 - destruct (CUT eq_refl) as [DONE [POST OBS]];unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
       split;[reflexivity|exists WriterInterruptedResponse;split;[reflexivity|split;[exact SERVICES|exact I]]].
Qed.

Theorem generated_writer_services_terminal vi oi initial events valid view f h a old image s e counter r word_max
 encode plan result base (checked:bool) :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 mapped_registry_base base ->
 generated_writer_continuation vi oi initial events valid view f h a old image s e counter r word_max ->
 boss_generation_format g sector encode (counter_decoder e) ->
 checked_boss_plan encode image counter r=Some plan ->
 writer_execution g sector r true f plan result ->
 writer_tail_services view h a old s (counter_decoder e) counter r result ->
 owner_terminal word_max vi oi initial events.
Proof.
 intros MARK DEC WORD GEO INIT NUM BASE CONT FORMAT PLAN WRITE SERVICES.
 apply (owner_terminal_forget_index (fun _=>True)).
 eapply (generated_writer_services_terminal_for (fun _=>True));try eassumption.
 apply (proj1 (writer_tail_services_unindexed _ _ _ _ _ _ _ _ _));exact SERVICES.
Qed.


(* These are finite executions, not promises that a service terminates or
   preserves a transaction invariant. In particular each later service is
   demanded only on the successful result of its predecessor. *)
Definition boss_writer_services view f h a old image s read counter r :=
 exists encode plan result,
 boss_generation_format g sector encode read /\
 checked_boss_plan encode image counter r=Some plan /\
 writer_execution g sector r true f plan result /\
 writer_tail_services view h a old s read counter r result.

Definition boss_acquisition_services word_max total view f h a old image s e counter :=
 (exists cursor probe_final,
   option_map allocation_append (volatile_allocation e)=Some cursor /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
     (cursor_contract sector (pages*256) (fun _=>Some total) cursor f)
     (probe_cursor_checked word_max)) s ProbeRejected probe_final /\
   restoration_services view old) \/
 (exists fuel recognize req round alignment start reply,
   boss_search_inputs word_max total e s f req start /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply /\
   (reply=SearchMiss \/ reply=SearchError) /\ restoration_services view old) \/
 (exists fuel shape verify req round alignment start target fatal,
   boss_search_inputs word_max total e s f req start /\
   reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
     f (protection_table s) req round alignment pages start target /\
   recognition_interruption shape verify f target fatal) \/
 (exists span,
   boss_erased_admission word_max total e s f span /\
   ((boss_writer_services view f h a old image (reservation_state true span s)
       (counter_decoder e) counter span) \/ (exists point:acquisition_ram_point,True))) \/
 (exists recognize magic fuel req round alignment start r nsectors recycled,
   recognizer_local sector recognize /\
   boss_search_inputs word_max total e s f req start /\
   reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r /\
   erase_geometry g sector r nsectors /\ recycling_run g sector recognize magic r nsectors f recycled /\
   match neutral_end_ recycled with
   | NeutralSuccess=>
     boss_writer_services view (neutral_flash recycled) h a old image
       (reservation_state true (block_pages (recycle_lo r) (useful_pages r)) s)
       (counter_decoder e) counter (block_pages (recycle_lo r) (useful_pages r)) \/
       (exists point:acquisition_ram_point,True)
   | NeutralError=>restoration_services view old
   | NeutralFatal | NeutralReset=>True
   end).

Definition boss_pipeline_services word_max view f h a old image s e :=
 match boss_size_preflight word_max image with
 | BossLengthRejected | BossScratchRejected _=>restoration_services view old
 | BossSizeReady total=>forall counter,volatile_counter e=Some counter ->
   match boss_checked_generation (counter_value counter) with
   | None=>restoration_services view old
   | Some _=>boss_acquisition_services word_max total view f h a old image s e counter
   end
 end.

Local Notation boss_writer_services_for := (boss_writer_services_for g sector data_len marker ranges pages validate).

Local Notation boss_acquisition_services_for := (boss_acquisition_services_for g sector data_len marker ranges pages validate).

Local Notation boss_pipeline_services_for := (boss_pipeline_services_for g sector data_len marker ranges pages validate).

Lemma restoration_services_unindexed view old :
 restoration_services view old <-> restoration_services_for (fun _=>True) view old.
Proof. unfold restoration_services_for;rewrite restoration_services_refine;
   split;[intros [reply RUN];exists reply;split;[exact RUN|exact I]|
     intros [reply [RUN _]];exists reply;exact RUN]. Qed.
Lemma boss_writer_services_unindexed view f h a old image s read counter r :
 boss_writer_services view f h a old image s read counter r <->
 boss_writer_services_for (fun _=>True) view f h a old image s read counter r.
Proof.
 unfold boss_writer_services,boss_writer_services_for;split.
 - intros [encode [plan [result [FORMAT [PLAN [WRITE TAIL]]]]]].
   exists encode,plan,result;split;[exact FORMAT|]. split;[exact PLAN|]. split;[exact WRITE|].
   apply (proj1 (writer_tail_services_unindexed _ _ _ _ _ _ _ _ _));exact TAIL.
 - intros [encode [plan [result [FORMAT [PLAN [WRITE TAIL]]]]]].
   exists encode,plan,result;split;[exact FORMAT|]. split;[exact PLAN|]. split;[exact WRITE|].
   apply (proj2 (writer_tail_services_unindexed _ _ _ _ _ _ _ _ _));exact TAIL.
Qed.

Lemma boss_acquisition_services_unindexed word_max total view f h a old image s e counter :
 boss_acquisition_services word_max total view f h a old image s e counter <->
 boss_acquisition_services_for (fun _=>True) word_max total view f h a old image s e counter.
Proof.
 unfold boss_acquisition_services,boss_acquisition_services_for;cbn beta.
 split;intros [A|[B|[C|[D|E]]]].
 - left;destruct A as [cursor [probe [CURSOR [RUN REST]]]].
   exists cursor,probe;split;[exact CURSOR|]. split;[exact RUN|].
   apply (proj1 (restoration_services_unindexed _ _));exact REST.
 - right;left;destruct B as [fuel [recognize [req [round [alignment [start [reply [INPUT [RUN [ERROR REST]]]]]]]]]].
   exists fuel,recognize,req,round,alignment,start,reply;split;[exact INPUT|]. split;[exact RUN|]. split;[exact ERROR|].
   apply (proj1 (restoration_services_unindexed _ _));exact REST.
 - right;right;left.
   destruct C as [fuel [shape [verify [req [round [alignment [start [target [fatal [INPUT [PREFIX STOP]]]]]]]]]]].
   exists fuel,shape,verify,req,round,alignment,start,target,fatal;split;[exact INPUT|]. split;[exact PREFIX|].
   split;[exact STOP|exact I].
 - right;right;right;left;destruct D as [span [ADMIT [WRITE|CUT]]];exists span;split;[exact ADMIT| |exact ADMIT|].
   + left;apply (proj1 (boss_writer_services_unindexed _ _ _ _ _ _ _ _ _ _));exact WRITE.
   + right;exact CUT.
 - right;right;right;right.
   destruct E as [recognize [magic [fuel [req [round [alignment [start [r [nsectors [recycled [LOC [INPUT [SEARCH [GEOM [RUN LAST]]]]]]]]]]]]]]].
   exists recognize,magic,fuel,req,round,alignment,start,r,nsectors,recycled.
   split;[exact LOC|]. split;[exact INPUT|]. split;[exact SEARCH|]. split;[exact GEOM|]. split;[exact RUN|].
   destruct (neutral_end_ recycled).
   + destruct LAST as [WRITE|CUT].
     * left;apply (proj1 (boss_writer_services_unindexed _ _ _ _ _ _ _ _ _ _));exact WRITE.
     * right;exact CUT.
   + apply (proj1 (restoration_services_unindexed _ _));exact LAST.
   + exact I.
   + exact I.
 - left;destruct A as [cursor [probe [CURSOR [RUN REST]]]].
   exists cursor,probe;split;[exact CURSOR|]. split;[exact RUN|].
   apply (proj2 (restoration_services_unindexed _ _));exact REST.
 - right;left;destruct B as [fuel [recognize [req [round [alignment [start [reply [INPUT [RUN [ERROR REST]]]]]]]]]].
   exists fuel,recognize,req,round,alignment,start,reply;split;[exact INPUT|]. split;[exact RUN|]. split;[exact ERROR|].
   apply (proj2 (restoration_services_unindexed _ _));exact REST.
 - right;right;left.
   destruct C as [fuel [shape [verify [req [round [alignment [start [target [fatal [INPUT [PREFIX [STOP _]]]]]]]]]]]].
   exists fuel,shape,verify,req,round,alignment,start,target,fatal;split;[exact INPUT|]. split;[exact PREFIX|].
   exact STOP.
 - right;right;right;left;destruct D as [span [ADMIT [WRITE|CUT]]];exists span;split;[exact ADMIT| |exact ADMIT|].
   + left;apply (proj2 (boss_writer_services_unindexed _ _ _ _ _ _ _ _ _ _));exact WRITE.
   + right;exact CUT.
 - right;right;right;right.
   destruct E as [recognize [magic [fuel [req [round [alignment [start [r [nsectors [recycled [LOC [INPUT [SEARCH [GEOM [RUN LAST]]]]]]]]]]]]]]].
   exists recognize,magic,fuel,req,round,alignment,start,r,nsectors,recycled.
   split;[exact LOC|]. split;[exact INPUT|]. split;[exact SEARCH|]. split;[exact GEOM|]. split;[exact RUN|].
   destruct (neutral_end_ recycled).
   + destruct LAST as [WRITE|CUT].
     * left;apply (proj2 (boss_writer_services_unindexed _ _ _ _ _ _ _ _ _ _));exact WRITE.
     * right;exact CUT.
   + apply (proj2 (restoration_services_unindexed _ _));exact LAST.
   + exact I.
   + exact I.
Qed.


Lemma boss_pipeline_services_unindexed word_max view f h a old image s e :
 boss_pipeline_services word_max view f h a old image s e <->
 boss_pipeline_services_for (fun _=>True) word_max view f h a old image s e.
Proof.
 unfold boss_pipeline_services,boss_pipeline_services_for.
 destruct (boss_size_preflight word_max image);try apply restoration_services_unindexed.
 split;intros SERVICES counter VALUE;specialize (SERVICES counter VALUE);
 destruct (boss_checked_generation (counter_value counter));
 try (apply (proj1 (boss_acquisition_services_unindexed _ _ _ _ _ _ _ _ _ _ _));exact SERVICES);
 try (apply (proj2 (boss_acquisition_services_unindexed _ _ _ _ _ _ _ _ _ _ _));exact SERVICES);
 try (apply (proj1 (restoration_services_unindexed _ _));exact SERVICES);
 try (apply (proj2 (restoration_services_unindexed _ _));exact SERVICES).
Qed.

Theorem owned_entry_marked_recycling valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 volatile_latest_registry e=Some old -> mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 runtime_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 generation_decoding_matches sector decode (counter_decoder e) ->
 generation_decoding_local sector (counter_decoder e) ->
 counter_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 allocation_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode e ->
 allocation_append_bound pages e ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 exists vo oo destination,
 owned_controller_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)
   vo oo destination /\
 publications (boundary_journal destination)=h /\
 boundary_receipts destination=client_receipts e /\
 (marked_boss_requested result pc final=true -> open_destination destination /\
   vo=vf /\ oo=of_ /\ destination=marked_selected_boundary final) /\
 ((exists exit,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination exit /\
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination)
  \/
  exists j image ram ev,
   destination=((j,OpenBoundary image [] ram),ev) /\
   finish_selected (controller_read ev)=Some FinishPublish /\
   owner_armed (controller_read ev)=true /\ outer_live (controller_read ev)=true /\
   (exists allocation,volatile_allocation ev=Some allocation) /\
   allocation_range_origin sector pages decode ev /\
   allocation_append_bound pages ev /\
   (forall ff req start, runtime_search_inputs sector pages word_max ev ram ff req start ->
     exists allocation,volatile_allocation ev=Some allocation /\
     Nat.min word_max (extent_end (allocation_latest allocation))=extent_end (allocation_latest allocation) /\
     256*start=extent_end (allocation_latest allocation) /\ start<=pages) /\
   match boss_size_preflight word_max image with
   | BossSizeReady total =>
   total=((boss_live_count image*40+40+255)/256)*256 /\
   boss_live_count image*40+40+255<=word_max /\ total<=4096 /\
   exists counter,
   volatile_counter ev=Some counter /\
   (volatile_counter e=Some counter \/
    exists v o installed prefix suffix id decoded,
    Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) prefix v o installed /\
    Trace v o installed suffix vo oo destination /\
    decode (object_flash sector (control_image (journal_control (boundary_journal installed)))) id=Some decoded /\
    read_counter (counter_decoder (snd installed))
      (control_image (journal_control (boundary_journal installed))) id=Some counter) /\
   generation_decoding_matches sector decode (counter_decoder ev) /\
   generation_decoding_local sector (counter_decoder ev) /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
     controller_contract next_generation_probe) destination
       (boss_checked_generation (counter_value counter)) destination /\
   (forall answer reached,
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
       controller_contract next_generation_probe) destination answer reached ->
     answer=boss_checked_generation (counter_value counter) /\ reached=destination) /\
   ((exists next,boss_checked_generation (counter_value counter)=Some next /\ next=N.succ (counter_value counter)) \/
    (counter_value counter=boss_generation_max /\ boss_checked_generation (counter_value counter)=None)) /\
   (forall ff aa rd ins chk observed resolved' restore_cut,
    j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)=None ->
    (match restore_cut with Some point=>restore_cut_reached rd ins chk point
     | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
       (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
    (forall mask,resolved'=Some mask -> mask=collect_ranges oo marker (Some old) (object_extents (oo old)) []) ->
    exists last exit,
    (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
    completed_operation g sector data_len marker ranges decode topology pages
      valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last exit /\
    controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last /\
    publications (boundary_journal last)=h /\
    control_image (journal_control (boundary_journal last))=ff) /\
   volatile_runtime_initialized ev=Some true /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
     controller_contract runtime_initialized_probe) destination true destination /\
   (forall answer reached,
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
       controller_contract runtime_initialized_probe) destination answer reached ->
     answer=true /\ reached=destination) /\
   volatile_page_size ev=Some 256 /\
   (marker_header_covered marker -> persistence_marker_recognized sector f ->
     forall area_len,8<=area_len ->
     persistence_marker_test sector area_len
       (control_image (journal_control j))=true) /\
   post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
     controller_contract ensure_protection_probe) destination true destination /\
   (forall answer reached,
     post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
       controller_contract ensure_protection_probe) destination answer reached ->
     answer=true /\ reached=destination) /\
   (forall ff aa area_len req cursor probe_final rd ins chk observed resolved' restore_cut,
    j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)<>None ->
    area_len=pages*256 /\ option_map allocation_append (volatile_allocation ev)=Some cursor /\
    req=(fun _=>Some total) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor ff) (probe_cursor_checked word_max))
      ram ProbeRejected probe_final ->
    (match restore_cut with Some point=>restore_cut_reached rd ins chk point
     | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
       (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
    (forall mask,resolved'=Some mask -> mask=collect_ranges oo marker (Some old) (object_extents (oo old)) []) ->
    probe_final=ram /\
    exists last exit,
    (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
    completed_operation g sector data_len marker ranges decode topology pages
      valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last exit /\
    controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last /\
    publications (boundary_journal last)=h /\
    control_image (journal_control (boundary_journal last))=ff) /\
   (forall ff aa fuel recognize req round alignment start reply rd ins chk observed resolved' restore_cut,
    j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)<>None ->
    boss_search_inputs word_max total ev ram ff req start ->
    reusable_search sector fuel recognize ff (protection_table ram) req round alignment pages start=reply ->
    (reply=SearchMiss \/ reply=SearchError) ->
    (match restore_cut with Some point=>restore_cut_reached rd ins chk point
     | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
       (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
    (forall mask,resolved'=Some mask -> mask=collect_ranges oo marker (Some old) (object_extents (oo old)) []) ->
    exists last exit,
    (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
    completed_operation g sector data_len marker ranges decode topology pages
      valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last exit /\
    controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last /\
    publications (boundary_journal last)=h /\
    control_image (journal_control (boundary_journal last))=ff) /\
   (forall ff aa fuel shape verify req round alignment start target fatal,
    j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)<>None ->
    boss_search_inputs word_max total ev ram ff req start ->
    reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
      ff (protection_table ram) req round alignment pages start target ->
    recognition_interruption shape verify ff target fatal ->
    let reset:=if fatal then ((Logged (Ready ff) h aa,FatalBoundary),forget_volatile_evidence ev)
      else ((Logged (Boot ff) h aa,RebuildingBoundary Selecting),forget_volatile_evidence ev) in
    completed_operation g sector data_len marker ranges decode topology pages
      valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo reset (if fatal then InterruptedFatal else InterruptedReset) /\
    controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo reset) /\
   (forall ff aa span, j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)<>None ->
    boss_erased_admission word_max total ev ram ff span ->
    let reserved:=((Logged (Ready ff) h aa,OpenBoundary image [] (reservation_state true span ram)),advance_allocation_evidence span ev) in
    Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo reserved /\
    Safe vo oo reserved /\
    phase_numeric word_max marker ranges (snd (fst reserved)) /\
    reservation_handoff sector ff (reservation_state true span ram) (reservation_token true span) /\
    generated_writer_continuation valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
      vo oo ff h aa old image (reservation_state true span ram) (advance_allocation_evidence span ev) counter span word_max /\
    boss_rehome_call word_max image (reservation_state true span ram) (advance_allocation_evidence span ev) span /\
    (forall point,
      let dest:=acquisition_ram_reset point true span ram ev (Logged (Ready ff) h aa) in
      completed_operation g sector data_len marker ranges decode topology pages
        valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo dest InterruptedReset /\
      controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo dest /\
      boundary_receipts dest=client_receipts e)) /\
   forall ff aa, j=Logged (Ready ff) h aa ->
    boss_checked_generation (counter_value counter)<>None ->
   forall recognize magic fuel req round alignment start r nsectors recycled,
   recognizer_local sector recognize ->
   boss_search_inputs word_max total ev ram ff req start ->
   reusable_search sector fuel recognize ff (protection_table ram) req round alignment pages start=FoundRecyclable r ->
   erase_geometry g sector r nsectors ->
   recycling_run g sector recognize magic r nsectors ff recycled ->
   let extent:=block_pages (recycle_lo r) (useful_pages r) in
   exists previous,
   let reached:=(recycling_acquisition_boundary old image [] ram h aa recycled extent true,
     phase_evidence (snd (recycling_acquisition_boundary old image [] ram h aa recycled extent true))
       (selected_evidence old previous (recycling_cursor_evidence recycled extent ev))) in
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
     (validate (neutral_flash recycled)) oo reached /\
   Safe (validate (neutral_flash recycled)) oo reached /\
   phase_numeric word_max marker ranges (snd (fst reached)) /\
   raw_order sector 256 data_len (boundary_journal reached) /\
   publications (boundary_journal reached)=h /\
   boundary_receipts reached=client_receipts e /\
   (neutral_end_ recycled=NeutralSuccess ->
     ram_reservation_check true word_max extent ram=None /\
     reservation_handoff sector (neutral_flash recycled)
       (reservation_state true extent ram) (reservation_token true extent) /\
     generated_writer_continuation valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo (neutral_flash recycled) h aa old image
       (reservation_state true extent ram) (selected_evidence old previous (recycling_cursor_evidence recycled extent ev)) counter extent word_max /\
     boss_rehome_call word_max image (reservation_state true extent ram) (selected_evidence old previous (recycling_cursor_evidence recycled extent ev)) extent /\
     (forall point,
       let dest:=acquisition_ram_reset point true extent ram (selected_evidence old previous ev)
         (Logged (Ready (neutral_flash recycled)) h aa) in
       completed_operation g sector data_len marker ranges decode topology pages
         valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] (validate (neutral_flash recycled)) oo dest InterruptedReset /\
       controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
         (validate (neutral_flash recycled)) oo dest /\
       boundary_receipts dest=client_receipts e)) /\
   (neutral_end_ recycled=NeutralError ->
     forall rd ins chk observed (restore_cut:option RestoreCut),
     (match restore_cut with Some point=>restore_cut_reached rd ins chk point
      | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
     exists last exit,
     (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
     completed_operation g sector data_len marker ranges decode topology pages
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last exit /\
     controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last /\
     publications (boundary_journal last)=h /\
     control_image (journal_control (boundary_journal last))=neutral_flash recycled) /\
   (neutral_end_ recycled=NeutralFatal \/ neutral_end_ recycled=NeutralReset ->
     exists last exit,
     completed_operation g sector data_len marker ranges decode topology pages
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last exit /\
     controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last /\
     exit_observation exit=None /\
     publications (boundary_journal last)=h /\
     control_image (journal_control (boundary_journal last))=neutral_flash recycled) /\
   (neutral_end_ recycled=NeutralSuccess ->
     exists last exit,
     completed_operation g sector data_len marker ranges decode topology pages
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last exit /\
     controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) []
       (validate (neutral_flash recycled)) oo last /\
     exit_observation exit=None /\
     publications (boundary_journal last)=h /\
     control_image (journal_control (boundary_journal last))=neutral_flash recycled)
   | BossLengthRejected | BossScratchRejected _ =>
     forall ff aa rd ins chk observed resolved' restore_cut,
     j=Logged (Ready ff) h aa ->
     (match restore_cut with Some point=>restore_cut_reached rd ins chk point
      | None=>post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
        (restore_contract rd ins chk) restore_probe) tt observed tt end) ->
     (forall mask,resolved'=Some mask -> mask=collect_ranges oo marker (Some old) (object_extents (oo old)) []) ->
     exists last exit,
     (exit=ReturnedOrdinary FinishPublish \/ exit=InterruptedFatal \/ exit=InterruptedReset) /\
     completed_operation g sector data_len marker ranges decode topology pages
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last exit /\
     controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo last /\
     publications (boundary_journal last)=h /\
     control_image (journal_control (boundary_journal last))=ff
   end).
Proof.
 intros MARKER_HEADER OBJECT_MAPPING INITIAL_LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION DECODE_GEOMETRY INITIAL_ORIGIN INITIAL_APPEND OUT ARM ENTRY BODY RESTORE MASK.
 destruct (owned_entry_marked_controller_indexed valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut
   MARK DEC WORD GEO INIT META OUT ARM ENTRY BODY RESTORE MASK)
   as [vo [oo [destination [RESULT [PUB [RECEIPTS DISPATCH]]]]]].
 exists vo,oo,destination;split;[exact RESULT|].
 split;[exact PUB|]. split;[exact RECEIPTS|]. split;[exact DISPATCH|].
 destruct RESULT as [[exit [KIND [COMPLETE POST]]]|[j [image [root [ram [ev [DEST [PATH [SAFE [NUM [ROOT [P [CHOSEN [ARMED [LIVE [CALL [MARKER_FRAME [CONCRETE_ROOTS JOURNAL_READY]]]]]]]]]]]]]]]]]].
 - left;exists exit;split;assumption.
 - right;subst root;exists j,image,ram,ev;split;[exact DEST|].
   split;[exact CHOSEN|]. split;[exact ARMED|]. split;[exact LIVE|].
   split.
   { pose proof (proj1 (episode_trace_allocation_known g sector data_len marker ranges decode topology pages G DIV
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination
       GENERATION ALLOCATION INIT PATH)) as KNOWN.
     rewrite DEST in KNOWN;exact KNOWN. }
   assert (ORIGIN:allocation_range_origin sector pages decode ev).
   { pose proof (episode_trace_allocation_origin g sector data_len marker ranges decode topology pages G DIV
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination
       GENERATION DECODE_GEOMETRY INITIAL_ORIGIN INIT PATH) as REACHED.
     rewrite DEST in REACHED;exact REACHED. }
   split;[exact ORIGIN|].
   split.
   { pose proof (episode_trace_allocation_transport g sector data_len marker ranges decode topology pages G DIV
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination
       GENERATION DECODE_GEOMETRY (conj ALLOCATION (conj INITIAL_ORIGIN INITIAL_APPEND)) INIT PATH) as TRANSPORT.
     rewrite DEST in TRANSPORT;exact (proj2 (proj2 TRANSPORT)). }
   split.
   { intros ff req start INPUTS;eapply runtime_search_calculation;[exact ORIGIN| |exact INPUTS].
     destruct MAPPING as [_ SIZE];nia. }

   assert (INITIAL_NUM:phase_numeric word_max marker ranges (IdleBoundary old d s)).
   { exact (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
       (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)). }
   destruct (boss_size_preflight word_max image) as [|too_large|total] eqn:SIZE.
   all: try solve [
     intros ff aa rd ins chk observed resolved' restore_cut J RESTORE_RUN COLLECT;
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)) by (rewrite -J -DEST;exact PATH);
     assert (HEAD:hd_error h=Some (N.of_nat old)) by
       exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT)))))));
     eapply selected_preallocation_error_return;try eassumption;exact I ].
   destruct (boss_size_preflight_ready _ _ _ SIZE) as [TOTAL [BOUNDED SCRATCH]].
   split;[exact TOTAL|]. split;[exact BOUNDED|]. split;[exact SCRATCH|].
   destruct (episode_trace_counter g sector data_len marker ranges decode topology pages G DIV
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination
     GENERATION COUNTER INIT PATH) as [COUNTER_READY COUNTER_SOURCE].
   rewrite DEST in COUNTER_READY;destruct COUNTER_READY as [counter VALUE].
   exists counter;split;[exact VALUE|].
   split.
   { destruct (episode_trace_counter_origin g sector data_len marker ranges decode topology pages G DIV
       valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination INIT PATH)
       as [UNCHANGED|[NONE|[v [o [installed [prefix [suffix [id [decoded [PRE [POST [READ OBS]]]]]]]]]]]].
     - rewrite DEST in UNCHANGED;cbn [snd] in UNCHANGED;rewrite VALUE in UNCHANGED;left;congruence.
     - rewrite DEST in NONE;cbn [snd] in NONE;rewrite VALUE in NONE;discriminate.
     - right;exists v,o,installed,prefix,suffix,id,decoded;split;[exact PRE|]. split;[exact POST|].
       split;[exact READ|]. rewrite DEST in OBS;cbn [snd] in OBS;rewrite VALUE in OBS;congruence. }

   rewrite DEST in COUNTER_SOURCE;cbn [snd] in COUNTER_SOURCE.
   split;[rewrite COUNTER_SOURCE;exact GENERATION|].
   split;[rewrite COUNTER_SOURCE;exact GENERATION_LOCAL|]. split.
   { apply next_generation_probe_ready;rewrite DEST;exact VALUE. }
   split.
   { intros answer reached PROBE.
     destruct (next_generation_probe_result _ _ _ PROBE) as [[n [N A]] REACHED].
     rewrite DEST in N;cbn [snd] in N;rewrite VALUE in N;inversion N;subst n;auto. }
   split.
   { destruct (boss_checked_generation (counter_value counter)) as [next|] eqn:DECISION.
     - left;exists next;split;[reflexivity|].
       exact (proj2 (proj1 (boss_checked_generation_success _ _) DECISION)).
     - right;split;[|reflexivity].
       apply (proj1 (boss_checked_generation_overflow _ (counter_u32 counter)));exact DECISION. }
   split.
   { intros ff aa rd ins chk observed resolved' restore_cut J OVERFLOW RESTORE_RUN COLLECT.
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)).
     { rewrite -J -DEST;exact PATH. }
   assert (HEAD:hd_error h=Some (N.of_nat old)).
     { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
     eapply selected_generation_overflow_return;try eassumption;exact I. }

   assert (RUNTIME_READY:volatile_runtime_initialized ev=Some true).
   { pose proof (episode_trace_runtime g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ RUNTIME PATH) as COHERENT.
     rewrite DEST in COHERENT;exact COHERENT. }
   split;[exact RUNTIME_READY|]. split.
   { apply runtime_initialized_probe_ready;rewrite DEST;exact RUNTIME_READY. }
   split.
   { intros answer reached PROBE.
     destruct (runtime_initialized_probe_result _ _ _ PROBE) as [ANSWER REACHED].
     rewrite DEST in ANSWER;cbn [snd] in ANSWER;rewrite RUNTIME_READY in ANSWER.
     split;[congruence|exact REACHED]. }
   assert (PAGES:volatile_page_size ev=Some 256).
   { pose proof (episode_trace_pages g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ META PATH) as COHERENT.
     rewrite DEST in COHERENT;exact COHERENT. }
   split;[exact PAGES|]. split.
   { intros HEADER INITIAL area_len LEN.
     pose proof (episode_trace_marker_probe g sector data_len marker ranges decode topology pages
       G DIV _ _ _ _ _ _ _ area_len INIT I HEADER INITIAL PATH LEN) as TEST.
     rewrite DEST in TEST;exact TEST. }
   split.
   { apply ensure_protection_probe_ready;rewrite DEST;exact PAGES. }
   split.
   { intros answer reached PROBE.
     destruct (ensure_protection_probe_result _ _ _ PROBE) as [ANSWER REACHED].
     rewrite DEST in ANSWER;cbn [snd] in ANSWER;rewrite PAGES in ANSWER.
     split;[exact ANSWER|exact REACHED]. }
   split.
   { intros ff aa area_len req cursor probe_final rd ins chk observed resolved' restore_cut
       J GENERATION_OK [AREA [CURSOR REQUEST]] PROBE RESTORE_RUN COLLECT.
     assert (INPUTS:area_len=pages*256 /\ option_map allocation_append (volatile_allocation ev)=Some cursor) by auto.
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)).
     { rewrite -J -DEST;exact PATH. }
     assert (HEAD:hd_error h=Some (N.of_nat old)).
     { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
     eapply selected_probe_error_return;try eassumption;exact I. }
   split.
   { intros ff aa fuel recognize req round alignment start reply rd ins chk observed resolved' restore_cut
       J GENERATION_OK BOSS_INPUTS SEARCH ERROR RESTORE_RUN COLLECT.
     pose proof (boss_search_inputs_runtime _ _ _ _ _ _ _ BOSS_INPUTS) as INPUTS.
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)).
     { rewrite -J -DEST;exact PATH. }
     assert (HEAD:hd_error h=Some (N.of_nat old)).
     { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
     eapply selected_search_error_return;try eassumption;exact I. }
   split.
   { intros ff aa fuel shape verify req round alignment start target fatal J GENERATION_OK BOSS_INPUTS SEARCH_CUT CUT reset.
     pose proof (boss_search_inputs_runtime _ _ _ _ _ _ _ BOSS_INPUTS) as INPUTS.
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)).
     { rewrite -J -DEST;exact PATH. }
     exact (conj (proj1 (selected_search_interruption valid view _ [] vo oo ff h aa image ram ev
       fuel shape verify req round alignment start target fatal word_max
       MARK DEC WORD GEO INIT INITIAL_NUM PREFIX P SEARCH_CUT CUT))
       (proj1 (proj2 (selected_search_interruption valid view _ [] vo oo ff h aa image ram ev
       fuel shape verify req round alignment start target fatal word_max
       MARK DEC WORD GEO INIT INITIAL_NUM PREFIX P SEARCH_CUT CUT)))). }
   split.
   + intros ff aa span J GENERATION_OK BOSS_ADMIT reserved.
     pose proof (boss_erased_admission_runtime _ _ _ _ _ _ BOSS_ADMIT) as RUNTIME_ADMIT.
     pose proof (runtime_erased_admission_mapped _ _ _ _ _ _ RUNTIME_ADMIT) as MAPPED_ADMIT.
     pose proof (mapped_erased_admission_forget _ _ _ _ _ MAPPED_ADMIT) as ADMIT.
     pose proof (mapped_erased_admission_bound _ _ _ _ _ MAPPED_ADMIT) as EXTENT_BOUND.
     destruct (erased_admission_alignment _ _ _ _ ADMIT) as [ALIGNED SPAN_ALIGNED].
     assert (PREFIX:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
       ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)).
     { rewrite -J -DEST;exact PATH. }
     assert (LATEST:volatile_latest_registry ev=Some old).
     { eapply idle_trace_open_latest;eassumption. }
     assert (ACQUIRE:Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo reserved).
     { eapply episodes_append with (more:=[]);[exact PREFIX|].
       eapply episodes_cons with (event:=None) (events:=[]);
         [eapply acquire_erased; eassumption|apply episodes_nil]. }
     destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT INITIAL_NUM ACQUIRE) as [PROTECTED NUMBER].
     split;[exact ACQUIRE|]. split;[exact PROTECTED|]. split;[exact NUMBER|].
     split.
     * split;[reflexivity|exact (proj2 (erased_admission_guards _ _ _ _ ADMIT))].
     * split.
       2: { split.
            - destruct CONCRETE_ROOTS as [rootid ROOTS].
              eapply boss_rehome_from_roots_numeric;[exact NUMBER|reflexivity|exact ROOTS].
            - intro point;eapply boss_acquisition_ram_cut;eassumption. }
       eapply generated_pending_writer_from_trace;try eassumption;try exact LATEST;try exact MAPPING;try exact I;
         try (autorewrite with control_evidence;assumption).
       -- cbn;rewrite COUNTER_SOURCE;exact GENERATION.
       -- exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))).
       -- split;[reflexivity|exact (proj2 (erased_admission_guards _ _ _ _ ADMIT))].
       -- destruct CONCRETE_ROOTS as [rootid ROOTS].
          eapply boss_rehome_from_roots_numeric;[exact NUMBER|reflexivity|exact ROOTS].
   + intros ff aa J GENERATION_OK recognize magic fuel req round alignment start r nsectors recycled
     LOCAL BOSS_INPUTS SEARCH GEOMETRY RECYCLE extent.
   pose proof (boss_search_inputs_runtime _ _ _ _ _ _ _ BOSS_INPUTS) as INPUTS.
   subst j;rewrite DEST in PATH.
     assert (LATEST:volatile_latest_registry ev=Some old).
   { eapply idle_trace_open_latest;eassumption. }
   assert (EXTENT_BOUND:offset extent+span extent<=pages*256).
   { pose proof (reusable_search_extent_bound _ _ _ _ _ _ _ _ _ _ _ SEARCH) as LIMIT.
     pose proof (proj2 (proj2 (proj2 (proj2 (proj2 GEOMETRY))))) as USEFUL.
     unfold extent,block_pages;cbn;nia. }
   assert (ALIGNED:offset extent mod 256=0).
   { change ((256*recycle_lo r) mod 256=0). rewrite Nat.mul_comm;apply Nat.mod_mul;lia. }
   assert (SPAN_ALIGNED:span extent mod 256=0).
   { change ((256*useful_pages r) mod 256=0). rewrite Nat.mul_comm;apply Nat.mod_mul;lia. }

   assert (HEAD:hd_error h=Some (N.of_nat old)).
   { exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
   destruct (recycling_acquisition_from_trace valid view _ [] vo oo ff h aa old image [] ram ev
     recognize magic fuel req round alignment start r nsectors recycled true
     INIT RAW PATH HEAD P LOCAL SEARCH GEOMETRY RECYCLE)
     as [previous [ACQUIRE [PROTECTED [ORDER HANDOFF]]]].
   exists previous;split;[exact ACQUIRE|]. split;[exact PROTECTED|].
   destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT INITIAL_NUM ACQUIRE) as [SAFE' NUMERIC].
   split;[exact NUMERIC|]. split;[exact ORDER|].
   split.
   + unfold boundary_journal,recycling_acquisition_boundary,neutral_open_boundary;
       destruct (neutral_end_ recycled);reflexivity.
   + split.
     * exact (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
         _ _ _ _ _ _ _ INIT ACQUIRE))).
     * split.
       { intro SUCCESS;split.
         2: { split;[exact (HANDOFF SUCCESS)|]. split.
              2: { split.
                   - destruct CONCRETE_ROOTS as [rootid ROOTS].
                     eapply boss_rehome_from_roots_numeric;[|reflexivity|exact ROOTS].
                     unfold recycling_acquisition_boundary in NUMERIC;rewrite SUCCESS in NUMERIC;exact NUMERIC.
                   - intro point;eapply boss_acquisition_ram_cut;try eassumption.
                     unfold recycling_acquisition_boundary,recycling_cursor_evidence in ACQUIRE;
                       rewrite SUCCESS in ACQUIRE;exact ACQUIRE. }
              eapply generated_pending_writer_from_trace;try eassumption;try exact LATEST;try exact MAPPING;try exact I;
         try (autorewrite with control_evidence;assumption).
              - cbn;rewrite COUNTER_SOURCE;exact GENERATION.
              - unfold recycling_acquisition_boundary in ACQUIRE;rewrite SUCCESS in ACQUIRE;exact ACQUIRE.
              - exact (HANDOFF SUCCESS).
              - unfold recycling_acquisition_boundary in NUMERIC;rewrite SUCCESS in NUMERIC;exact NUMERIC.
              - destruct CONCRETE_ROOTS as [rootid ROOTS].
                eapply boss_rehome_from_roots_numeric;[|reflexivity|exact ROOTS].
                unfold recycling_acquisition_boundary in NUMERIC;rewrite SUCCESS in NUMERIC;exact NUMERIC. }
         pose proof (proj1 (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
           _ _ _ _ _ _ _ INIT RAW PATH)) as SOURCE.
         destruct (recycling_physical_handoff g sector fuel recognize magic ff (protection_table ram)
           req round alignment pages start r nsectors recycled (required_ranges ram)
           LOCAL (proj1 (proj1 (proj1 (proj1 SOURCE))))
           (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 SOURCE)))))) SEARCH GEOMETRY RECYCLE)
           as [VALID [KEEP [FRAME DONE]]].
         pose proof (proj1 (DONE SUCCESS)) as FREE.
         pose proof NUMERIC as NUMBER.
         unfold recycling_acquisition_boundary in NUMBER;rewrite SUCCESS in NUMBER.
         change (state_numeric word_max (reservation_state true extent ram)) in NUMBER.
         pose proof (numeric_pending word_max _ (reservation_token true extent) NUMBER eq_refl) as CERT.
         change (range_check true word_max extent=None) in CERT.
         apply AllocationAdmission.vacantb_spec in FREE.
         unfold ram_reservation_check;rewrite FREE.
         unfold range_check in CERT.
         destruct (offset extent+span extent<=?word_max);[|discriminate].
         destruct (AllocationAdmission.page_limit extent<=?1024);[reflexivity|discriminate]. }
       split.
       -- intros ERROR rd ins chk observed restore_cut RESTORE_RUN.
          eapply selected_recycling_error_return;try eassumption;exact I.
       -- split.
          ++ intro STOP; eapply selected_recycling_interruption; eassumption.
          ++ intro SUCCESS; eapply selected_recycling_before_reserve_reset; eassumption.
Qed.

(* A10 boot prefixes may themselves reset or stop. Only Usable can resume
   an ordinary episode; no pre-reset RAM is supplied to the reconstruction. *)
Theorem owned_reset_boot_prefix vi oi initial valid view f h a abandoned word_max final :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 Trace vi oi initial [] valid view
   ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence abandoned) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (Logged (Boot f) h a,Selecting) final ->
 let reached:=((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence abandoned) in
 Trace vi oi initial [] valid view reached /\ Safe valid view reached /\
 phase_numeric word_max marker ranges (snd (fst reached)) /\
 boundary_receipts reached=boundary_receipts initial /\
 publications (boot_journal final)=h /\
 (forall j id d ram,final=(j,Usable id d ram) ->
   let resumed:=((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence abandoned)) in
   Trace vi oi initial [] valid view resumed /\ Safe valid view resumed /\
   phase_numeric word_max marker ranges (IdleBoundary id d ram) /\
   data_caller DataBegin ram /\
   controller_read (snd resumed)=idle_control).
Proof.
 intros MARK DEC WORD GEO INIT NUM PREFIX BOOT reached.
 assert (ALL:Trace vi oi initial [] valid view reached).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   apply (boot_episode g sector data_len marker ranges decode topology pages valid view
     (Logged (Boot f) h a,Selecting) final abandoned);[intros;apply READERS|exact BOOT]. }
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT NUM ALL) as [SAFE NUMERIC].
 pose proof (proj1 (proj2 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ INIT ALL))) as RECEIPTS.
 assert (HISTORY:publications (boot_journal final)=h).
 { pose proof (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ INIT PREFIX)) as START.
   exact (proj2 (boundary_boot_prefix_safe g sector data_len valid view marker ranges decode topology pages
     G DIV (Logged (Boot f) h a,Selecting) final abandoned START
     (fun c _=>READERS c) BOOT)). }
 split;[exact ALL|]. split;[exact SAFE|]. split;[exact NUMERIC|].
 split;[exact RECEIPTS|]. split;[exact HISTORY|].
 intros j id d ram EQ;subst final;cbn [boot_journal boot_pc fst snd] in *.
 assert (RESUME:Trace vi oi initial [] valid view
   ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence abandoned))).
 { eapply episodes_append with (more:=[]);[exact ALL|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply resume_episode|constructor]. }
 destruct (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max _ _ _ _ _ _ _ MARK DEC WORD GEO INIT NUM RESUME) as [FRESH FRESHNUM].
 split;[exact RESUME|]. split;[exact FRESH|]. split;[exact FRESHNUM|].
 split;[exact (proj1 (common_begin sector data_len valid view marker ranges decode pages j id d ram (proj1 FRESH)))|reflexivity].
Qed.

Theorem owned_failed_cut_repeated_boot valid view f h a old d s e count same compare first selected
 word_max log tail vf of_ failed read inspect check point :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same))
   tt (PairSelected (first::selected)) tt ->
 owned_body_run BodyWaiting (first::selected) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
     owned_local_evidence old d s e) log BodyFailed tail vf of_ failed ->
 owned_restore_cut_guard old of_ failed read inspect check point ->
 exists ff acks abandoned,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_
   ((Logged (Boot ff) h acks,RebuildingBoundary Selecting),forget_volatile_evidence abandoned) InterruptedReset /\
 ff=control_image (journal_control (boundary_journal failed)) /\
 (forall j id decoded ram,
   clos_refl_trans boot_state (boot_step g sector data_len vf marker ranges decode topology pages)
     (Logged (Boot ff) h acks,Selecting) (j,Usable id decoded ram) ->
   let resumed:=((j,IdleBoundary id decoded ram),recovered_page_evidence j id (forget_volatile_evidence abandoned)) in
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vf of_ resumed /\
   Safe vf of_ resumed /\ phase_numeric word_max marker ranges (IdleBoundary id decoded ram) /\
   data_caller DataBegin ram /\ controller_read (snd resumed)=idle_control /\
   boundary_receipts resumed=client_receipts e /\ publications j=h /\
   id=old /\ decoded=d /\
   unchanged (certificate_ranges ranges (Certificate old d))
     (object_flash sector f) (object_flash sector (control_image (journal_control j)))).
Proof.
 intros MARK DEC WORD GEO INIT OUT ARM PREPASS RUN CUT.
 destruct (owned_marked_failed_cut valid view f h a old d s e count same compare first selected
   word_max log tail vf of_ failed read inspect check point MARK DEC WORD GEO INIT OUT ARM PREPASS RUN CUT)
   as [ff [acks [abandoned [COMPLETE [POST FLASH]]]]].
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as NUM.
 exists ff,acks,abandoned;split;[exact COMPLETE|]. split;[exact FLASH|].
 intros j id decoded ram BOOT.
 destruct (owned_reset_boot_prefix valid view _ vf of_ ff h acks abandoned word_max (j,Usable id decoded ram)
   MARK DEC WORD GEO INIT NUM (proj1 POST) BOOT)
   as [PATH [SAFE [NUMERIC [RECEIPTS [HISTORY RESUME]]]]].
 assert (SEL:selected_live ((Logged (Ready f) h a,IdleBoundary old d s),e) (Certificate old d)).
 { split;[exact (proj2 (proj2 INIT))|].
   exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INIT))))))). }
 destruct (episode_no_publication_transport g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ (Certificate old d) INIT SEL PATH HISTORY) as [LAST [SAME KEEP]].
 destruct (selected_usable_identity sector data_len vf of_ marker ranges decode pages
   _ _ _ _ _ _ LAST SAME) as [ID [IMAGE CALL]].
 destruct (RESUME j id decoded ram eq_refl) as [NEXT [FRESH [FRESHNUM [BEGIN CONTROL]]]].
 split;[exact NEXT|]. split;[exact FRESH|]. split;[exact FRESHNUM|].
 split;[exact BEGIN|]. split;[exact CONTROL|]. split;[exact RECEIPTS|].
 split;[exact HISTORY|]. split;[exact ID|]. split;[exact IMAGE|exact KEEP].
Qed.

(* Recovery reads a physical marker preserved by its journal prefix, including
   interrupted erases and repeated resets. No volatile evidence supplies it. *)
Theorem boot_rechecks_physical_marker valid view initial final e area_len :
 Safe valid view ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence e) ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages) initial final ->
 persistence_marker_recognized sector (control_image (journal_control (boot_journal initial))) ->
 8<=area_len ->
 persistence_marker_test sector area_len (control_image (journal_control (boot_journal final)))=true.
Proof.
 intros INV LOCAL RUN INITIAL LEN;apply persistence_marker_test_spec;split;[exact LEN|].
 intros i I;unfold object_flash.
 rewrite (boundary_boot_objects_preserved g sector data_len valid view marker ranges decode topology pages
   G DIV initial final e INV LOCAL RUN (2*sector+i) ltac:(lia)).
 exact (INITIAL i I).
Qed.

Theorem owned_body_reset_marker_recovery pc todo vi oi initial log tail vf of_ reset_state e
 boot_final area_len :
 Safe vi oi initial -> external_structure marker initial -> marker_header_covered marker ->
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal initial))) ->
 owned_body_run pc todo vi oi initial log BodyInterrupted tail vf of_
   ((boot_journal reset_state,RebuildingBoundary (boot_pc reset_state)),forget_volatile_evidence e) ->
 clos_refl_trans boot_state (boot_step g sector data_len vf marker ranges decode topology pages)
   reset_state boot_final -> 8<=area_len ->
 Trace vi oi initial [] vf of_
   ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence e) /\
 Safe vf of_ ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence e) /\
 persistence_marker_test sector area_len (control_image (journal_control (boot_journal boot_final)))=true.
Proof.
 intros INV STRUCT HEADER INITIAL RUN BOOT LEN.
 pose proof (owned_body_run_trace _ _ _ _ _ _ _ _ _ _ _ RUN) as PREFIX.
 pose proof (owned_body_run_marker _ _ _ _ _ _ _ _ _ _ _ INV STRUCT RUN) as KEEP.
 assert (AT_RESET:Safe vf of_
   ((boot_journal reset_state,RebuildingBoundary (boot_pc reset_state)),forget_volatile_evidence e)).
 { exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
     G DIV _ _ _ _ _ _ _ INV PREFIX)). }
 assert (PHYSICAL:persistence_marker_recognized sector (control_image (journal_control (boot_journal reset_state)))).
 { eapply persistence_marker_transport;[exact HEADER|exact KEEP|exact INITIAL]. }
 assert (TRACE:Trace vi oi initial [] vf of_
   ((boot_journal boot_final,RebuildingBoundary (boot_pc boot_final)),forget_volatile_evidence e)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   eapply boot_episode;[intros;apply READERS|exact BOOT]. }
 split;[exact TRACE|]. split.
 - exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages
     G DIV _ _ _ _ _ _ _ INV TRACE)).
 - eapply boot_rechecks_physical_marker;[exact AT_RESET|intros;apply READERS|exact BOOT|exact PHYSICAL|exact LEN].
Qed.

(* RAM-cut representatives consumed by the existing marked interruption route.
   Only the physical/reset projection is equated; no partial index is completed. *)
Theorem owned_erased_ram_cut pc selected vi oi x prefix valid view f h a image root s e i todo r point :
 owned_body_run pc selected vi oi x prefix BodyAcquiring (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 pending_preparation s=None -> runtime_erased_admission sector pages e s f r ->
 owned_body_run pc selected vi oi x prefix BodyInterrupted (i::todo) valid view
   (acquisition_ram_reset point false r s e (Logged (Ready f) h a)).
Proof.
 intros PREFIX P ADMIT;rewrite acquisition_ram_reset_same.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 eapply body_cons with (log:=[]) (logs:=[]);[eapply body_erased;eauto|].
 eapply body_cons with (log:=[]) (logs:=[]);[apply body_reset_reserved;apply record_step;apply reset_ready|constructor].
Qed.

Theorem owned_recycled_ram_cut pc selected vi oi x prefix valid view f h a old previous image root s e i todo
 recognize magic fuel req round alignment start r count result word_max point :
 owned_body_run pc selected vi oi x prefix BodyAcquiring (i::todo) valid view
   ((Logged (Ready f) h a,OperationBoundary image root s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 recognizer_local sector recognize -> pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 runtime_search_inputs sector pages word_max e s f req start -> neutral_end_ result=NeutralSuccess ->
 owned_body_run pc selected vi oi x prefix BodyInterrupted (i::todo) (validate (neutral_flash result)) view
   (acquisition_ram_reset point false (block_pages (recycle_lo r) (useful_pages r)) s
      (selected_evidence old previous e) (Logged (Ready (neutral_flash result)) h a)).
Proof.
 intros PREFIX RAW HEAD IN LOCAL P SEARCH GEO RUN INPUTS OK;rewrite acquisition_ram_reset_same.
 rewrite -(app_nil_r prefix);eapply owned_body_run_append;[exact PREFIX|].
 pose proof (body_recycled valid view f h a old previous image root s e i todo
   recognize magic fuel req round alignment start r count result word_max RAW HEAD IN LOCAL P SEARCH GEO RUN INPUTS) as EDGE.
 unfold acquisition_pc,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,
   recycling_cursor_evidence in EDGE;rewrite OK in EDGE;cbn in EDGE.
 eapply body_cons with (log:=[]) (logs:=[]);[exact EDGE|].
 eapply body_cons with (log:=[]) (logs:=[]);[apply body_reset_reserved;apply record_step;apply reset_ready|constructor].
Qed.

(* A bundle of existing observations, not a new state or transition relation.
   None of these facts is supplied again at an intermediate boundary. *)


Theorem owner_invariants_trace vi oi initial events vf of_ final :
 marker_header_covered marker -> decoded_allocation_geometry pages decode -> owner_invariants vi oi initial ->
 Trace vi oi initial events vf of_ final -> owner_invariants vf of_ final.
Proof.
 intros HEADER GEO [SAFE RAW PAGE RUNTIME MATCH LOCAL COUNTER ALLOC ORIGIN BOUND LATEST STRUCT PHYSICAL] RUN.
 destruct (episode_trace_raw g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ SAFE RAW RUN) as [SAFE' RAW'].
 destruct (episode_trace_counter g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ MATCH COUNTER SAFE RUN) as [COUNTER' SOURCE].
 constructor;try assumption.
 - eapply episode_trace_pages;eassumption.
 - eapply episode_trace_runtime;eassumption.
 - rewrite SOURCE;exact MATCH.
 - rewrite SOURCE;exact LOCAL.
 - exact (proj1 (episode_trace_allocation_known g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ MATCH ALLOC SAFE RUN)).
 - eapply episode_trace_allocation_origin;eassumption.
 - eapply episode_trace_append_bound;eassumption.
 - eapply episode_trace_ordinary_latest;eassumption.
 - exact (episode_trace_external_structure g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ SAFE STRUCT RUN).
 - exact (proj2 (episode_trace_marker g sector data_len marker ranges decode topology pages G DIV
     _ _ _ _ _ _ _ SAFE STRUCT HEADER PHYSICAL RUN)).
Qed.

Lemma owner_invariants_idle_latest valid view j id d ram e :
 owner_invariants valid view ((j,IdleBoundary id d ram),e) ->
 volatile_latest_registry e=Some id.
Proof.
 intros INV.
 pose proof (owner_latest _ _ _ INV) as LATEST.
 pose proof (latest_idle_head sector data_len valid view marker ranges decode pages j id d ram e
   (owner_safe _ _ _ INV)) as HEAD.
 change (option_map N.of_nat (volatile_latest_registry e)=hd_error (publications j)) in LATEST.
 rewrite HEAD in LATEST;destruct (volatile_latest_registry e) as [actual|] eqn:E;cbn in LATEST;try discriminate.
 inversion LATEST;assert(actual=id) by lia;subst;reflexivity.
Qed.

Lemma owner_invariants_idle_ready valid view j id d ram e :
 owner_invariants valid view ((j,IdleBoundary id d ram),e) -> data_caller DataBegin ram.
Proof.
 intro INV;exact (proj1 (common_begin sector data_len valid view marker ranges decode pages j id d ram
   (proj1 (owner_safe _ _ _ INV)))).
Qed.

(* A delivered result permits ordinary reuse only at Idle/Client.  Frozen
   preserves the delivered error, but does not authorize DataBegin. *)
Definition owner_return_reentry valid view (reached:execution_boundary) :=
 match snd (fst reached) with
 | IdleBoundary id d ram | ClientBoundary id d ram =>
   let ready:=((fst (fst reached),IdleBoundary id d ram),snd reached) in
   Trace valid view reached [] valid view ready /\
   owner_invariants valid view ready /\
   delivered_owner_closed (snd ready) /\ data_caller DataBegin ram
 | FrozenBoundary old candidate root ram => ~boundary_begin_caller (fst reached)
 | _=>True
 end.

Theorem owner_delivered_reentry vi oi initial receipts valid view reached exit :
 marker_header_covered marker -> decoded_allocation_geometry pages decode ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts valid view reached exit ->
 owner_invariants valid view reached ->
 exit_observation exit<>None -> owner_return_reentry valid view reached.
Proof.
 intros HEADER GEO DONE INV RETURN.
 pose proof (completed_operation_owner_closed g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ DONE RETURN) as CLOSED.
 destruct reached as [[j phase] ev];destruct phase;cbn [owner_return_reentry fst snd];try exact I.
 - split;[constructor|]. split;[exact INV|]. split;[exact CLOSED|].
   eapply owner_invariants_idle_ready;exact INV.
 - assert (RESUME:Trace valid view ((j,ClientBoundary id decoded ram),ev) [] valid view
       ((j,IdleBoundary id decoded ram),ev)).
   { eapply episodes_cons with (event:=None) (events:=[]);[apply resume_client_episode|constructor]. }
   pose proof (owner_invariants_trace _ _ _ _ _ _ _ HEADER GEO INV RESUME) as READY.
   split;[exact RESUME|]. split;[exact READY|]. split;[exact CLOSED|].
   eapply owner_invariants_idle_ready;exact READY.
 - apply frozen_no_begin.
Qed.

Lemma operation_unpublished_not_open vi oi initial events vf of_ final exit :
 operation_execution g sector data_len marker ranges decode topology pages vi oi initial events vf of_ final exit ->
 delivered_receipts exit=[] -> ~open_destination final.
Proof.
 intros RUN;induction RUN;intros EMPTY [jz [iz [rz [sz [ez EQ]]]]];try discriminate.
 - subst y;destruct event as [receipt|].
   + cbn [edge_exit] in H0;inversion H0;subst;discriminate.
   + discriminate H0.
 - apply (IHRUN EMPTY);repeat eexists;exact EQ.
Qed.
Lemma completed_empty_not_open vi oi initial vf of_ final exit :
 completed_operation g sector data_len marker ranges decode topology pages vi oi initial [] vf of_ final exit ->
 ~open_destination final.
Proof.
 intro DONE;pose proof (completed_no_receipts _ _ _ _ _ _ _ DONE) as EMPTY.
 destruct DONE as [vm [om [before [previous [returned [PREFIX [RUN EQ]]]]]]].
 eapply operation_unpublished_not_open;eassumption.
Qed.
Lemma returned_prepass_no_boss result pc final success :
 pair_prepass_return result=Some success -> marked_boss_requested result pc final=false.
Proof. destruct result as [|idx|[|first rest]];cbn;intros H;try discriminate;reflexivity. Qed.
Theorem owned_entry_services_terminal_for (Q:owner_service_response->Prop) valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> persistence_marker_recognized sector f -> journal_object_mapping data_len pages ->
 volatile_latest_registry e=Some old -> mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 runtime_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 generation_decoding_matches sector decode (counter_decoder e) ->
 generation_decoding_local sector (counter_decoder e) ->
 counter_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 allocation_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode e ->
 allocation_append_bound pages e ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (local_cleanup_mask pc final outcome resolved cut=None -> forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   (marked_boss_requested result pc final=true -> vo=vf /\ oo=of_ /\
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)=marked_selected_boundary final) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services_for Q word_max oo ff h aa old image ram ev) ->
 (marked_boss_requested result pc final=false -> Q (indexed_prebody_response result pc final outcome resolved cut)) ->
 owner_terminal_for Q word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [].
Proof.
 intros MARKER_HEADER PHYSICAL_MARKER OBJECT_MAPPING INITIAL_LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION DECODE_GEOMETRY INITIAL_ORIGIN INITIAL_APPEND OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES PREBODY.
 destruct (pair_prepass_return result) as [success|] eqn:ENTRY_RETURN.
 { destruct (owned_pair_entry_return valid view (Logged (Ready f) h a) old d s e count same compare result success word_max
     MARK DEC WORD GEO INIT OUT ARM ENTRY ENTRY_RETURN) as [DONE [POST [COMPUTED OBS]]].
   unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
   split;[reflexivity|]. exists (EntryResponse result);split;[cbn [owner_response_matches];rewrite ENTRY_RETURN;reflexivity|].
   specialize (PREBODY (returned_prepass_no_boss _ _ _ _ ENTRY_RETURN));
   unfold indexed_prebody_response in PREBODY;rewrite ENTRY_RETURN in PREBODY;split;[exact PREBODY|exact I]. }
 destruct (local_cleanup_mask pc final outcome resolved cut) as [local_mask|] eqn:LOCAL_CASE.
 { destruct (local_cleanup_mask_spec _ _ _ _ _ _ LOCAL_CASE)
     as [PC [OBS [COLLECT [CUT [current ORDINARY]]]]];subst pc outcome resolved cut.
   destruct result as [|index|selected];try discriminate.
   destruct selected as [|first selected];[discriminate|].
   destruct (BODY (first::selected) eq_refl) as [RUN FINISHED].
   specialize (RESTORE (first::selected) eq_refl (or_introl eq_refl)).
   specialize (MASK (first::selected) eq_refl).
   destruct (owned_marked_local_cleanup_returned valid view f h a old d s e count same compare first selected
     word_max log tail vf of_ final read inspect check local_mask current
     MARK DEC WORD GEO INIT OUT ARM ENTRY RUN RESTORE MASK ORDINARY)
     as [destination [DONE [POST [FLASH [ff [hh [aa [restored [ram [ev DEST]]]]]]]]]].
   assert (INDEX:Q (LocalBodyCleanupResponse local_mask)).
   { specialize (PREBODY eq_refl).
     unfold indexed_prebody_response in PREBODY;cbn [pair_prepass_return] in PREBODY.
     rewrite LOCAL_CASE in PREBODY;exact PREBODY. }
   unfold owner_terminal_for;exists [],vf,of_,destination,ReturnedBodyError.
   split;[exact DONE|]. split;[exact POST|]. split;[reflexivity|].
   exists (LocalBodyCleanupResponse local_mask);split;[reflexivity|]. split;[exact INDEX|].
   exists ff,hh,aa,old,restored,ram,ev;exact DEST. }
 specialize (SERVICES eq_refl).
 unfold indexed_prebody_response in PREBODY;rewrite ENTRY_RETURN in PREBODY;rewrite LOCAL_CASE in PREBODY.
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 destruct (owned_entry_marked_recycling valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut
   MARKER_HEADER OBJECT_MAPPING INITIAL_LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION DECODE_GEOMETRY INITIAL_ORIGIN INITIAL_APPEND OUT ARM ENTRY BODY RESTORE MASK)
   as [vo [oo [destination [RESULT [PUB [RECEIPTS [DISPATCH ROUTES]]]]]]].
 assert (PREBODY_RETURN:forall exit,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo destination exit ->
   Q (prebody_response result pc outcome resolved cut)).
 { intros exit DONE;apply PREBODY.
   destruct (marked_boss_requested result pc final) eqn:WANT;[|reflexivity].
   exfalso;eapply completed_empty_not_open;[exact DONE|exact (proj1 (DISPATCH eq_refl))]. }
 destruct RESULT as [[exit [KIND [DONE POST]]]|[j0 [image0 [root0 [ram0 [ev0 [DEST0 [PATH [SAFE [NUM [ROOT [P [CHOSEN [ARMED [LIVE [CALL [FRAME [ROOTS READY]]]]]]]]]]]]]]]]]].
 - unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (prebody_response result pc outcome resolved cut);split;[unfold prebody_response;rewrite ENTRY_RETURN;apply (completed_no_receipts _ _ _ _ _ _ _ DONE)|(split;[exact (PREBODY_RETURN _ DONE)|unfold prebody_response;rewrite ENTRY_RETURN;exact I])].
 - destruct ROUTES as [[exit [DONE POST]]|[j [image [ram [ev [DEST [SELECT [ARMED_ [LIVE_ [ALLOC [ORIGIN [APPEND_BOUND [INPUTS STAGE]]]]]]]]]]]]].
   + unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (prebody_response result pc outcome resolved cut);split;[unfold prebody_response;rewrite ENTRY_RETURN;apply (completed_no_receipts _ _ _ _ _ _ _ DONE)|(split;[exact (PREBODY_RETURN _ DONE)|unfold prebody_response;rewrite ENTRY_RETURN;exact I])].
   + rewrite DEST in DEST0;inversion DEST0;subst j0 image0 root0 ram0 ev0.
     destruct j as [jc pubs acks];destruct READY as [ff READY];cbn in READY;subst jc.
     rewrite DEST in PUB;change (pubs=h) in PUB;subst pubs.
     rewrite DEST in PATH.
     assert (MARKER_TEST:persistence_marker_test sector (pages*256) ff=true).
     { exact (episode_trace_marker_probe g sector data_len marker ranges decode topology pages G DIV
         _ _ _ _ _ _ _ (pages*256) INIT I MARKER_HEADER PHYSICAL_MARKER PATH ltac:(destruct MAPPING;lia)). }
     pose proof (episode_trace_runtime g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ RUNTIME PATH) as INITIALIZED.
     pose proof (episode_trace_pages g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ META PATH) as PAGE_SIZE.
     assert (COORDS:marked_boss_requested result pc final=true -> vo=vf /\ oo=of_ /\
       ((Logged (Ready ff) h acks,OpenBoundary image [] ram),ev)=marked_selected_boundary final).
     { intro WANT;destruct (DISPATCH WANT) as [_ [V [O STATE]]];split;[exact V|]. split;[exact O|].
       rewrite <-DEST;exact STATE. }
     specialize (SERVICES vo oo ff acks image ram ev PATH COORDS SELECT MARKER_TEST INITIALIZED PAGE_SIZE).
     unfold boss_pipeline_services_for in SERVICES.
     destruct (boss_size_preflight word_max image) as [|total|total] eqn:SIZE.
     * destruct SERVICES as [cleanup [REST INDEX]].
       destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [RUN MASK_]]]]]]]];subst cleanup.
       destruct (STAGE ff acks rd ins chk observed resolved' restore_cut eq_refl RUN MASK_)
         as [last [exit [KIND [DONE [POST OTHER]]]]].
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 0 (cleanup_response observed resolved' restore_cut));split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
     * destruct SERVICES as [cleanup [REST INDEX]].
       destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [RUN MASK_]]]]]]]];subst cleanup.
       destruct (STAGE ff acks rd ins chk observed resolved' restore_cut eq_refl RUN MASK_)
         as [last [exit [KIND [DONE [POST OTHER]]]]].
       unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 1 (cleanup_response observed resolved' restore_cut));split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
     * destruct STAGE as [FORM [BOUND [CAP [counter [VALUE [SOURCE [MATCH [LOCAL [PROBE [UNIQUE [NEXT [OVERFLOW [RUNTIME_ [RP [RU [PAGE [MARKER [ENSURE [EU [REJECT [SEARCH [STOP [ERASE RECYCLE]]]]]]]]]]]]]]]]]]]]]]].
       specialize (SERVICES counter VALUE).
       destruct (boss_checked_generation (counter_value counter)) as [next|] eqn:GEN.
       2: { destruct SERVICES as [cleanup [REST INDEX]].
       destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [RUN MASK_]]]]]]]];subst cleanup.
         destruct (OVERFLOW ff acks rd ins chk observed resolved' restore_cut eq_refl eq_refl RUN MASK_)
           as [last [exit [KIND [DONE [POST OTHER]]]]].
         unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 2 (cleanup_response observed resolved' restore_cut));split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE). }
       assert (NONZERO:Some next<>@None N) by discriminate.
       destruct SERVICES as [[cursor [probe_final [CURSOR [RUN REST]]]]|
         [[fuel [recognize [req [round [alignment [start [reply [INPUT [RUN [ERROR REST]]]]]]]]]]|
         [[fuel [shape [verify [req [round [alignment [start [target [fatal [INPUT [PREFIX [INTERRUPTED INDEX]]]]]]]]]]]]|
         [[span [ADMIT LAST]]|[recognize [magic [fuel [req [round [alignment [start [r [nsectors [recycled [LOC [INPUT [SEARCH_RUN [GEOM [RUN LAST]]]]]]]]]]]]]]]]]]].
       -- destruct REST as [cleanup [REST INDEX]].
          destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [REST MASK_]]]]]]]];subst cleanup.
          destruct (REJECT ff acks (pages*256) (fun _=>Some total) cursor probe_final rd ins chk observed resolved' restore_cut
             eq_refl NONZERO (conj eq_refl (conj CURSOR eq_refl)) RUN REST MASK_)
            as [UNCHANGED [last [exit [KIND [DONE [POST OTHER]]]]]].
          unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 0 (cleanup_response observed resolved' restore_cut));split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct REST as [cleanup [REST INDEX]].
          destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [REST MASK_]]]]]]]];subst cleanup.
          destruct (SEARCH ff acks fuel recognize req round alignment start reply rd ins chk observed resolved' restore_cut
             eq_refl NONZERO INPUT RUN ERROR REST MASK_)
            as [last [exit [KIND [DONE [POST OTHER]]]]].
          unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 1 (cleanup_response observed resolved' restore_cut));split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct (STOP ff acks fuel shape verify req round alignment start target fatal eq_refl NONZERO INPUT PREFIX INTERRUPTED)
            as [DONE POST].
          unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (SearchInterruptedResponse fatal);split;[|(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct (ERASE ff acks span eq_refl NONZERO ADMIT)
            as [TRACE_ [SAFE_ [NUM_ [HANDOFF [WRITER [REHOME CUT]]]]]].
          destruct LAST as [[encode [plan [result_ [FORMAT [PLAN [WRITE TAIL]]]]]]|[point INDEX]].
          ++ eapply (generated_writer_services_terminal_for Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ base checked);
               try eassumption;exact TAIL.
          ++ destruct (CUT point) as [DONE [POST RECEIPT_]].
             unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionCutResponse point);split;[reflexivity|(split;[exact INDEX|exact I])].
       -- destruct (RECYCLE ff acks eq_refl NONZERO recognize magic fuel req round alignment start r nsectors recycled
             LOC INPUT SEARCH_RUN GEOM RUN) as [previous [TRACE_ [SAFE_ [NUM_ [RAW_ [PUB_ [REC_ [SUCCESS [ERROR [INTERRUPT CUT]]]]]]]]]].
          destruct (neutral_end_ recycled) eqn:END.
          ++ destruct (SUCCESS eq_refl) as [CHECK [HANDOFF [WRITER [REHOME CUT_]]]].
             destruct LAST as [[encode [plan [result_ [FORMAT [PLAN [WRITE TAIL]]]]]]|[point INDEX]].
             ** eapply (generated_writer_services_terminal_for Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ base checked);
                  try eassumption;exact TAIL.
             ** destruct (CUT_ point) as [DONE [POST RECEIPT_]].
                unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionCutResponse point);split;[reflexivity|(split;[exact INDEX|exact I])].
          ++ destruct LAST as [cleanup [REST INDEX]].
             destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [CEQ [REST MASK_]]]]]]]];subst cleanup.
             destruct (ERROR eq_refl rd ins chk observed restore_cut REST)
               as [last [exit [KIND [DONE [POST OTHER]]]]].
             unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 2 (cleanup_response observed None restore_cut));split;[|destruct restore_cut;(split;[exact INDEX|exact I])];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
          ++ destruct (INTERRUPT (or_intror eq_refl)) as [last [exit [DONE [POST OTHER]]]].
             unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (RecyclingInterruptedResponse NeutralReset);split;[|split;[exact LAST|exact I]];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
          ++ destruct (INTERRUPT (or_introl eq_refl)) as [last [exit [DONE [POST OTHER]]]].
             unfold owner_terminal_for;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (RecyclingInterruptedResponse NeutralFatal);split;[|split;[exact LAST|exact I]];apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
Qed.

Theorem owned_entry_services_terminal valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> persistence_marker_recognized sector f -> journal_object_mapping data_len pages ->
 volatile_latest_registry e=Some old -> mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 page_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 runtime_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 generation_decoding_matches sector decode (counter_decoder e) ->
 generation_decoding_local sector (counter_decoder e) ->
 counter_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 allocation_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode e ->
 allocation_append_bound pages e ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev) ->
 owner_terminal word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [].
Proof.
 intros MARKER_HEADER PHYSICAL_MARKER OBJECT_MAPPING INITIAL_LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION DECODE_GEOMETRY INITIAL_ORIGIN INITIAL_APPEND OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES.
 destruct (pair_prepass_return result) as [success|] eqn:ENTRY_RETURN.
 { destruct (owned_pair_entry_return valid view (Logged (Ready f) h a) old d s e count same compare result success word_max
     MARK DEC WORD GEO INIT OUT ARM ENTRY ENTRY_RETURN) as [DONE [POST [COMPUTED OBS]]].
   unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
   split;[reflexivity|]. exists (EntryResponse result);cbn [owner_response_matches];rewrite ENTRY_RETURN;reflexivity. }
 pose proof (proj1 (episode_trace_idle_numeric g sector data_len marker ranges decode topology pages G DIV
   word_max valid view _ [] valid view (Logged (Ready f) h a) old d s e INIT
   (episodes_nil _ _ _ _ _ _ _ _ valid view _) MARK DEC)) as INITIAL_NUM.
 destruct (owned_entry_marked_recycling valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut
   MARKER_HEADER OBJECT_MAPPING INITIAL_LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION DECODE_GEOMETRY INITIAL_ORIGIN INITIAL_APPEND OUT ARM ENTRY BODY RESTORE MASK)
   as [vo [oo [destination [RESULT [PUB [RECEIPTS [DISPATCH ROUTES]]]]]]].
 destruct RESULT as [[exit [KIND [DONE POST]]]|[j0 [image0 [root0 [ram0 [ev0 [DEST0 [PATH [SAFE [NUM [ROOT [P [CHOSEN [ARMED [LIVE [CALL [FRAME [ROOTS READY]]]]]]]]]]]]]]]]]].
 - unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (prebody_response result pc outcome resolved cut);unfold prebody_response;rewrite ENTRY_RETURN;apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
 - destruct ROUTES as [[exit [DONE POST]]|[j [image [ram [ev [DEST [SELECT [ARMED_ [LIVE_ [ALLOC [ORIGIN [APPEND_BOUND [INPUTS STAGE]]]]]]]]]]]]].
   + unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (prebody_response result pc outcome resolved cut);unfold prebody_response;rewrite ENTRY_RETURN;apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
   + rewrite DEST in DEST0;inversion DEST0;subst j0 image0 root0 ram0 ev0.
     destruct j as [jc pubs acks];destruct READY as [ff READY];cbn in READY;subst jc.
     rewrite DEST in PUB;change (pubs=h) in PUB;subst pubs.
     rewrite DEST in PATH.
     assert (MARKER_TEST:persistence_marker_test sector (pages*256) ff=true).
     { exact (episode_trace_marker_probe g sector data_len marker ranges decode topology pages G DIV
         _ _ _ _ _ _ _ (pages*256) INIT I MARKER_HEADER PHYSICAL_MARKER PATH ltac:(destruct MAPPING;lia)). }
     pose proof (episode_trace_runtime g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ RUNTIME PATH) as INITIALIZED.
     pose proof (episode_trace_pages g sector data_len marker ranges decode topology pages
       _ _ _ _ _ _ _ META PATH) as PAGE_SIZE.
     specialize (SERVICES vo oo ff acks image ram ev PATH SELECT MARKER_TEST INITIALIZED PAGE_SIZE).
     unfold boss_pipeline_services in SERVICES.
     destruct (boss_size_preflight word_max image) as [|total|total] eqn:SIZE.
     * destruct SERVICES as [rd [ins [chk [observed [resolved' [restore_cut [RUN MASK_]]]]]]].
       destruct (STAGE ff acks rd ins chk observed resolved' restore_cut eq_refl RUN MASK_)
         as [last [exit [KIND [DONE [POST OTHER]]]]].
       unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 0 (cleanup_response observed resolved' restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
     * destruct SERVICES as [rd [ins [chk [observed [resolved' [restore_cut [RUN MASK_]]]]]]].
       destruct (STAGE ff acks rd ins chk observed resolved' restore_cut eq_refl RUN MASK_)
         as [last [exit [KIND [DONE [POST OTHER]]]]].
       unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 1 (cleanup_response observed resolved' restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
     * destruct STAGE as [FORM [BOUND [CAP [counter [VALUE [SOURCE [MATCH [LOCAL [PROBE [UNIQUE [NEXT [OVERFLOW [RUNTIME_ [RP [RU [PAGE [MARKER [ENSURE [EU [REJECT [SEARCH [STOP [ERASE RECYCLE]]]]]]]]]]]]]]]]]]]]]]].
       specialize (SERVICES counter VALUE).
       destruct (boss_checked_generation (counter_value counter)) as [next|] eqn:GEN.
       2: { destruct SERVICES as [rd [ins [chk [observed [resolved' [restore_cut [RUN MASK_]]]]]]].
         destruct (OVERFLOW ff acks rd ins chk observed resolved' restore_cut eq_refl eq_refl RUN MASK_)
           as [last [exit [KIND [DONE [POST OTHER]]]]].
         unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (PreflightResponse 2 (cleanup_response observed resolved' restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE). }
       assert (NONZERO:Some next<>@None N) by discriminate.
       destruct SERVICES as [[cursor [probe_final [CURSOR [RUN REST]]]]|
         [[fuel [recognize [req [round [alignment [start [reply [INPUT [RUN [ERROR REST]]]]]]]]]]|
         [[fuel [shape [verify [req [round [alignment [start [target [fatal [INPUT [PREFIX INTERRUPTED]]]]]]]]]]]|
         [[span [ADMIT LAST]]|[recognize [magic [fuel [req [round [alignment [start [r [nsectors [recycled [LOC [INPUT [SEARCH_RUN [GEOM [RUN LAST]]]]]]]]]]]]]]]]]]].
       -- destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [REST MASK_]]]]]]].
          destruct (REJECT ff acks (pages*256) (fun _=>Some total) cursor probe_final rd ins chk observed resolved' restore_cut
             eq_refl NONZERO (conj eq_refl (conj CURSOR eq_refl)) RUN REST MASK_)
            as [UNCHANGED [last [exit [KIND [DONE [POST OTHER]]]]]].
          unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 0 (cleanup_response observed resolved' restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct REST as [rd [ins [chk [observed [resolved' [restore_cut [REST MASK_]]]]]]].
          destruct (SEARCH ff acks fuel recognize req round alignment start reply rd ins chk observed resolved' restore_cut
             eq_refl NONZERO INPUT RUN ERROR REST MASK_)
            as [last [exit [KIND [DONE [POST OTHER]]]]].
          unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 1 (cleanup_response observed resolved' restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct (STOP ff acks fuel shape verify req round alignment start target fatal eq_refl NONZERO INPUT PREFIX INTERRUPTED)
            as [DONE POST].
          unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (SearchInterruptedResponse fatal);apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
       -- destruct (ERASE ff acks span eq_refl NONZERO ADMIT)
            as [TRACE_ [SAFE_ [NUM_ [HANDOFF [WRITER [REHOME CUT]]]]]].
          destruct LAST as [[encode [plan [result_ [FORMAT [PLAN [WRITE TAIL]]]]]]|[point _]].
          ++ eapply (generated_writer_services_terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ base checked);
               try eassumption;exact TAIL.
          ++ destruct (CUT point) as [DONE [POST RECEIPT_]].
             unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionCutResponse point);reflexivity.
       -- destruct (RECYCLE ff acks eq_refl NONZERO recognize magic fuel req round alignment start r nsectors recycled
             LOC INPUT SEARCH_RUN GEOM RUN) as [previous [TRACE_ [SAFE_ [NUM_ [RAW_ [PUB_ [REC_ [SUCCESS [ERROR [INTERRUPT CUT]]]]]]]]]].
          destruct (neutral_end_ recycled) eqn:END.
          ++ destruct (SUCCESS eq_refl) as [CHECK [HANDOFF [WRITER [REHOME CUT_]]]].
             destruct LAST as [[encode [plan [result_ [FORMAT [PLAN [WRITE TAIL]]]]]]|[point _]].
             ** eapply (generated_writer_services_terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ base checked);
                  try eassumption;exact TAIL.
             ** destruct (CUT_ point) as [DONE [POST RECEIPT_]].
                unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionCutResponse point);reflexivity.
          ++ destruct LAST as [rd [ins [chk [observed [resolved' [restore_cut [REST MASK_]]]]]]].
             destruct (ERROR eq_refl rd ins chk observed restore_cut REST)
               as [last [exit [KIND [DONE [POST OTHER]]]]].
             unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (AcquisitionResponse 2 (cleanup_response observed None restore_cut));apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
          ++ destruct (INTERRUPT (or_intror eq_refl)) as [last [exit [DONE [POST OTHER]]]].
             unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (RecyclingInterruptedResponse NeutralReset);apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
          ++ destruct (INTERRUPT (or_introl eq_refl)) as [last [exit [DONE [POST OTHER]]]].
             unfold owner_terminal;do 5 eexists;split;[exact DONE|]. split;[exact POST|].
     split;[rewrite (completed_no_receipts _ _ _ _ _ _ _ DONE);reflexivity|].
     exists (RecyclingInterruptedResponse NeutralFatal);apply (completed_no_receipts _ _ _ _ _ _ _ DONE).
Qed.

Theorem owned_entry_services_with_invariants_for (Q:owner_service_response->Prop) valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 decoded_allocation_geometry pages decode ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (local_cleanup_mask pc final outcome resolved cut=None -> forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   (marked_boss_requested result pc final=true -> vo=vf /\ oo=of_ /\
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev)=marked_selected_boundary final) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services_for Q word_max oo ff h aa old image ram ev) ->
 (marked_boss_requested result pc final=false -> Q (indexed_prebody_response result pc final outcome resolved cut)) ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\
   owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\
 exists response,owner_response_matches response exit /\ Q response /\ owner_reply_ready response reached.
Proof.
 intros HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO INV DECODE_GEOMETRY OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES PREBODY.
 pose proof (owner_invariants_idle_latest _ _ _ _ _ _ _ INV) as LATEST.
 destruct INV as [INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION ORIGIN APPEND_BOUND COHERENT STRUCT PHYSICAL].
 destruct (owned_entry_services_terminal_for Q valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked
   HEADER PHYSICAL OBJECT_MAPPING LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL
   COUNTER ALLOCATION DECODE_GEOMETRY ORIGIN APPEND_BOUND OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES PREBODY)
   as [receipts [vo [oo [reached [exit [DONE [POST [EXACT REPORT]]]]]]]].
 exists receipts,vo,oo,reached,exit;split;[exact DONE|]. split;[exact POST|]. split.
 - eapply owner_invariants_trace;[exact HEADER|exact DECODE_GEOMETRY|constructor;eassumption|exact (proj1 POST)].
 - split.
   + intro RETURN;split.
     * eapply completed_operation_owner_closed;eassumption.
     * eapply owner_delivered_reentry;try eassumption.
     eapply owner_invariants_trace;[exact HEADER|exact DECODE_GEOMETRY|constructor;eassumption|exact (proj1 POST)].
   + split;[rewrite app_nil_r in EXACT;exact EXACT|exact REPORT].
Qed.

Theorem owned_entry_services_with_invariants valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 decoded_allocation_geometry pages decode ->
 outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev) ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\
   owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\
 exists response,owner_response_matches response exit.
Proof.
 intros HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO INV DECODE_GEOMETRY OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES.
 pose proof (owner_invariants_idle_latest _ _ _ _ _ _ _ INV) as LATEST.
 destruct INV as [INIT RAW META RUNTIME GENERATION GENERATION_LOCAL COUNTER ALLOCATION ORIGIN APPEND_BOUND COHERENT STRUCT PHYSICAL].
 destruct (owned_entry_services_terminal valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked
   HEADER PHYSICAL OBJECT_MAPPING LATEST MAPPING ADDRESS MARK DEC WORD GEO INIT RAW META RUNTIME GENERATION GENERATION_LOCAL
   COUNTER ALLOCATION DECODE_GEOMETRY ORIGIN APPEND_BOUND OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES)
   as [receipts [vo [oo [reached [exit [DONE [POST [EXACT REPORT]]]]]]]].
 exists receipts,vo,oo,reached,exit;split;[exact DONE|]. split;[exact POST|]. split.
 - eapply owner_invariants_trace;[exact HEADER|exact DECODE_GEOMETRY|constructor;eassumption|exact (proj1 POST)].
 - split.
   + intro RETURN;split.
     * eapply completed_operation_owner_closed;eassumption.
     * eapply owner_delivered_reentry;try eassumption.
     eapply owner_invariants_trace;[exact HEADER|exact DECODE_GEOMETRY|constructor;eassumption|exact (proj1 POST)].
   + split;[rewrite app_nil_r in EXACT;exact EXACT|exact REPORT].
Qed.

Theorem owner_completed_reset_reentry vi oi initial receipts valid view j ev recovered id decoded ram :
 marker_header_covered marker -> decoded_allocation_geometry pages decode ->
 owner_invariants vi oi initial ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial receipts valid view ((j,RebuildingBoundary Selecting),forget_volatile_evidence ev) InterruptedReset ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (j,Selecting) (recovered,Usable id decoded ram) ->
 let rebuilt:=((recovered,IdleBoundary id decoded ram),
   recovered_page_evidence recovered id (forget_volatile_evidence ev)) in
 Trace vi oi initial receipts valid view rebuilt /\
 owner_invariants valid view rebuilt /\
 outer_live (controller_read (snd rebuilt))=false /\
 owner_armed (controller_read (snd rebuilt))=false /\
 data_caller DataBegin ram /\ exit_observation InterruptedReset=None.
Proof.
 intros HEADER GEO INV DONE BOOT rebuilt.
 pose proof (completed_operation_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ DONE) as PREFIX.
 assert (FULL:Trace vi oi initial receipts valid view rebuilt).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]).
   - eapply boot_episode with (initial:=(j,Selecting)) (final:=(recovered,Usable id decoded ram));[intros;apply READERS|exact BOOT].
   - eapply episodes_cons with (event:=None) (events:=[]);[apply resume_episode|constructor]. }
 pose proof (owner_invariants_trace _ _ _ _ _ _ _ HEADER GEO INV FULL) as READY.
 split;[exact FULL|]. split;[exact READY|]. split;[reflexivity|]. split;[reflexivity|].
 split;[eapply owner_invariants_idle_ready;exact READY|reflexivity].
Qed.

Theorem owned_recovered_services_terminal vi oi initial earlier reset_j previous_ev valid view f h a old d s count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 decoded_allocation_geometry pages decode ->
 owner_invariants vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial earlier valid view ((reset_j,RebuildingBoundary Selecting),forget_volatile_evidence previous_ev) InterruptedReset ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (reset_j,Selecting) (Logged (Ready f) h a,Usable old d s) ->
 let e:=recovered_page_evidence (Logged (Ready f) h a) old (forget_volatile_evidence previous_ev) in
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev) ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial (receipts++earlier) vo oo reached exit /\
 controller_result_post word_max vi oi initial (receipts++earlier) vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\
   owner_return_reentry vo oo reached) /\
 exists response,owner_response_matches response exit.
Proof.
 intros HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO DECODE_GEOMETRY INIT NUM RESET BOOT e ENTRY BODY RESTORE MASK BASE SERVICES.
 destruct (owner_completed_reset_reentry vi oi initial earlier valid view reset_j previous_ev
   (Logged (Ready f) h a) old d s HEADER DECODE_GEOMETRY INIT RESET BOOT)
   as [PREFIX [READY [OUT [ARM [BEGIN OBS]]]]].
 destruct (owned_entry_services_with_invariants valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked
   HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO READY DECODE_GEOMETRY OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES)
   as [receipts [vo [oo [reached [exit [DONE [POST [INV [CLOSED [EXACT REPORT]]]]]]]]]].
 assert (FULL:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial (receipts++earlier) vo oo reached exit).
 { destruct DONE as [vm [om [before [previous [returned [PRE [OP EQ]]]]]]].
   exists vm,om,before,(previous++earlier),returned;split.
   - eapply episodes_append;[exact PREFIX|exact PRE].
   - split;[exact OP|]. rewrite EQ;rewrite app_assoc;reflexivity. }
 exists receipts,vo,oo,reached,exit;split;[exact FULL|]. split;[|split;[exact INV|split;[exact CLOSED|exact REPORT]]].
 eapply controller_finalization_from_trace;try eassumption;exact (owner_safe _ _ _ INIT).
Qed.

Theorem owned_returned_services_terminal vi oi initial earlier (published:bool) previous_exit valid view f h a old d s e count same compare result
 word_max log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut) base (checked:bool) :
 marker_header_covered marker -> journal_object_mapping data_len pages ->
 mapped_pages pages ->
 decoding_address_contract decode ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 decoded_allocation_geometry pages decode ->
 owner_invariants vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial earlier valid view
     ((Logged (Ready f) h a,if published then ClientBoundary old d s else IdleBoundary old d s),e) previous_exit ->
 exit_observation previous_exit<>None ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 (forall selected,result=PairSelected selected -> match selected with []=>True | _::_=>
   owned_body_run BodyWaiting selected valid view
     ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),
       owned_local_evidence old d s e)
     log pc tail vf of_ final /\
   (pc=BodyFinished \/ pc=BodyFailed \/ pc=BodyInterrupted) end) ->
 (forall selected,result=PairSelected selected -> match selected with []=>cut=None | _::_=>
   match cut with
   | None=>(pc=BodyFailed \/
       (pc=BodyFinished /\ abort_requested (controller_read (snd final))=true)) ->
       owned_restore_reply old of_ final read inspect check outcome
   | Some point=>(pc=BodyFinished \/ pc=BodyFailed) /\
       (pc=BodyFinished -> abort_requested (controller_read (snd final))=true) /\
       owned_restore_cut_guard old of_ final read inspect check point
   end end) ->
 (forall selected,result=PairSelected selected -> match selected,cut with _::_,None=>
   forall mask,resolved=Some mask -> mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) []
   | _,_=>True end) ->
 mapped_registry_base base ->
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev) ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial (receipts++earlier) vo oo reached exit /\
 controller_result_post word_max vi oi initial (receipts++earlier) vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\
   owner_return_reentry vo oo reached) /\
 exists response,owner_response_matches response exit.
Proof.
 intros HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO DECODE_GEOMETRY INIT NUM PREVIOUS RETURN ENTRY BODY RESTORE MASK BASE SERVICES.
 pose proof (completed_operation_trace g sector data_len marker ranges decode topology pages
   _ _ _ _ _ _ _ _ PREVIOUS) as BEFORE.
 pose proof (owner_invariants_trace _ _ _ _ _ _ _ HEADER DECODE_GEOMETRY INIT BEFORE) as REACHED.
 pose proof (owner_delivered_reentry _ _ _ _ _ _ _ _ HEADER DECODE_GEOMETRY PREVIOUS REACHED RETURN) as REENTRY.
 assert (SUFFIX:Trace valid view
   ((Logged (Ready f) h a,if published then ClientBoundary old d s else IdleBoundary old d s),e) []
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) /\
   owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) /\
   delivered_owner_closed e /\ data_caller DataBegin s).
 { destruct published;exact REENTRY. }
 destruct SUFFIX as [RESUME [READY [[OUT ARM] BEGIN]]].
 assert (PREFIX:Trace vi oi initial earlier valid view ((Logged (Ready f) h a,IdleBoundary old d s),e)).
 { eapply episodes_append with (more:=[]);eassumption. }
 destruct (owned_entry_services_with_invariants valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked
   HEADER OBJECT_MAPPING MAPPING ADDRESS MARK DEC WORD GEO READY DECODE_GEOMETRY OUT ARM ENTRY BODY RESTORE MASK BASE SERVICES)
   as [receipts [vo [oo [reached [exit [DONE [POST [INV [CLOSED [EXACT REPORT]]]]]]]]]].
 assert (FULL:completed_operation g sector data_len marker ranges decode topology pages
   vi oi initial (receipts++earlier) vo oo reached exit).
 { destruct DONE as [vm [om [before [previous [returned [PRE [OP EQ]]]]]]].
   exists vm,om,before,(previous++earlier),returned;split.
   - eapply episodes_append;[exact PREFIX|exact PRE].
   - split;[exact OP|]. rewrite EQ;rewrite app_assoc;reflexivity. }
 exists receipts,vo,oo,reached,exit;split;[exact FULL|]. split;[|split;[exact INV|split;[exact CLOSED|exact REPORT]]].
 eapply controller_finalization_from_trace;try eassumption;exact (owner_safe _ _ _ INIT).
Qed.


(* A finite execution interface contains service runs, never a final boundary
   invariant or an arbitrary A11 trace offered as a substitute for the body. *)
Definition erased_owned_call_services word_max valid view f h a old d s e :=
 exists count same compare result log pc tail vf of_ final read inspect check outcome resolved (cut:option RestoreCut),
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
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev).

Definition owned_call_services_at word_max valid view f h a old d s e (result:pair_prepass_result) :=
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
 (forall vo oo ff aa image ram ev,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) [] vo oo
     ((Logged (Ready ff) h aa,OpenBoundary image [] ram),ev) ->
   finish_selected (controller_read ev)=Some FinishPublish ->
   persistence_marker_test sector (pages*256) ff=true ->
   volatile_runtime_initialized ev=Some true -> volatile_page_size ev=Some 256 ->
   boss_pipeline_services word_max oo ff h aa old image ram ev).

Local Notation owned_nonentry_services_for := (owned_nonentry_services_for g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).

Local Notation owned_call_services_for := (owned_call_services_for g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Lemma owned_services_from_local_failed_body word_max valid view f h a old d s e
 count same compare first rest log tail vf of_ failed read inspect check mask current :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (first::rest)) tt ->
 owned_body_run BodyWaiting (first::rest) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFailed tail vf of_ failed ->
 owned_error_observation failed=Some(false,current) ->
 owned_restore_reply old of_ failed read inspect check RestoreValidated ->
 mask=collect_ranges of_ marker (Some old) (object_extents (of_ old)) [] ->
 owned_call_services_for (eq (LocalBodyCleanupResponse mask))
   word_max valid view f h a old d s e (PairSelected (first::rest)).
Proof.
 intros ENTRY BODY ORDINARY RESTORE MASK.
 change (owned_nonentry_services_for (eq (LocalBodyCleanupResponse mask))
   word_max valid view f h a old d s e (PairSelected (first::rest))).
 exists count,same,compare,log,BodyFailed,tail,vf,of_,failed,read,inspect,check,RestoreValidated,(Some mask),None.
 split;[exact ENTRY|]. split.
 - intros indices EQ;inversion EQ;subst;split;[exact BODY|tauto].
 - split.
   + intros indices EQ;inversion EQ;subst;intros _;exact RESTORE.
   + split.
     * intros indices EQ;inversion EQ;subst;intros m SAME_MASK;inversion SAME_MASK;subst;reflexivity.
     * split.
       -- unfold local_cleanup_mask;rewrite ORDINARY;discriminate.
       -- intros _;unfold indexed_prebody_response;cbn [pair_prepass_return local_cleanup_mask].
          rewrite ORDINARY;reflexivity.
Qed.

(* Only the BOSS services at the boundary computed from this marked body are
   required. The unused cleanup slots are erased parameters, not executions. *)
Lemma owned_services_from_finished_body (Q:owner_service_response->Prop)
 word_max valid view f h a old d s e count same compare first rest
 log tail vf of_ ff hh aa image ram ev :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt (PairSelected (first::rest)) tt ->
 owned_body_run BodyWaiting (first::rest) valid view
   ((Logged (Ready f) h a,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),owned_local_evidence old d s e)
   log BodyFinished tail vf of_ ((Logged (Ready ff) hh aa,OperationBoundary image [] ram),ev) ->
 abort_requested (controller_read ev)=false ->
 let accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram in
 let taken:=controller_evidence (TakeLocal true) (OperationBoundary image [] ram) ev in
 let closed:=controller_evidence LocalClosed (OpenBoundary image [] accepted) taken in
 let selected:=controller_evidence SelectFinish (OpenBoundary image [] accepted) closed in
 boss_pipeline_services_for Q word_max of_ ff h aa old image accepted selected ->
 owned_call_services_for Q word_max valid view f h a old d s e (PairSelected (first::rest)).
Proof.
 intros ENTRY BODY AB accepted taken closed selected SERVICES.
 change (owned_nonentry_services_for Q word_max valid view f h a old d s e (PairSelected (first::rest))).
 exists count,same,compare,log,BodyFinished,tail,vf,of_,
   ((Logged (Ready ff) hh aa,OperationBoundary image [] ram),ev),
   (@None (list N)),(fun _ : list N=>false),(fun _ : list N=>false),RestoreReadFailed,None,None.
 split;[exact ENTRY|]. split.
 - intros indices EQ;inversion EQ;subst;split;[exact BODY|tauto].
 - split.
   + intros indices EQ;inversion EQ;subst;intros [BAD|[_ BAD]];[discriminate|].
     cbn in BAD;rewrite AB in BAD;discriminate.
   + split.
     * intros indices EQ;inversion EQ;subst;intros mask BAD;discriminate.
     * split.
       -- intros NOLOCAL vo oo fz az imagez ramz evz PATH COORDS ROUTE MARKER RUNTIME PAGE.
          assert (WANT:marked_boss_requested (PairSelected (first::rest)) BodyFinished
            ((Logged (Ready ff) hh aa,OperationBoundary image [] ram),ev)=true).
          { cbn [marked_boss_requested phase_dirty fst snd];rewrite AB;reflexivity. }
          destruct (COORDS WANT) as [V [O STATE]];subst vo oo.
          cbn [marked_selected_boundary fst snd] in STATE;inversion STATE;subst.
          exact SERVICES.
       -- cbn [marked_boss_requested phase_dirty fst snd];rewrite AB;discriminate.
Qed.

Lemma owned_call_services_unindexed word_max valid view f h a old d s e result :
 owned_call_services_at word_max valid view f h a old d s e result ->
 owned_call_services_for (fun _=>True) word_max valid view f h a old d s e result.
Proof.
 intros [count [same [compare [log [pc [tail [vf [of_ [final [read [inspect [check [outcome [resolved [cut [ENTRY [BODY [RESTORE [MASK SERVICES]]]]]]]]]]]]]]]]]]].
 unfold owned_call_services_for;destruct (pair_prepass_return result).
 - exists count,same,compare;split;[exact ENTRY|exact I].
 - exists count,same,compare,log,pc,tail,vf,of_,final,read,inspect,check,outcome,resolved,cut.
   split;[exact ENTRY|]. split;[exact BODY|]. split;[exact RESTORE|]. split;[exact MASK|]. split;[|intros;exact I].
   intros;eapply (proj1 (boss_pipeline_services_unindexed _ _ _ _ _ _ _ _ _));eapply SERVICES;eassumption.
Qed.


Definition owned_call_services word_max valid view f h a old d s e :=
 exists result,owned_call_services_at word_max valid view f h a old d s e result.
Lemma owned_call_services_erase word_max valid view f h a old d s e :
 owned_call_services word_max valid view f h a old d s e <->
 erased_owned_call_services word_max valid view f h a old d s e.
Proof.
 split.
 - intros [result [count [same [compare REST]]]];exists count,same,compare,result;exact REST.
 - intros [count [same [compare [result REST]]]];exists result,count,same,compare;exact REST.
Qed.

Definition owned_call_result word_max valid view source :=
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view source receipts vo oo reached exit /\
 controller_result_post word_max valid view source receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\
   owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\
 exists response,owner_response_matches response exit.

Theorem owned_call_services_terminal word_max base (checked:bool) valid view f h a old d s e :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 delivered_owner_closed e -> owned_call_services word_max valid view f h a old d s e ->
 owned_call_result word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e).
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV [OUT ARM]
   [result [count [same [compare [log [pc [tail [vf [of_ [final [read [inspect [check [outcome [resolved [cut [ENTRY [BODY [RESTORE [MASK SERVICES]]]]]]]]]]]]]]]]]]]].
 eapply (owned_entry_services_with_invariants valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked);eassumption.
Qed.

Theorem owned_call_services_terminal_indexed (Q:owner_service_response->Prop) word_max base (checked:bool) valid view f h a old d s e result :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 delivered_owner_closed e -> owned_nonentry_services_for Q word_max valid view f h a old d s e result ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\ owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\ exists response,owner_response_matches response exit /\ Q response /\ owner_reply_ready response reached.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV [OUT ARM]
   [count [same [compare [log [pc [tail [vf [of_ [final [read [inspect [check [outcome [resolved [cut [ENTRY [BODY [RESTORE [MASK [SERVICES PREBODY]]]]]]]]]]]]]]]]]]]].
 eapply (owned_entry_services_with_invariants_for Q valid view f h a old d s e count same compare result
   word_max log pc tail vf of_ final read inspect check outcome resolved cut base checked);eassumption.
Qed.

Theorem owned_call_services_terminal_at word_max base (checked:bool) valid view f h a old d s e result :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 delivered_owner_closed e -> owned_call_services_at word_max valid view f h a old d s e result ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\ owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\
 (exists response,owner_response_matches response exit) /\
 prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV CLOSED SERVICES.
 destruct (pair_prepass_return result) as [success|] eqn:RETURN.
 - destruct SERVICES as [count [same [compare [log [pc [tail [vf [of_ [final [read [inspect [check [outcome [resolved [cut [ENTRY REST]]]]]]]]]]]]]]]].
   destruct CLOSED as [OUT ARM].
   destruct (owned_pair_entry_return valid view (Logged (Ready f) h a) old d s e count same compare result success word_max
     MARK DEC WORD GEO (owner_safe _ _ _ INV) OUT ARM ENTRY RETURN) as [DONE [POST REST_]].
   exists [],valid,view,((Logged (Ready f) h a,IdleBoundary old d s),e),(ReturnedEntry success).
   split;[exact DONE|]. split;[exact POST|]. split;[exact INV|]. split.
   + intro OBS;split;[split;assumption|]. eapply owner_delivered_reentry;try eassumption.
   + split;[reflexivity|]. split.
     * exists (EntryResponse result);cbn [owner_response_matches];rewrite RETURN;reflexivity.
     * unfold prepass_completion_matches;rewrite RETURN;repeat split;reflexivity.
 - destruct (owned_call_services_terminal word_max base checked valid view f h a old d s e
     HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV CLOSED (ex_intro _ result SERVICES))
     as [receipts [vo [oo [reached [exit [DONE [POST [REACHED [CLOSE [EXACT REPORT]]]]]]]]]].
   exists receipts,vo,oo,reached,exit;split;[exact DONE|]. split;[exact POST|]. split;[exact REACHED|].
   split;[exact CLOSE|]. split;[exact EXACT|]. split;[exact REPORT|].
   unfold prepass_completion_matches;rewrite RETURN;exact I.
Qed.

Theorem owned_call_services_terminal_for (Q:owner_service_response->Prop) word_max base (checked:bool) valid view f h a old d s e result :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 delivered_owner_closed e -> owned_call_services_for Q word_max valid view f h a old d s e result ->
 exists receipts vo oo reached exit,
 completed_operation g sector data_len marker ranges decode topology pages
   valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit /\
 controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached /\
 owner_invariants vo oo reached /\
 (exit_observation exit<>None -> delivered_owner_closed (snd reached) /\ owner_return_reentry vo oo reached) /\
 receipts=delivered_receipts exit /\
 (exists response,owner_response_matches response exit /\ Q response /\ owner_reply_ready response reached) /\
 prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV CLOSED SERVICES.
 unfold owned_call_services_for in SERVICES;destruct (pair_prepass_return result) as [success|] eqn:RETURN.
 - destruct SERVICES as [count [same [compare [ENTRY INDEX]]]].
   destruct CLOSED as [OUT ARM].
   destruct (owned_pair_entry_return valid view (Logged (Ready f) h a) old d s e count same compare result success word_max
     MARK DEC WORD GEO (owner_safe _ _ _ INV) OUT ARM ENTRY RETURN) as [DONE [POST REST_]].
   exists [],valid,view,((Logged (Ready f) h a,IdleBoundary old d s),e),(ReturnedEntry success).
   split;[exact DONE|]. split;[exact POST|]. split;[exact INV|]. split.
   + intro OBS;split;[split;assumption|]. eapply owner_delivered_reentry;try eassumption.
   + split;[reflexivity|]. split.
     * exists (EntryResponse result);split;[cbn [owner_response_matches];rewrite RETURN;reflexivity|].
       split;[exact INDEX|exact I].
     * unfold prepass_completion_matches;rewrite RETURN;repeat split;reflexivity.
 - destruct (owned_call_services_terminal_indexed Q word_max base checked valid view f h a old d s e result
     HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV CLOSED SERVICES)
     as [receipts [vo [oo [reached [exit [DONE [POST [REACHED [CLOSE [EXACT REPORT]]]]]]]]]].
   exists receipts,vo,oo,reached,exit;split;[exact DONE|]. split;[exact POST|]. split;[exact REACHED|].
   split;[exact CLOSE|]. split;[exact EXACT|]. split;[exact REPORT|].
   unfold prepass_completion_matches;rewrite RETURN;exact I.
Qed.


Lemma operation_ordinary_observation vi oi source receipts valid view reached exit :
 operation_execution g sector data_len marker ranges decode topology pages
   vi oi source receipts valid view reached exit ->
 match snd (fst reached) with IdleBoundary _ _ _ | ClientBoundary _ _ _ =>
   exit_observation exit<>None | _=>True end.
Proof.
 intro RUN;induction RUN;try exact I;try exact IHRUN;try (cbn;discriminate).
 remember (snd (fst y)) as phase eqn:PH;destruct phase;try exact I;
 intro SILENT;destruct exit;cbn in SILENT;try discriminate;
 unfold edge_exit in H0;destruct event;try discriminate;rewrite <-PH in H0;
 try discriminate;
 destruct (finish_selected (controller_read (snd x)));
 destruct (finish_selected (controller_read (snd y)));try discriminate;
 repeat match type of H0 with context[if ?b then _ else _]=>destruct b end;discriminate.
Qed.
Lemma completed_ordinary_closed vi oi source receipts valid view reached exit :
 completed_operation g sector data_len marker ranges decode topology pages
   vi oi source receipts valid view reached exit -> ordinary_owner_closed reached.
Proof.
 intro DONE;pose proof DONE as [vm [om [before [previous [returned [PREFIX [RUN EQ]]]]]]].
 pose proof (operation_ordinary_observation _ _ _ _ _ _ _ _ RUN) as OBS.
 unfold ordinary_owner_closed;destruct (snd (fst reached));try exact I;
 eapply completed_operation_owner_closed;eassumption.
Qed.

(* Only a finite closure of the existing consumer. NEXT supplies raw services
   for subsequent calls, not their safety or a chosen final outcome. Reset and
   resume nodes add no client observation. The bound is not a liveness claim. *)
Local Notation owned_service_schedule := (owned_service_schedule g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_stop := (schedule_stop g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_call := (schedule_call g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_resume := (schedule_resume g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_reset := (schedule_reset g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).
Local Notation schedule_boot := (schedule_boot g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan).


Lemma owner_response_receipts_exact response exit :
 owner_response_matches response exit ->
 delivered_receipts exit=owner_response_receipts response.
Proof.
 destruct response;cbn [owner_response_matches owner_response_receipts];
 try (intro EQ;rewrite EQ;reflexivity);try tauto.
 destruct (pair_prepass_return entry);[intro EQ;rewrite EQ;reflexivity|contradiction].
Qed.
Lemma owner_response_logs_exact responses exits :
 Forall2 owner_response_matches responses exits ->
 delivered_receipt_log exits=owner_response_receipt_log responses.
Proof.
 intro MATCH;induction MATCH;cbn;[reflexivity|].
 rewrite IHMATCH;rewrite (owner_response_receipts_exact _ _ H);reflexivity.
Qed.
Lemma owner_response_append_observation id d reply exit :
 owner_response_matches (AppendResponse id d reply) exit ->
 exit_observation exit=append_reply_observation reply.
Proof. intro EQ;rewrite EQ;apply append_reply_observation_exact. Qed.

Theorem owned_schedule_run word_max base (checked:bool) n requests valid view source :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owned_service_schedule word_max n requests valid view source ->
 owner_invariants valid view source -> phase_numeric word_max marker ranges (snd (fst source)) ->
 ordinary_owner_closed source ->
 exists vf of_ final exits responses,
 Trace valid view source (delivered_receipt_log exits) vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\ Forall2 owner_response_matches responses exits /\
 Forall2 (fun predicate response=>predicate response) requests responses.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE RUN.
 induction RUN as [n valid view state
   |n requests Q valid view f h a old d s e result SERVICES NEXT IH
   |n requests valid view j id d ram e PLAN IH
   |n requests valid view j phase e RESET PLAN IH
   |n requests valid view j e recovered id d ram BOOT PLAN IH];intros INV NUM CLOSED.
 - exists valid,view,state,[],[];split;[constructor|]. split;[exact INV|]. split;[exact NUM|]. split;[exact CLOSED|split;constructor].
 - destruct (owned_call_services_terminal_for Q word_max base checked valid view f h a old d s e result
     HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV CLOSED SERVICES)
     as [receipts [vo [oo [reached [exit [DONE [POST [REACHED [RETURN [EXACT [[response [RESPONSE [INDEX REPLY_READY]]] PREPASS]]]]]]]]]]].
   destruct (IH receipts vo oo reached exit response DONE POST REACHED EXACT RESPONSE INDEX REPLY_READY PREPASS REACHED (proj1 (proj2 (proj2 POST)))
     (completed_ordinary_closed _ _ _ _ _ _ _ _ DONE))
     as [vf [of_ [final [exits [responses [TAIL [LAST [NUMBER [CONTROL [REPORTS INDICES]]]]]]]]]].
   exists vf,of_,final,(exit::exits),(response::responses);split.
   + cbn [delivered_receipt_log];rewrite <-EXACT.
     eapply episodes_append;[exact (proj1 POST)|exact TAIL].
   + split;[exact LAST|]. split;[assumption|]. split;[exact CONTROL|]. split;constructor;assumption.
 - assert (PREFIX:Trace valid view ((j,ClientBoundary id d ram),e) [] valid view
       ((j,IdleBoundary id d ram),e)).
   { eapply episodes_cons with (event:=None) (events:=[]);[apply resume_client_episode|constructor]. }
   pose proof (owner_invariants_trace _ _ _ _ _ _ _ HEADER DECODE INV PREFIX) as READY.
   pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEO (owner_safe _ _ _ INV) NUM PREFIX)) as NUMBER.
   destruct (IH READY NUMBER CLOSED) as [vf [of_ [final [exits [responses [TAIL [LAST [NUMBER' [CONTROL [REPORTS INDICES]]]]]]]]]].
   exists vf,of_,final,exits,responses;split.
   + rewrite <- (app_nil_r (delivered_receipt_log exits));eapply episodes_append;[exact PREFIX|exact TAIL].
   + split;[exact LAST|]. split;[assumption|]. split;[exact CONTROL|]. split;assumption.
 - assert (PREFIX:Trace valid view ((j,phase),e) [] valid view
       ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e)).
   { eapply episodes_cons with (event:=None) (events:=[]);[apply reset_episode;exact RESET|constructor]. }
   pose proof (owner_invariants_trace _ _ _ _ _ _ _ HEADER DECODE INV PREFIX) as READY.
   pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEO (owner_safe _ _ _ INV) NUM PREFIX)) as NUMBER.
   destruct (IH READY NUMBER I) as [vf [of_ [final [exits [responses [TAIL [LAST [NUMBER' [CONTROL [REPORTS INDICES]]]]]]]]]].
   exists vf,of_,final,exits,responses;split.
   + rewrite <- (app_nil_r (delivered_receipt_log exits));eapply episodes_append;[exact PREFIX|exact TAIL].
   + split;[exact LAST|]. split;[assumption|]. split;[exact CONTROL|]. split;assumption.
 - assert (DONE:completed_operation g sector data_len marker ranges decode topology pages
     valid view ((j,RebuildingBoundary Selecting),forget_volatile_evidence e) [] valid view
     ((j,RebuildingBoundary Selecting),forget_volatile_evidence e) InterruptedReset).
   { exists valid,view,((j,RebuildingBoundary Selecting),forget_volatile_evidence e),[],[];
     split;[constructor|]. split;[apply operation_already_reset;reflexivity|reflexivity]. }
   destruct (owner_completed_reset_reentry valid view
     ((j,RebuildingBoundary Selecting),forget_volatile_evidence e) [] valid view j e recovered id d ram
     HEADER DECODE INV DONE BOOT)
     as [PREFIX [READY [OUT [ARM [BEGIN OBS]]]]].
   pose proof (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
     word_max _ _ _ _ _ _ _ MARK DEC WORD GEO (owner_safe _ _ _ INV) NUM PREFIX)) as NUMBER.
   destruct (IH READY NUMBER (conj OUT ARM)) as [vf [of_ [final [exits [responses [TAIL [LAST [NUMBER' [CONTROL [REPORTS INDICES]]]]]]]]]].
   exists vf,of_,final,exits,responses;split.
   + rewrite <- (app_nil_r (delivered_receipt_log exits));eapply episodes_append;[exact PREFIX|exact TAIL].
   + split;[exact LAST|]. split;[assumption|]. split;[exact CONTROL|]. split;assumption.
Qed.

Lemma delivered_receipt_log_app first later :
 delivered_receipt_log (first++later)=delivered_receipt_log later++delivered_receipt_log first.
Proof. induction first;cbn;[rewrite app_nil_r;reflexivity|rewrite IHfirst;rewrite app_assoc;reflexivity]. Qed.
Lemma delivered_observations_app first later :
 delivered_observations (first++later)=delivered_observations first++delivered_observations later.
Proof. induction first;cbn;[reflexivity|rewrite IHfirst;destruct (exit_observation a);reflexivity]. Qed.
Lemma interrupted_logs_empty :
 delivered_receipt_log [InterruptedFatal;InterruptedReset]=[] /\
 delivered_observations [InterruptedFatal;InterruptedReset]=[].
Proof. split;reflexivity. Qed.
Lemma unchanged_log_no_receipt :
 delivered_receipt_log [ReturnedEntry true]=[] /\
 delivered_observations [ReturnedEntry true]=[RetainedResult].
Proof. split;reflexivity. Qed.

Lemma delivered_observations_fold exits history :
 history++delivered_observations exits=fold_left append_operation_observation exits history.
Proof.
 revert history;induction exits as [|exit rest IH];intro history;cbn.
 - rewrite app_nil_r;reflexivity.
 - destruct (exit_observation exit) eqn:OBS;rewrite <-IH;
     unfold append_operation_observation;try rewrite OBS;
     try reflexivity;rewrite <-app_assoc;reflexivity.
Qed.

Theorem owned_schedule_consumer word_max base (checked:bool) n requests valid view source :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owned_service_schedule word_max n requests valid view source ->
 owner_invariants valid view source -> phase_numeric word_max marker ranges (snd (fst source)) ->
 ordinary_owner_closed source ->
 exists vf of_ final exits responses,
 Trace valid view source (delivered_receipt_log exits) vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=delivered_receipt_log exits++boundary_receipts source /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) (delivered_receipt_log exits) /\
 (forall history,history++delivered_observations exits=
   fold_left append_operation_observation exits history) /\
 (forall events vp op prefix,
   Trace valid view source events vp op prefix ->
   Safe vp op prefix /\ phase_numeric word_max marker ranges (snd (fst prefix))) /\
 Forall2 owner_response_matches responses exits /\
 Forall2 (fun predicate response=>predicate response) requests responses /\
 delivered_receipt_log exits=owner_response_receipt_log responses.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE RUN INV NUM CLOSED.
 destruct (owned_schedule_run word_max base checked n requests valid view source
   HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE RUN INV NUM CLOSED)
   as [vf [of_ [final [exits [responses [TRACE [LAST [NUMBER [CONTROL [REPORTS INDICES]]]]]]]]]].
 destruct (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ (owner_safe _ _ _ INV) TRACE) as [SAFE [RECEIPTS [VALID HISTORICAL]]].
 exists vf,of_,final,exits,responses;split;[exact TRACE|]. split;[exact LAST|]. split;[exact NUMBER|].
 split;[exact CONTROL|]. split;[exact RECEIPTS|]. split;[exact VALID|]. split;[exact HISTORICAL|]. split.
 - apply delivered_observations_fold.
 - split;[|split;[exact REPORTS|split;[exact INDICES|apply owner_response_logs_exact;exact REPORTS]]]. intros events vp op prefix PREFIX;split.
   + exact (proj1 (a11_external_reserved_data_safety g sector data_len marker ranges decode topology pages G DIV
       _ _ _ _ _ _ _ (owner_safe _ _ _ INV) PREFIX)).
   + exact (proj2 (episode_trace_numeric g sector data_len marker ranges decode topology pages G DIV
       word_max _ _ _ _ _ _ _ MARK DEC WORD GEO (owner_safe _ _ _ INV) NUM PREFIX)).
Qed.

Lemma owned_schedule_weaken word_max n requests valid view source extra :
 owned_service_schedule word_max n requests valid view source ->
 owned_service_schedule word_max (n+extra) requests valid view source.
Proof.
 intro PLAN;induction PLAN;cbn.
 - constructor.
 - eapply schedule_call;[exact H|exact H1].
 - apply schedule_resume;assumption.
 - eapply schedule_reset;eassumption.
 - eapply schedule_boot;eassumption.
Qed.

(* Binding finite raw-service schedules is not assuming a safe suffix: the
   continuation contains only the next prepass/body/service executions. *)
Lemma owned_schedule_bind word_max n requests valid view source m extra_requests :
 owned_service_schedule word_max n requests valid view source ->
 (forall vf of_ final, owned_service_schedule word_max m extra_requests vf of_ final) ->
 owned_service_schedule word_max (n+m) (requests++extra_requests) valid view source.
Proof.
 intros PLAN NEXT;induction PLAN;cbn.
 - rewrite Nat.add_comm;apply owned_schedule_weaken;apply NEXT.
 - eapply schedule_call;[exact H|exact H1].
 - apply schedule_resume;assumption.
 - eapply schedule_reset;eassumption.
 - eapply schedule_boot;eassumption.
Qed.

Lemma owned_single_schedule word_max valid view f h a old d s e :
 owned_call_services word_max valid view f h a old d s e ->
 owned_service_schedule word_max 1 [fun _=>True] valid view ((Logged (Ready f) h a,IdleBoundary old d s),e).
Proof. intros [result SERVICES];eapply schedule_call;[|intros;constructor].
 apply (owned_call_services_unindexed _ _ _ _ _ _ _ _ _ _ _);exact SERVICES. Qed.

Lemma owned_boot_call_schedule word_max valid view j e f h a id d ram :
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (j,Selecting) (Logged (Ready f) h a,Usable id d ram) ->
 owned_call_services word_max valid view f h a id d ram
   (recovered_page_evidence (Logged (Ready f) h a) id (forget_volatile_evidence e)) ->
 owned_service_schedule word_max 2 [fun _=>True] valid view
   ((j,RebuildingBoundary Selecting),forget_volatile_evidence e).
Proof.
 intros BOOT SERVICES;eapply schedule_boot;[exact BOOT|].
 apply owned_single_schedule;exact SERVICES.
Qed.

(* Public finite-call consumer: the first node cannot be an arbitrary A11
   prefix, a resume, or a caller-chosen result. It is a marked owner call. *)
(* Concrete A/B/C and offered predicates are re-exported from the owner
   semantics modules. OwnedDataBinding interprets the public signature. *)
Theorem owned_calls_from_idle word_max base (checked:bool) n requests (Q:owner_service_response->Prop) valid view f h a old d s e result :
 marker_header_covered marker -> journal_object_mapping data_len pages -> mapped_pages pages ->
 decoding_address_contract decode -> range_numeric word_max marker ->
 decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 area_start g+area_length g<=2*sector+1024*256 -> decoded_allocation_geometry pages decode ->
 mapped_registry_base base ->
 owner_invariants valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 phase_numeric word_max marker ranges (snd (fst ((Logged (Ready f) h a,IdleBoundary old d s),e))) -> delivered_owner_closed e ->
 owned_call_services_for Q word_max valid view f h a old d s e result ->
 (forall receipts vo oo reached exit response,
   completed_operation g sector data_len marker ranges decode topology pages
     valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached exit ->
   controller_result_post word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) receipts vo oo reached ->
   owner_invariants vo oo reached -> receipts=delivered_receipts exit ->
      owner_response_matches response exit -> Q response -> owner_reply_ready response reached ->
   prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e) reached exit ->
   owned_service_schedule word_max n requests vo oo reached) ->
 exists vf of_ final exits responses,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) (delivered_receipt_log exits) vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=delivered_receipt_log exits++boundary_receipts ((Logged (Ready f) h a,IdleBoundary old d s),e) /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) (delivered_receipt_log exits) /\
 (forall history,history++delivered_observations exits=
   fold_left append_operation_observation exits history) /\
 (forall events vp op prefix,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) events vp op prefix ->
   Safe vp op prefix /\ phase_numeric word_max marker ranges (snd (fst prefix))) /\
 Forall2 owner_response_matches responses exits /\
 Forall2 (fun predicate response=>predicate response) (Q::requests) responses /\
 delivered_receipt_log exits=owner_response_receipt_log responses.
Proof.
 intros HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED SERVICES NEXT.
 eapply (owned_schedule_consumer word_max base checked (S n) (Q::requests));try eassumption.
 eapply schedule_call;[exact SERVICES|exact NEXT].
Qed.


End OrderedBody.

(* All RAM cut points after the physical recycling commands share the existing
   reset/recovery representative. This is not a reserve before the effects. *)
Theorem recycling_ram_cut_recovery word_max vi oi initial events valid view f h a old image root s e
 recognize magic fuel req round alignment start r count result j chosen decoded ram point boss :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_numeric_contract word_max ranges decode ->
 Trace vi oi initial events valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=None -> recognizer_local sector recognize ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 neutral_end_ result=NeutralSuccess ->
 clos_refl_trans boot_state (boot_step g sector data_len (validate (neutral_flash result)) marker ranges decode topology pages)
   (Logged (Boot (neutral_flash result)) h a,Selecting) (j,Usable chosen decoded ram) ->
 exists previous,
 let old_e:=selected_evidence old previous e in
 let rebuilt:=recovered_page_evidence j chosen (forget_volatile_evidence old_e) in
 acquisition_ram_reset point boss (block_pages (recycle_lo r) (useful_pages r)) s old_e
   (Logged (Ready (neutral_flash result)) h a)=
   ((Logged (Boot (neutral_flash result)) h a,RebuildingBoundary Selecting),forget_volatile_evidence old_e) /\
 Trace vi oi initial events (validate (neutral_flash result)) view ((j,IdleBoundary chosen decoded ram),rebuilt) /\
 Safe (validate (neutral_flash result)) view ((j,IdleBoundary chosen decoded ram),rebuilt) /\
 volatile_allocation rebuilt=Some (allocation_from_decoded decoded) /\
 extent_end (recovered_boss decoded)<=word_max /\
 Nat.min word_max (extent_end (recovered_boss decoded))=extent_end (recovered_boss decoded) /\
 data_caller DataBegin ram.
Proof.
 intros INIT RAW MATCH NUM PREFIX HEAD P LOCAL SEARCH GEO RUN OK BOOT.
 destruct (recycling_cut_boot_from_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   INIT RAW PREFIX HEAD P LOCAL SEARCH GEO RUN OK BOOT) as [previous [PATH [SAFE RECEIPTS]]].
 destruct (resume_allocation_bounded_from_trace g sector data_len marker ranges decode topology pages G DIV
   word_max vi oi initial events (validate (neutral_flash result)) view j chosen decoded ram
   (selected_evidence old previous e) INIT MATCH NUM PATH) as [READY [INV [OBS [BOUND SAT]]]].
 exists previous;cbn zeta;split;[apply acquisition_ram_reset_same|].
 split;[exact READY|]. split;[exact INV|]. split;[exact OBS|]. split;[exact BOUND|].
 split;[exact SAT|].
 exact (proj1 (episode_next_begin g sector data_len marker ranges decode topology pages G DIV
   _ _ _ _ _ _ _ _ _ _ _ INIT READY)).
Qed.


End EvolvingConsumption.
