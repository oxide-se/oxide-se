From Stdlib Require Import List Arith NArith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import RecyclingErase RecyclingEraseBoundary FreerReachableNeutralization
 FreerRawBoundary FreerGlobalDataTrace FreerAdmittedTrace JournalRawOrder RawNeutralizationBoundary
 RecyclingSearch Neutralization NeutralizationBoundary FlashSpec PreparedAuthority RetentionCoverage
 CompactImage JournalHistory JournalRequests JournalReachableShape TransactionBoundary
 PersistentBoundary DataEpisode BootReconstruction PublicationPreparation.
Import ListNotations.

Theorem a11_reachable_recycling_reservation g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r count result validate :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate ->
 boundary_safe sector data_len prior_valid view marker ranges decode pages initial ->
 logged_reachable g sector 256 data_len prior_valid (boundary_journal initial) ->
 stationary_episode_trace g sector data_len prior_valid view marker ranges decode topology pages initial events
  ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram)) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 recycling_run g sector recognize magic r count f result ->
 data_caller DataBegin ram /\
 (forall i, i<count ->
  erase_request g (2*sector+256*recycle_lo r+i*sector) /\
  free_range 256 (protection_table (data_next DataBegin ram))
   {|offset:=256*recycle_lo r+i*sector;span:=sector|}) /\ exists decoded,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a result)
   (selected_evidence old decoded e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old (recovered_image d) [recovered_boss d]
   (data_next DataBegin ram) h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e)) /\
 (neutral_end_ result=NeutralSuccess ->
   erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r)) /\
   data_caller (DataReserve (block_pages (recycle_lo r) (useful_pages r))) (data_next DataBegin ram) /\
   forall exit,
   enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
     (late_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a (neutral_flash result)
       (block_pages (recycle_lo r) (useful_pages r)) exit) (selected_evidence old decoded e) /\
   ((exit=ResetBeforeReserve \/ exit=ResetAfterReserve) ->
    episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e))).
Proof.
 intros G DIV C L PROVIDER INITIAL REACH TRACE SEARCH GEO RUN.
 destruct (initialized_a11_trace_raw g sector data_len prior_valid view marker ranges decode topology pages
  G DIV initial events _ INITIAL REACH TRACE) as [FINAL RAW].
 pose proof FINAL as [[JI [IDLE [FMT IMAGE]]] [EV CERT]].
 destruct (common_begin sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a) old d ram (proj1 FINAL)) as [CALL NEXT].
 assert (OPEN : enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)) e).
 { split; [exact NEXT|split; [exact EV|exact I]]. }
 destruct (searched_recycling_dynamic g sector data_len prior_valid view marker ranges decode topology pages
  recognize magic fuel f h a old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) e req round alignment start
  r count result validate G DIV C L PROVIDER OPEN RAW (proj1 (proj2 (proj2 (proj2 IDLE)))) SEARCH GEO RUN)
  as [decoded [SAFE [ORDER [BOOT DONE]]]].
 split; [exact CALL|]. split.
 - intros i I; split.
   + eapply erase_command_admissible; eauto.
   + eapply selected_sector_free; [exact SEARCH|exact (proj1 (proj2 (proj2 GEO)))|exact I].
 - exists decoded. split; [exact SAFE|]. split; [exact ORDER|]. split; [exact BOOT|].
 intro OK. destruct (DONE OK) as [FREE BLANK]. split; [exact BLANK|].
 assert (P:pending_preparation (data_next DataBegin ram)=None) by reflexivity.
 assert (F:protection_frozen (data_next DataBegin ram)=false) by reflexivity.
 split; [simpl; auto|]. intro exit.
 eapply recycling_late_boundary; [exact G|exact DIV|exact C| |exact P|exact FREE].
 unfold neutral_open_boundary in SAFE; rewrite OK in SAFE; exact SAFE.
Qed.

(* A typed internal service reuses the existing boundary witness. Callee gives
   execution only; preservation is a theorem. Non-returning outcomes remain
   prefixes in recycling_run, never normal Freer responses. *)
Inductive RecycleAPI : interface := Recycle : RecycleAPI neutral_observation.
Definition recycle_caller (state:transaction_boundary) A (op:RecycleAPI A) :=
 match snd state with OpenBoundary _ _ s => protection_frozen s=false | _=>False end.
Definition recycle_callee g sector recognize magic r count (state:transaction_boundary) A
 (op:RecycleAPI A) (reply:A) :=
 match op in RecycleAPI T return T->Prop with
 | Recycle => fun result => recycling_run g sector recognize magic r count
   (control_image (journal_control (fst state))) result /\
   neutral_end_ result<>NeutralReset /\ neutral_end_ result<>NeutralFatal
 end reply.
Definition recycle_update old image root s h a (_:transaction_boundary) A (op:RecycleAPI A) (reply:A) :=
 match op in RecycleAPI T return T->transaction_boundary with
 | Recycle => neutral_open_boundary old image root s h a
 end reply.
Definition recycle_contract g sector recognize magic r count old image root s h a :=
 make_contract (recycle_update old image root s h a) recycle_caller
 (recycle_callee g sector recognize magic r count).
Definition run_recycling : impure RecycleAPI neutral_observation :=
 request_then Recycle (fun r=>local r).
Theorem recycling_normal_execution g sector recognize magic r count old image root s f h a result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecycleAPI)
  (recycle_contract g sector recognize magic r count old image root s h a) run_recycling)
  (Logged (Ready f) h a,OpenBoundary image root s) result final ->
 recycling_run g sector recognize magic r count f result /\
 neutral_end_ result<>NeutralReset /\ neutral_end_ result<>NeutralFatal /\
 final=neutral_open_boundary old image root s h a result.
Proof.
 intros P. simpl in P. unroll_post P.
 destruct P as [reply [middle [[CALL EQ] REST]]]; subst middle.
 unroll_post REST. destruct REST as [R S]; subst.
 destruct CALL as [RUN [END FATAL]]. auto.
Qed.

From OxideSE.Registry Require Import PreparationOutcomes.
Theorem admitted_reachable_recycling_reservation g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r count result validate bytes dw bw dp bp :
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
 data_caller DataBegin ram /\
 (forall i, i<count ->
  erase_request g (2*sector+256*recycle_lo r+i*sector) /\
  free_range 256 (protection_table (data_next DataBegin ram))
   {|offset:=256*recycle_lo r+i*sector;span:=sector|}) /\ exists decoded,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a result)
   (selected_evidence old decoded e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old (recovered_image d) [recovered_boss d]
   (data_next DataBegin ram) h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e)) /\
 (neutral_end_ result=NeutralSuccess ->
   erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r)) /\
   data_caller (DataReserve (block_pages (recycle_lo r) (useful_pages r))) (data_next DataBegin ram) /\
   forall exit,
   enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
     (late_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a (neutral_flash result)
       (block_pages (recycle_lo r) (useful_pages r)) exit) (selected_evidence old decoded e) /\
   ((exit=ResetBeforeReserve \/ exit=ResetAfterReserve) ->
    episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e))).
Proof.
 intros G DIV C L PROVIDER W INITIAL REACH TRACE SEARCH GEO RUN.
 eapply a11_reachable_recycling_reservation; [exact G|exact DIV|exact C|exact L|exact PROVIDER|
  exact INITIAL|exact REACH| |exact SEARCH|exact GEO|exact RUN].
 exact (erased_trace_refines g sector data_len prior_valid view marker ranges decode topology pages G DIV C
  bytes dw bw dp bp W initial events _ INITIAL TRACE).
Qed.

(* pages::reserve is a separate RAM service, AFTER erasure. [numeric_ok]
   abstracts initialized page size, checked range and MAX_PAGES admission.
   Occupancy is not hidden here: caller is derived from the search theorem. *)
Inductive LateReserveAPI : interface := ReserveLate : LateReserveAPI bool.
Definition late_caller r (state:transaction_boundary) A (op:LateReserveAPI A) :=
 match snd state with OpenBoundary _ _ s => data_caller (DataReserve r) s | _=>False end.
Definition late_callee numeric_ok (_:transaction_boundary) A (op:LateReserveAPI A) (reply:A) :=
 match op in LateReserveAPI T return T->Prop with ReserveLate => fun b=>b=numeric_ok end reply.
Definition late_update old image root s h a f r (_:transaction_boundary) A (op:LateReserveAPI A) (reply:A) :=
 match op in LateReserveAPI T return T->transaction_boundary with
 | ReserveLate => fun b=>late_boundary old image root s h a f r
   (if b then ReservedReturn else ReservationRejected)
 end reply.
Definition late_contract numeric_ok old image root s h a f r :=
 make_contract (late_update old image root s h a f r) (late_caller r) (late_callee numeric_ok).
Definition reserve_late : impure LateReserveAPI bool := request_then ReserveLate (fun b=>local b).
Theorem late_reserve_execution numeric_ok old image root s h a f r reply final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure LateReserveAPI)
  (late_contract numeric_ok old image root s h a f r) reserve_late)
  (Logged (Ready f) h a,OpenBoundary image root s) reply final ->
 reply=numeric_ok /\ final=late_boundary old image root s h a f r
  (if reply then ReservedReturn else ReservationRejected).
Proof.
 intros P; simpl in P; unroll_post P.
 destruct P as [answer [middle [[CALL EQ] REST]]]; subst middle.
 unroll_post REST; destruct REST as [R S]; subst; auto.
Qed.

Theorem recycling_normal_then_reserve g sector data_len prior_valid view marker ranges decode (topology:recovery_decoding->bool) pages
 recognize magic fuel f h a old image root s e req round alignment start r count result validate numeric_ok reply final intermediate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecycleAPI)
   (recycle_contract g sector recognize magic r count old image root s h a) run_recycling)
   (Logged (Ready f) h a,OpenBoundary image root s) result intermediate ->
 neutral_end_ result=NeutralSuccess ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure LateReserveAPI)
   (late_contract numeric_ok old image root s h a (neutral_flash result)
    (block_pages (recycle_lo r) (useful_pages r))) reserve_late)
   intermediate reply final ->
 exists d, enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   final (selected_evidence old d e) /\
 erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r)) /\
 reply=numeric_ok.
Proof.
 intros G DIV C L PROVIDER INV RAW HEAD P SEARCH GEO RUN OK RESERVE.
 destruct (recycling_normal_execution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN) as [EXEC [_ [_ MID]]].
 subst intermediate. unfold neutral_open_boundary in RESERVE; rewrite OK in RESERVE.
 destruct (late_reserve_execution _ _ _ _ _ _ _ _ _ _ _ RESERVE) as [REPLY FINAL]. subst final.
 destruct (searched_recycling_dynamic g sector data_len prior_valid view marker ranges decode topology pages
  recognize magic fuel f h a old image root s e req round alignment start r count result validate
  G DIV C L PROVIDER INV RAW HEAD SEARCH GEO EXEC) as [d [SAFE [_ [_ DONE]]]].
 destruct (DONE OK) as [FREE BLANK].
 unfold neutral_open_boundary in SAFE; rewrite OK in SAFE.
 exists d. split; [|auto].
 exact (proj1 (recycling_late_boundary g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
  (neutral_flash result) h a old image root s (selected_evidence old d e) (block_pages (recycle_lo r) (useful_pages r))
  (if reply then ReservedReturn else ReservationRejected) G DIV C SAFE P FREE)).
Qed.
