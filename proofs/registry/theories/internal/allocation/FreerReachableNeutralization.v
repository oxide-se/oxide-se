From Stdlib Require Import List Arith NArith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FreerRawBoundary FreerGlobalDataTrace FreerAdmittedTrace
 JournalRawOrder RawNeutralizationBoundary RecyclingSearch Neutralization NeutralizationBoundary
 FlashSpec PreparedAuthority RetentionCoverage CompactImage JournalHistory JournalRequests
 JournalReachableShape TransactionBoundary PersistentBoundary DataEpisode BootReconstruction.
Import ListNotations.

(* A single initial enriched boundary plus an actual A11 trace. No raw order,
   selected-candidate guard, intermediate decoding or ordinary-append suffix
   is supplied at the reached allocation boundary. *)
Theorem a11_reachable_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r result validate :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate ->
 boundary_safe sector data_len prior_valid view marker ranges decode pages initial ->
 logged_reachable g sector 256 data_len prior_valid (boundary_journal initial) ->
 stationary_episode_trace g sector data_len prior_valid view marker ranges decode topology pages initial events
  ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram)) req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 data_caller DataBegin ram /\ exists decoded,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a result)
   (selected_evidence old decoded e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old (recovered_image d) [recovered_boss d]
   (data_next DataBegin ram) h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e)).
Proof.
 intros G DIV C L PROVIDER INITIAL REACH TRACE SEARCH RUN.
 destruct (initialized_a11_trace_raw g sector data_len prior_valid view marker ranges decode topology pages
  G DIV initial events _ INITIAL REACH TRACE) as [FINAL RAW].
 pose proof FINAL as [[JI [IDLE [FMT IMAGE]]] [EV CERT]].
 destruct (common_begin sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a) old d ram (proj1 FINAL)) as [CALL NEXT].
 assert (OPEN : enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)) e).
 { split; [exact NEXT|split; [exact EV|exact I]]. }
 split; [exact CALL|].
 exact (raw_searched_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
  recognize magic fuel f h a old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) e req round alignment start
  r result validate G DIV C L PROVIDER OPEN RAW (proj1 (proj2 (proj2 (proj2 IDLE)))) SEARCH RUN).
Qed.

From OxideSE.Registry Require Import PreparationOutcomes.
Theorem admitted_reachable_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
 initial events f h a old d ram e recognize magic fuel req round alignment start r result validate bytes dw bw dp bp :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate ->
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 boundary_safe sector data_len prior_valid view marker ranges decode pages initial ->
 logged_reachable g sector 256 data_len prior_valid (boundary_journal initial) ->
 erased_episode_trace g sector data_len prior_valid view marker ranges decode topology pages initial events
  ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram)) req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 data_caller DataBegin ram /\ exists decoded,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old (recovered_image d) [recovered_boss d] (data_next DataBegin ram) h a result)
   (selected_evidence old decoded e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old (recovered_image d) [recovered_boss d]
   (data_next DataBegin ram) h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old decoded e)).
Proof.
 intros G DIV C L PROVIDER W INITIAL REACH TRACE SEARCH RUN.
 eapply a11_reachable_neutralization_dynamic; [exact G|exact DIV|exact C|exact L|exact PROVIDER|
  exact INITIAL|exact REACH| |exact SEARCH|exact RUN].
 exact (erased_trace_refines g sector data_len prior_valid view marker ranges decode topology pages G DIV C
  bytes dw bw dp bp W initial events _ INITIAL TRACE).
Qed.
