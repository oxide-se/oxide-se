From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import JournalRawOrder JournalValidator RecyclingSearch RecyclingSearchBoundary
 Neutralization NeutralizationBoundary DataEpisode TransactionBoundary PersistentBoundary
 JournalHistory JournalRequests JournalReachableShape JournalProtocolAuthority JournalScan
 JournalRecoveryTrace JournalIndex PreparedAuthority RetentionCoverage FlashSpec BootReconstruction.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export BossDecodingContract.
Import ListNotations.

(* A local format-provider obligation: a completed full decoding is accepted
   by journal.rs::validate. No authority or history appears in this contract. *)

Lemma raw_ready_revalidate sector data_len f h a id validate :
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some id ->
 validate id=true -> logged_invariant sector 256 data_len validate (Logged (Ready f) h a).
Proof.
 intros RAW HEAD VALID. destruct (ready_raw_witness _ _ _ _ _ _ _ RAW HEAD) as [index W].
 destruct RAW as [PHYSICAL [HIST ACK]]. split; [exact PHYSICAL|]. split; [|exact ACK].
 change (observed sector 256 data_len validate f=hd_error h).
 unfold observed, latest_in_model. rewrite HEAD.
 rewrite (raw_latest_validated_selects _ _ _ _ _ _ validate W VALID). reflexivity.
Qed.

Theorem raw_searched_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
 recognize magic fuel f h a old image root s e req round alignment start r result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 hd_error h=Some (N.of_nat old) ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 exists d,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old image root s h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)).
Proof.
 intros G DIV C L PROVIDER INITIAL RAW HEAD SEARCH RUN.
 pose proof (reusable_search_check _ _ _ _ _ _ _ _ _ _ _ SEARCH) as GUARD.
 destruct (neutralization_open_transport g sector data_len prior_valid view marker ranges decode pages
  recognize magic fuel (recycle_lo r) (recycle_lo r+erase_pages r) f h a old image root s e result
  C L INITIAL HEAD GUARD RUN) as [FREE [KEEP [d OPEN]]].
 assert (RAW' : raw_order sector 256 data_len (Logged (Ready (neutral_flash result)) h a)).
 { destruct INITIAL as [[JI [DI REST]] OTHER].
   destruct (search_to_neutralization g sector fuel recognize magic f (protection_table s) req round alignment pages start
     r result (required_ranges s) L (proj1 (proj1 JI)) (proj1 (proj1 (proj1 DI))) SEARCH RUN)
     as [_ [V [_ FRAME]]].
   exact (neutral_ready_frame sector data_len (fun _=>true) _ _ _ _ RAW V FRAME). }
 destruct OPEN as [[JN REST] [EN LINK]].
 assert (CERT : certificate_valid sector view ranges decode (Logged (Ready (neutral_flash result)) h a) (Certificate old d)).
 { exact (Forall_inv (proj1 EN)). }
 assert (VALID : validate (neutral_flash result) (N.of_nat old)=true).
 { eapply PROVIDER; exact (proj1 CERT). }
 pose proof (raw_ready_revalidate sector data_len _ h a _ _ RAW' HEAD VALID) as JNEW.
 assert (OPEN' : enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
  (Logged (Ready (neutral_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e)).
 { split; [split; [exact JNEW|exact REST]|split; assumption]. }
 assert (RESET : enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
  (logged_after_reset (Logged (Ready (neutral_flash result)) h a),RebuildingBoundary Selecting) (selected_evidence old d e)).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact OPEN'|]. apply record_step; apply reset_ready. }
 exists d. split.
 - unfold neutral_open_boundary; destruct (neutral_end_ result).
   + exact OPEN'.
   + eapply neutral_freeze_open; [exact OPEN'|exact HEAD].
   + exact RESET.
   + split; [split; [exact JNEW|exact I]|split; [exact EN|exact I]].
 - split.
   + unfold neutral_open_boundary; destruct (neutral_end_ result); exact RAW'.
   + intros _. eapply boot_entry_post; eauto.
Qed.

Theorem neutralization_preserves_observations old image root ram h a result d e :
 publications (fst (neutral_open_boundary old image root ram h a result))=h /\
 acknowledgements (fst (neutral_open_boundary old image root ram h a result))=a /\
 client_receipts (selected_evidence old d e)=client_receipts e.
Proof. unfold neutral_open_boundary; destruct (neutral_end_ result); repeat split; reflexivity. Qed.
