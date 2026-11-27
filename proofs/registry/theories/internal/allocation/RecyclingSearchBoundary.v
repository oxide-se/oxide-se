From Coq Require Import List Arith NArith.
From OxideSE.Registry Require Import RecyclingSearch Neutralization NeutralizationBoundary
 DataEpisode TransactionBoundary PersistentBoundary JournalHistory JournalRequests
 JournalReachableShape PreparedAuthority FlashSpec RetentionCoverage BootReconstruction.

(* Search -> existing open boundary consumer. The caller no longer supplies
   candidate_guard, safe pages or a post-neutralization certificate. *)
Theorem searched_neutralization_open_boundary g sector data_len boss_ok view marker ranges decode topology pages
 recognize magic fuel f h a old image root s e req round alignment start r result :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 exists d,
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 (neutral_end_ result=NeutralReset ->
   episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)).
Proof.
 intros G DIV C L INITIAL HEAD SEARCH RUN.
 pose proof (reusable_search_check _ _ _ _ _ _ _ _ _ _ _ SEARCH) as GUARD.
 destruct (selected_neutralization_open_boundary g sector data_len boss_ok view marker ranges decode topology
  pages recognize magic fuel (recycle_lo r) (recycle_lo r+erase_pages r) f h a old image root s e result
  G DIV C L INITIAL HEAD GUARD RUN) as [FREE [KEEP [d [FINAL BOOT]]]].
 exists d; auto.
Qed.

Theorem fatal_neutralization_reset_boot g sector data_len boss_ok view marker ranges decode topology pages f h a e :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,FatalBoundary) e ->
 episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready f) h a)) e.
Proof.
 intros G DIV C INITIAL. eapply boot_entry_post; [exact G|exact DIV|exact C|].
 eapply enriched_reset; [exact G|exact DIV|exact C|exact INITIAL|].
 apply record_step; apply reset_ready.
Qed.

From OxideSE.Registry Require Import JournalValidator JournalProtocolAuthority JournalIndex JournalAppendSelection
 JournalWriteEntry JournalComplement CollectionRoots.

(* Actual evolving-validator consumer for the suffix following an ordinary
   successful append. Its raw-order fact is PRODUCED by that append, not an
   invariant assumed at the neutralization boundary. Rotation/boot producers
   and global transport remain separate obligations. *)
Theorem appended_search_neutralization_dynamic g sector data_len view marker ranges decode topology pages
 recognize magic fuel before f h a old image root s e req round alignment start r result index aligned within :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 forall validate:flash->N->bool, validator_root_local sector view validate ->
 enriched_invariant sector data_len (validate f) view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) ->
 aligned+within=8*index -> within+8<=256 ->
 first_empty_slot (sector_bytes before 0 sector)=Some index ->
 erased_suffix (sector_bytes before 0 sector) ->
 program_step g before aligned
   (write_entry_page before aligned 256 within (code_bytes (N.of_nat old))) Success f ->
 u32 (N.of_nat old) -> (256<=N.of_nat old<data_len)%N -> (N.of_nat old mod 256=0)%N ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 exists d,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 (neutral_end_ result=NeutralReset ->
   episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)).
Proof.
 intros G DIV C L validate VL INITIAL HEAD ADDR WITHIN FIRST SHAPE STEP U RANGE ALIGN SEARCH RUN.
 pose proof INITIAL as [[JI [DI [FR [IMAGE LINK]]]] [EV CERT]].
 assert (VALID : validate f (N.of_nat old)=true).
 { pose proof (proj1 (proj2 JI)) as OBS.
   change (observed sector 256 data_len (validate f) f=hd_error h) in OBS.
   rewrite HEAD in OBS. unfold observed in OBS.
   destruct (JournalScan.latest_in_model (validate f) data_len (N.of_nat 256) (sector_bytes f 0 sector))
     as [[ix id]|] eqn:SCAN; [|simpl in OBS; discriminate]. inversion OBS; subst id.
   exact (proj2 (proj2 (JournalScan.latest_in_has_validated_slot _ _ _ _ _ _ SCAN))). }
 assert (INC : forall x, In x (root_extents (view (N.to_nat (N.of_nat old)))) -> In x (required_ranges s)).
 { unfold protection_history_link in LINK; cbn in LINK; rewrite HEAD in LINK; cbn in LINK.
   rewrite Nat2N.id in LINK. intros x IN; rewrite Nat2N.id in IN.
   unfold required_ranges; repeat rewrite in_app_iff; rewrite LINK; tauto. }
 pose proof (successful_append_then_search_neutralization g sector fuel recognize magic req round alignment pages start
  before f result (protection_table s) (required_ranges s) view validate r index aligned within (N.of_nat old) data_len
  DIV ADDR WITHIN FIRST SHAPE STEP U RANGE ALIGN L VL (proj1 (proj1 JI))
  (proj1 (proj1 (proj1 DI))) INC VALID SEARCH RUN) as SCAN.
 pose proof (reusable_search_check _ _ _ _ _ _ _ _ _ _ _ SEARCH) as GUARD.
 destruct (neutralization_open_transport g sector data_len (validate f) view marker ranges decode pages
  recognize magic fuel (recycle_lo r) (recycle_lo r+erase_pages r) f h a old image root s e result
  C L INITIAL HEAD GUARD RUN) as [FREE [KEEP [d OPEN]]].
 pose proof OPEN as [[JN REST] [EN CERTN]].
 assert (JN' : logged_invariant sector 256 data_len (validate (neutral_flash result))
  (Logged (Ready (neutral_flash result)) h a)).
 { destruct JN as [PHYSICAL [OBS ACK]]. split; [exact PHYSICAL|]. split; [|exact ACK].
   change (observed sector 256 data_len (validate (neutral_flash result)) (neutral_flash result)=hd_error h).
   unfold observed, JournalScan.latest_in_model. rewrite HEAD.
   replace (length (sector_bytes (neutral_flash result) 0 sector)/8) with (sector/8)
    by (unfold sector_bytes; rewrite map_length, seq_length; reflexivity).
   change (option_map snd (JournalScan.latest_scan (validate (neutral_flash result)) data_len 256
     (sector_bytes (neutral_flash result) 0 sector) (sector/8))=Some (N.of_nat old)).
   rewrite SCAN; reflexivity. }
 assert (OPEN' : enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (Logged (Ready (neutral_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e)).
 { split; [split; [exact JN'|exact REST]|split; assumption]. }
 assert (RESET : enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
  (logged_after_reset (Logged (Ready (neutral_flash result)) h a),RebuildingBoundary Selecting)
  (selected_evidence old d e)).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact OPEN'|]. apply record_step; apply reset_ready. }
 exists d; split.
 - unfold neutral_open_boundary; destruct (neutral_end_ result).
   + exact OPEN'.
   + eapply neutral_freeze_open; [exact OPEN'|exact HEAD].
   + exact RESET.
   + split; [split; [exact JN'|exact I]|split; [exact EN|exact I]].
 - intros _. eapply boot_entry_post; eauto.
Qed.
