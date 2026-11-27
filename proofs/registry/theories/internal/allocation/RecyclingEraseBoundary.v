From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import RecyclingErase RawNeutralizationBoundary
 NeutralizationBoundary Neutralization RecyclingSearch JournalRawOrder JournalHistory
 PersistentBoundary TransactionBoundary DataEpisode BootReconstruction PreparedAuthority
 FlashSpec RetentionCoverage PageOwnership JournalReachableShape JournalRequests
 JournalProtocolAuthority JournalRecoveryTrace PublicationPreparation.
Import ListNotations.

(* General frame adapter: the physical caller must PROVE KEEP and FRAME.
   The public consumer below derives them from selection and erase execution. *)
Lemma recycling_open_frame sector data_len boss_ok view marker ranges decode pages
 f f' h a old image root s e :
 recovery_local_contracts view ranges decode ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) -> valid_flash f' ->
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector f') ->
 (forall x, x<2*sector -> f' x=f x) ->
 exists d, enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f') h a,OpenBoundary image root s) (selected_evidence old d e).
Proof.
 intros CONTRACT [[JI [DI [FR [IMAGE LINK]]]] [EV CERT]] HEAD VALID KEEP FRAME.
 assert (JN : logged_invariant sector 256 data_len boss_ok (Logged (Ready f') h a)).
 { eapply neutral_ready_frame; eauto. }
 assert (PH : physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK. rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 destruct (proj1 (proj2 EV) old HEAD) as [c [IN ID]]. destruct c as [id d]; simpl in ID; subst id.
 assert (READ : certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate old d)).
 { apply (proj1 (Forall_forall _ _) (proj1 EV)); exact IN. }
 assert (READ' : certificate_valid sector view ranges decode
   (Logged (Ready f') h a) (Certificate old d)).
 { destruct READ as [R F]. split; [|exact F]. simpl in R |- *.
   rewrite <- (recovery_locality_contract _ _ _ CONTRACT
     (object_flash sector f) (object_flash sector f') old).
   - exact R.
   - intros r x IN' AT. apply (KEEP r x); [|exact AT].
     unfold required_ranges; repeat rewrite in_app_iff; rewrite PH; tauto. }
 exists d. split.
 - split; [exact JN|]. split; [exact DI|]. split; [exact FR|]. split; assumption.
 - split.
   + split; [constructor; [exact READ'|constructor]|]. split.
     * intros id H; change (hd_error h=Some (N.of_nat id)) in H.
       assert (id=old) by (apply Nat2N.inj; congruence). subst id.
       exists (Certificate old d); simpl; auto.
     * exact (proj2 (proj2 EV)).
   + exact I.
Qed.

Theorem searched_erase_dynamic g sector data_len prior_valid view marker ranges decode topology pages
 recognize fuel searched f h a old image root s e req round alignment start r count result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 hd_error h=Some (N.of_nat old) ->
 reusable_search sector fuel recognize searched (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 erase_run g (2*sector+256*recycle_lo r) count f result ->
 exists d,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old image root s h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)) /\
 (neutral_end_ result=NeutralSuccess ->
  free_range 256 (protection_table s) (block_pages (recycle_lo r) (useful_pages r)) /\
  erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r))).
Proof.
 intros G DIV C PROVIDER INITIAL RAW HEAD SEARCH GEO RUN.
 pose proof INITIAL as [[JI [DI REST]] OTHER].
 destruct (selected_erase_preserves g sector fuel recognize searched (protection_table s) req round alignment pages start r count
   f result (required_ranges s) (proj1 (proj1 (proj1 DI))) SEARCH GEO (proj1 (proj1 JI)) RUN)
   as [VALID [KEEP [FRAME DONE]]].
 destruct (recycling_open_frame sector data_len prior_valid view marker ranges decode pages f (neutral_flash result)
   h a old image root s e C INITIAL HEAD VALID KEEP FRAME) as [d OPEN].
 assert (RAW' : raw_order sector 256 data_len (Logged (Ready (neutral_flash result)) h a)).
 { eapply neutral_ready_frame; eauto. }
 destruct OPEN as [[JN OTHEROPEN] [EN LINK]].
 assert (CERT : certificate_valid sector view ranges decode (Logged (Ready (neutral_flash result)) h a) (Certificate old d)).
 { exact (Forall_inv (proj1 EN)). }
 assert (V : validate (neutral_flash result) (N.of_nat old)=true).
 { eapply PROVIDER; exact (proj1 CERT). }
 pose proof (raw_ready_revalidate sector data_len _ h a _ _ RAW' HEAD V) as JNEW.
 assert (OPEN' : enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
  (Logged (Ready (neutral_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e)).
 { split; [split; [exact JNEW|exact OTHEROPEN]|split; assumption]. }
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
   + split; [intros _; eapply boot_entry_post; eauto|exact DONE].
Qed.

(* Neutralization errors/fatal/reset cannot enter erase. Successful neutralization
   passes its actual flash; the unique RAM table is unchanged until reserve. *)
Inductive recycling_run g sector recognize magic r count f : neutral_observation -> Prop :=
| recycle_stopped n :
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f n ->
 neutral_end_ n<>NeutralSuccess -> recycling_run g sector recognize magic r count f n
| recycle_erased n result :
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f n ->
 neutral_end_ n=NeutralSuccess ->
 erase_run g (2*sector+256*recycle_lo r) count (neutral_flash n) result ->
 recycling_run g sector recognize magic r count f
  (NeutralObservation (neutral_flash result) (neutral_events n++neutral_events result) (neutral_end_ result)).

(* Physical part of A12.f, independent of any offset-indexed decoder law. *)
Theorem recycling_physical_handoff g sector fuel recognize magic f t req round alignment pages start r count result live :
 recognizer_local sector recognize -> valid_flash f -> protected (needed 256 live) t ->
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 valid_flash (neutral_flash result) /\
 unchanged live (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 (forall x,x<2*sector -> neutral_flash result x=f x) /\
 (neutral_end_ result=NeutralSuccess ->
   free_range 256 t (block_pages (recycle_lo r) (useful_pages r)) /\
   erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r))).
Proof.
 intros LOCAL VALID COVER SEARCH GEO RUN;destruct RUN.
 - destruct (search_to_neutralization g sector fuel recognize magic f t req round alignment pages start r n live
     LOCAL VALID COVER SEARCH H) as [FREE [V [KEEP FRAME]]].
   split;[exact V|]. split;[exact KEEP|]. split;[exact FRAME|intros BAD;contradiction].
 - destruct (search_to_neutralization g sector fuel recognize magic f t req round alignment pages start r n live
     LOCAL VALID COVER SEARCH H) as [FREE [V [KEEP FRAME]]].
   destruct (selected_erase_preserves g sector fuel recognize f t req round alignment pages start r count
     (neutral_flash n) result live COVER SEARCH GEO V H1) as [V' [KEEP' [FRAME' DONE]]].
   cbn [neutral_flash neutral_end_]. split;[exact V'|]. split.
   + intros extent address IN AT;rewrite (KEEP' extent address IN AT);exact (KEEP extent address IN AT).
   + split;[intros x X;rewrite (FRAME' x X);exact (FRAME x X)|exact DONE].
Qed.

Theorem searched_recycling_dynamic g sector data_len prior_valid view marker ranges decode topology pages
 recognize magic fuel f h a old image root s e req round alignment start r count result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len prior_valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 recycling_run g sector recognize magic r count f result ->
 exists d,
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 raw_order sector 256 data_len (fst (neutral_open_boundary old image root s h a result)) /\
 (neutral_end_ result=NeutralReset ->
  episode_boot_post g sector data_len (validate (neutral_flash result)) view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)) /\
 (neutral_end_ result=NeutralSuccess ->
  free_range 256 (protection_table s) (block_pages (recycle_lo r) (useful_pages r)) /\
  erased_object_extent sector (neutral_flash result) (block_pages (recycle_lo r) (useful_pages r))).
Proof.
 intros G DIV C L PROVIDER INITIAL RAW HEAD SEARCH GEO RUN. destruct RUN.
 - destruct (raw_searched_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
   recognize magic fuel f h a old image root s e req round alignment start r n validate
   G DIV C L PROVIDER INITIAL RAW HEAD SEARCH H) as [d [SAFE [ORDER BOOT]]].
   exists d; split; [exact SAFE|]. split; [exact ORDER|]. split; [exact BOOT|]. intros BAD; contradiction.
 - destruct (raw_searched_neutralization_dynamic g sector data_len prior_valid view marker ranges decode topology pages
   recognize magic fuel f h a old image root s e req round alignment start r n validate
   G DIV C L PROVIDER INITIAL RAW HEAD SEARCH H) as [d [SAFE [ORDER BOOT]]].
   unfold neutral_open_boundary in SAFE, ORDER; rewrite H0 in SAFE, ORDER.
   destruct (searched_erase_dynamic g sector data_len (validate (neutral_flash n)) view marker ranges decode topology pages
    recognize fuel f (neutral_flash n) h a old image root s (selected_evidence old d e) req round alignment start r count result validate
    G DIV C PROVIDER SAFE ORDER HEAD SEARCH GEO H1) as [d' POST].
   exists d'. exact POST.
Qed.

Lemma recycling_reserve_open sector data_len valid view marker ranges decode pages j image root s e r :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,OpenBoundary image root s) e ->
 pending_preparation s=None -> free_range 256 (protection_table s) r ->
 enriched_invariant sector data_len valid view marker ranges decode pages
 (j,OpenBoundary image root (data_next (DataReserve r) s)) e.
Proof.
 intros [[JI [DI [FR [COR LINK]]]] [EV CERT]] P FREE.
 split; [|split; [exact EV|exact I]]. split; [exact JI|].
 split; [apply data_command_preserves; [exact DI|simpl; auto]|].
 split; [reflexivity|]. split; assumption.
Qed.

(* Numeric/initialized-table rejection is before either reserve loop writes.
   Cursor advancement has no table/flash effect. No interleaving allocation is
   introduced between the synchronous erase loop and these RAM operations. *)
Inductive late_exit := ReservedReturn | ReservationRejected | ResetBeforeReserve | ResetAfterReserve.
Definition late_boundary (old:nat) image root s h a f r exit :=
 let j:=Logged (Ready f) h a in
 match exit with
 | ReservedReturn => (j,OpenBoundary image root (data_next (DataReserve r) s))
 | ReservationRejected => (j,OpenBoundary image root s)
 | ResetBeforeReserve | ResetAfterReserve => (logged_after_reset j,RebuildingBoundary Selecting)
 end.

Theorem recycling_late_boundary g sector data_len valid view marker ranges decode topology pages
 f h a old image root s e r exit :
 journal_geometry g sector 256 -> sector mod 8=0 -> recovery_local_contracts view ranges decode ->
 enriched_invariant sector data_len valid view marker ranges decode pages (Logged (Ready f) h a,OpenBoundary image root s) e ->
 pending_preparation s=None -> free_range 256 (protection_table s) r ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (late_boundary old image root s h a f r exit) e /\
 ((exit=ResetBeforeReserve \/ exit=ResetAfterReserve) ->
 episode_boot_post g sector data_len valid view marker ranges decode topology pages
   (logged_after_reset (Logged (Ready f) h a)) e).
Proof.
 intros G DIV C INV P FREE.
 pose proof (recycling_reserve_open sector data_len valid view marker ranges decode pages _ image root s e r INV P FREE) as RESERVED.
 assert (RESET : enriched_invariant sector data_len valid view marker ranges decode pages
  (logged_after_reset (Logged (Ready f) h a),RebuildingBoundary Selecting) e).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact INV|]. apply record_step; apply reset_ready. }
 assert (RESET_RESERVED : enriched_invariant sector data_len valid view marker ranges decode pages
  (logged_after_reset (Logged (Ready f) h a),RebuildingBoundary Selecting) e).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact RESERVED|]. apply record_step; apply reset_ready. }
 split.
 - destruct exit; simpl; [exact RESERVED|exact INV|exact RESET|exact RESET_RESERVED].
 - intros _; eapply boot_entry_post; eauto.
Qed.

Theorem late_reservation_preserves_observations old image root s h a f r exit :
 publications (fst (late_boundary old image root s h a f r exit))=h /\
 acknowledgements (fst (late_boundary old image root s h a f r exit))=a.
Proof. destruct exit; split; reflexivity. Qed.
