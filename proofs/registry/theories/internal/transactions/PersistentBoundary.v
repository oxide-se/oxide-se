From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec PageOwnership ScopeOwnership RetentionCoverage
  CompactImage CompactUpdates CollectionRoots PreparedAuthority JournalHistory JournalReachableShape
  JournalRecoveryTrace JournalRequests JournalAppendAuthority PublicationPreparation PreparationOutcomes
  BootReconstruction BootTransaction TransactionBoundary.
Import ListNotations.

Lemma publication_history_extension history c c' :
  exists prefix, publication_history_after history c c' = prefix ++ history.
Proof.
  destruct c as [f|f|f|f i d|f i d|slot old d state]; simpl; try (exists []; reflexivity).
  - unfold record_candidate; destruct candidate_completed; [exists [d]|exists []]; reflexivity.
  - destruct state as [p f]; destruct p; simpl; try (exists []; reflexivity).
    unfold record_candidate; destruct candidate_completed; [exists [d]|exists []]; reflexivity.
Qed.
Lemma logged_history_extension g sector page data_len boss_ok j j' :
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok) j j' ->
  exists prefix, publications j' = prefix ++ publications j.
Proof.
  intro T; induction T.
  - destruct H; apply publication_history_extension.
  - exists []; reflexivity.
  - destruct IHT1 as [a A], IHT2 as [b B]. exists (b++a). rewrite B,A,app_assoc; reflexivity.
Qed.
Lemma receipts_extend view ranges history prefix receipts :
  Forall (receipt_valid view ranges history) receipts ->
  Forall (receipt_valid view ranges (prefix ++ history)) receipts.
Proof.
  apply Forall_impl. intros r [newer [older [H N]]].
  exists (prefix++newer), older. split; [rewrite H,app_assoc; reflexivity|exact N].
Qed.

Section Transport.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8 = 0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.

Lemma certificate_frame j j' c :
  certificate_valid sector view ranges decode j c ->
  (forall x, 2*sector <= x -> control_image (journal_control j') x = control_image (journal_control j) x) ->
  certificate_valid sector view ranges decode j' c /\
  unchanged (certificate_ranges ranges c)
    (object_flash sector (control_image (journal_control j)))
    (object_flash sector (control_image (journal_control j'))).
Proof.
  intros [READ FORMAT] FRAME.
  assert (KEEP : unchanged (root_extents (view (certificate_id c)))
    (object_flash sector (control_image (journal_control j)))
    (object_flash sector (control_image (journal_control j')))).
  { intros r a IN AT; apply FRAME; lia. }
  split.
  - split; [rewrite <- (recovery_locality_contract _ _ _ CONTRACT _ _ _ KEEP); exact READ|exact FORMAT].
  - intros r a IN AT; apply FRAME; lia.
Qed.

Lemma evidence_frame j j' e :
  persistent_evidence sector view ranges decode j e ->
  publications j' = publications j ->
  (forall x, 2*sector <= x -> control_image (journal_control j') x = control_image (journal_control j) x) ->
  persistent_evidence sector view ranges decode j' e.
Proof.
  intros [CERT [SELECT RECEIPTS]] HIST FRAME. split.
  - eapply Forall_impl; [|exact CERT]. intros c C; exact (proj1 (certificate_frame j j' c C FRAME)).
  - rewrite HIST; split; assumption.
Qed.

Lemma reset_evidence j e : persistent_evidence sector view ranges decode j e ->
  persistent_evidence sector view ranges decode (logged_after_reset j) e.
Proof.
  intro E. eapply evidence_frame; [exact E|reflexivity|].
  destruct j as [c h a]; destruct c; intros; reflexivity.
Qed.

Theorem enriched_boot_transport initial final e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal initial,RebuildingBoundary (boot_pc initial)) e ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) initial final ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal final,RebuildingBoundary (boot_pc final)) e /\
  (forall c, In c (live_certificates e) -> unchanged (certificate_ranges ranges c)
    (object_flash sector (control_image (journal_control (boot_journal initial))))
    (object_flash sector (control_image (journal_control (boot_journal final))))).
Proof.
  intros [COMMON [EVIDENCE LINK]] TRACE.
  destruct COMMON as [JI BI].
  destruct (boot_finite_trace g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT initial final BI TRACE) as [FINAL PROJ].
  destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [PUB [ACK LOG]].
  assert (FRAME : forall x, 2*sector <= x ->
    control_image (journal_control (boot_journal final)) x = control_image (journal_control (boot_journal initial)) x).
  { intros; eapply logged_trace_frame_after_journal; eauto. }
  split.
  - split; [apply rebuilding_common; exact FINAL|]. split; [eapply evidence_frame; eauto|exact I].
  - intros c IN. assert (C : certificate_valid sector view ranges decode (boot_journal initial) c).
    { eapply Forall_forall; [exact (proj1 EVIDENCE)|exact IN]. }
    exact (proj2 (certificate_frame _ _ c C FRAME)).
Qed.

Theorem enriched_boot_usable j id d ram e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,RebuildingBoundary (Usable id d ram)) e ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary id d ram) e /\
  (exists c, In c (live_certificates e) /\ certificate_id c = id /\ certificate_decoded c = d) /\
  data_caller DataBegin ram /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)) e.
Proof.
  intros [[JI BI] [E LINK]].
  pose proof (completed_boot_common sector data_len boss_ok view marker ranges decode pages j id d ram BI) as COMMON.
  destruct (common_begin sector data_len boss_ok view marker ranges decode pages j id d ram COMMON) as [CALL NEXT].
  assert (MATCH : In (Certificate id d) (live_certificates e)).
  { destruct BI as [_ [_ [[READY [HEAD [READ FORMAT]]] RAM]]].
    destruct (proj1 (proj2 E) id HEAD) as [c [IN ID]].
    assert (C : certificate_valid sector view ranges decode j c).
    { eapply Forall_forall; [exact (proj1 E)|exact IN]. }
    destruct C as [R F]; rewrite ID in R.
    change (decode (object_flash sector (control_image (journal_control j))) id = Some d) in READ.
    rewrite READ in R. inversion R. destruct c; simpl in *; subst; exact IN. }
  split; [split; [exact COMMON|split; assumption]|]. split.
  - destruct BI as [_ [_ [[READY [HEAD [READ FORMAT]]] RAM]]].
    destruct (proj1 (proj2 E) id HEAD) as [c [IN ID]]. exists c; split; [exact IN|]. split; [exact ID|].
    assert (C : certificate_valid sector view ranges decode j c).
    { eapply Forall_forall; [exact (proj1 E)|exact IN]. }
    destruct C as [R F]; rewrite ID in R. change (decode (object_flash sector (control_image (journal_control j))) id = Some d) in READ. rewrite READ in R; inversion R; reflexivity.
  - split; [exact CALL|]. split; [exact NEXT|]. split; [exact E|exact I].
Qed.

Theorem enriched_boot_fatal j e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,RebuildingBoundary Stopped) e ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,FatalBoundary) e.
Proof. intros [[J B] [E LINK]]; split; [apply boot_stopped_common; exact B|]. split; [exact E|exact I]. Qed.

(* Reset from Ready, a recovery phase, or an actual returned-error phase.
   No ordinary RAM is kept. Interrupted publication reset edges are supplied
   by their journal trace, not fabricated by this adapter. *)
Theorem enriched_reset j phase e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,phase) e ->
  logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (logged_after_reset j,RebuildingBoundary Selecting) e.
Proof.
  intros [[JI REST] [E LINK]] STEP. split.
  - apply rebuilding_common. split.
    + eapply logged_step_preserves_invariant; eauto.
    + split; [destruct j as [c h a]; destruct c; exact I|exact I].
  - split; [apply reset_evidence; exact E|exact I].
Qed.

Theorem receipt_extension_wellformed j phase e c :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,phase) e ->
  In c (live_certificates e) -> hd_error (publications j) = Some (N.of_nat (certificate_id c)) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,phase) (observe_client j c e).
Proof.
  intros [CORE [[CERT [SEL RECEIPTS]] LINK]] IN HEAD.
  assert (C : certificate_valid sector view ranges decode j c).
  { eapply Forall_forall; eauto. }
  split; [exact CORE|]. split; [|exact LINK]. split; [exact CERT|]. split; [exact SEL|].
  constructor; [|exact RECEIPTS].
  destruct (publications j) as [|id tail] eqn:P; [discriminate|].
  simpl in HEAD; inversion HEAD; subst id. exists [],tail; simpl; rewrite P; simpl; split; reflexivity.
Qed.

(* Pruning is not reclamation: it removes unused logical certificates only.
   Historical receipts require no current read or retained pages. *)
Lemma evidence_prune j e kept :
  persistent_evidence sector view ranges decode j e ->
  (forall c, In c kept -> In c (live_certificates e)) ->
  (forall id, hd_error (publications j) = Some (N.of_nat id) -> exists c, In c kept /\ certificate_id c = id) ->
  persistent_evidence sector view ranges decode j (evidence_with_live e kept).
Proof.
  intros [C [S R]] SUB SEL. split; [|split; assumption].
  apply Forall_forall; intros c IN; eapply Forall_forall; [exact C|apply SUB; exact IN].
Qed.
Theorem prepared_certificates data_bytes data_writer boss_writer
    old id d index entry span s f data_flash prepared_flash history acks e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s))
    (boss_extent (view id)) ->
  erased_object_extent sector f span -> erased_object_extent sector data_flash (boss_extent (view id)) ->
  successful_writer_contracts sector view data_bytes data_writer boss_writer decode ->
  data_writer f span entry = Some data_flash ->
  boss_writer data_flash id (image_replace (recovered_image d) index (Some entry)) = Some prepared_flash ->
  let next := RecoveryDecoding (boss_extent (view id)) (image_replace (recovered_image d) index (Some entry)) in
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready prepared_flash) history acks,
      PublishingBoundary CandidatePrepared id next
        (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s))
    (evidence_with_live e [Certificate old d; Certificate id next]).
Proof.
  intros [[JI [IDLE [FORMAT COR]]] [EV IN]] RANGE FREE BFREE ERASED BERASED WRITERS DATA BOSS next.
  assert (OLDREAD : decode (object_flash sector f) old = Some d).
  { assert (C : certificate_valid sector view ranges decode (Logged (Ready f) history acks) (Certificate old d)).
    { eapply Forall_forall; [exact (proj1 EV)|exact IN]. } exact (proj1 C). }
  destruct (transaction_preparation_on_common_flash sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer decode old id (recovered_image d) index entry span s f data_flash prepared_flash
    history acks d IDLE (eq_sym (proj2 FORMAT)) RANGE FREE BFREE ERASED BERASED WRITERS CONTRACT DATA BOSS OLDREAD)
    as [DI [P [CUR [LINK [J [HEAD [OLD [NEW KEEP]]]]]]]].
  assert (NF : decoded_root_agrees view ranges id next).
  { eapply recovery_format_contract; [exact CONTRACT|exact NEW]. }
  split.
  - split; [exact J|]. split; [exact (proj1 DI)|]. split; [reflexivity|]. split; [exact P|].
    split; [exact NF|]. split.
    + unfold image_current_correspondence. rewrite CUR. destruct NF as [B E]; rewrite B,E; reflexivity.
    + split; assumption.
  - split.
    + split.
      * constructor; [split; [exact OLD|exact FORMAT]|]. constructor; [split; [exact NEW|exact NF]|constructor].
      * split.
        -- intros selected H. change (hd_error history = Some (N.of_nat selected)) in H.
           assert (selected = old) by (apply Nat2N.inj; congruence). subst selected.
           exists (Certificate old d); simpl; auto.
        -- exact (proj2 (proj2 EV)).
    + unfold boundary_certificate_link; simpl; auto.
Qed.

Theorem successful_exit_evidence old id image index entry span s prepared ready old_decoded e
    out slot pubs acks :
  persistent_evidence sector view ranges decode ready e ->
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id :: acks)) ->
  let j := Logged (Ready out) pubs (N.of_nat id :: acks) in
  let d := RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)) in
  let result := finish_data_client view marker id ranges image index entry span s in
  let evidence := observe_client j (Certificate id d) (evidence_with_live e [Certificate id d]) in
  snd result = DataClientSuccess id (recovered_image d) /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,ClientBoundary id d (fst result)) evidence.
Proof.
  intros EV CONT TRACE ACK j d result evidence.
  destruct (successful_continuation_common sector data_len boss_ok view marker ranges decode pages
    g old id image index entry span s prepared ready old_decoded out slot pubs acks CONTRACT CONT TRACE ACK)
    as [CLIENT [CORE IDLE]].
  destruct (proj1 CONT out slot pubs acks TRACE ACK) as [_ [JI [READ REST]]].
  assert (HEAD : hd_error pubs = Some (N.of_nat id)) by (exact (proj1 (proj2 (proj2 (proj2 JI))))).
  assert (FORMAT : decoded_root_agrees view ranges id d).
  { eapply recovery_format_contract; [exact CONTRACT|exact READ]. }
  assert (LOG : clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok) ready j).
  { eapply rt_trans; [eapply successful_trace_is_logged; exact TRACE|apply rt_step; exact ACK]. }
  destruct (logged_history_extension _ _ _ _ _ _ _ LOG) as [prefix EXT].
  assert (BASE : enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,ClientBoundary id d (fst result)) (evidence_with_live e [Certificate id d])).
  { split; [exact CORE|]. split.
    - split; [constructor; [split; assumption|constructor]|]. split.
      + intros selected H. change (hd_error pubs = Some (N.of_nat selected)) in H.
        assert (selected=id) by (apply Nat2N.inj; congruence). subst selected.
        exists (Certificate id d); simpl; auto.
      + change (Forall (receipt_valid view ranges (publications j)) (client_receipts e)).
        rewrite EXT. apply receipts_extend; exact (proj2 (proj2 EV)).
    - unfold boundary_certificate_link; simpl; auto. }
  split; [exact CLIENT|]. apply receipt_extension_wellformed; [exact BASE|simpl; auto|exact HEAD].
Qed.

Theorem uncertain_cleanup_evidence id d s j error_j commands e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary CandidatePrepared id d s) e ->
  forall old, hd_error (publications j) = Some old ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) j error_j ->
  let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
  data_calls commands (uncertain_return selected s) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (error_j,FrozenBoundary old (N.of_nat id) None (execute_data commands (uncertain_return selected s))) e.
Proof.
  intros [[JI [PI [F [P [FORMAT [COR [LINK DI]]]]]]] [EV IN]] old HEAD TRACE selected CALL.
  assert (CUR : protection_current s ++ attached_ranges s = root_extents (view id)).
  { unfold image_current_correspondence in COR. destruct FORMAT as [B E]; rewrite B,E in COR; exact COR. }
  assert (CORE : common_invariant sector data_len boss_ok view marker ranges decode pages
    (error_j,FrozenBoundary old (N.of_nat id) None (execute_data commands (uncertain_return selected s)))).
  { eapply frozen_cleanup_common; eauto. rewrite Nat2N.id; exact CUR. }
  destruct (uncertain_trace_reset_boundary _ _ _ _ _ _ _ _ G DIV JI TRACE) as [JERR [CHOICE [ACK FRAME]]].
  destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ TRACE) as [_ [_ LOG]].
  destruct (logged_history_extension _ _ _ _ _ _ _ LOG) as [prefix EXT].
  split; [exact CORE|]. split; [|exact I]. split.
  - eapply Forall_impl; [|exact (proj1 EV)]. intros c C; exact (proj1 (certificate_frame j error_j c C FRAME)).
  - split.
    + intros chosen H. change (hd_error (publications error_j) = Some (N.of_nat chosen)) in H. cbn [fst] in CHOICE. destruct CHOICE as [SAME|NEW].
      * apply (proj1 (proj2 EV) chosen). change (hd_error (publications j) = Some (N.of_nat chosen)). rewrite <- SAME; exact H.
      * assert (chosen=id) by (apply Nat2N.inj; congruence). subst chosen.
        exists (Certificate id d); split; [exact IN|reflexivity].
    + change (Forall (receipt_valid view ranges (publications error_j)) (client_receipts e)). rewrite EXT. apply receipts_extend; exact (proj2 (proj2 EV)).
Qed.

(* Main no-later-publication consumer: the certificate and receipt are supplied
   ONCE by the client boundary. Every finite boot prefix, including fatal and
   reset prefixes, carries them; a completed boot reconstructs the exact image. *)
Theorem client_reset_repeated_boot j id d ram e final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,ClientBoundary id d ram) e ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (logged_after_reset j,Selecting) final ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal final,RebuildingBoundary (boot_pc final)) e /\
  Forall (receipt_valid view ranges (publications (boot_journal final))) (client_receipts e) /\
  forall jf chosen decoded restored, final=(jf,Usable chosen decoded restored) ->
    chosen=id /\ decoded=d /\
    enriched_invariant sector data_len boss_ok view marker ranges decode pages (jf,IdleBoundary id d restored) e /\
    data_caller DataBegin restored /\
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (jf,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin restored)) e.
Proof.
  intros START TRACE. pose proof START as START0.
  destruct START as [CORE [EV IN]].
  destruct CORE as [JI [[IDLE [FORMAT COR]] APPEND]].
  destruct IDLE as [ROOT [_ [READY [HEAD LINK]]]].
  assert (RESET : logged_step g sector 256 data_len boss_ok j (logged_after_reset j)).
  { destruct j as [c h a]; destruct READY as [f EQ]; simpl in EQ; subst c.
    apply (record_step g sector 256 data_len boss_ok); apply reset_ready. }
  assert (ENTRY : enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (logged_after_reset j,RebuildingBoundary Selecting) e).
  { eapply enriched_reset; [exact START0|exact RESET]. }
  destruct (enriched_boot_transport (logged_after_reset j,Selecting) final e ENTRY TRACE) as [FINAL FRAME].
  split; [exact FINAL|]. split; [exact (proj2 (proj2 (proj1 (proj2 FINAL))))|].
  intros jf chosen decoded restored EQ; subst final.
  destruct (enriched_boot_usable jf chosen decoded restored e FINAL) as [USE [C [CALL NEXT]]].
  destruct (boot_prefix_safety g sector data_len boss_ok view marker ranges decode topology pages
    (logged_after_reset j) (jf,Usable chosen decoded restored) G DIV CONTRACT
    (proj1 (proj1 ENTRY)) ltac:(destruct j as [c h a]; destruct c; exact I) TRACE)
    as [_ [PUB REST]].
  assert (CHOSEN : chosen=id).
  { destruct USE as [[_ [IDLE' _]] _].
    pose proof (proj1 (proj2 (proj2 (proj2 IDLE')))) as H.
    change (hd_error (publications jf) = Some (N.of_nat chosen)) in H.
    change (publications jf = publications j) in PUB. change (hd_error (publications j) = Some (N.of_nat id)) in HEAD. rewrite PUB,HEAD in H.
    apply Nat2N.inj; congruence. }
  subst chosen.
  assert (OLD : certificate_valid sector view ranges decode jf (Certificate id d)).
  { eapply Forall_forall; [exact (proj1 (proj1 (proj2 FINAL)))|exact IN]. }
  destruct (proj2 (proj1 FINAL)) as [_ [_ [[R [H [READ FMT]]] RAM]]].
  destruct OLD as [READ' FMT']; simpl in READ'.
  change (decode (object_flash sector (control_image (journal_control jf))) id = Some decoded) in READ.
  assert (decoded=d) by congruence. subst decoded. split; [reflexivity|]. split; [reflexivity|]. split; [exact USE|]. split; assumption.
Qed.
Theorem enriched_slot_completed s j f index id history acks d e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary CandidatePrepared id d s) e ->
  logged_step g sector 256 data_len boss_ok j (Logged (AwaitAck f index (N.of_nat id)) history acks) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (AwaitAck f index (N.of_nat id)) history acks,
      PublishingBoundary SlotVisible id d (slot_publication (root_extents (view id)) s)) e.
Proof.
  intros [[JI [PI [F [P [FMT [COR [LINK DI]]]]]]] [EV IN]] STEP.
  assert (CUR : protection_current s ++ attached_ranges s = root_extents (view id)).
  { unfold image_current_correspondence in COR. destruct FMT as [B E]; rewrite B,E in COR; exact COR. }
  pose proof (completed_slot_common sector data_len boss_ok view marker ranges decode pages
    g s j f index id history acks d G DIV JI STEP PI F P CUR FMT) as CORE.
  assert (LOG : clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok) j
    (Logged (AwaitAck f index (N.of_nat id)) history acks)) by (apply rt_step; exact STEP).
  assert (FRAME : forall x, 2*sector <= x -> f x=control_image (journal_control j) x).
  { intros; exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ _ G DIV JI LOG H). }
  destruct (logged_history_extension _ _ _ _ _ _ _ LOG) as [prefix EXT].
  split; [exact CORE|]. split; [|exact IN]. split.
  - eapply Forall_impl; [|exact (proj1 EV)]. intros c C; exact (proj1 (certificate_frame j (Logged (AwaitAck f index (N.of_nat id)) history acks) c C FRAME)).
  - split.
    + intros chosen H. change (hd_error history = Some (N.of_nat chosen)) in H.
      pose proof (proj2 (proj1 (proj2 (proj1 CORE)))) as HEAD.
      change (hd_error history = Some (N.of_nat id)) in HEAD.
      assert (chosen=id) by (apply Nat2N.inj; congruence). subst chosen.
      exists (Certificate id d); split; [exact IN|reflexivity].
    + change (Forall (receipt_valid view ranges history) (client_receipts e)).
      change (history = prefix ++ publications j) in EXT. rewrite EXT; apply receipts_extend; exact (proj2 (proj2 EV)).
Qed.

Theorem enriched_append_return f index id history acks d s e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (AwaitAck f index (N.of_nat id)) history acks,PublishingBoundary SlotVisible id d s) e ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history (N.of_nat id::acks),PublishingBoundary AppendReturned id d s) e.
Proof.
  intros [[JI [PI [F [P [FMT [COR [LINK HEAD]]]]]]] [EV IN]].
  split.
  - split; [eapply append_return_preserves_logged_invariant; eauto|].
    split; [exact PI|]. split; [exact F|]. split; [exact P|]. split; [exact FMT|].
    split; [exact COR|]. split; [exact LINK|]. split; [exact HEAD|reflexivity].
  - split; assumption.
Qed.

Theorem enriched_durable_sync j id d s e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary AppendReturned id d s) e ->
  In marker (protection_base s) ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary DurableSynchronized id d (durable_ram_update marker (root_extents (view id)) s)) e.
Proof.
  intros [[JI [PI [F [P [FMT [COR [LINK [HEAD ACK]]]]]]]] [EV IN]] MARK.
  assert (CUR : protection_current s ++ attached_ranges s = root_extents (view id)).
  { unfold image_current_correspondence in COR. destruct FMT as [B E]; rewrite B,E in COR; exact COR. }
  split.
  - split; [exact JI|]. split; [apply durable_ram_update_preserves; assumption|].
    split; [exact F|]. split; [exact P|]. split; [exact FMT|]. split; [exact COR|].
    split; [exact LINK|]. split; [exact HEAD|]. split; [exact ACK|]. split; reflexivity.
  - split; assumption.
Qed.

Theorem enriched_client_next j id d ram e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,ClientBoundary id d ram) e ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary id d ram) e /\
  data_caller DataBegin ram /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)) e.
Proof.
  intros [[JI [USE ACK]] [EV IN]].
  assert (IDLE : common_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary id d ram)) by (split; assumption).
  destruct (common_begin sector data_len boss_ok view marker ranges decode pages j id d ram IDLE) as [CALL NEXT].
  split; [split; [exact IDLE|split; assumption]|]. split; [exact CALL|]. split; [exact NEXT|]. split; [exact EV|exact I].
Qed.

Definition client_restart_post j id d ram e :=
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,ClientBoundary id d ram) e /\
  forall final,
    clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
      (logged_after_reset j,Selecting) final ->
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (boot_journal final,RebuildingBoundary (boot_pc final)) e /\
    Forall (receipt_valid view ranges (publications (boot_journal final))) (client_receipts e) /\
    forall jf chosen decoded restored, final=(jf,Usable chosen decoded restored) ->
      chosen=id /\ decoded=d /\
      enriched_invariant sector data_len boss_ok view marker ranges decode pages (jf,IdleBoundary id d restored) e /\
      data_caller DataBegin restored /\
      enriched_invariant sector data_len boss_ok view marker ranges decode pages
        (jf,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin restored)) e.

Theorem publication_success_boot old id image index entry span s prepared ready old_decoded e out slot pubs acks :
  persistent_evidence sector view ranges decode ready e ->
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id :: acks)) ->
  let j := Logged (Ready out) pubs (N.of_nat id :: acks) in
  let d := RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)) in
  let result := finish_data_client view marker id ranges image index entry span s in
  snd result = DataClientSuccess id (recovered_image d) /\
  client_restart_post j id d (fst result)
    (observe_client j (Certificate id d) (evidence_with_live e [Certificate id d])).
Proof.
  intros E CONT TRACE ACK j d result.
  destruct (successful_exit_evidence old id image index entry span s prepared ready old_decoded e out slot pubs acks
    E CONT TRACE ACK) as [RETURN INV].
  split; [exact RETURN|]. split; [exact INV|]. intros final T; eapply client_reset_repeated_boot; eauto.
Qed.

Theorem prepared_client_repeated_boot data_bytes data_writer boss_writer
    old id d index entry span s f data_flash prepared_flash history acks e out slot pubs append_acks :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)) ->
  erased_object_extent sector f span -> erased_object_extent sector data_flash (boss_extent (view id)) ->
  successful_writer_contracts sector view data_bytes data_writer boss_writer decode ->
  data_writer f span entry = Some data_flash ->
  boss_writer data_flash id (image_replace (recovered_image d) index (Some entry)) = Some prepared_flash ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    (Logged (Ready prepared_flash) history acks) (Logged (AwaitAck out slot (N.of_nat id)) pubs append_acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs append_acks)
    (Logged (Ready out) pubs (N.of_nat id :: append_acks)) ->
  let next := RecoveryDecoding (boss_extent (view id)) (image_replace (recovered_image d) index (Some entry)) in
  let j := Logged (Ready out) pubs (N.of_nat id :: append_acks) in
  let result := finish_data_client view marker id ranges (recovered_image d) index entry span s in
  snd result = DataClientSuccess id (recovered_image next) /\
  client_restart_post j id next (fst result)
    (observe_client j (Certificate id next) (evidence_with_live e [Certificate id next])).
Proof.
  intros START RANGE FREE BFREE ERASED BERASED WRITERS DATA BOSS TRACE ACK next j result.
  pose proof (prepared_certificates data_bytes data_writer boss_writer old id d index entry span s f data_flash prepared_flash
    history acks e START RANGE FREE BFREE ERASED BERASED WRITERS DATA BOSS) as PREP.
  destruct START as [[JI [IDLE [FORMAT COR]]] [EV IN]].
  assert (READ : decode (object_flash sector f) old = Some d).
  { assert (C : certificate_valid sector view ranges decode (Logged (Ready f) history acks) (Certificate old d)).
    { eapply Forall_forall; [exact (proj1 EV)|exact IN]. } exact (proj1 C). }
  pose proof (prepared_publication_client_or_uncertain g sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer decode old id (recovered_image d) index entry span s f data_flash prepared_flash
    history acks d G DIV IDLE (eq_sym (proj2 FORMAT)) RANGE FREE BFREE ERASED BERASED WRITERS CONTRACT DATA BOSS READ) as CONT.
  exact (publication_success_boot old id (recovered_image d) index entry span s _ _ d _ out slot pubs append_acks
    (proj1 (proj2 PREP)) CONT TRACE ACK).
Qed.

Theorem uncertain_cleanup_repeated_boot id d s j error_j commands e old final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,PublishingBoundary CandidatePrepared id d s) e ->
  hd_error (publications j) = Some old ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) j error_j ->
  returned_error_control (journal_control error_j) ->
  let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
  data_calls commands (uncertain_return selected s) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (logged_after_reset error_j,Selecting) final ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (error_j,FrozenBoundary old (N.of_nat id) None (execute_data commands (uncertain_return selected s))) e /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal final,RebuildingBoundary (boot_pc final)) e /\
  forall jf chosen decoded restored, final=(jf,Usable chosen decoded restored) ->
    (N.of_nat chosen=old \/ chosen=id) /\
    (exists c, In c (live_certificates e) /\ certificate_id c=chosen /\ certificate_decoded c=decoded) /\
    data_caller DataBegin restored /\
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (jf,OpenBoundary (recovered_image decoded) [recovered_boss decoded] (data_next DataBegin restored)) e.
Proof.
  intros START HEAD TRACE ERROR selected CALL BOOT.
  pose proof (uncertain_cleanup_evidence id d s j error_j commands e START old HEAD TRACE CALL) as FROZEN.
  pose proof (enriched_reset error_j _ e FROZEN
    (returned_error_reset_step g sector 256 data_len boss_ok error_j ERROR)) as RESET.
  destruct (enriched_boot_transport (logged_after_reset error_j,Selecting) final e RESET BOOT) as [FINAL FRAME].
  split; [exact FROZEN|]. split; [exact FINAL|]. intros jf chosen decoded restored EQ; subst final.
  destruct (enriched_boot_usable jf chosen decoded restored e FINAL) as [USE [C [CALL' NEXT]]].
  split; [|split; [exact C|split; assumption]].
  destruct (boot_prefix_safety g sector data_len boss_ok view marker ranges decode topology pages
    (logged_after_reset error_j) (jf,Usable chosen decoded restored) G DIV CONTRACT
    (proj1 (proj1 RESET)) ltac:(destruct error_j as [ctrl h a]; destruct ctrl; exact I) BOOT)
    as [_ [PUB REST]].
  destruct USE as [[_ [IDLE' _]] _].
  pose proof (proj1 (proj2 (proj2 (proj2 IDLE')))) as CHOSEN.
  change (hd_error (publications jf)=Some (N.of_nat chosen)) in CHOSEN.
  change (publications jf=publications error_j) in PUB; rewrite PUB in CHOSEN.
  destruct (proj2 (proj1 FROZEN)) as [_ [_ [_ [CHOICE COVER]]]].
  cbn [fst] in CHOICE. destruct CHOICE as [A|B]; [left|right; apply Nat2N.inj]; congruence.
Qed.
Theorem prepared_uncertain_repeated_boot data_bytes data_writer boss_writer
    old id d index entry span s f data_flash prepared_flash history acks e error_j commands final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)) ->
  erased_object_extent sector f span -> erased_object_extent sector data_flash (boss_extent (view id)) ->
  successful_writer_contracts sector view data_bytes data_writer boss_writer decode ->
  data_writer f span entry = Some data_flash ->
  boss_writer data_flash id (image_replace (recovered_image d) index (Some entry)) = Some prepared_flash ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    (Logged (Ready prepared_flash) history acks) error_j ->
  returned_error_control (journal_control error_j) ->
  let prepared := prepared_transaction_candidate view id ranges (recovered_image d) index entry span s in
  let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
  data_calls commands (uncertain_return selected prepared) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (logged_after_reset error_j,Selecting) final ->
  let next := RecoveryDecoding (boss_extent (view id)) (image_replace (recovered_image d) index (Some entry)) in
  let kept := evidence_with_live e [Certificate old d;Certificate id next] in
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (error_j,FrozenBoundary (N.of_nat old) (N.of_nat id) None (execute_data commands (uncertain_return selected prepared))) kept /\
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal final,RebuildingBoundary (boot_pc final)) kept /\
  forall jf chosen decoded restored, final=(jf,Usable chosen decoded restored) ->
    ((chosen=old /\ decoded=d) \/ (chosen=id /\ decoded=next)) /\
    data_caller DataBegin restored /\
    enriched_invariant sector data_len boss_ok view marker ranges decode pages
      (jf,OpenBoundary (recovered_image decoded) [recovered_boss decoded] (data_next DataBegin restored)) kept.
Proof.
  intros START RANGE FREE BFREE ERASED BERASED WRITERS DATA BOSS TRACE ERROR prepared selected CALL BOOT next kept.
  pose proof (prepared_certificates data_bytes data_writer boss_writer old id d index entry span s f data_flash prepared_flash
    history acks e START RANGE FREE BFREE ERASED BERASED WRITERS DATA BOSS) as PREP.
  assert (HEAD : hd_error history = Some (N.of_nat old)).
  { pose proof (proj1 (proj2 (proj1 START))) as IDLE. exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
  destruct (uncertain_cleanup_repeated_boot id next prepared _ error_j commands kept (N.of_nat old) final
    PREP HEAD TRACE ERROR CALL BOOT) as [FROZEN [FINAL USE]].
  split; [exact FROZEN|]. split; [exact FINAL|].
  intros jf chosen decoded restored EQ.
  destruct (USE jf chosen decoded restored EQ) as [CHOICE [[c [IN [ID DECODED]]] [BEGIN NEXT]]].
  split; [|split; assumption].
  change (In c [Certificate old d;Certificate id next]) in IN.
  destruct IN as [A|[B|[]]]; subst c; simpl in ID, DECODED; [left|right]; split; congruence.
Qed.

Theorem enriched_fatal_view j phase e :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,phase) e ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,FatalBoundary) e.
Proof. intros [[JI REST] [EV IN]]; split; [split; [exact JI|exact I]|split; [exact EV|exact I]]. Qed.

Theorem initialized_boundary_evidence j id d ram :
  journal_idle sector 256 data_len boss_ok view marker id ram j ->
  decode (object_flash sector (control_image (journal_control j))) id = Some d ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (j,IdleBoundary id d ram) (Evidence [Certificate id d] []).
Proof.
  intros IDLE READ.
  assert (FMT : decoded_root_agrees view ranges id d) by (eapply recovery_format_contract; eauto).
  split; [apply journal_idle_common; assumption|]. split.
  - split; [constructor; [split; assumption|constructor]|]. split; [|constructor].
    intros chosen H. change (hd_error (publications j)=Some (N.of_nat chosen)) in H. pose proof (proj1 (proj2 (proj2 (proj2 IDLE)))) as HEAD.
    assert (chosen=id) by (apply Nat2N.inj; congruence). subst chosen.
    exists (Certificate id d); simpl; auto.
  - unfold boundary_certificate_link; simpl; auto.
Qed.

Theorem failed_writer_boot_evidence old d s f history acks e reserved saved result final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) history acks,IdleBoundary old d s) e ->
  preparation_failed_post g sector data_len boss_ok view marker ranges decode
    old d history acks reserved saved result ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (Logged (Boot (writer_flash result)) history acks,Selecting) final ->
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (boot_journal final,RebuildingBoundary (boot_pc final))
    (evidence_with_live e [Certificate old d]).
Proof.
  intros [[JI [IDLE [FMT COR]]] [EV IN]] [AFTER [READ REST]] TRACE.
  pose proof (proj1 (proj2 (proj2 (proj2 IDLE)))) as HEAD.
  assert (REACHED : persistent_evidence sector view ranges decode
    (Logged (Ready (writer_flash result)) history acks)
    (evidence_with_live e [Certificate old d])).
  { split.
    - constructor; [split; [exact READ|exact FMT]|constructor].
    - split; [|exact (proj2 (proj2 EV))]. intros chosen H.
      change (hd_error history = Some (N.of_nat chosen)) in H.
      change (hd_error history = Some (N.of_nat old)) in HEAD.
      assert (chosen=old) by (apply Nat2N.inj; congruence). subst chosen.
      exists (Certificate old d); simpl; auto. }
  assert (STEP : logged_step g sector 256 data_len boss_ok
    (Logged (Ready (writer_flash result)) history acks) (Logged (Boot (writer_flash result)) history acks)).
  { apply (record_step g sector 256 data_len boss_ok); apply reset_ready. }
  assert (RESET : enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Boot (writer_flash result)) history acks,RebuildingBoundary Selecting)
    (evidence_with_live e [Certificate old d])).
  { split.
    - apply rebuilding_common. split; [eapply logged_step_preserves_invariant; eauto|split; exact I].
    - split; [exact (reset_evidence _ _ REACHED)|exact I]. }
  exact (proj1 (enriched_boot_transport (Logged (Boot (writer_flash result)) history acks,Selecting) final _ RESET TRACE)).
Qed.

Lemma equal_offsets_different_events id history : history <> [] ->
  pred (length history) < pred (length (N.of_nat id :: history)).
Proof. destruct history; simpl; intros; [contradiction|lia]. Qed.
End Transport.
