From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Neutralization DataEpisode TransactionBoundary
 PersistentBoundary PublicationPreparation JournalHistory PreparedAuthority
 RetentionCoverage PageOwnership CollectionRoots CompactUpdates JournalPhaseShape
 JournalProtocolAuthority JournalIndex JournalReachableShape JournalRecoveryTrace JournalRequests BootReconstruction FlashSpec.
Import ListNotations.

Lemma neutral_ready_frame sector data_len boss_ok f f' h a :
 logged_invariant sector 256 data_len boss_ok (Logged (Ready f) h a) ->
 valid_flash f' -> (forall x, x<2*sector -> f' x=f x) ->
 logged_invariant sector 256 data_len boss_ok (Logged (Ready f') h a).
Proof.
 intros [[V [SH CLEAN]] [HEAD ACK]] V' FRAME.
 assert (BYTES : sector_bytes f' 0 sector=sector_bytes f 0 sector).
 { unfold sector_bytes; apply map_ext_in; intros x X; apply in_seq in X; apply FRAME; lia. }
 split; [split; [exact V'|split]|split; [|exact ACK]].
 - unfold JournalPhaseShape.shape in *; rewrite BYTES; exact SH.
 - intros i I; rewrite FRAME by lia; apply CLEAN; exact I.
 - change (observed sector 256 data_len boss_ok f'=hd_error h).
   unfold observed; rewrite BYTES; exact HEAD.
Qed.

(* Drop obsolete live certificates, never historical receipts. The selected
   authority is derived from the idle boundary, not from authentication. *)
Definition selected_evidence old d e := evidence_with_live e [Certificate old d].

Theorem neutralization_idle_transport g sector data_len boss_ok view marker ranges decode pages
 recognize magic fuel lo hi f h a old d s e result :
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,IdleBoundary old d s) e ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 neutral_run g sector recognize magic hi lo f result ->
 free_range 256 (protection_table s) (block_pages lo (hi-lo)) /\
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready (neutral_flash result)) h a,IdleBoundary old d s) (selected_evidence old d e).
Proof.
 intros CONTRACT LOCAL [[JI [IDLE [FORMAT IMAGE]]] [EV CERT]] SELECT RUN.
 destruct IDLE as [ROOT [JI0 [READY [HEAD LINK]]]].
 pose proof (proj1 ROOT) as DI.
 pose proof (proj1 (proj1 (proj1 DI))) as COVER.
 destruct (neutralization_consumer g sector recognize magic lo hi (protection_table s) f result
   (required_ranges s) LOCAL (proj1 (proj1 JI)) COVER
   (selected_check_sound _ _ _ _ _ _ SELECT) RUN) as [FREE [VALID [KEEP FRAME]]].
 assert (JN : logged_invariant sector 256 data_len boss_ok (Logged (Ready (neutral_flash result)) h a)).
 { eapply neutral_ready_frame; eauto. }
 assert (ROOTIN : forall r, In r (root_extents (view old)) -> In r (required_ranges s)).
 { intros r IN. destruct ROOT as [_ [_ [_ [_ [_ [_ [PH ACK]]]]]]].
   unfold required_ranges. repeat rewrite in_app_iff. rewrite PH. tauto. }
 assert (READ : certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate old d)).
 { apply (proj1 (Forall_forall _ _) (proj1 EV)); exact CERT. }
 assert (READ' : certificate_valid sector view ranges decode
   (Logged (Ready (neutral_flash result)) h a) (Certificate old d)).
 { destruct READ as [R F]. split; [|exact F]. simpl in R |- *.
   rewrite <- (recovery_locality_contract _ _ _ CONTRACT (object_flash sector f) (object_flash sector (neutral_flash result)) old).
   - exact R.
   - intros r x IN AT; exact (KEEP r x (ROOTIN r IN) AT). }
 split; [exact FREE|]. split; [exact KEEP|]. split.
 - split; [exact JN|]. split.
   + split; [exact ROOT|]. split; [exact JN|]. split; [eexists; reflexivity|]. split; assumption.
   + split; assumption.
 - split.
   + split; [constructor; [exact READ'|constructor]|]. split.
     * intros id H. change (hd_error h=Some (N.of_nat id)) in H.
       change (hd_error h=Some (N.of_nat old)) in HEAD.
       assert (id=old) by (apply Nat2N.inj; congruence). subst id.
       exists (Certificate old d); simpl; auto.
     * exact (proj2 (proj2 EV)).
   + unfold boundary_certificate_link, selected_evidence; simpl; auto.
Qed.

(* The Idle witness above is a logical frame lemma, NOT permission to resume
   after an error/reset. The following adapter chooses the actual control. *)
Definition neutral_boundary old d s h a result :=
 let j := Logged (Ready (neutral_flash result)) h a in
 match neutral_end_ result with
 | NeutralSuccess => (j,IdleBoundary old d s)
 | NeutralError => (j,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some [recovered_boss d]) (data_next DataFreeze s))
 | NeutralReset => (logged_after_reset j,RebuildingBoundary Selecting)
 | NeutralFatal => (j,FatalBoundary)
 end.

Lemma neutral_freeze_idle sector data_len boss_ok view marker ranges decode pages j old d s e :
 enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary old d s) e ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (j,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some [recovered_boss d]) (data_next DataFreeze s)) e.
Proof.
 intros [[JI [[ROOT [_ [_ [HEAD LINK]]]] REST]] [EV CERT]].
 pose proof (proj1 ROOT) as DI.
 split; [|split; [exact EV|exact I]]. split; [exact JI|].
 split; [apply data_command_preserves; [exact DI|exact I]|].
 split; [reflexivity|]. split; [exact LINK|]. split; [left; exact HEAD|].
 change (protected (needed 256 (root_extents (view (N.to_nat (N.of_nat old))) ++
   root_extents (view (N.to_nat (N.of_nat old))))) (protection_table s)).
 rewrite Nat2N.id. intros p NEED.
 apply (proj1 (proj1 (proj1 DI))). destruct NEED as [r [IN HIT]].
 exists r; split; [|exact HIT].
 destruct ROOT as [_ [_ [_ [_ [_ [_ [PH ACK]]]]]]].
 apply in_app_iff in IN. unfold required_ranges. repeat rewrite in_app_iff. rewrite PH. tauto.
Qed.

Theorem selected_neutralization_boundary g sector data_len boss_ok view marker ranges decode topology pages
 recognize magic fuel lo hi f h a old d s e result :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,IdleBoundary old d s) e ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 neutral_run g sector recognize magic hi lo f result ->
 free_range 256 (protection_table s) (block_pages lo (hi-lo)) /\
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (neutral_boundary old d s h a result) (selected_evidence old d e) /\
 (neutral_end_ result=NeutralReset ->
   episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)).
Proof.
 intros G DIV C L INV SEL RUN.
 destruct (neutralization_idle_transport _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C L INV SEL RUN)
   as [FREE [KEEP IDLE]].
 assert (RESET : enriched_invariant sector data_len boss_ok view marker ranges decode pages
  (logged_after_reset (Logged (Ready (neutral_flash result)) h a),RebuildingBoundary Selecting)
  (selected_evidence old d e)).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact IDLE|].
   apply record_step. apply reset_ready. }
 split; [exact FREE|]. split; [exact KEEP|]. split.
 - unfold neutral_boundary. destruct (neutral_end_ result).
   + exact IDLE.
   + apply neutral_freeze_idle with (d:=d); exact IDLE.
   + exact RESET.
   + destruct IDLE as [[JI REST] [EV LINK]]. split; [split; [exact JI|exact I]|].
     split; [exact EV|exact I].
 - intros _. eapply boot_entry_post; eauto.
Qed.

Theorem neutralization_frozen_cleanups sector data_len boss_ok view marker ranges decode pages
 j old current s e commands :
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (j,FrozenBoundary old old current s) e -> data_calls commands s ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (j,FrozenBoundary old old (opaque_frozen_root current commands) (execute_data commands s)) e /\
 protection_table (execute_data commands s)=protection_table s /\
 physical_authority (execute_data commands s)=physical_authority s /\
 acknowledged_authority (execute_data commands s)=acknowledged_authority s.
Proof.
 intros [[JI [DI [FR [LINK [CHOICE COVER]]]]] [EV CERT]] CALL.
 pose proof (data_execution_preserves commands s DI CALL) as NEXT.
 pose proof (data_execution_refines commands s DI CALL) as TRACE.
 destruct (frozen_preparation_trace_keeps_storage 256 _ _ FR TRACE) as [FR' [TABLE AUTH]].
 destruct (data_execution_no_publication commands s) as [PH ACK].
 split; [|auto]. split; [|split; [exact EV|exact I]]. split; [exact JI|].
 split; [exact NEXT|]. split; [exact FR'|]. split.
 - unfold protection_history_link in *; rewrite PH; exact LINK.
 - split; [exact CHOICE|]. rewrite TABLE; exact COVER.
Qed.

(* The same table and certificates, now at the actual open-transaction
   allocation point (including the BOSS allocation after Data attachment). *)
Theorem neutralization_open_transport g sector data_len boss_ok view marker ranges decode pages
 recognize magic fuel lo hi f h a old image root s e result :
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 neutral_run g sector recognize magic hi lo f result ->
 free_range 256 (protection_table s) (block_pages lo (hi-lo)) /\
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 exists d,
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready (neutral_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e).
Proof.
 intros CONTRACT LOCAL [[JI [DI [FR [IMAGE LINK]]]] [EV CERT]] HEAD SELECT RUN.
 pose proof (proj1 (proj1 (proj1 DI))) as COVER.
 destruct (neutralization_consumer g sector recognize magic lo hi (protection_table s) f result
   (required_ranges s) LOCAL (proj1 (proj1 JI)) COVER
   (selected_check_sound _ _ _ _ _ _ SELECT) RUN) as [FREE [VALID [KEEP FRAME]]].
 assert (JN : logged_invariant sector 256 data_len boss_ok (Logged (Ready (neutral_flash result)) h a)).
 { eapply neutral_ready_frame; eauto. }
 assert (PH : physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK. rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 destruct (proj1 (proj2 EV) old HEAD) as [c [IN ID]]. destruct c as [id d]; simpl in ID; subst id.
 assert (READ : certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate old d)).
 { apply (proj1 (Forall_forall _ _) (proj1 EV)); exact IN. }
 assert (READ' : certificate_valid sector view ranges decode
   (Logged (Ready (neutral_flash result)) h a) (Certificate old d)).
 { destruct READ as [R F]. split; [|exact F]. simpl in R |- *.
   rewrite <- (recovery_locality_contract _ _ _ CONTRACT
     (object_flash sector f) (object_flash sector (neutral_flash result)) old).
   - exact R.
   - intros r x IN' AT. apply (KEEP r x); [|exact AT].
     unfold required_ranges; repeat rewrite in_app_iff; rewrite PH; tauto. }
 split; [exact FREE|]. split; [exact KEEP|]. exists d. split.
 - split; [exact JN|]. split; [exact DI|]. split; [exact FR|]. split; assumption.
 - split.
   + split; [constructor; [exact READ'|constructor]|]. split.
     * intros id H; change (hd_error h=Some (N.of_nat id)) in H.
       assert (id=old) by (apply Nat2N.inj; congruence). subst id.
       exists (Certificate old d); simpl; auto.
     * exact (proj2 (proj2 EV)).
   + exact I.
Qed.

Lemma neutral_freeze_open sector data_len boss_ok view marker ranges decode pages j old image root s e :
 enriched_invariant sector data_len boss_ok view marker ranges decode pages (j,OpenBoundary image root s) e ->
 hd_error (publications j)=Some (N.of_nat old) ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (j,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) (data_next DataFreeze s)) e.
Proof.
 intros [[JI [DI [FR [IMAGE LINK]]]] [EV CERT]] HEAD.
 assert (PH : physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; cbn in LINK; rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 split; [|split; [exact EV|exact I]]. split; [exact JI|].
 split; [apply data_command_preserves; [exact DI|exact I]|].
 split; [reflexivity|]. split; [exact LINK|]. split; [left; exact HEAD|].
 change (protected (needed 256 (root_extents (view (N.to_nat (N.of_nat old))) ++
   root_extents (view (N.to_nat (N.of_nat old))))) (protection_table s)).
 rewrite Nat2N.id. intros p [r [IN HIT]]. apply (proj1 (proj1 (proj1 DI))).
 exists r; split; [|exact HIT]. apply in_app_iff in IN.
 unfold required_ranges; repeat rewrite in_app_iff; rewrite PH; tauto.
Qed.

Definition neutral_open_boundary old image root s h a result :=
 let j := Logged (Ready (neutral_flash result)) h a in
 match neutral_end_ result with
 | NeutralSuccess => (j,OpenBoundary image root s)
 | NeutralError => (j,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) (data_next DataFreeze s))
 | NeutralReset => (logged_after_reset j,RebuildingBoundary Selecting)
 | NeutralFatal => (j,FatalBoundary)
 end.

Theorem selected_neutralization_open_boundary g sector data_len boss_ok view marker ranges decode topology pages
 recognize magic fuel lo hi f h a old image root s e result :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 neutral_run g sector recognize magic hi lo f result ->
 free_range 256 (protection_table s) (block_pages lo (hi-lo)) /\
 unchanged (required_ranges s) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 exists d,
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (neutral_open_boundary old image root s h a result) (selected_evidence old d e) /\
 (neutral_end_ result=NeutralReset ->
   episode_boot_post g sector data_len boss_ok view marker ranges decode topology pages
     (logged_after_reset (Logged (Ready (neutral_flash result)) h a)) (selected_evidence old d e)).
Proof.
 intros G DIV C L INV HEAD SEL RUN.
 destruct (neutralization_open_transport g sector data_len boss_ok view marker ranges decode pages
   recognize magic fuel lo hi f h a old image root s e result C L INV HEAD SEL RUN)
   as [FREE [KEEP [d OPEN]]].
 assert (RESET : enriched_invariant sector data_len boss_ok view marker ranges decode pages
  (logged_after_reset (Logged (Ready (neutral_flash result)) h a),RebuildingBoundary Selecting)
  (selected_evidence old d e)).
 { eapply enriched_reset; [exact G|exact DIV|exact C|exact OPEN|].
   apply record_step. apply reset_ready. }
 split; [exact FREE|]. split; [exact KEEP|]. exists d; split.
 - unfold neutral_open_boundary; destruct (neutral_end_ result).
   + exact OPEN.
   + eapply neutral_freeze_open; [exact OPEN|exact HEAD].
   + exact RESET.
   + destruct OPEN as [[JI REST] [EV LINK]]. split; [split; [exact JI|exact I]|].
     split; [exact EV|exact I].
 - intros _. eapply boot_entry_post; eauto.
Qed.
