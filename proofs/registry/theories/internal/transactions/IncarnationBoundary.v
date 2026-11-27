From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PageOwnership ScopeOwnership
 PreparedAuthority CompactImage CompactUpdates CollectionRoots JournalHistory JournalReachableShape JournalRequests
 JournalRecoveryTrace JournalScan JournalIndex TransactionBoundary PersistentBoundary DataEpisode RecycledWriter PreparationOutcomes PublicationPreparation
 AllocationAdmission BootReconstruction RawNeutralizationBoundary JournalRawOrder NeutralizationBoundary.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export BossDecodingContract DecodedGeometryContract IncarnationReaderContract.
Import ListNotations.

(* [persistent_certificate] carries address plus exact decoded BOSS content.
   This is not a unique allocation counter: equal decoded values do not prove
   identical physical incarnations. Publication positions distinguish receipts.
   The view below is an observer updated from the actual decoding,
   not a second storage state and not an identity selected independently of bytes.
   Preparation does not acquire a publication event number. *)
Definition decoded_view ranges d := Build_root_view (recovered_boss d)
 (image_dependencies ranges (recovered_image d)).
Definition install_decoded_view (view:nat->root_view) ranges id d :=
 fun address => if Nat.eq_dec address id then decoded_view ranges d else view address.
Lemma installed_view_same view ranges id d :
 install_decoded_view view ranges id d id=decoded_view ranges d.
Proof. unfold install_decoded_view; destruct Nat.eq_dec; congruence. Qed.
Lemma installed_view_other view ranges id d other : other<>id ->
 install_decoded_view view ranges id d other=view other.
Proof. intro NE; unfold install_decoded_view; destruct Nat.eq_dec; congruence. Qed.
Lemma installed_decoding_agrees view ranges id d :
 decoded_root_agrees (install_decoded_view view ranges id d) ranges id d.
Proof. unfold decoded_root_agrees; rewrite installed_view_same; split; reflexivity. Qed.

Lemma certificate_reindex sector before after ranges decode j c :
 before (certificate_id c)=after (certificate_id c) ->
 certificate_valid sector before ranges decode j c -> certificate_valid sector after ranges decode j c.
Proof. intros SAME [READ FMT]; split; [exact READ|]. unfold decoded_root_agrees in *; rewrite <-SAME; exact FMT. Qed.

Theorem evidence_reindex sector before after ranges decode j e :
 persistent_evidence sector before ranges decode j e ->
 (forall c, In c (live_certificates e) -> before (certificate_id c)=after (certificate_id c)) ->
 persistent_evidence sector after ranges decode j e.
Proof.
 intros [CERT [SELECT RECEIPTS]] SAME; split.
 - apply Forall_forall; intros c IN. eapply certificate_reindex; [apply SAME; exact IN|].
   apply (proj1 (Forall_forall _ _) CERT); exact IN.
 - split; [exact SELECT|exact RECEIPTS].
Qed.

(* Pruning has no flash/table effect. It removes obsolete logical certificates,
   never receipts. At a Ready allocation frontier only the selected authority
   is required by persistent_evidence; the table invariant protects other RAM roots. *)
Theorem retire_unselected_certificates sector view ranges decode j e old d :
 persistent_evidence sector view ranges decode j e ->
 In (Certificate old d) (live_certificates e) ->
 hd_error (publications j)=Some (N.of_nat old) ->
 persistent_evidence sector view ranges decode j (selected_evidence old d e).
Proof.
 intros [CERT [SELECT RECEIPTS]] IN HEAD; split.
 - constructor; [apply (proj1 (Forall_forall _ _) CERT); exact IN|constructor].
 - split; [|exact RECEIPTS]. intros id H.
   assert (id=old) by (apply Nat2N.inj; congruence); subst; exists (Certificate old d); simpl; auto.
Qed.

Lemma prepared_decoding_covered s p image root ranges id fresh :
 data_invariant s -> pending_preparation s=Some p ->
 image_current_correspondence ranges image root s ->
 recovered_boss fresh=prep_range p -> recovered_image fresh=image ->
 protected (needed 256 (certificate_ranges ranges (Certificate id fresh))) (protection_table s).
Proof.
 intros DI P COR BOSS IMAGE q [r [IN TOUCH]].
 apply (proj1 (proj1 (proj1 DI)) q). exists r; split; [|exact TOUCH].
 unfold certificate_ranges in IN; simpl in IN. rewrite BOSS, IMAGE in IN.
 destruct IN as [EQ|IN].
 - subst r. unfold required_ranges, pending_ranges; rewrite P; simpl.
   repeat rewrite in_app_iff; simpl; tauto.
 - assert (CUR:In r (protection_current s++attached_ranges s)).
   { rewrite COR; apply in_or_app; right; exact IN. }
   apply in_app_iff in CUR. unfold required_ranges, context_ranges, surviving_ranges, context_scopes; simpl.
   repeat rewrite in_app_iff; tauto.
Qed.

Theorem prepared_incarnation_from_reserved_writer g sector data_len valid view marker ranges decode pages
 f h a old image root s e p boss plan result id fresh validate :
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=Some p -> contains (prep_range p) id ->
 contains (boss_extent (view old)) old ->
 (forall after, unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector after) ->
   decode (object_flash sector f) old=decode (object_flash sector after) old) ->
 validator_accepts_decoded sector decode validate ->
 writer_execution g sector (prep_range p) boss f plan result ->
 decode (object_flash sector (writer_flash result)) id=Some fresh ->
 recovered_boss fresh=prep_range p -> recovered_image fresh=image ->
 exists previous,
 old<>id /\
 enriched_invariant sector data_len (validate (writer_flash result))
   (install_decoded_view view ranges id fresh) marker ranges decode pages
   (Logged (Ready (writer_flash result)) h a,OpenBoundary image root s)
   (evidence_with_live e [Certificate old previous;Certificate id fresh]) /\
 unchanged (protected_roots s) (object_flash sector f) (object_flash sector (writer_flash result)) /\
 protected (needed 256 (certificate_ranges ranges (Certificate id fresh))) (protection_table s).
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] RAW HEAD P AT OLDAT LOCAL ACCEPT RUN NEWREAD BOSS IMAGE.
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK; rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 assert (ROOTS:forall r, In r (root_extents (view old)) -> In r (protected_roots s)).
 { intros r IN; unfold protected_roots; repeat rewrite in_app_iff; rewrite PH; tauto. }
 assert (NE:old<>id).
 { intro EQ; subst id. eapply (reserved_address_not_live s p (boss_extent (view old)) old DI P);
   [apply ROOTS; unfold root_extents; simpl; auto|exact AT|exact OLDAT]. }
 destruct (proj1 (proj2 EV) old HEAD) as [[which previous] [IN ID]]; simpl in ID; subst which.
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old previous) IN) as [READ FMT].
 pose proof (pending_writer_preserves_roots _ _ _ _ _ _ _ _ DI P (proj1 (proj1 JI)) RUN) as KEEP.
 assert (OLDREAD:decode (object_flash sector (writer_flash result)) old=Some previous).
 { rewrite <-LOCAL; [exact READ|intros r x I A; exact (KEEP r x (ROOTS r I) A)]. }
 pose proof (raw_writer_prefix _ _ _ _ _ _ _ _ _ _ RAW RUN) as RAW'.
 assert (V:validate (writer_flash result) (N.of_nat old)=true) by (eapply ACCEPT; exact OLDREAD).
 pose proof (raw_ready_revalidate _ _ _ _ _ _ _ RAW' HEAD V) as NEWJI.
 exists previous; split; [exact NE|]. split.
 2: { split; [exact KEEP|eapply prepared_decoding_covered; eauto]. }
 split.
 - split; [exact NEWJI|]. split; [exact DI|]. split; [exact F|]. split; [exact COR|].
   unfold protection_history_link; simpl; rewrite HEAD; simpl; rewrite Nat2N.id.
   rewrite installed_view_other by exact NE; exact PH.
 - split; [|exact I]. split.
   + constructor.
     * split; [exact OLDREAD|]. unfold decoded_root_agrees; rewrite installed_view_other by exact NE; exact FMT.
     * constructor; [split; [exact NEWREAD|apply installed_decoding_agrees]|constructor].
   + split; [|exact (proj2 (proj2 EV))]. intros x H.
     change (hd_error h=Some (N.of_nat x)) in H.
     assert (x=old) by (apply Nat2N.inj; congruence); subst; exists (Certificate old previous); simpl; auto.
Qed.

(* Locality of one certified incarnation. It permits arbitrary other decodings
   at the same address when its bytes change. No view-indexed global format law. *)

Lemma incarnation_evidence_frame sector view ranges decode j j' e :
 persistent_evidence sector view ranges decode j e ->
 (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 publications j'=publications j ->
 (forall x,2*sector<=x -> control_image (journal_control j') x=control_image (journal_control j) x) ->
 persistent_evidence sector view ranges decode j' e.
Proof.
 intros [CERT [SELECT RECEIPTS]] LOCAL HIST FRAME; split.
 - apply Forall_forall; intros c IN.
   destruct (proj1 (Forall_forall _ _) CERT c IN) as [READ FMT]. split; [|exact FMT].
   eapply (LOCAL c IN); [exact READ|]. intros r x I AT; apply FRAME; lia.
 - rewrite HIST; split; assumption.
Qed.

Theorem certified_boot_step g sector data_len valid view marker ranges decode topology pages s s' e :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (boot_journal s,RebuildingBoundary (boot_pc s)) e ->
 (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 boot_step g sector data_len valid marker ranges decode topology pages s s' ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (boot_journal s',RebuildingBoundary (boot_pc s')) e /\
 publications (boot_journal s')=publications (boot_journal s).
Proof.
 intros G DIV [[JI BI] [EV LINK]] LOCAL STEP.
 assert (FORMAT:forall id d, hd_error (publications (boot_journal s))=Some (N.of_nat id) ->
   decode (object_flash sector (control_image (journal_control (boot_journal s)))) id=Some d ->
   decoded_root_agrees view ranges id d).
 { intros id d HEAD READ.
   destruct (proj1 (proj2 EV) id HEAD) as [c [IN ID]].
   destruct (proj1 (Forall_forall _ _) (proj1 EV) c IN) as [CR CF].
   cbn in CR. rewrite ID in CR, CF. rewrite READ in CR; inversion CR; subst; exact CF. }
 pose proof (boot_step_preserves_certified_read g sector data_len valid view marker ranges decode topology pages
   G DIV s s' BI FORMAT STEP) as NEXT.
 pose proof (boot_projection g sector data_len valid view marker ranges decode topology pages s s' BI STEP) as TRACE.
 destruct (recovery_trace_history _ _ _ _ _ _ _ TRACE) as [HIST [ACK LOG]].
 split; [|exact HIST]. split; [apply rebuilding_common; exact NEXT|]. split; [|exact I].
 eapply incarnation_evidence_frame; [exact EV|exact LOCAL|exact HIST|].
 intros; eapply logged_trace_frame_after_journal; eauto.
Qed.

Theorem certified_boot_trace g sector data_len valid view marker ranges decode topology pages s s' e :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (boot_journal s,RebuildingBoundary (boot_pc s)) e ->
 (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages) s s' ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (boot_journal s',RebuildingBoundary (boot_pc s')) e /\
 publications (boot_journal s')=publications (boot_journal s).
Proof.
 intros G DIV INV LOCAL TRACE; induction TRACE.
 - eapply certified_boot_step; eauto.
 - split; [exact INV|reflexivity].
 - destruct (IHTRACE1 INV) as [MID H1]; destruct (IHTRACE2 MID) as [LAST H2]. split; [exact LAST|congruence].
Qed.

Theorem certified_boot_selected_image g sector data_len valid view marker ranges decode topology pages s jf id d ram e c :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (boot_journal s,RebuildingBoundary (boot_pc s)) e ->
 (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 In c (live_certificates e) -> hd_error (publications (boot_journal s))=Some (N.of_nat (certificate_id c)) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
  s (jf,Usable id d ram) ->
 id=certificate_id c /\ d=certificate_decoded c /\ data_caller DataBegin ram.
Proof.
 intros G DIV INV LOCAL IN HEAD TRACE.
 destruct (certified_boot_trace g sector data_len valid view marker ranges decode topology pages s (jf,Usable id d ram) e G DIV INV LOCAL TRACE) as [FINAL HIST].
 pose proof FINAL as [[JI [J0 [REC [[READY [HD [READ FMT]]] RAM]]]] [EV LINK]].
 simpl in HIST, HD, READ. rewrite HIST, HEAD in HD.
 assert (ID:id=certificate_id c) by (apply Nat2N.inj; congruence).
 destruct (proj1 (Forall_forall _ _) (proj1 EV) c IN) as [CR CF].
 simpl in CR. rewrite ID in READ. assert (DEC:d=certificate_decoded c) by congruence.
 split; [exact ID|]. split; [exact DEC|].
 exact (proj1 (proj2 (proj2 (enriched_boot_usable sector data_len valid view marker ranges decode pages jf id d ram e FINAL)))).
Qed.

(* Operational publication witness: begin_append, physical programming and
   reset_before_ack. Completion creates an event even without append/client
   acknowledgement. The old receipt may refer to this SAME offset. *)
Theorem reincarnation_append_reset g sector data_len valid view marker ranges decode topology pages
 f after h a index id fresh receipts :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 logged_invariant sector 256 data_len valid (Logged (Ready f) h a) ->
 candidate_valid 256 data_len valid (N.of_nat id) ->
 JournalIndex.first_empty_slot (sector_bytes f 0 sector)=Some index ->
 program_step g f (8*index/256*256) (candidate_buffer 256 f index (N.of_nat id)) Success after ->
 certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate id fresh) ->
 incarnation_reader_local ranges decode (Certificate id fresh) ->
 Forall (receipt_valid view ranges h) receipts ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid)
   (Logged (Ready f) h a) (Logged (Boot after) (N.of_nat id::h) a) /\
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Boot after) (N.of_nat id::h) a,RebuildingBoundary Selecting)
   (Evidence [Certificate id fresh] receipts) /\
 (forall jf selected restored ram,
   clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
    (Logged (Boot after) (N.of_nat id::h) a,Selecting) (jf,Usable selected restored ram) ->
   selected=id /\ restored=fresh /\ data_caller DataBegin ram).
Proof.
 intros G DIV INV CAND EMPTY PROGRAM CERT LOCAL RECEIPTS.
 assert (BEGIN:logged_step g sector 256 data_len valid
  (Logged (Ready f) h a) (Logged (Writing f index (N.of_nat id)) h a)).
 { apply record_step; apply begin_append; assumption. }
 pose proof (logged_step_preserves_invariant _ _ _ _ _ G DIV _ _ INV BEGIN) as IW.
 set (history:=publication_history_after h (Writing f index (N.of_nat id)) (AwaitAck after index (N.of_nat id))).
 assert (WRITE:logged_step g sector 256 data_len valid
  (Logged (Writing f index (N.of_nat id)) h a) (Logged (AwaitAck after index (N.of_nat id)) history a)).
 { apply record_step. exact (candidate_program g sector 256 data_len valid f after index (N.of_nat id) Success PROGRAM). }
 pose proof (logged_step_preserves_invariant _ _ _ _ _ G DIV _ _ IW WRITE) as IA.
 assert (HIST:history=N.of_nat id::h).
 { unfold history, publication_history_after; simpl; unfold record_candidate.
   rewrite (await_ack_slot_completed sector 256 data_len valid after index (N.of_nat id) history a DIV IA); reflexivity. }
 rewrite HIST in WRITE, IA.
 assert (RESET:logged_step g sector 256 data_len valid
  (Logged (AwaitAck after index (N.of_nat id)) (N.of_nat id::h) a)
  (Logged (Boot after) (N.of_nat id::h) a)).
 { apply record_step; apply reset_before_ack. }
 assert (TRACE:clos_refl_trans logged_state (logged_step g sector 256 data_len valid)
  (Logged (Ready f) h a) (Logged (Boot after) (N.of_nat id::h) a)).
 { eapply rt_trans; [apply rt_step; exact BEGIN|]. eapply rt_trans; apply rt_step; eassumption. }
 assert (FINAL:logged_invariant sector 256 data_len valid (Logged (Boot after) (N.of_nat id::h) a)).
 { exact (arbitrary_finite_history_preserves_invariant g sector 256 data_len valid G DIV _ _ INV TRACE). }
 assert (CF:certificate_valid sector view ranges decode (Logged (Boot after) (N.of_nat id::h) a) (Certificate id fresh)).
 { destruct CERT as [READ FMT]; split; [|exact FMT].
   eapply LOCAL; [exact READ|]. intros r x IN AT.
   exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ (2*sector+x) G DIV INV TRACE ltac:(lia)). }
 assert (EN:enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Boot after) (N.of_nat id::h) a,RebuildingBoundary Selecting) (Evidence [Certificate id fresh] receipts)).
 { split; [split; [exact FINAL|split; [exact FINAL|split; exact I]]|]. split; [|exact I].
   split; [constructor; [exact CF|constructor]|]. split.
   - intros x HX; simpl in HX. assert (x=id) by (apply Nat2N.inj; congruence). subst; exists (Certificate id fresh); simpl; auto.
   - change (Forall (receipt_valid view ranges ([N.of_nat id]++h)) receipts).
     apply receipts_extend; exact RECEIPTS. }
 split; [exact TRACE|]. split; [exact EN|]. intros jf selected restored ram BOOT.
 exact (certified_boot_selected_image g sector data_len valid view marker ranges decode topology pages
  (Logged (Boot after) (N.of_nat id::h) a,Selecting) jf selected restored ram
  (Evidence [Certificate id fresh] receipts) (Certificate id fresh) G DIV EN
  ltac:(intros c [EQ|NO]; [subst; exact LOCAL|contradiction]) (or_introl eq_refl) eq_refl BOOT).
Qed.

Theorem reused_offset_operational_witness g sector data_len valid view marker ranges decode topology pages
 f h a old image root s e p plan written id fresh validate index published receipt :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=Some p -> contains (prep_range p) id -> contains (boss_extent (view old)) old ->
 (forall after, unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector after) ->
   decode (object_flash sector f) old=decode (object_flash sector after) old) ->
 validator_accepts_decoded sector decode validate ->
 writer_execution g sector (prep_range p) true f plan written -> writer_end written=WriterComplete ->
 decode (object_flash sector (writer_flash written)) id=Some fresh -> recovered_boss fresh=prep_range p -> recovered_image fresh=image ->
 incarnation_reader_local ranges decode (Certificate id fresh) ->
 candidate_valid 256 data_len (validate (writer_flash written)) (N.of_nat id) ->
 first_empty_slot (sector_bytes (writer_flash written) 0 sector)=Some index ->
 program_step g (writer_flash written) (8*index/256*256)
   (candidate_buffer 256 (writer_flash written) index (N.of_nat id)) Success published ->
 In receipt (client_receipts e) -> certificate_id (receipt_certificate receipt)=id ->
 image_dependencies ranges (recovered_image (certificate_decoded (receipt_certificate receipt))) <>
 image_dependencies ranges (recovered_image fresh) ->
 let next_view:=install_decoded_view view ranges id fresh in
 old<>id /\
 logged_invariant sector 256 data_len (validate (writer_flash written))
   (Logged (Ready (writer_flash written)) h a) /\
 clos_refl_trans logged_state (logged_step g sector 256 data_len (validate (writer_flash written)))
   (Logged (Ready (writer_flash written)) h a) (Logged (Boot published) (N.of_nat id::h) a) /\
 enriched_invariant sector data_len (validate (writer_flash written)) next_view marker ranges decode pages
   (Logged (Boot published) (N.of_nat id::h) a,RebuildingBoundary Selecting)
   (evidence_with_live e [Certificate id fresh]) /\
 receipt_valid next_view ranges (N.of_nat id::h) receipt /\
 (forall jf selected restored ram,
   clos_refl_trans boot_state (boot_step g sector data_len (validate (writer_flash written)) marker ranges decode topology pages)
    (Logged (Boot published) (N.of_nat id::h) a,Selecting) (jf,Usable selected restored ram) ->
   selected=id /\ restored=fresh /\ data_caller DataBegin ram).
Proof.
 intros G DIV INV RAW HEAD P AT OLDAT LOCAL ACCEPT RUN COMPLETED READ BOSS IMAGE FRESHLOCAL NUM EMPTY PROGRAM IN RID DIFFERENT next_view.
 destruct (prepared_incarnation_from_reserved_writer g sector data_len valid view marker ranges decode pages
  f h a old image root s e p true plan written id fresh validate INV RAW HEAD P AT OLDAT LOCAL ACCEPT RUN READ BOSS IMAGE)
   as [previous [NE [PRE [KEEP COVER]]]].
 pose proof PRE as [[JI CONTEXT] [EV LINK]].
 assert (CERT:certificate_valid sector next_view ranges decode (Logged (Ready (writer_flash written)) h a) (Certificate id fresh)).
 { exact (Forall_inv (Forall_inv_tail (proj1 EV))). }
 destruct (reincarnation_append_reset g sector data_len (validate (writer_flash written)) next_view marker ranges decode topology pages
   (writer_flash written) published h a index id fresh (client_receipts e)
   G DIV JI NUM EMPTY PROGRAM CERT FRESHLOCAL (proj2 (proj2 EV))) as [TRACE [FINAL BOOT]].
 split; [exact NE|]. split; [exact JI|]. split; [exact TRACE|]. split; [exact FINAL|]. split; [|exact BOOT].
 exact (proj1 (Forall_forall _ _) (proj2 (proj2 (proj1 (proj2 FINAL)))) receipt IN).
Qed.

(* Reset copies no RAM and performs no cleanup. This adapter does not need the
   old global format contract: journal_control retains the same physical bytes. *)
Theorem incarnation_reset_boundary g sector data_len valid view marker ranges decode pages j phase e :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages (j,phase) e ->
 logged_step g sector 256 data_len valid j (logged_after_reset j) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (logged_after_reset j,RebuildingBoundary Selecting) e.
Proof.
 intros G DIV [[JI REST] [EV LINK]] STEP; split.
 - apply rebuilding_common; split.
   + eapply logged_step_preserves_invariant; eauto.
   + split; [destruct j as [ctrl h a]; destruct ctrl; exact I|exact I].
 - split; [|exact I]. destruct j as [ctrl h a]; destruct ctrl; exact EV.
Qed.

(* Concrete discriminant for the former logical obstruction, supplementary to
   the operational writer/append/reset witness above. It is NOT by itself a
   complete flash execution. *)
Definition incarnation_example_entry := Build_compact_entry
 (repeat 0%N 17) (repeat 0%N 17) [0%N;0%N] [0%N;3%N;0%N;0%N].
Definition incarnation_example_ranges (_:compact_entry) := [{|offset:=768;span:=256|}].
Definition incarnation_example_old := RecoveryDecoding {|offset:=256;span:=256|} [].
Definition incarnation_example_new := RecoveryDecoding {|offset:=256;span:=256|} [Some incarnation_example_entry].
Definition incarnation_example_view := fun _ : nat => decoded_view incarnation_example_ranges incarnation_example_new.
Example historical_receipts_different_dependencies :
 receipt_valid incarnation_example_view incarnation_example_ranges [256%N;512%N;256%N]
   (Receipt 0 (Certificate 256 incarnation_example_old)) /\
 receipt_valid incarnation_example_view incarnation_example_ranges [256%N;512%N;256%N]
   (Receipt 2 (Certificate 256 incarnation_example_new)) /\
 image_dependencies incarnation_example_ranges (recovered_image incarnation_example_old) <>
 image_dependencies incarnation_example_ranges (recovered_image incarnation_example_new).
Proof.
 split; [exists [256%N;512%N], []; split; reflexivity|].
 split; [exists [], [512%N;256%N]; split; reflexivity|]. discriminate.
Qed.

(* A handoff describes the existing token and the flash at handoff. It performs
   NO reservation and does not require the now-owned pages to be free. *)
Definition reservation_handoff sector f s p :=
 pending_preparation s=Some p /\ erased_object_extent sector f (prep_range p).
Definition pending_writer_run g sector s p boss f plan result :=
 reservation_handoff sector f s p /\ writer_execution g sector (prep_range p) boss f plan result.

Theorem pending_writer_consumes g sector data_len valid view marker ranges decode pages
 f h a old previous image root s e p boss plan result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 incarnation_reader_local ranges decode (Certificate old previous) ->
 validator_accepts_decoded sector decode validate ->
 pending_writer_run g sector s p boss f plan result ->
 enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
  (writer_exit_boundary old image root s h a result) (selected_evidence old previous e) /\
 unchanged (certificate_ranges ranges (Certificate old previous)) (object_flash sector f)
   (object_flash sector (writer_flash result)) /\
 raw_order sector 256 data_len (fst (writer_exit_boundary old image root s h a result)).
Proof.
 intros G DIV INITIAL RAW HEAD IN LOCAL ACCEPT [[P BLANK] RUN].
 pose proof INITIAL as [[JI [DI [FR [COR LINK]]]] [EV CERT]].
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old previous) IN) as [READ [B O]].
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK; rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 pose proof (pending_writer_preserves_roots _ _ _ _ _ _ _ _ DI P (proj1 (proj1 JI)) RUN) as KEEP.
 assert (COVER:unchanged (certificate_ranges ranges (Certificate old previous))
    (object_flash sector f) (object_flash sector (writer_flash result))).
 { unfold certificate_ranges; simpl in B,O |- *. rewrite B,O.
   intros r x I AT; apply (KEEP r x); [|exact AT].
   unfold protected_roots; repeat rewrite in_app_iff; rewrite PH; tauto. }
 assert (NEWREAD:decode (object_flash sector (writer_flash result)) old=Some previous).
 { exact (LOCAL _ _ READ COVER). }
 pose proof (raw_writer_prefix _ _ _ _ _ _ _ _ _ _ RAW RUN) as ORDER.
 assert (NEXT:enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
   (Logged (Ready (writer_flash result)) h a,OpenBoundary image root s) (selected_evidence old previous e)).
 { split.
   - split; [eapply raw_ready_revalidate; [exact ORDER|exact HEAD|eapply ACCEPT;exact NEWREAD]|].
     simpl; auto.
   - split; [|exact I]. split.
     + constructor; [split; [exact NEWREAD|split;assumption]|constructor].
     + split; [|exact (proj2 (proj2 EV))]. intros id H.
       change (hd_error h=Some (N.of_nat id)) in H.
       assert (id=old) by (apply Nat2N.inj; congruence); subst; exists (Certificate old previous); simpl; auto. }
 split; [eapply writer_exit_phase; eauto|]. split; [exact COVER|].
 unfold writer_exit_boundary; destruct (writer_end result); exact ORDER.
Qed.

From OxideSE.Registry Require Import RecyclingErase RecyclingEraseBoundary RecyclingSearch Neutralization.
(* Kind is determined by the allocation caller, before writing. These are
   the existing DataReserve/snapshot_reserve updates, with the SAME table. *)
Definition reservation_state (boss:bool) r s :=
 if boss then snapshot_reserve r s else data_next (DataReserve r) s.
Definition reservation_token (boss:bool) r :=
 Build_preparation (if boss then BossPreparation else ObjectPreparation) r Reserved.
Lemma reservation_state_open sector data_len valid view marker ranges decode pages j image root s e r boss :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,OpenBoundary image root s) e ->
 pending_preparation s=None -> free_range 256 (protection_table s) r ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root (reservation_state boss r s)) e.
Proof.
 intros INV P FREE; destruct boss; [|eapply recycling_reserve_open;eauto].
 destruct INV as [[JI [DI [FR [COR LINK]]]] [EV CERT]].
 split;[|split;[exact EV|exact I]]. split;[exact JI|].
 split;[apply snapshot_reserve_preserves;assumption|]. split;[reflexivity|]. split;assumption.
Qed.
Definition recycling_acquisition_boundary old image root s h a result r boss :=
 match neutral_end_ result with
 | NeutralSuccess => (Logged (Ready (neutral_flash result)) h a,
     OpenBoundary image root (reservation_state boss r s))
 | _ => neutral_open_boundary old image root s h a result
 end.

Theorem recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
 f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) -> incarnation_reader_local ranges decode (Certificate old previous) ->
 recognizer_local sector recognize -> validator_accepts_decoded sector decode validate -> pending_preparation s=None ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 let span:=block_pages (recycle_lo r) (useful_pages r) in
 enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (recycling_acquisition_boundary old image root s h a result span boss) (selected_evidence old previous e) /\
 unchanged (certificate_ranges ranges (Certificate old previous)) (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 raw_order sector 256 data_len (fst (recycling_acquisition_boundary old image root s h a result span boss)) /\
 (neutral_end_ result=NeutralSuccess ->
  reservation_handoff sector (neutral_flash result) (reservation_state boss span s)
    (reservation_token boss span)).
Proof.
 intros G DIV INITIAL RAW HEAD IN LOCAL RECOGNIZE ACCEPT P SEARCH GEO RUN span.
 pose proof INITIAL as [[JI [DI [FR [COR LINK]]]] [EV CERT]].
 destruct (recycling_physical_handoff g sector fuel recognize magic f (protection_table s) req round alignment pages start
   r count result (required_ranges s) RECOGNIZE (proj1 (proj1 JI)) (proj1 (proj1 (proj1 DI))) SEARCH GEO RUN)
   as [VALID [KEEP [FRAME DONE]]].
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old previous) IN) as [READ [B O]].
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK;rewrite HEAD in LINK;simpl in LINK;rewrite Nat2N.id in LINK;exact LINK. }
 assert (BYTES:unchanged (certificate_ranges ranges (Certificate old previous))
   (object_flash sector f) (object_flash sector (neutral_flash result))).
 { unfold certificate_ranges;simpl in B,O |- *;rewrite B,O.
   intros ext addr I AT;apply (KEEP ext addr);[|exact AT].
   unfold required_ranges;repeat rewrite in_app_iff;rewrite PH;tauto. }
 assert (NEWREAD:decode (object_flash sector (neutral_flash result)) old=Some previous) by (exact (LOCAL _ _ READ BYTES)).
 assert (ORDER:raw_order sector 256 data_len (Logged (Ready (neutral_flash result)) h a)).
 { exact (neutral_ready_frame sector data_len (fun _=>true) _ _ _ _ RAW VALID FRAME). }
 assert (OPEN:enriched_invariant sector data_len (validate (neutral_flash result)) view marker ranges decode pages
   (Logged (Ready (neutral_flash result)) h a,OpenBoundary image root s) (selected_evidence old previous e)).
 { split.
   - split;[eapply raw_ready_revalidate;[exact ORDER|exact HEAD|eapply ACCEPT;exact NEWREAD]|]. simpl;auto.
   - split;[|exact I]. split.
     + constructor;[split;[exact NEWREAD|split;assumption]|constructor].
     + split;[|exact (proj2 (proj2 EV))]. intros id H.
       change (hd_error h=Some (N.of_nat id)) in H.
       assert (id=old) by (apply Nat2N.inj;congruence);subst;exists (Certificate old previous);simpl;auto. }
 split.
 - unfold recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result) eqn:END.
   + apply reservation_state_open;[exact OPEN|exact P|exact (proj1 (DONE eq_refl))].
   + eapply neutral_freeze_open;[exact OPEN|exact HEAD].
   + eapply incarnation_reset_boundary;[exact G|exact DIV|exact OPEN|]. apply record_step;apply reset_ready.
   + split;[split;[exact (proj1 (proj1 OPEN))|exact I]|split;[exact (proj1 (proj2 OPEN))|exact I]].
 - split;[exact BYTES|]. split.
   + unfold recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result);exact ORDER.
   + intros END;split;[destruct boss;reflexivity|exact (proj2 (DONE END))].
Qed.

(* Installation consumes the Written BOSS token. It changes no flash/history.
   The empty current-root list is produced by exact Data attachment. *)
Theorem install_completed_candidate sector data_len valid view marker ranges decode pages
 j image s e p id d :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image [] s) e ->
 pending_preparation s=Some p -> prep_kind p=BossPreparation ->
 (prep_phase p=Written \/ prep_phase p=Detached) ->
 In (Certificate id d) (live_certificates e) ->
 recovered_boss d=prep_range p -> recovered_image d=image ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,PublishingBoundary CandidatePrepared id d (install_candidate s)) e.
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] P KIND PHASE IN BOSS IMAGE.
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate id d) IN) as [READ FMT].
 pose proof (install_candidate_completed_preserves s p DI F P KIND PHASE) as NEXT.
 split;[|split;[exact EV|exact IN]]. split;[exact JI|].
 split;[exact (proj1 NEXT)|]. unfold install_candidate;rewrite P.
 unfold data_next;rewrite P.
 split;[reflexivity|]. split;[reflexivity|]. split;[exact FMT|]. split.
 - unfold image_current_correspondence in COR |- *; simpl in COR.
   simpl. rewrite app_nil_r, BOSS, IMAGE, COR;reflexivity.
 - split;[exact LINK|]. unfold install_candidate in NEXT;rewrite P in NEXT.
   unfold data_next in NEXT;rewrite P in NEXT;exact NEXT.
Qed.

Theorem install_certified_candidate sector data_len valid view marker ranges decode pages
 j image s e p id d :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image [] s) e ->
 pending_preparation s=Some p -> prep_kind p=BossPreparation -> prep_phase p=Written ->
 In (Certificate id d) (live_certificates e) ->
 recovered_boss d=prep_range p -> recovered_image d=image ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,PublishingBoundary CandidatePrepared id d (install_candidate s)) e.
Proof. intros; eapply install_completed_candidate; eauto. Qed.

(* The setter observation survives the caller's root assignment. Detached
   still contributes pending_ranges until that assignment consumes it. *)
Definition install_candidate_observed s :=
 image_generation_observe (protection_image_generation s) (install_candidate s).

(* usize -> u32 truncation, then the build's u32 addition, then NonZeroU32.
   None is arithmetic panic; Some None is Address::new's InvalidData.
   The configuration condition is about the mapped base, not root safety. *)
Definition rust_absolute_address (checked:bool) (base:N) (relative:nat) : option (option N) :=
 let mapped := (base mod 4294967296)%N in (* persistence_area().start as u32 *)
 let off := (N.of_nat relative mod 4294967296)%N in
 let sum := (mapped + off)%N in
 if andb checked (4294967296 <=? sum)%N then None
 else let raw := (sum mod 4294967296)%N in
      Some (if N.eqb raw 0 then None else Some raw).
Definition mapped_registry_base (base:N) :=
 (0 < base /\ base + 262144 < 4294967296)%N.

Lemma rust_absolute_address_success checked base relative :
 mapped_registry_base base -> relative<=262144 ->
 rust_absolute_address checked base relative=Some (Some (base+N.of_nat relative)%N) /\
 ((base+N.of_nat relative)-base=N.of_nat relative)%N.
Proof.
 intros [POS TOP] BOUND.
 assert (B:(N.of_nat relative<=262144)%N).
 { change (N.of_nat relative<=N.of_nat 262144)%N;lia. }
 assert (OFF:(N.of_nat relative<4294967296)%N) by lia.
 assert (SUM:(base+N.of_nat relative<4294967296)%N) by lia.
 assert (BASE:(base<4294967296)%N) by lia.
 unfold rust_absolute_address;rewrite (N.mod_small base 4294967296 BASE).
 rewrite N.mod_small by exact OFF.
 assert (CHECK:(4294967296 <=? base+N.of_nat relative)%N=false)
   by (apply N.leb_gt;exact SUM).
 rewrite CHECK;destruct checked;cbn [andb];rewrite N.mod_small by exact SUM;
 assert (NZ:(base+N.of_nat relative=?0)%N=false) by (apply N.eqb_neq;lia);
 rewrite NZ;split;try reflexivity;lia.
Qed.

Lemma test_registry_base_mapped : mapped_registry_base 268435456%N.
Proof. unfold mapped_registry_base;split;reflexivity. Qed.
Lemma pico_registry_base_mapped : mapped_registry_base 270270464%N.
Proof. unfold mapped_registry_base;split;reflexivity. Qed.
Lemma pico2_registry_base_mapped : mapped_registry_base 272367616%N.
Proof. unfold mapped_registry_base;split;reflexivity. Qed.

Lemma detached_installation_transfer s p : pending_preparation s=Some p ->
 pending_preparation (install_candidate_observed s)=None /\
 In (prep_range p) (protection_current (install_candidate_observed s)) /\
 protection_table (install_candidate_observed s)=protection_table s /\
 protection_image_generation (install_candidate_observed s)=protection_image_generation s.
Proof.
 intro P;unfold install_candidate_observed,install_candidate;rewrite P.
 unfold data_next;rewrite P;cbn;repeat split;auto.
Qed.


Lemma reserved_decoded_candidate_distinct sector data_len valid view marker ranges decode pages
 f h a old previous image s e p id fresh :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image [] s) e ->
 hd_error h=Some (N.of_nat old) -> In (Certificate old previous) (live_certificates e) ->
 decoding_address_contract decode -> pending_preparation s=Some p ->
 decode (object_flash sector f) id=Some fresh -> recovered_boss fresh=prep_range p ->
 id<>old.
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] HEAD LIVE ADDRESS P READ BOSS EQ;subst id.
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old previous) LIVE) as [OLDREAD FMT].
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK;simpl in LINK;rewrite HEAD in LINK;
   simpl in LINK;rewrite Nat2N.id in LINK;exact LINK. }
 eapply (reserved_address_not_live s p (boss_extent (view old)) old DI P).
 - unfold protected_roots;repeat rewrite in_app_iff;rewrite PH.
   assert (IN:In (boss_extent (view old)) (root_extents (view old)))
     by (unfold root_extents;simpl;auto). tauto.
 - rewrite <-BOSS;eapply ADDRESS;exact READ.
 - destruct FMT as [BF IF];cbn in BF;rewrite <-BF;eapply ADDRESS;exact OLDREAD.
Qed.

Theorem install_detached_decoded sector data_len valid view marker ranges decode pages
 f h a old previous image s e p id fresh :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image [] s) e ->
 hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 decoding_address_contract decode ->
 pending_preparation s=Some p -> prep_kind p=BossPreparation -> prep_phase p=Detached ->
 decode (object_flash sector f) id=Some fresh ->
 recovered_boss fresh=prep_range p -> recovered_image fresh=image ->
 enriched_invariant sector data_len valid (install_decoded_view view ranges id fresh)
   marker ranges decode pages
   (Logged (Ready f) h a,PublishingBoundary CandidatePrepared id fresh
      (install_candidate_observed s))
   (evidence_with_live e [Certificate old previous;Certificate id fresh]).
Proof.
 intros SOURCE HEAD LIVE ADDRESS P KIND PHASE READ BOSS IMAGE.
 pose proof SOURCE as [[JI [DI [F [COR LINK]]]] [EV CERT]].
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old previous) LIVE) as [OLDREAD FMT].
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK;rewrite HEAD in LINK;
   simpl in LINK;rewrite Nat2N.id in LINK;exact LINK. }
 assert (NE:old<>id).
 { intro EQ;subst id.
   eapply (reserved_address_not_live s p (boss_extent (view old)) old DI P).
   - unfold protected_roots;repeat rewrite in_app_iff;rewrite PH.
     assert (IN:In (boss_extent (view old)) (root_extents (view old)))
       by (unfold root_extents;simpl;auto). tauto.
   - rewrite <-BOSS;eapply ADDRESS;exact READ.
   - destruct FMT as [BF IF];cbn in BF;rewrite <-BF;eapply ADDRESS;exact OLDREAD. }
 assert (REINDEX:enriched_invariant sector data_len valid
   (install_decoded_view view ranges id fresh) marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image [] s)
   (evidence_with_live e [Certificate old previous;Certificate id fresh])).
 { split.
   - split;[exact JI|]. split;[exact DI|]. split;[exact F|]. split;[exact COR|].
     unfold protection_history_link;simpl;rewrite HEAD;simpl;rewrite Nat2N.id.
     rewrite installed_view_other by exact NE;exact PH.
   - split;[|exact I]. split.
     + constructor.
       * split;[exact OLDREAD|]. unfold decoded_root_agrees;
         rewrite installed_view_other by exact NE;exact FMT.
       * constructor;[split;[exact READ|apply installed_decoding_agrees]|constructor].
     + split;[|exact (proj2 (proj2 EV))]. intros x HX.
       change (hd_error h=Some (N.of_nat x)) in HX.
       assert (x=old) by (apply Nat2N.inj;congruence);subst.
       exists (Certificate old previous);simpl;auto. }
 pose proof (install_completed_candidate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   REINDEX P KIND (or_intror PHASE) ltac:(simpl;auto) BOSS IMAGE) as INSTALLED.
 exact INSTALLED.
Qed.

(* Local certificate transport across the actual journal trace. Unlike the
   historical format contract this does not freeze all incarnations at offsets. *)
Theorem certified_journal_transport g sector data_len valid view ranges decode j next e candidate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 logged_invariant sector 256 data_len valid j ->
 persistent_evidence sector view ranges decode j e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 (exists c,In c (live_certificates e) /\ N.of_nat (certificate_id c)=candidate) ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid) j next ->
 (hd_error (publications next)=hd_error (publications j) \/ hd_error (publications next)=Some candidate) ->
 logged_invariant sector 256 data_len valid next /\ persistent_evidence sector view ranges decode next e.
Proof.
 intros G DIV J EV LOCAL C TRACE CHOICE.
 assert (FRAME:forall x,2*sector<=x -> control_image (journal_control next) x=control_image (journal_control j) x).
 { intros; eapply logged_trace_frame_after_journal;eauto. }
 destruct (logged_history_extension _ _ _ _ _ _ _ TRACE) as [prefix EXT].
 split;[eapply arbitrary_finite_history_preserves_invariant;eauto|]. split.
 - apply Forall_forall;intros c IN.
   destruct (proj1 (Forall_forall _ _) (proj1 EV) c IN) as [READ FMT].
   split;[|exact FMT]. eapply (LOCAL c IN);[exact READ|]. intros r x I AT;apply FRAME;lia.
 - split.
   + intros id H;destruct CHOICE as [SAME|NEW].
     * apply (proj1 (proj2 EV) id);congruence.
     * destruct C as [c [IN ID]]. exists c;split;[exact IN|]. apply Nat2N.inj;congruence.
   + rewrite EXT;apply receipts_extend;exact (proj2 (proj2 EV)).
Qed.

Theorem certified_uncertain_cleanup g sector data_len valid view marker ranges decode pages
 id d s j error_j commands e old :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 hd_error (publications j)=Some old ->
 clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) j error_j ->
 data_calls commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (error_j,FrozenBoundary old (N.of_nat id) None
     (execute_data commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s))) e.
Proof.
 intros G DIV [[JI [PI [F [P [FORMAT [COR [LINK DI]]]]]]] [EV IN]] LOCAL HEAD TRACE CALL.
 assert (CUR:protection_current s++attached_ranges s=root_extents (view id)).
 { unfold image_current_correspondence in COR;destruct FORMAT as [B E];rewrite B,E in COR;exact COR. }
 destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ TRACE) as [CHOICE [ACK LOG]].
 split.
 - eapply frozen_cleanup_common;eauto. rewrite Nat2N.id;exact CUR.
 - split;[|exact I]. eapply (proj2 (certified_journal_transport g sector data_len valid view ranges decode
     j error_j e (N.of_nat id) G DIV JI EV LOCAL
       (ex_intro _ (Certificate id d) (conj IN eq_refl)) LOG CHOICE)).
Qed.

Theorem certified_publication_reset g sector data_len valid view marker ranges decode pages
 ready cut id d s e :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 publication_reset_prefix g sector data_len valid (N.of_nat id) ready cut ->
 enriched_invariant sector data_len valid view marker ranges decode pages (cut,RebuildingBoundary Selecting) e.
Proof.
 intros G DIV [[JI CORE] [EV IN]] LOCAL [before [PREFIX [BEFORE [STEP DEST]]]].
 destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX) as [H1 [A1 LOG]].
 destruct (cut_step_heads _ _ _ _ _ _ _ BEFORE STEP DEST) as [H2 A2].
 assert (CHOICE:hd_error (publications cut)=hd_error (publications ready) \/ hd_error (publications cut)=Some (N.of_nat id)).
 { destruct H1,H2;[left|right|right|right];congruence. }
 assert (TRACE:clos_refl_trans logged_state (logged_step g sector 256 data_len valid) ready cut).
 { eapply rt_trans;[exact LOG|apply rt_step;exact STEP]. }
 destruct (certified_journal_transport g sector data_len valid view ranges decode ready cut e (N.of_nat id)
   G DIV JI EV LOCAL (ex_intro _ (Certificate id d) (conj IN eq_refl)) TRACE CHOICE) as [JC EC].
 split;[|split;[exact EC|exact I]]. apply rebuilding_common.
 split;[exact JC|]. split;[apply reset_destination_recovers;exact DEST|exact I].
Qed.

(* External rollback facts are produced at DataBegin and transported by the
   operational episode trace. They do not constrain a newly allocated range. *)
Definition rollback_structure marker s :=
 protection_saved s=[physical_authority s] /\
 protection_base s=marker::physical_authority s /\
 acknowledged_authority s=physical_authority s.
Definition normal_external_rollback s :=
 data_next (DataClose [] (physical_authority s) false) s.

Theorem certified_normal_rollback sector data_len valid view marker ranges decode pages
 f h a image root s e old d resolved :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 rollback_structure marker s -> pending_preparation s=None ->
 hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
 (forall mask, resolved=Some mask ->
    mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)) e.
Proof.
 intros [[JI [DI [NF [COR LINK]]]] [EV CERT]] [STACK [BASE ACK]] P HEAD IN MASK.
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK;simpl in LINK;rewrite HEAD in LINK;simpl in LINK.
   rewrite Nat2N.id in LINK;exact LINK. }
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old d) IN) as [READ FMT].
 assert (CALL:data_caller (DataClose [] (physical_authority s) false) s).
 { split;assumption. }
 assert (RI:data_invariant (normal_external_rollback s)).
 { apply data_command_preserves;assumption. }
 assert (BOUND:collection_boundary view marker (Some old) (Some old)
   (object_extents (view old)) [] (normal_external_rollback s)).
 { unfold collection_boundary,current_agrees,normal_external_rollback;simpl.
   rewrite app_nil_r,BASE,ACK,PH;repeat split;auto;intros;congruence. }
 pose proof (idle_collection_restores_data true view marker (Some old) (Some old)
   (object_extents (view old)) (normal_external_rollback s) resolved RI eq_refl eq_refl BOUND MASK) as CI.
 assert (NORMAL:forall final,
   final=collection_return 256 true (Some old) (Some old) resolved (normal_external_rollback s) ->
   enriched_invariant sector data_len valid view marker ranges decode pages
    (Logged (Ready f) h a,IdleBoundary old d final) e).
 { intros final EQ;subst final. split;[apply journal_idle_common;[|exact FMT]|split;[exact EV|exact IN]].
   assert (SH:forall final,
     final=collection_return 256 true (Some old) (Some old) resolved (normal_external_rollback s) ->
     idle_root view marker old final).
   { intros final EQ;subst final. unfold idle_root;split;[exact CI|].
     unfold collection_return;destruct collection_enabled;[destruct resolved|];
       unfold normal_external_rollback;simpl;rewrite ?app_nil_r,?BASE,?ACK,?PH,?NF;
       repeat split;reflexivity. }
   split;[apply SH;reflexivity|]. split;[exact JI|]. split;[exists f;reflexivity|].
   split;[exact HEAD|]. unfold protection_history_link;simpl;rewrite HEAD;simpl;rewrite Nat2N.id.
   unfold collection_return;destruct collection_enabled;[destruct resolved|];exact PH. }
 unfold failure_phase.
 destruct (collection_enabled true (Some old) (Some old) (normal_external_rollback s)) eqn:ENABLE.
 - destruct resolved as [mask|].
   + unfold preparation_collection;rewrite ENABLE.
     change (protection_frozen s) with (protection_frozen s);simpl.
     rewrite NF. apply NORMAL. unfold collection_return;rewrite ENABLE;reflexivity.
   + split;[split;[exact JI|exact I]|split;[exact EV|exact I]].
 - change (protection_frozen (normal_external_rollback s)) with (protection_frozen s).
   rewrite NF. apply NORMAL. unfold collection_return;rewrite ENABLE;reflexivity.
Qed.


(* Clean close retains scopes without a journal command or a fictitious receipt. *)
Definition clean_external_close s :=
 data_next (DataClose [] (physical_authority s) true) s.

Theorem certified_clean_retained sector data_len valid view marker ranges decode pages
 f h a s e old d resolved :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] s) e ->
 rollback_structure marker s -> pending_preparation s=None ->
 hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
 (forall mask, resolved=Some mask ->
    mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,failure_phase old d resolved (clean_external_close s)) e.
Proof.
 intros [[JI [DI [NF [COR LINK]]]] [EV CERT]] [STACK [BASE ACK]] P HEAD IN MASK.
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK;simpl in LINK;rewrite HEAD in LINK;simpl in LINK.
   rewrite Nat2N.id in LINK;exact LINK. }
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old d) IN) as [READ FMT].
 assert (CUR:protection_current s++attached_ranges s=root_extents (view old)).
 { unfold image_current_correspondence in COR;cbn in COR.
   destruct FMT as [B O];cbn in B,O. unfold root_extents;rewrite <- B,<- O;exact COR. }
 assert (CALL:data_caller (DataClose [] (physical_authority s) true) s).
 { split;assumption. }
 assert (RI:data_invariant (clean_external_close s)).
 { apply data_command_preserves;assumption. }
 assert (BOUND:collection_boundary view marker (Some old) (Some old)
   (object_extents (view old)) [] (clean_external_close s)).
 { unfold collection_boundary,current_agrees,clean_external_close;simpl.
   rewrite CUR,BASE,ACK,PH;repeat split;auto;intros;congruence. }
 pose proof (idle_collection_restores_data true view marker (Some old) (Some old)
   (object_extents (view old)) (clean_external_close s) resolved RI eq_refl eq_refl BOUND MASK) as CI.
 assert (NORMAL:forall final,
   final=collection_return 256 true (Some old) (Some old) resolved (clean_external_close s) ->
   enriched_invariant sector data_len valid view marker ranges decode pages
    (Logged (Ready f) h a,IdleBoundary old d final) e).
 { intros final EQ;subst final. split;[apply journal_idle_common;[|exact FMT]|split;[exact EV|exact IN]].
   assert (SH:forall final,
     final=collection_return 256 true (Some old) (Some old) resolved (clean_external_close s) ->
     idle_root view marker old final).
   { intros final EQ;subst final. unfold idle_root;split;[exact CI|].
     unfold collection_return;destruct collection_enabled;[destruct resolved|];
       unfold clean_external_close;simpl;rewrite ?CUR,?BASE,?ACK,?PH,?NF;
       repeat split;reflexivity. }
   split;[apply SH;reflexivity|]. split;[exact JI|]. split;[exists f;reflexivity|].
   split;[exact HEAD|]. unfold protection_history_link;simpl;rewrite HEAD;simpl;rewrite Nat2N.id.
   unfold collection_return;destruct collection_enabled;[destruct resolved|];exact PH. }
 unfold failure_phase.
 destruct (collection_enabled true (Some old) (Some old) (clean_external_close s)) eqn:ENABLE.
 - destruct resolved as [mask|].
   + unfold preparation_collection;rewrite ENABLE.
     change (protection_frozen s) with (protection_frozen s);simpl.
     rewrite NF. apply NORMAL. unfold collection_return;rewrite ENABLE;reflexivity.
   + split;[split;[exact JI|exact I]|split;[exact EV|exact I]].
 - change (protection_frozen (clean_external_close s)) with (protection_frozen s).
   rewrite NF. apply NORMAL. unfold collection_return;rewrite ENABLE;reflexivity.
Qed.

Theorem certified_drop_pending sector data_len valid view marker ranges decode pages
 j image root s e p :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,OpenBoundary image root s) e ->
 pending_preparation s=Some p ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root (data_next DataDrop s)) e.
Proof.
 intros [[JI [DI [NF [COR LINK]]]] [EV CERT]] P.
 pose proof (snapshot_error_preserves s p false DI P) as [NEXT [S [C A]]].
 split;[|split;[exact EV|exact I]]. split;[exact JI|]. split;[exact NEXT|].
 split;[unfold data_next;exact NF|]. split.
 - unfold image_current_correspondence in *;unfold snapshot_error in C,A;rewrite C,A;exact COR.
 - unfold protection_history_link,data_next in *;exact LINK.
Qed.

Lemma normal_rollback_phase old d resolved s :
 protection_frozen s=false ->
 failure_phase old d resolved (normal_external_rollback s)=
 if collection_enabled true (Some old) (Some old) (normal_external_rollback s)
 then match resolved with
      | Some mask => IdleBoundary old d (install_collection 256 mask (normal_external_rollback s))
      | None => FatalBoundary end
 else IdleBoundary old d (normal_external_rollback s).
Proof.
 intro NF;unfold failure_phase.
 destruct collection_enabled eqn:E;[destruct resolved|].
 - unfold preparation_collection;rewrite E;simpl;rewrite NF;reflexivity.
 - reflexivity.
 - simpl;rewrite NF;reflexivity.
Qed.

Theorem certified_prepared_rollback sector data_len valid view marker ranges decode pages
 f h a id candidate s e old previous resolved :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s) e ->
 rollback_structure marker s -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)) e.
Proof.
 intros [[JI [PI [NF [P [FMT [COR [LINK DI]]]]]]] [EV CERT]] CTX HEAD IN MASK.
 eapply certified_normal_rollback;try eassumption.
 split;[split;[exact JI|split;[exact DI|split;[exact NF|split;[exact COR|exact LINK]]]]|].
 split;[exact EV|exact I].
Qed.

Theorem normal_rollback_callers view marker old s :
 rollback_structure marker s -> pending_preparation s=None ->
 physical_authority s=root_extents (view old) ->
 data_caller (DataClose [] (physical_authority s) false) s /\
 collection_boundary view marker (Some old) (Some old) (object_extents (view old)) []
   (normal_external_rollback s).
Proof.
 intros [STACK [BASE ACK]] P PH;split;[split;assumption|].
 unfold collection_boundary,current_agrees,normal_external_rollback;simpl.
 rewrite app_nil_r,BASE,ACK,PH;repeat split;auto;intros;congruence.
Qed.

(* pages.rs::reserve: two read-only checks precede the first table write.
   The initialized 256-byte geometry and usize bounds are local admission
   inputs, not a claim about preservation by a failing physical operation. *)
Definition ram_reservation_check (initialized:bool) word_max r s :=
 if initialized then
   if Nat.leb (offset r+span r) word_max then
     if Nat.leb (AllocationAdmission.page_limit r) 1024 then
       if AllocationAdmission.vacantb (protection_table s) r then None else Some PageOccupied
     else Some TableCapacity
   else Some RangeOverflow
 else Some TableUninitialized.
Definition checked_reservation initialized word_max boss r s :=
 match ram_reservation_check initialized word_max r s with
 | Some err => (Some err,s)
 | None => (None,reservation_state boss r s)
 end.
Theorem checked_reservation_error_unchanged initialized word_max boss r s err :
 ram_reservation_check initialized word_max r s=Some err ->
 checked_reservation initialized word_max boss r s=(Some err,s).
Proof. intro E;unfold checked_reservation;rewrite E;reflexivity. Qed.
Theorem free_admitted_reservation_cannot_fail word_max r s :
 offset r+span r<=word_max -> AllocationAdmission.page_limit r<=1024 ->
 free_range 256 (protection_table s) r -> ram_reservation_check true word_max r s=None.
Proof.
 intros B C F;unfold ram_reservation_check.
 apply AllocationAdmission.vacantb_spec in F;rewrite F.
 apply Nat.leb_le in B,C;rewrite B,C;reflexivity.
Qed.

(* Checked RAM services; no flash effects. All fallible checks precede writes.
   The flag/word limit are concrete-metadata observations, not safety oracles. *)
Definition checked_release initialized word_max r t :=
 match range_check initialized word_max r with
 | Some err=>(Some err,t)
 | None=>(None,release_extent 256 r t)
 end.
Definition rehome_extent r depth (t:page_table) := fun p =>
 if touches 256 r p then Build_page_cell (S depth) (validated (t p)) else t p.
Definition checked_rehome initialized word_max r depth t :=
 if 6 <? depth then (Some TableCapacity,t) else
 match range_check initialized word_max r with
 | Some err=>(Some err,t)
 | None=>(None,rehome_extent r depth t)
 end.
Lemma range_check_from_reservation initialized word_max r s :
 ram_reservation_check initialized word_max r s=None -> range_check initialized word_max r=None.
Proof.
 unfold ram_reservation_check,range_check.
 destruct initialized;[|discriminate].
 destruct (offset r+span r <=? word_max);[|discriminate].
 destruct (AllocationAdmission.page_limit r <=? 1024);[reflexivity|discriminate].
Qed.
Lemma checked_release_failure initialized word_max r t err t' :
 checked_release initialized word_max r t=(Some err,t') -> t'=t.
Proof. unfold checked_release;destruct range_check;intros E;inversion E;reflexivity. Qed.
Lemma checked_rehome_failure initialized word_max r depth t err t' :
 checked_rehome initialized word_max r depth t=(Some err,t') -> t'=t.
Proof.
 unfold checked_rehome;destruct (6 <? depth);[|destruct range_check];intros E;inversion E;reflexivity.
Qed.
Lemma checked_release_after_reservation initialized word_max r source current :
 ram_reservation_check initialized word_max r source=None ->
 checked_release initialized word_max r current=(None,release_extent 256 r current).
Proof. intro CHECK;unfold checked_release;rewrite (range_check_from_reservation _ _ _ _ CHECK);reflexivity. Qed.
Lemma checked_rehome_after_reservation initialized word_max r source current roots :
 ram_reservation_check initialized word_max r source=None -> length roots<=6 ->
 checked_rehome initialized word_max r (DeferredSnapshots.snapshot_owner roots) current=
 (None,rehome_extent r (DeferredSnapshots.snapshot_owner roots) current).
Proof.
 intros CHECK DEPTH;unfold checked_rehome.
 assert (B:(6 <? DeferredSnapshots.snapshot_owner roots)=false).
 { apply Nat.ltb_ge;unfold DeferredSnapshots.snapshot_owner;pose proof (Nat.le_min_r (DeferredSnapshots.first_unresolved roots) (length roots));lia. }
 rewrite B,(range_check_from_reservation _ _ _ _ CHECK);reflexivity.
Qed.
Lemma rehome_extent_keeps_protection required r depth t :
 protected required t -> protected required (rehome_extent r depth t).
Proof. intros COVER p NEED;unfold rehome_extent;destruct touches;simpl;[lia|apply COVER;exact NEED]. Qed.

Lemma completed_writer_retain_error g sector r f plan result :
 writer_execution g sector r true f plan result -> writer_end result=WriterComplete ->
 writer_execution g sector r true f plan
   (WriterObservation (writer_flash result) (writer_prefix result) WriterRetainError).
Proof.
 intros RUN;induction RUN;intro DONE;simpl in DONE;try discriminate.
 - apply writer_retain_error;reflexivity.
 - exact (writer_successful_command g sector r true f c tail after
     (WriterObservation (writer_flash result) (writer_prefix result) WriterRetainError) H H0 (IHRUN DONE)).
Qed.
Lemma checked_release_matches_drop initialized word_max source s p :
 ram_reservation_check initialized word_max (prep_range p) source=None ->
 pending_preparation s=Some p -> protection_frozen s=false ->
 checked_release initialized word_max (prep_range p) (protection_table s)=
   (None,protection_table (data_next DataDrop s)).
Proof.
 intros CHECK P F;rewrite (checked_release_after_reservation _ _ _ _ _ CHECK).
 unfold data_next;simpl;rewrite F,P;reflexivity.
Qed.

(* OperationScope uses the existing stack and ownership table. These are real
   begin/close updates, not a renumbering of an externally stored table. *)
Theorem certified_local_begin sector data_len valid view marker ranges decode pages
 j image root s e saved :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root s) e ->
 protection_saved s=[saved] -> pending_preparation s=None ->
 data_caller DataBegin s /\
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root (data_next DataBegin s)) e /\
 protection_saved (data_next DataBegin s)=[saved;protection_current s++attached_ranges s].
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] STACK P.
 assert (CALL:data_caller DataBegin s) by (simpl;rewrite F,P,STACK;simpl;repeat split;auto;lia).
 split;[exact CALL|]. split;[|simpl;rewrite STACK;reflexivity].
 split;[|split;[exact EV|exact I]]. split;[exact JI|].
 split;[apply data_command_preserves;assumption|]. split;[reflexivity|]. split.
 - unfold image_current_correspondence in *;simpl;rewrite app_nil_r;exact COR.
 - apply local_data_keeps_history_link;exact LINK.
Qed.

Theorem certified_local_accept sector data_len valid view marker ranges decode pages
 j image root s e saved :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root s) e ->
 protection_saved s=[saved;saved] -> pending_preparation s=None ->
 data_caller (DataClose [saved] saved true) s /\
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary image root (data_next (DataClose [saved] saved true) s)) e.
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] STACK P.
 assert (CALL:data_caller (DataClose [saved] saved true) s) by (simpl;auto).
 split;[exact CALL|]. split;[|split;[exact EV|exact I]]. split;[exact JI|].
 split;[apply data_command_preserves;assumption|]. split;[exact F|]. split.
 - exact COR.
 - apply local_data_keeps_history_link;exact LINK.
Qed.

Lemma local_accept_skips_collection current durable s saved :
 collection_enabled true current durable (data_next (DataClose [saved] saved true) s)=false.
Proof. unfold collection_enabled;simpl;reflexivity. Qed.
Lemma local_accept_retains_outer s saved :
 protection_saved (data_next (DataClose [saved] saved true) s)=[saved].
Proof. reflexivity. Qed.

Theorem certified_written_member g sector data_len valid view marker ranges decode pages
 f h a old previous image root s e r index entry plan result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 In (Certificate old previous) (live_certificates e) ->
 incarnation_reader_local ranges decode (Certificate old previous) -> validator_accepts_decoded sector decode validate ->
 pending_preparation s=None -> (vacantb (protection_table s) r=true /\ blankb sector f r=true) ->
 writer_execution g sector r false f plan result -> writer_end result=WriterComplete -> ranges entry=[r] ->
 enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
   (Logged (Ready (writer_flash result)) h a,OpenBoundary (image_replace image index (Some entry)) []
     (exact_member ranges image index entry r s)) (selected_evidence old previous e) /\
 unchanged (certificate_ranges ranges (Certificate old previous)) (object_flash sector f) (object_flash sector (writer_flash result)) /\
 raw_order sector 256 data_len (Logged (Ready (writer_flash result)) h a).
Proof.
 intros G DIV INV RAW HEAD IN LOCAL VALID P HIT WRITE OK RANGE.
 destruct HIT as [FREE BLANK];apply vacantb_spec in FREE;apply blankb_spec in BLANK.
 pose proof (reservation_state_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ false INV P FREE) as RESERVED.
 destruct (pending_writer_consumes g sector data_len valid view marker ranges decode pages
   f h a old previous image root (reservation_state false r s) e (reservation_token false r) false plan result validate
   G DIV RESERVED RAW HEAD IN LOCAL VALID ltac:(split;[split;[reflexivity|exact BLANK]|exact WRITE]))
   as [NEXT [KEEP ORDER]].
 unfold writer_exit_boundary in NEXT,ORDER;rewrite OK in NEXT,ORDER.
 split;[|split;assumption].
 pose proof (reserved_exact_attachment sector data_len (validate (writer_flash result)) view marker ranges decode pages
   (Logged (Ready (writer_flash result)) h a) image root
   (snapshot_written (reservation_state false r s)) (selected_evidence old previous e)
   (Build_preparation ObjectPreparation r Written) index entry NEXT eq_refl eq_refl RANGE) as ATTACH.
 exact ATTACH.
Qed.
Definition outer_local_begin s := data_next DataBegin (data_next DataBegin s).
Definition pair_body ranges image ia ib ea eb ra rb s :=
 exact_member ranges (image_replace image ia (Some ea)) ib eb rb
   (exact_member ranges image ia ea ra (outer_local_begin s)).
Definition pair_accept ranges image ia ib ea eb ra rb s :=
 data_next (DataClose [protection_current s++attached_ranges s]
   (protection_current s++attached_ranges s) true)
   (pair_body ranges image ia ib ea eb ra rb s).

Theorem certified_outer_pair g sector data_len valid view marker ranges decode pages
 f h a old d s e ia ib ea eb ra rb pa pb wa wb validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,IdleBoundary old d s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 incarnation_reader_local ranges decode (Certificate old d) -> validator_accepts_decoded sector decode validate ->
 (vacantb (protection_table (outer_local_begin s)) ra=true /\ blankb sector f ra=true) ->
 writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges ea=[ra] ->
 (vacantb (protection_table (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s))) rb=true /\
   blankb sector (writer_flash wa) rb=true) ->
 writer_execution g sector rb false (writer_flash wa) pb wb -> writer_end wb=WriterComplete -> ranges eb=[rb] ->
 enriched_invariant sector data_len (validate (writer_flash wb)) view marker ranges decode pages
   (Logged (Ready (writer_flash wb)) h a,
    OpenBoundary (image_replace (image_replace (recovered_image d) ia (Some ea)) ib (Some eb)) []
      (pair_accept ranges (recovered_image d) ia ib ea eb ra rb s)) (selected_evidence old d e) /\
 unchanged (certificate_ranges ranges (Certificate old d)) (object_flash sector f) (object_flash sector (writer_flash wb)) /\
 raw_order sector 256 data_len (Logged (Ready (writer_flash wb)) h a).
Proof.
 intros G DIV INIT RAW LOCAL VALID HA WA OA RA HB WB OB RB.
 pose proof INIT as [[J [IDLE [FMT COR]]] [EV IN]].
 pose proof IDLE as [[DI [NF [STACK [P [CUR [BASE [PH ACK]]]]]]] [JI [READY [HEAD LINK]]]].
 destruct (common_begin sector data_len valid view marker ranges decode pages _ _ _ _ (proj1 INIT)) as [CALL OUTER].
 assert (OUTER_E:enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin s)) e).
 { split;[exact OUTER|split;[exact EV|exact I]]. }
 destruct (certified_local_begin sector data_len valid view marker ranges decode pages
   _ _ _ _ _ (protection_current s++attached_ranges s) OUTER_E
   ltac:(simpl;rewrite STACK;reflexivity) eq_refl) as [BEGIN [INNER FRAMES]].
 destruct (certified_written_member g sector data_len valid view marker ranges decode pages
   f h a old d (recovered_image d) [recovered_boss d] (outer_local_begin s) e ra ia ea pa wa validate
   G DIV INNER RAW HEAD IN LOCAL VALID eq_refl HA WA OA RA) as [A [KEEP_A RAW_A]].
 destruct (certified_written_member g sector data_len (validate (writer_flash wa)) view marker ranges decode pages
   (writer_flash wa) h a old d (image_replace (recovered_image d) ia (Some ea)) []
   (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) (selected_evidence old d e)
   rb ib eb pb wb validate G DIV A RAW_A HEAD ltac:(simpl;auto) LOCAL VALID eq_refl HB WB OB RB)
   as [B [KEEP_B RAW_B]].
 split.
 - apply (proj2 (certified_local_accept sector data_len (validate (writer_flash wb)) view marker ranges decode pages
     _ _ _ _ _ (protection_current s++attached_ranges s) B
     ltac:(unfold exact_member,outer_local_begin;simpl;rewrite STACK;rewrite app_nil_r;reflexivity) eq_refl)).
 - split;[|exact RAW_B]. intros r x R X;rewrite (KEEP_B r x R X);exact (KEEP_A r x R X).
Qed.

Theorem outer_local_materialized_roots boss old deps s :
 protection_saved s=[] -> protection_current s++attached_ranges s=boss old::deps ->
 DeferredSnapshots.begin_scope (Some old) []=Some [Some old] /\
 DeferredSnapshots.begin_scope (Some old) [Some old]=Some [Some old;Some old] /\
 (forall r,In r [Some old;Some old] -> r<>None) /\
 protection_saved (outer_local_begin s)=
   map (snapshot_dependencies boss) [(Some old,deps);(Some old,deps)].
Proof.
 intros STACK CUR;split;[reflexivity|]. split;[reflexivity|]. split.
 - intros r [E|[E|[]]];subst r;discriminate.
 - unfold outer_local_begin;simpl;rewrite STACK;rewrite app_nil_r;rewrite CUR;reflexivity.
Qed.
Theorem pair_saved_roots_preserved ranges image ia ib ea eb ra rb s :
 protection_saved (pair_body ranges image ia ib ea eb ra rb s)=protection_saved (outer_local_begin s).
Proof. reflexivity. Qed.

(* A live OperationScope is a control phase, not another scope stack. *)
Definition operation_rollback_structure marker s :=
 protection_saved s=[physical_authority s;physical_authority s] /\
 protection_base s=marker::physical_authority s /\
 acknowledged_authority s=physical_authority s.
Definition operation_cancel s :=
 data_next (DataClose [physical_authority s] (physical_authority s) false) s.
Definition operation_phase phase := match phase with
 | OpenBoundary image root s => OperationBoundary image root s
 | other => other end.
Definition operation_writer_exit old image root s h a result :=
 let out:=writer_exit_boundary old image root s h a result in
 (fst out,operation_phase (snd out)).
Lemma operation_phase_safe sector data_len valid view marker ranges decode pages j phase e :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,phase) e ->
 enriched_invariant sector data_len valid view marker ranges decode pages (j,operation_phase phase) e.
Proof. destruct phase;exact (fun H=>H). Qed.

Theorem certified_operation_first g sector data_len valid view marker ranges decode pages
 f h a old d s e index entry r plan result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,IdleBoundary old d s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 incarnation_reader_local ranges decode (Certificate old d) -> validator_accepts_decoded sector decode validate ->
 (vacantb (protection_table (outer_local_begin s)) r=true /\ blankb sector f r=true) ->
 writer_execution g sector r false f plan result -> writer_end result=WriterComplete -> ranges entry=[r] ->
 let out:=exact_member ranges (recovered_image d) index entry r (outer_local_begin s) in
 enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
  (Logged (Ready (writer_flash result)) h a,OperationBoundary
    (image_replace (recovered_image d) index (Some entry)) [] out) (selected_evidence old d e) /\
 operation_rollback_structure marker out /\
 unchanged (certificate_ranges ranges (Certificate old d)) (object_flash sector f)
   (object_flash sector (writer_flash result)) /\
 raw_order sector 256 data_len (Logged (Ready (writer_flash result)) h a).
Proof.
 intros G DIV INIT RAW LOCAL VALID HIT WRITE OK RANGE out.
 pose proof (proj1 (proj1 (proj2 (proj1 INIT)))) as [DI [NF [STACK [P [CUR [BASE [PH ACK]]]]]]].
 pose proof (proj2 (proj1 (proj2 (proj1 INIT)))) as [JI [READY [HEAD LINK]]].
 destruct (common_begin sector data_len valid view marker ranges decode pages _ _ _ _ (proj1 INIT)) as [BEGIN NEXT_BEGIN].
 assert (OUTER:enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin s)) e).
 { split;[exact NEXT_BEGIN|split;[exact (proj1 (proj2 INIT))|exact I]]. }
 destruct (certified_local_begin sector data_len valid view marker ranges decode pages
   _ _ _ _ _ (protection_current s++attached_ranges s) OUTER
   ltac:(simpl;rewrite STACK;reflexivity) eq_refl) as [_ [INNER SS]].
 destruct (certified_written_member g sector data_len valid view marker ranges decode pages
   f h a old d (recovered_image d) [recovered_boss d] (outer_local_begin s) e r index entry plan result validate
   G DIV INNER RAW HEAD (proj2 (proj2 INIT)) LOCAL VALID eq_refl HIT WRITE OK RANGE) as [NEXT [KEEP ORDER]].
 split;[exact NEXT|]. split;[|split;assumption].
 unfold operation_rollback_structure,out,exact_member,outer_local_begin;simpl.
 rewrite STACK;rewrite app_nil_r;rewrite CUR,BASE,PH,ACK;repeat split;reflexivity.
Qed.

Theorem certified_operation_cancel sector data_len valid view marker ranges decode pages
 f h a image root s e old d :
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OperationBoundary image root s) e ->
 operation_rollback_structure marker s -> pending_preparation s=None ->
 hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
 data_caller (DataClose [physical_authority s] (physical_authority s) false) s /\
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)) e /\
 rollback_structure marker (operation_cancel s) /\
 collection_enabled true (Some old) (Some old) (operation_cancel s)=false.
Proof.
 intros [[JI [DI [NF [COR LINK]]]] [EV CERT]] [STACK [BASE ACK]] P HEAD IN.
 assert (CALL:data_caller (DataClose [physical_authority s] (physical_authority s) false) s)
   by (split;assumption).
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK;simpl in LINK;rewrite HEAD in LINK;simpl in LINK.
   rewrite Nat2N.id in LINK;exact LINK. }
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) (Certificate old d) IN) as [READ [B O]].
 simpl in B,O.
 split;[exact CALL|]. split.
 - split;[|split;[exact EV|exact I]]. split;[exact JI|].
   split;[apply data_command_preserves;assumption|]. split;[exact NF|]. split.
   + unfold image_current_correspondence,operation_cancel;simpl;rewrite app_nil_r,B,O,PH;reflexivity.
   + apply local_data_keeps_history_link;exact LINK.
 - split;[unfold rollback_structure,operation_cancel;simpl;auto|reflexivity].
Qed.

Definition operation_abort_commands saved :=
 [DataClose [saved] saved false;DataClose [] saved false].
Lemma operation_abort_calls s :
 pending_preparation s=None -> protection_saved s=[physical_authority s;physical_authority s] ->
 data_calls (operation_abort_commands (physical_authority s)) s.
Proof.
 intros P STACK;unfold operation_abort_commands;simpl.
 split;[split;assumption|]. split;[split;reflexivity|exact I].
Qed.
Lemma operation_abort_frozen_table s : protection_frozen s=true ->
 protection_table (execute_data (operation_abort_commands (physical_authority s)) s)=protection_table s /\
 physical_authority (execute_data (operation_abort_commands (physical_authority s)) s)=physical_authority s /\
 protection_saved (execute_data (operation_abort_commands (physical_authority s)) s)=[].
Proof. intro F;unfold operation_abort_commands;simpl;rewrite F;simpl;repeat split;reflexivity. Qed.
Lemma operation_no_begin j image root s : ~ boundary_begin_caller (j,OperationBoundary image root s).
Proof. intros [id [d [ram [E CALL]]]];discriminate. Qed.

(* The acquisition protocol is unchanged; only its live control phase is
   OperationScope. This projection stores no RAM, flash or table of its own. *)
Definition operation_acquisition_boundary old image root s h a result span :=
 let out:=recycling_acquisition_boundary old image root s h a result span false in
 (fst out,operation_phase (snd out)).

Theorem certified_operation_begin sector data_len valid view marker ranges decode pages j old d s e :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,IdleBoundary old d s) e ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)) e /\
 operation_rollback_structure marker (outer_local_begin s).
Proof.
 intro INIT.
 pose proof (proj1 (proj1 (proj2 (proj1 INIT)))) as [DI [NF [STACK [P [CUR [BASE [PH ACK]]]]]]].
 destruct (common_begin sector data_len valid view marker ranges decode pages _ _ _ _ (proj1 INIT)) as [CALL NEXT].
 assert (OUTER:enriched_invariant sector data_len valid view marker ranges decode pages
   (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin s)) e).
 { split;[exact NEXT|split;[exact (proj1 (proj2 INIT))|exact I]]. }
 destruct (certified_local_begin sector data_len valid view marker ranges decode pages
   _ _ _ _ _ (protection_current s++attached_ranges s) OUTER
   ltac:(simpl;rewrite STACK;reflexivity) eq_refl) as [_ [INNER SS]].
 split;[exact INNER|].
 unfold operation_rollback_structure,outer_local_begin;simpl.
 rewrite STACK;rewrite app_nil_r;rewrite CUR,BASE,PH,ACK;repeat split;reflexivity.
Qed.

(* Numeric facts name the SAME token/range; they never assert vacancy or
   permission to mutate. Authority to release is still data_caller/invariant. *)
Definition token_numeric_certificate word_max p :=
 range_check true word_max (prep_range p)=None.
Lemma acquired_token_numeric word_max r source :
 ram_reservation_check true word_max r source=None ->
 token_numeric_certificate word_max (reservation_token false r).
Proof. apply range_check_from_reservation. Qed.
Lemma numeric_token_phase word_max p phase :
 token_numeric_certificate word_max p -> token_numeric_certificate word_max (set_phase p phase).
Proof. exact (fun H=>H). Qed.
Lemma numeric_token_release word_max p t :
 token_numeric_certificate word_max p ->
 checked_release true word_max (prep_range p) t=(None,release_extent 256 (prep_range p) t).
Proof. intro C;unfold checked_release;rewrite C;reflexivity. Qed.
Lemma numeric_token_rehome word_max p depth t :
 token_numeric_certificate word_max p -> depth<=6 ->
 checked_rehome true word_max (prep_range p) depth t=(None,rehome_extent (prep_range p) depth t).
Proof.
 intros C D;unfold checked_rehome;assert (B:(6 <? depth)=false) by (apply Nat.ltb_ge;exact D).
 rewrite B,C;reflexivity.
Qed.

(* Numeric facts follow the live descriptors, not an artificially retained
   preparation token. They do not assert ownership, vacancy or release rights. *)
Lemma range_numeric_offset word_max r : range_numeric word_max r -> offset r<=262144.
Proof.
 unfold range_numeric,range_check.
 destruct (offset r+span r<=?word_max);[|discriminate].
 destruct (AllocationAdmission.page_limit r<=?1024) eqn:LIMIT;[|discriminate].
 intros UNUSED;apply Nat.leb_le in LIMIT;unfold AllocationAdmission.page_limit in LIMIT.
 pose proof (Nat.div_mod (offset r+span r+255) 256 ltac:(lia)) as DIVISION.
 pose proof (Nat.mod_upper_bound (offset r+span r+255) 256 ltac:(lia)) as REMAINDER.
 change (offset r<=1024*256).
 lia.
Qed.

Lemma range_numeric_end word_max r : range_numeric word_max r ->
 offset r + span r <= word_max.
Proof.
 unfold range_numeric,range_check.
 destruct (offset r+span r<=?word_max) eqn:BOUND;[|discriminate].
 intros _;now apply Nat.leb_le in BOUND.
Qed.
Lemma range_numeric_usize_end word_max r : range_numeric word_max r ->
 offset r<=word_max /\ span r<=word_max /\
 Nat.min word_max (offset r+span r)=offset r+span r.
Proof.
 intro NUM;pose proof (range_numeric_end _ _ NUM) as BOUND.
 split;[lia|]. split;[lia|apply Nat.min_r;exact BOUND].
Qed.

Definition state_numeric word_max s :=
 Forall (range_numeric word_max) (protection_current s) /\
 Forall (range_numeric word_max) (attached_ranges s) /\
 Forall (Forall (range_numeric word_max)) (protection_saved s) /\
 Forall (range_numeric word_max) (protection_base s) /\
 Forall (range_numeric word_max) (physical_authority s) /\
 Forall (range_numeric word_max) (acknowledged_authority s) /\
 Forall (range_numeric word_max) (pending_ranges s).
Definition data_numeric_caller word_max cmd := match cmd with
 | DataReserve r => range_numeric word_max r
 | _ => True end.
Lemma data_numeric_preserves word_max cmd s :
 state_numeric word_max s -> data_caller cmd s -> data_numeric_caller word_max cmd ->
 state_numeric word_max (data_next cmd s).
Proof.
 intros [C [A [S [B [P [K T]]]]]] CALL NUM.
 destruct cmd;unfold state_numeric,data_next;cbn in CALL,NUM |- *.
 - repeat split;auto.
 - destruct (pending_preparation s) eqn:E;[|repeat split;assumption].
   unfold pending_ranges in T;rewrite E in T;cbn in T.
   repeat split;auto.
 - destruct (pending_preparation s) eqn:E;[|repeat split;assumption].
   unfold pending_ranges in T;rewrite E in T;cbn in T.
   inversion T;subst;repeat split;auto;constructor;auto.
 - repeat split;auto;constructor.
 - repeat split;auto;try constructor.
   + apply Forall_app;auto.
   + apply Forall_app;split;[exact S|constructor;[apply Forall_app;auto|constructor]].
 - destruct CALL as [NONE STACK]. rewrite STACK in S;apply Forall_app in S;destruct S as [V LAST].
   inversion LAST;subst. destruct accept;repeat split;auto;constructor.
 - repeat split;auto.
 - repeat split;auto.
Qed.
Definition data_numeric_calls word_max commands := Forall (data_numeric_caller word_max) commands.
Lemma data_numeric_execution word_max commands s :
 state_numeric word_max s -> data_calls commands s -> data_numeric_calls word_max commands ->
 state_numeric word_max (execute_data commands s).
Proof.
 revert s;induction commands as [|cmd commands IH];intros s NUM CALL ADMIT;[exact NUM|].
 inversion ADMIT;subst;simpl in CALL |- *;destruct CALL as [C REST].
 apply IH;auto;eapply data_numeric_preserves;eauto.
Qed.
Lemma numeric_pending word_max s p : state_numeric word_max s -> pending_preparation s=Some p ->
 token_numeric_certificate word_max p.
Proof.
 intros [_ [_ [_ [_ [_ [_ T]]]]]] E;unfold pending_ranges in T;rewrite E in T;inversion T;assumption.
Qed.
Lemma numeric_close_no_token word_max s views saved accept :
 state_numeric word_max s -> data_caller (DataClose views saved accept) s ->
 state_numeric word_max (data_next (DataClose views saved accept) s) /\
 pending_preparation (data_next (DataClose views saved accept) s)=None.
Proof. intros N C;split;[eapply data_numeric_preserves;[exact N|exact C|exact I]|reflexivity]. Qed.

Lemma numeric_exact_attach word_max ranges image root index entry s p :
 state_numeric word_max s -> data_caller DataAttach s -> pending_preparation s=Some p ->
 image_current_correspondence ranges image root s -> ranges entry=[prep_range p] ->
 state_numeric word_max (exact_attach ranges image index entry s).
Proof.
 intros NUM CALL P COR RANGE.
 pose proof (numeric_pending _ _ _ NUM P) as TOKEN.
 destruct NUM as [C [A [S [B [PH [ACK T]]]]]].
 assert (OLD:Forall (range_numeric word_max) (image_dependencies ranges image)).
 { apply Forall_forall;intros r IN.
   assert (MEM:In r (protection_current s++attached_ranges s)).
   { rewrite COR;apply in_or_app;right;exact IN. }
   apply in_app_or in MEM;destruct MEM as [MEM|MEM].
   - exact (proj1 (Forall_forall _ _) C r MEM).
   - exact (proj1 (Forall_forall _ _) A r MEM). }
 assert (NEW:Forall (range_numeric word_max)
    (image_dependencies ranges (image_replace image index (Some entry)))).
 { apply Forall_forall;intros r IN;apply dependencies_replace_subset in IN.
   destruct IN as [IN|IN].
   - simpl in IN;rewrite RANGE in IN;destruct IN as [EQ|[]];subst;exact TOKEN.
   - exact (proj1 (Forall_forall _ _) OLD r IN). }
 unfold exact_attach,replace_current_dependencies,data_next;rewrite P.
 unfold state_numeric;cbn;repeat split;auto;constructor.
Qed.

(* Fresh reconstruction consumes local decoded-range checks, not pre-reset RAM. *)
Lemma idle_numeric_from_ranges word_max view marker id s :
 idle_root view marker id s ->
 Forall (range_numeric word_max) (marker::root_extents (view id)) ->
 state_numeric word_max s.
Proof.
 intros [_ [_ [STACK [P [CUR [BASE [PH ACK]]]]]]] R.
 inversion R as [|? ? M ROOT];subst.
 assert (CA:Forall (range_numeric word_max) (protection_current s++attached_ranges s)) by (rewrite CUR;exact ROOT).
 apply Forall_app in CA;destruct CA as [C A].
 unfold state_numeric,pending_ranges;rewrite STACK,P,BASE,PH,ACK.
 repeat split;auto;constructor.
Qed.

Lemma numeric_snapshot_error word_max s frozen :
 state_numeric word_max s -> state_numeric word_max (snapshot_error frozen s).
Proof.
 intros [C [A [S [B [P [K T]]]]]];destruct frozen;
 unfold snapshot_error,data_next,state_numeric;cbn;repeat split;auto;constructor.
Qed.

(* The cursor selects a candidate; successful executable checks, not a
   provenance claim about the cursor, establish this numeric admission. *)
Lemma cursor_probe_numeric word_max sector area_len req cursor s f r :
 area_len<=word_max -> area_len<=1024*256 ->
 cursor_probe sector area_len req cursor (protection_table s) f=Some r ->
 range_numeric word_max r.
Proof.
 intros WORD AREA HIT.
 destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT) as [_ [_ [BOUND _]]].
 unfold range_numeric,range_check.
 assert (W:(offset r+span r<=?word_max)=true) by (apply Nat.leb_le;lia).
 assert (P:(page_limit r<=?1024)=true).
 { apply Nat.leb_le;unfold page_limit.
   assert ((offset r+span r+255)/256<1025) by (apply Nat.div_lt_upper_bound;lia). lia. }
 now rewrite W,P.
Qed.
Lemma cursor_reserve_numeric word_max sector area_len req cursor s f r :
 state_numeric word_max s -> protection_frozen s=false -> pending_preparation s=None ->
 area_len<=word_max -> area_len<=1024*256 ->
 cursor_probe sector area_len req cursor (protection_table s) f=Some r ->
 state_numeric word_max (data_next (DataReserve r) s).
Proof.
 intros NUM F P W A HIT.
 eapply data_numeric_preserves;[exact NUM| |eapply cursor_probe_numeric;eauto].
 destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT) as [_ [_ [_ [_ [FREE _]]]]].
 exact (conj F (conj P FREE)).
Qed.

Theorem operation_abort_numeric word_max s :
 state_numeric word_max s -> pending_preparation s=None ->
 protection_saved s=[physical_authority s;physical_authority s] ->
 state_numeric word_max
   (execute_data (operation_abort_commands (physical_authority s)) s).
Proof.
 intros NUM P STACK;apply data_numeric_execution;[exact NUM|apply operation_abort_calls;assumption|].
 repeat constructor.
Qed.

Theorem idle_numeric_begin word_max view marker id s :
 idle_root view marker id s ->
 Forall (range_numeric word_max) (marker::root_extents (view id)) ->
 state_numeric word_max s /\
 (data_caller DataBegin s -> state_numeric word_max (data_next DataBegin s)).
Proof.
 intros IDLE RANGES;pose proof (idle_numeric_from_ranges _ _ _ _ _ IDLE RANGES) as NUM.
 split;[exact NUM|intro CALL;eapply data_numeric_preserves;[exact NUM|exact CALL|exact I]].
Qed.

(* Numeric obligations are phase dependent. A reset discards every RAM clause;
   a partial reconstruction has only the descriptors it has actually rebuilt. *)
Definition boot_numeric word_max marker ranges pc := match pc with
 | Selecting | Decoding _ | Stopped => True
 | Installing _ d _ => Forall (range_numeric word_max) (decoded_ranges marker ranges d)
 | Retaining _ d todo ram =>
     Forall (range_numeric word_max) (decoded_ranges marker ranges d) /\
     Forall (range_numeric word_max) todo /\ state_numeric word_max ram
 | Caching _ d ram | Returning _ d ram | Usable _ d ram =>
     Forall (range_numeric word_max) (decoded_ranges marker ranges d) /\ state_numeric word_max ram
 end.
Definition phase_numeric word_max marker ranges phase := match phase with
 | IdleBoundary _ _ ram | ClientBoundary _ _ ram | OpenBoundary _ _ ram
 | OperationBoundary _ _ ram | PublishingBoundary _ _ _ ram
 | FrozenBoundary _ _ _ ram => state_numeric word_max ram
 | RebuildingBoundary pc => boot_numeric word_max marker ranges pc
 | FatalBoundary => True
 end.

(* A local decoder result: no coverage, authority, ownership or transactional
   conclusion is part of this service contract. The marker is admitted separately. *)

Lemma decoded_allocation_usize word_max sector ranges decode read f id d :
 decoded_numeric_contract word_max ranges decode ->
 generation_decoding_matches sector decode read ->
 decode (object_flash sector f) id=Some d ->
 read_allocation read f id=Some (allocation_from_decoded d) /\
 extent_end (recovered_boss d)<=word_max /\
 Nat.min word_max (extent_end (recovered_boss d))=extent_end (recovered_boss d).
Proof.
 intros NUM MATCH READ.
 split.
 - unfold read_allocation;specialize (MATCH f id);rewrite READ in MATCH.
   destruct (read f id) as [[decoded n]|];cbn in MATCH;[|discriminate].
   inversion MATCH;reflexivity.
 - pose proof (NUM _ _ _ READ) as RANGES;inversion RANGES;subst.
   unfold extent_end;split;[eapply range_numeric_end;eassumption|].
   apply Nat.min_r;eapply range_numeric_end;eassumption.
Qed.

Lemma numeric_recovery_retains word_max retained s :
 state_numeric word_max s -> state_numeric word_max (recovery_retains retained s).
Proof.
 intro NUM;unfold state_numeric,pending_ranges in *.
 destruct (recovery_retains_observers retained s) as [C [S [B [A [P [PH [ACK REST]]]]]]].
 now rewrite C,S,B,A,P,PH,ACK.
Qed.
Lemma numeric_decoded_fresh word_max marker ranges d :
 Forall (range_numeric word_max) (decoded_ranges marker ranges d) ->
 state_numeric word_max (decoded_fresh marker ranges d).
Proof.
 intro NUM;inversion NUM;subst.
 unfold state_numeric,decoded_fresh,recovered_ram,pending_ranges;cbn;repeat split;auto;constructor.
Qed.

Theorem boot_numeric_from_local_decoding word_max sector data_len valid view marker ranges decode pages j pc :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 boot_invariant sector data_len valid view marker ranges decode pages (j,pc) ->
 boot_numeric word_max marker ranges pc.
Proof.
 intros MARK DECODE [_ [_ INV]]. destruct pc;cbn in INV |- *;try exact I.
 - destruct INV as [_ [_ [READ _]]];constructor;[exact MARK|eapply DECODE;exact READ].
 - destruct INV as [[_ [_ [READ _]]] [done [PART RAM]]];subst ram.
   assert (ALL:Forall (range_numeric word_max) (decoded_ranges marker ranges decoded))
     by (constructor;[exact MARK|eapply DECODE;exact READ]).
   split;[exact ALL|]. split.
   + rewrite <- PART in ALL;apply Forall_app in ALL;tauto.
   + apply numeric_recovery_retains,numeric_decoded_fresh;exact ALL.
 - destruct INV as [[_ [_ [READ _]]] RAM];subst ram.
   assert (ALL:Forall (range_numeric word_max) (decoded_ranges marker ranges decoded))
     by (constructor;[exact MARK|eapply DECODE;exact READ]).
   split;[exact ALL|]. apply numeric_recovery_retains,numeric_decoded_fresh;exact ALL.
 - destruct INV as [[_ [_ [READ _]]] RAM];subst ram.
   assert (ALL:Forall (range_numeric word_max) (decoded_ranges marker ranges decoded))
     by (constructor;[exact MARK|eapply DECODE;exact READ]).
   split;[exact ALL|]. change (state_numeric word_max (rebuild_decoded marker ranges decoded)).
   apply numeric_recovery_retains,numeric_decoded_fresh;exact ALL.
 - destruct INV as [[_ [_ [READ _]]] RAM];subst ram.
   assert (ALL:Forall (range_numeric word_max) (decoded_ranges marker ranges decoded))
     by (constructor;[exact MARK|eapply DECODE;exact READ]).
   split;[exact ALL|]. change (state_numeric word_max (rebuild_decoded marker ranges decoded)).
   apply numeric_recovery_retains,numeric_decoded_fresh;exact ALL.
Qed.

(* Needed by operation_recycled_pair: begin changes no range, and an exact
   member introduces only the single admitted range before consuming its token. *)
Lemma numeric_begin_unconditionally word_max s :
 state_numeric word_max s -> state_numeric word_max (data_next DataBegin s).
Proof.
 intros [C [A [S [B [P [K T]]]]]];unfold state_numeric,data_next;cbn.
 repeat split;auto;try constructor.
 - apply Forall_app;auto.
 - apply Forall_app;split;[exact S|constructor;[apply Forall_app;auto|constructor]].
Qed.
Lemma numeric_exact_member word_max ranges image root index entry r s :
 state_numeric word_max s -> range_numeric word_max r -> protection_frozen s=false ->
 image_current_correspondence ranges image root s -> ranges entry=[r] ->
 state_numeric word_max (exact_member ranges image index entry r s).
Proof.
 intros NUM RANGE F COR ENTRY;unfold exact_member.
 eapply numeric_exact_attach with (p:=Build_preparation ObjectPreparation r Written) (root:=root).
 - destruct NUM as [C [A [S [B [P [K T]]]]]].
   unfold execute_data,data_next,state_numeric,pending_ranges;cbn;repeat split;auto;constructor;auto.
 - split;[reflexivity|]. exists (Build_preparation ObjectPreparation r Written);repeat split;reflexivity.
 - reflexivity.
 - exact COR.
 - exact ENTRY.
Qed.

(* Numerical transport for the finite cases of reserved_execution. These
   lemmas change no physical/ownership contract. *)
Lemma numeric_reservation word_max boss r s :
 state_numeric word_max s -> range_numeric word_max r ->
 state_numeric word_max (reservation_state boss r s).
Proof.
 intros [C [A [S [B [P [K T]]]]]] R;destruct boss;
 unfold reservation_state,snapshot_reserve,change_preparation,data_next,state_numeric,pending_ranges;
 cbn;repeat split;auto;constructor;auto.
Qed.
Lemma numeric_written word_max s : state_numeric word_max s -> state_numeric word_max (snapshot_written s).
Proof.
 intros [C [A [S [B [P [K T]]]]]];unfold snapshot_written;
 destruct (pending_preparation s) eqn:E;[|repeat split;assumption].
 unfold pending_ranges in T;rewrite E in T;cbn in T.
 unfold state_numeric,change_preparation,pending_ranges;cbn;repeat split;auto.
Qed.
Lemma numeric_retain_error word_max s : state_numeric word_max s -> state_numeric word_max (snapshot_retain_error s).
Proof.
 intros [C [A [S [B [P [K T]]]]]];unfold snapshot_retain_error,state_numeric,change_preparation,pending_ranges;
 cbn;repeat split;auto;constructor.
Qed.
Lemma numeric_error_state word_max end_ s :
 state_numeric word_max s -> state_numeric word_max (preparation_error_state end_ s).
Proof. destruct end_;cbn [preparation_error_state];auto using numeric_snapshot_error,numeric_retain_error. Qed.
Lemma numeric_rollback word_max saved end_ s :
 state_numeric word_max s -> Forall (range_numeric word_max) saved ->
 state_numeric word_max (preparation_rollback saved end_ s).
Proof.
 intros NUM SAV;pose proof (numeric_error_state word_max end_ s NUM) as [C [A [S [B [P [K T]]]]]].
 unfold preparation_rollback,state_numeric,data_next;cbn;repeat split;auto;constructor.
Qed.
Lemma numeric_collection word_max page initialized durable current resolved s :
 state_numeric word_max s ->
 state_numeric word_max (collection_return page initialized durable current resolved s).
Proof.
 intro NUM;unfold collection_return;destruct collection_enabled;[destruct resolved|];exact NUM.
Qed.
Lemma numeric_failure_phase word_max marker ranges old d resolved s :
 state_numeric word_max s -> phase_numeric word_max marker ranges (failure_phase old d resolved s).
Proof.
 intro NUM;unfold failure_phase,preparation_collection;destruct resolved;
 repeat match goal with |- context[if ?b then _ else _] => destruct b end;
 cbn [phase_numeric];try exact I;exact NUM.
Qed.
Lemma numeric_slot word_max selected s :
 state_numeric word_max s -> Forall (range_numeric word_max) selected ->
 state_numeric word_max (slot_publication selected s).
Proof. intros [C [A [S [B [P [K T]]]]]] SEL;repeat split;assumption. Qed.
Lemma numeric_frozen_command word_max cmd s :
 state_numeric word_max s -> protection_frozen s=true -> data_caller cmd s ->
 state_numeric word_max (data_next cmd s) /\ protection_frozen (data_next cmd s)=true.
Proof.
 intros NUM F CALL;assert (AD:data_numeric_caller word_max cmd).
 { destruct cmd;try exact I;cbn in CALL;destruct CALL as [BAD _];congruence. }
 split;[eapply data_numeric_preserves;eauto|].
 destruct cmd;cbn in CALL;
 try match type of CALL with protection_frozen s=false /\ _ => destruct CALL as [BAD REST];congruence end;
 cbn;auto.
Qed.
Lemma numeric_frozen_commands word_max commands s :
 state_numeric word_max s -> protection_frozen s=true -> data_calls commands s ->
 state_numeric word_max (execute_data commands s).
Proof.
 revert s;induction commands as [|cmd commands IH];intros s NUM F CALL;[exact NUM|].
 destruct CALL as [CALL REST];destruct (numeric_frozen_command _ _ _ NUM F CALL) as [NEXT FR].
 apply IH;assumption.
Qed.
Lemma numeric_install word_max s : state_numeric word_max s -> state_numeric word_max (install_candidate s).
Proof.
 intros [C [A [S [B [PH [ACK T]]]]]];unfold install_candidate.
 destruct (pending_preparation s) eqn:P;[|repeat split;assumption].
 unfold pending_ranges in T;rewrite P in T;inversion T;subst.
 unfold replace_current_dependencies,data_next;rewrite P;unfold state_numeric;cbn.
 repeat split;auto;try constructor;auto. apply Forall_app;auto.
Qed.
Lemma numeric_materialize word_max r s :
 state_numeric word_max s -> range_numeric word_max r -> state_numeric word_max (materialize_candidate r s).
Proof.
 intros NUM R;apply numeric_install,numeric_written.
 change (state_numeric word_max (reservation_state true r s));apply numeric_reservation;assumption.
Qed.

Lemma range_numeric_monotone lo hi r : lo<=hi -> range_numeric lo r -> range_numeric hi r.
Proof.
 intros LE NUM;unfold range_numeric,range_check in *.
 destruct (offset r+span r<=?lo) eqn:L;[|discriminate].
 apply Nat.leb_le in L;assert (H:(offset r+span r<=?hi)=true) by (apply Nat.leb_le;lia).
 now rewrite H.
Qed.
Lemma certificate_numeric word_max sector view ranges decode j e c :
 decoded_numeric_contract word_max ranges decode ->
 persistent_evidence sector view ranges decode j e -> In c (live_certificates e) ->
 Forall (range_numeric word_max) (root_extents (view (certificate_id c))).
Proof.
 intros DEC [EV REST] IN;pose proof (proj1 (Forall_forall _ _) EV c IN) as [READ [B O]].
 unfold root_extents;rewrite <- B, <- O;exact (DEC _ _ _ READ).
Qed.
Lemma selected_numeric word_max sector view ranges decode j e :
 decoded_numeric_contract word_max ranges decode -> persistent_evidence sector view ranges decode j e ->
 Forall (range_numeric word_max) (optional_root view (option_map N.to_nat (hd_error (publications j)))).
Proof.
 intros DEC EV;destruct (hd_error (publications j)) as [id|] eqn:H;[|constructor].
 destruct (proj1 (proj2 EV) (N.to_nat id) ltac:(rewrite N2Nat.id;exact H)) as [c [IN ID]].
 cbn;rewrite <- ID;eapply certificate_numeric;eauto.
Qed.
Lemma enriched_idle_numeric word_max sector data_len valid view marker ranges decode pages j id d s e :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 enriched_invariant sector data_len valid view marker ranges decode pages (j,IdleBoundary id d s) e ->
 state_numeric word_max s.
Proof.
 intros MARK DEC SAFE.
 apply idle_numeric_from_ranges with (view:=view) (marker:=marker) (id:=id).
 - exact (proj1 (proj1 (proj2 (proj1 SAFE)))).
 - constructor;[exact MARK|].
   exact (certificate_numeric _ _ _ _ _ _ _ _ DEC (proj1 (proj2 SAFE)) (proj2 (proj2 SAFE))).
Qed.
Lemma enriched_client_numeric word_max sector data_len valid view marker ranges decode pages j id d s e :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 enriched_invariant sector data_len valid view marker ranges decode pages (j,ClientBoundary id d s) e ->
 state_numeric word_max s.
Proof.
 intros MARK DEC [COMMON [EV LINK]].
 apply (enriched_idle_numeric word_max sector data_len valid view marker ranges decode pages j id d s e MARK DEC).
 split;[split;[exact (proj1 COMMON)|exact (proj1 (proj2 COMMON))]|split;assumption].
Qed.
Lemma numeric_writer_exit word_max marker ranges old image root s h a result :
 state_numeric word_max s ->
 phase_numeric word_max marker ranges (snd (writer_exit_boundary old image root s h a result)).
Proof.
 intro NUM;unfold writer_exit_boundary;destruct (writer_end result).
 - exact (numeric_written _ _ NUM).
 - exact (numeric_snapshot_error word_max s false NUM).
 - exact (numeric_retain_error _ _ NUM).
 - exact (numeric_snapshot_error word_max s true NUM).
 - exact I.
Qed.
Lemma numeric_operation_phase word_max marker ranges phase :
 phase_numeric word_max marker ranges phase ->
 phase_numeric word_max marker ranges (operation_phase phase).
Proof. destruct phase;exact (fun N=>N). Qed.
Lemma numeric_acquisition word_max marker ranges old image root s h a result r boss :
 state_numeric word_max s -> range_numeric word_max r ->
 phase_numeric word_max marker ranges (snd (recycling_acquisition_boundary old image root s h a result r boss)).
Proof.
 intros NUM R;unfold recycling_acquisition_boundary,neutral_open_boundary;
 destruct (neutral_end_ result);try exact I;try exact NUM;apply numeric_reservation;assumption.
Qed.
Lemma numeric_recycled_extent word_max g sector r count :
 area_start g+area_length g<=2*sector+word_max ->
 area_start g+area_length g<=2*sector+1024*256 ->
 erase_geometry g sector r count ->
 range_numeric word_max (block_pages (recycle_lo r) (useful_pages r)).
Proof.
 intros WORD CAP [_ [_ [LEN [_ [[LOW HIGH] USE]]]]].
 change ((if 256*recycle_lo r+256*useful_pages r<=?word_max then
   if (256*recycle_lo r+256*useful_pages r+255)/256<=?1024 then None else Some TableCapacity
   else Some RangeOverflow)=None).
 assert (B:(256*recycle_lo r+256*useful_pages r<=?word_max)=true) by (apply Nat.leb_le;nia).
 assert (C:((256*recycle_lo r+256*useful_pages r+255)/256<=?1024)=true).
 { apply Nat.leb_le;assert ((256*recycle_lo r+256*useful_pages r+255)/256<1025)
     by (apply Nat.div_lt_upper_bound;nia). lia. }
 now rewrite B,C.
Qed.
Lemma numeric_attach_written word_max ranges image root index entry s p :
 state_numeric word_max s -> pending_preparation s=Some p -> prep_kind p=ObjectPreparation ->
 image_current_correspondence ranges image root s -> ranges entry=[prep_range p] ->
 state_numeric word_max (exact_attach ranges image index entry (data_next DataWritten s)).
Proof.
 intros NUM P KIND COR ENTRY.
 eapply numeric_exact_attach with (p:=set_phase p Written) (root:=root).
 - exact (numeric_written _ _ NUM).
 - unfold data_caller,data_next;rewrite P;cbn;split;[reflexivity|].
   exists (set_phase p Written);cbn;repeat split;auto.
 - unfold data_next;rewrite P;reflexivity.
 - unfold image_current_correspondence,data_next;rewrite P;exact COR.
 - exact ENTRY.
Qed.
Lemma numeric_close_ranges word_max views saved accept s :
 state_numeric word_max s -> Forall (Forall (range_numeric word_max)) views ->
 Forall (range_numeric word_max) saved ->
 state_numeric word_max (data_next (DataClose views saved accept) s).
Proof.
 intros [C [A [S [B [PH [ACK T]]]]]] VS SAV.
 destruct accept;unfold state_numeric,data_next;cbn;repeat split;auto;constructor.
Qed.
