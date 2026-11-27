From Coq Require Import List Arith Bool NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage ScopeOwnership PageOwnership
 CompactUpdates CompactImage PreparedAuthority PreparationOutcomes PublicationPreparation NeutralizationBoundary RawNeutralizationBoundary
 Neutralization RecyclingSearch RecyclingErase RecyclingEraseBoundary JournalRawOrder JournalHistory JournalReachableShape JournalRequests
 TransactionBoundary PersistentBoundary DataEpisode BootReconstruction.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export BossEncodingContract.
Import ListNotations.

(* Consume the pending reservation, not a fictitious free table before reserve. *)
Theorem pending_writer_preserves_roots g sector s p boss f plan result :
 data_invariant s -> pending_preparation s=Some p -> valid_flash f ->
 writer_execution g sector (prep_range p) boss f plan result ->
 unchanged (protected_roots s) (object_flash sector f) (object_flash sector (writer_flash result)).
Proof.
 intros [[[_ AP] SUM] OWN] P V RUN.
 rewrite P in AP.
 destruct (writer_execution_locality _ _ _ _ _ _ _ V RUN) as [_ FRAME].
 intros r a IN AT. unfold object_flash; apply FRAME. intros HIT.
 assert (T:touches 256 (prep_range p) (a/256)=true).
 { apply byte_page_touched; [lia|unfold contains; lia]. }
 assert (N:needed 256 (protected_roots s) (a/256)).
 { exists r; split; [exact IN|apply byte_page_touched; [lia|exact AT]]. }
 rewrite (AP _ N) in T; discriminate.
Qed.

(* Physical effects on a live token preserve the selected certificate, even
   if the address also occurs in an older journal slot. No writer outcome is
   assumed successful, and no newly written block is assumed invalid. *)
Theorem reserved_writer_dynamic g sector data_len valid view marker ranges decode topology pages
 f h a old image root s e p boss plan result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=Some p ->
 writer_execution g sector (prep_range p) boss f plan result ->
 exists d,
 decode (object_flash sector (writer_flash result)) old=Some d /\
 unchanged (protected_roots s) (object_flash sector f) (object_flash sector (writer_flash result)) /\
 raw_order sector 256 data_len (Logged (Ready (writer_flash result)) h a) /\
 enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
  (Logged (Ready (writer_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e) /\
 episode_boot_post g sector data_len (validate (writer_flash result)) view marker ranges decode topology pages
  (logged_after_reset (Logged (Ready (writer_flash result)) h a)) (selected_evidence old d e).
Proof.
 intros G DIV C PROVIDER INITIAL RAW HEAD P RUN.
 pose proof INITIAL as [[JI [DI [FR [COR LINK]]]] [EV CERT]].
 pose proof (pending_writer_preserves_roots _ _ _ _ _ _ _ _ DI P (proj1 (proj1 JI)) RUN) as KEEP.
 pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 (proj1 JI)) RUN) as FRAME.
 pose proof (raw_writer_prefix _ _ _ _ _ _ _ _ _ _ RAW RUN) as RAW'.
 assert (PH:physical_authority s=root_extents (view old)).
 { unfold protection_history_link in LINK; simpl in LINK; rewrite HEAD in LINK; simpl in LINK.
   rewrite Nat2N.id in LINK; exact LINK. }
 destruct (proj1 (proj2 EV) old HEAD) as [[id d] [IN ID]]; simpl in ID; subst id.
 assert (READ:certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate old d)).
 { apply (proj1 (Forall_forall _ _) (proj1 EV)); exact IN. }
 destruct READ as [READ FMT].
 assert (READ':decode (object_flash sector (writer_flash result)) old=Some d).
 { rewrite <- (recovery_locality_contract _ _ _ C (object_flash sector f) (object_flash sector (writer_flash result)) old).
   - exact READ.
   - intros r x IN' AT; apply (KEEP r x); [|exact AT].
     unfold protected_roots; repeat rewrite in_app_iff; rewrite PH; tauto. }
 assert (V:validate (writer_flash result) (N.of_nat old)=true) by (eapply PROVIDER; exact READ').
 pose proof (raw_ready_revalidate sector data_len _ h a _ _ RAW' HEAD V) as NEWJI.
 assert (NEXT:enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
  (Logged (Ready (writer_flash result)) h a,OpenBoundary image root s) (selected_evidence old d e)).
 { split; [split; [exact NEWJI|simpl; auto]|]. split; [|exact I].
   split; [constructor; [split; assumption|constructor]|]. split.
   - intros id H; change (hd_error h=Some (N.of_nat id)) in H.
     assert (id=old) by (apply Nat2N.inj; congruence). subst; exists (Certificate old d); simpl; auto.
   - exact (proj2 (proj2 EV)). }
 exists d. split; [exact READ'|]. split; [exact KEEP|]. split; [exact RAW'|]. split; [exact NEXT|].
 eapply boot_entry_post; [exact G|exact DIV|exact C|].
 eapply enriched_reset; [exact G|exact DIV|exact C|exact NEXT|]. apply record_step; apply JournalReachableShape.reset_ready.
Qed.

(* These are continuations only for RETURNED outcomes. The Open frame in the
   theorem above is a proof witness, not permission to resume after reset. *)
Theorem reserved_writer_returned_cleanup s p result :
 data_invariant s -> pending_preparation s=Some p -> writer_returned_error (writer_end result) ->
 data_invariant (preparation_error_state (writer_end result) s) /\
 pending_preparation (preparation_error_state (writer_end result) s)=None /\
 physical_authority (preparation_error_state (writer_end result) s)=physical_authority s /\
 acknowledged_authority (preparation_error_state (writer_end result) s)=acknowledged_authority s.
Proof. apply preparation_error_state_preserves. Qed.

Theorem reserved_writer_ready_to_attach s p :
 data_invariant s -> protection_frozen s=false -> pending_preparation s=Some p ->
 prep_kind p=ObjectPreparation ->
 data_invariant (data_next DataWritten s) /\ data_caller DataAttach (data_next DataWritten s).
Proof.
 intros I F P KIND; split.
 - apply data_command_preserves; [exact I|]. simpl; split; [exact F|].
   exists p; split; [exact P|]. split; [exact KIND|intros BAD; discriminate].
 - unfold data_caller, data_next; rewrite P; simpl; split; [reflexivity|].
   exists (set_phase p Written); split; [reflexivity|]. split; [exact KIND|reflexivity].
Qed.

(* An explicit obstruction in the existing representation, NOT a Rust bug.
   Both current certificates and historical receipts are tied to [view id]. *)
Theorem fixed_view_forces_same_dependencies view ranges id old fresh :
 decoded_root_agrees view ranges id old -> decoded_root_agrees view ranges id fresh ->
 image_dependencies ranges (recovered_image old)=image_dependencies ranges (recovered_image fresh).
Proof. intros [_ A] [_ B]; congruence. Qed.
(* Historical obstruction of A12.g.1, now explicitly a LEGACY premise.
   It is no longer implied by receipt_valid. *)
Theorem legacy_historical_receipt_blocks_changed_dependencies view ranges h receipt fresh :
 (decoded_root_agrees view ranges (certificate_id (receipt_certificate receipt))
   (certificate_decoded (receipt_certificate receipt)) /\ receipt_valid view ranges h receipt) ->
 decoded_root_agrees view ranges (certificate_id (receipt_certificate receipt)) fresh ->
 image_dependencies ranges (recovered_image (certificate_decoded (receipt_certificate receipt)))=
 image_dependencies ranges (recovered_image fresh).
Proof. intros [OLD REST] NEW; eapply fixed_view_forces_same_dependencies; eauto. Qed.

(* Incarnation-independent selection result: only the selected old block has
   a local reader contract. No fixed interpretation of every offset is used.
   [decode] may decode completely different objects at a recycled X. *)
Theorem reused_address_not_published g sector data_len s p boss f plan result h a old decoded old_ranges (decode:flash->nat->option recovery_decoding) validate :
 data_invariant s -> pending_preparation s=Some p ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 (forall r, In r old_ranges -> In r (protected_roots s)) ->
 decode (object_flash sector f) old=Some decoded ->
 (forall after, unchanged old_ranges (object_flash sector f) (object_flash sector after) ->
   decode (object_flash sector after) old=Some decoded) ->
 (forall after, decode (object_flash sector after) old=Some decoded -> validate after (N.of_nat old)=true) ->
 writer_execution g sector (prep_range p) boss f plan result ->
 decode (object_flash sector (writer_flash result)) old=Some decoded /\
 logged_invariant sector 256 data_len (validate (writer_flash result)) (Logged (Ready (writer_flash result)) h a).
Proof.
 intros INV P RAW HEAD ROOTS READ LOCAL ACCEPT RUN.
 pose proof (pending_writer_preserves_roots _ _ _ _ _ _ _ _ INV P (proj1 (proj1 RAW)) RUN) as KEEP.
 assert (READ':decode (object_flash sector (writer_flash result)) old=Some decoded).
 { apply LOCAL. intros r x IN AT; apply (KEEP r x (ROOTS r IN) AT). }
 split; [exact READ'|]. eapply raw_ready_revalidate; [|exact HEAD|apply ACCEPT; exact READ'].
 eapply raw_writer_prefix; eauto.
Qed.

Theorem reserved_exact_attachment sector data_len valid view marker ranges decode pages j image root s e p index entry :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,OpenBoundary image root s) e ->
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> ranges entry=[prep_range p] ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (j,OpenBoundary (image_replace image index (Some entry)) []
     (exact_attach ranges image index entry (data_next DataWritten s))) e.
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] P KIND RANGE.
 destruct (reserved_writer_ready_to_attach s p DI F P KIND) as [WRITTEN CALL].
 assert (PW:pending_preparation (data_next DataWritten s)=Some (set_phase p Written)).
 { unfold data_next; rewrite P; reflexivity. }
 assert (CW:image_current_correspondence ranges image root (data_next DataWritten s)).
 { unfold image_current_correspondence, data_next; rewrite P; exact COR. }
 destruct (exact_attach_preserves ranges image root index entry (data_next DataWritten s) (set_phase p Written)
   WRITTEN CALL PW CW RANGE) as [INV IMAGE].
 split; [|split; [exact EV|exact I]]. split; [exact JI|]. split; [exact INV|]. split.
 - unfold exact_attach, replace_current_dependencies, data_next; rewrite P; reflexivity.
 - split; [exact IMAGE|]. unfold protection_history_link in *.
   unfold exact_attach, replace_current_dependencies, data_next; rewrite P; exact LINK.
Qed.

Definition writer_exit_boundary old image root s h a result :=
 let j:=Logged (Ready (writer_flash result)) h a in
 match writer_end result with
 | WriterComplete => (j,OpenBoundary image root (snapshot_written s))
 | WriterLocalError => (j,OpenBoundary image root (snapshot_error false s))
 | WriterRetainError => (j,OpenBoundary image root (snapshot_retain_error s))
 | WriterPhysicalError => (j,FrozenBoundary (N.of_nat old) (N.of_nat old) (Some root) (snapshot_error true s))
 | WriterInterrupted => (logged_after_reset j,RebuildingBoundary Selecting)
 end.

Lemma writer_exit_phase g sector data_len valid view marker ranges decode pages old image root s e p h a result :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready (writer_flash result)) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) -> pending_preparation s=Some p ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (writer_exit_boundary old image root s h a result) e.
Proof.
 intros G DIV INITIAL HEAD P.
 pose proof INITIAL as [[JI [DI [F [COR LINK]]]] [EV CERT]].
 unfold writer_exit_boundary; destruct (writer_end result).
 - split; [|split; [exact EV|exact I]]. split; [exact JI|].
   split; [eapply snapshot_written_preserves; eauto|].
   unfold snapshot_written; rewrite P. split; [reflexivity|]. split; assumption.
 - pose proof (snapshot_error_preserves s p false DI P) as [INV [SAVED [CUR ATT]]].
   split; [|split; [exact EV|exact I]]. split; [exact JI|]. split; [exact INV|].
   split; [unfold snapshot_error, data_next; rewrite P; exact F|]. split.
   + unfold image_current_correspondence in *; rewrite CUR, ATT; exact COR.
   + unfold protection_history_link, snapshot_error, data_next in *; rewrite P, F; exact LINK.
 - split; [|split; [exact EV|exact I]]. split; [exact JI|].
   split; [apply snapshot_retain_error_preserves; exact DI|]. split; [exact F|]. split; assumption.
 - pose proof (neutral_freeze_open sector data_len valid view marker ranges decode pages _ old image root s e INITIAL HEAD) as FROZEN.
   pose proof (neutralization_frozen_cleanups sector data_len valid view marker ranges decode pages
    (Logged (Ready (writer_flash result)) h a) (N.of_nat old) (Some root) (data_next DataFreeze s) e [DataDrop] FROZEN) as CLEAN.
   apply (proj1 (CLEAN ltac:(simpl; split; [exists p; exact P|exact I]))).
 - split; [|split; [exact EV|exact I]]. apply rebuilding_common.
   split.
   + eapply logged_step_preserves_invariant; [exact G|exact DIV|exact JI|].
     apply record_step; apply reset_ready.
   + split; exact I.
Qed.

Theorem reserved_writer_outcomes g sector data_len valid view marker ranges decode topology pages
 f h a old image root s e p boss plan result validate :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> validator_accepts_decoded sector decode validate ->
 enriched_invariant sector data_len valid view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
 pending_preparation s=Some p -> writer_execution g sector (prep_range p) boss f plan result ->
 exists d,
 decode (object_flash sector (writer_flash result)) old=Some d /\
 unchanged (protected_roots s) (object_flash sector f) (object_flash sector (writer_flash result)) /\
 enriched_invariant sector data_len (validate (writer_flash result)) view marker ranges decode pages
  (writer_exit_boundary old image root s h a result) (selected_evidence old d e) /\
 episode_boot_post g sector data_len (validate (writer_flash result)) view marker ranges decode topology pages
  (logged_after_reset (Logged (Ready (writer_flash result)) h a)) (selected_evidence old d e).
Proof.
 intros G DIV C PROVIDER INV RAW HEAD P RUN.
 destruct (reserved_writer_dynamic g sector data_len valid view marker ranges decode topology pages
  f h a old image root s e p boss plan result validate G DIV C PROVIDER INV RAW HEAD P RUN)
  as [d [READ [KEEP [RAW' [FRAME BOOT]]]]].
 exists d; split; [exact READ|]. split; [exact KEEP|]. split; [|exact BOOT].
 eapply writer_exit_phase; eauto.
Qed.

Theorem reserved_address_not_live s p r x :
 data_invariant s -> pending_preparation s=Some p ->
 In r (protected_roots s) -> contains (prep_range p) x -> ~ contains r x.
Proof.
 intros [[[_ AP] SUM] OWN] P IN NEW OLD; rewrite P in AP.
 assert (T:touches 256 (prep_range p) (x/256)=true) by (apply byte_page_touched; [lia|exact NEW]).
 rewrite (AP (x/256)) in T; [discriminate|].
 exists r; split; [exact IN|apply byte_page_touched; [lia|exact OLD]].
Qed.

Theorem writer_exit_no_publication_or_receipt old image root s h a result d e :
 publications (fst (writer_exit_boundary old image root s h a result))=h /\
 acknowledgements (fst (writer_exit_boundary old image root s h a result))=a /\
 client_receipts (selected_evidence old d e)=client_receipts e.
Proof. unfold writer_exit_boundary; destruct (writer_end result); repeat split; reflexivity. Qed.


(* Physical object-area header: format.rs PERSISTENCE_AREA_MAGIC, little endian.
   This observation reads the common flash; no RAM initialization bit is used. *)
Definition persistence_magic_bytes : list N :=
  [10%N;176%N;16%N;96%N;85%N;176%N;16%N;96%N].
Definition persistence_marker_recognized sector (f:flash) :=
  forall i, i<8 -> object_flash sector f i=nth i persistence_magic_bytes 255%N.
Definition persistence_marker_test sector area_len (f:flash) :=
  (8 <=? area_len) && forallb
    (fun i=>N.eqb (object_flash sector f i) (nth i persistence_magic_bytes 255%N))
    (seq 0 8).
Definition marker_header_covered (marker:extent) :=
  forall i, i<8 -> contains marker i.

Lemma persistence_marker_test_spec sector area_len f :
 persistence_marker_test sector area_len f=true <->
 8<=area_len /\ persistence_marker_recognized sector f.
Proof.
 unfold persistence_marker_test,persistence_marker_recognized.
 rewrite andb_true_iff, Nat.leb_le, forallb_forall.
 split;intros [LEN BYTES];split;[exact LEN| |exact LEN|].
 - intros i I;apply N.eqb_eq;apply BYTES;apply in_seq;lia.
 - intros i I;apply N.eqb_eq;apply BYTES;apply in_seq in I;lia.
Qed.
Lemma persistence_marker_transport sector marker before after :
 marker_header_covered marker ->
 unchanged [marker] (object_flash sector before) (object_flash sector after) ->
 persistence_marker_recognized sector before -> persistence_marker_recognized sector after.
Proof. intros COVER KEEP INIT i I;rewrite (KEEP marker i (or_introl eq_refl) (COVER i I));auto. Qed.
Lemma base_marker_protected_roots marker s :
 In marker (protection_base s) -> In marker (protected_roots s).
Proof.
 unfold protected_roots,context_ranges,surviving_ranges,context_scopes;cbn.
 repeat rewrite in_app_iff;tauto.
Qed.
Lemma base_marker_required marker s :
 In marker (protection_base s) -> In marker (required_ranges s).
Proof.
 unfold required_ranges,context_ranges,surviving_ranges,context_scopes;cbn.
 repeat rewrite in_app_iff;tauto.
Qed.
Theorem pending_writer_marker_frame g sector marker s p boss f plan result :
 data_invariant s -> In marker (protection_base s) ->
 pending_preparation s=Some p -> valid_flash f ->
 writer_execution g sector (prep_range p) boss f plan result ->
 unchanged [marker] (object_flash sector f) (object_flash sector (writer_flash result)).
Proof.
 intros INV BASE TOKEN VALID RUN r i [EQ|BAD] AT;[subst r|contradiction].
 eapply pending_writer_preserves_roots; eauto using base_marker_protected_roots.
Qed.
Theorem recycling_marker_frame g sector marker fuel recognize magic f s req round alignment pages start r count result :
 recognizer_local sector recognize -> valid_flash f ->
 protected (needed 256 (required_ranges s)) (protection_table s) ->
 In marker (protection_base s) ->
 reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
 unchanged [marker] (object_flash sector f) (object_flash sector (neutral_flash result)).
Proof.
 intros LOCAL VALID COVER BASE SEARCH GEO RUN.
 destruct (recycling_physical_handoff g sector fuel recognize magic f (protection_table s)
   req round alignment pages start r count result (required_ranges s)
   LOCAL VALID COVER SEARCH GEO RUN) as [_ [KEEP _]].
 intros ext i [EQ|BAD] AT;[subst ext|contradiction].
 apply (KEEP marker i);auto using base_marker_required.
Qed.

(* Successful initialization establishes the physical fact. The checked Rust
   geometry and marker encoder must supply the local command/payload facts. *)
Theorem marker_program_success g sector before after payload :
 (forall i,i<8 -> nth_error payload i=Some (nth i persistence_magic_bytes 255%N)) ->
 program_step g before (2*sector) payload Success after ->
 persistence_marker_recognized sector after.
Proof.
 intros ENCODE WRITE i I;unfold object_flash.
 apply (program_success_contents _ _ _ _ _ WRITE i);auto.
Qed.
Theorem journal_trace_marker g sector page data_len valid j j' :
 journal_geometry g sector page -> sector mod 8=0 ->
 logged_invariant sector page data_len valid j ->
 clos_refl_trans logged_state (logged_step g sector page data_len valid) j j' ->
 persistence_marker_recognized sector (control_image (journal_control j)) ->
 persistence_marker_recognized sector (control_image (journal_control j')).
Proof.
 intros GEO DIV INV RUN INIT i I;unfold object_flash.
 rewrite (logged_trace_frame_after_journal g sector page data_len valid j j'
   (2*sector+i) GEO DIV INV RUN ltac:(lia));exact (INIT i I).
Qed.
Lemma concrete_marker_page : marker_header_covered {|offset:=0;span:=256|}.
Proof. intros i I;unfold contains;cbn;lia. Qed.


(* Admission before reservation: freedom is used only in this pre-reserve
   table; the writer after reservation uses pending_writer_marker_frame. *)
Theorem free_writer_marker_frame g sector marker s r boss f plan result :
 data_invariant s -> In marker (protection_base s) ->
 free_range 256 (protection_table s) r -> valid_flash f ->
 writer_execution g sector r boss f plan result ->
 unchanged [marker] (object_flash sector f) (object_flash sector (writer_flash result)).
Proof.
 intros INV BASE FREE VALID RUN.
 pose proof (free_object_write_preserves sector r (required_ranges s) (protection_table s)
   f (writer_flash result) (proj1 (proj1 (proj1 INV))) FREE
   (writer_execution_locality _ _ _ _ _ _ _ VALID RUN)) as KEEP.
 intros ext i [EQ|BAD] AT;[subst ext|contradiction].
 apply (KEEP marker i);auto using base_marker_required.
Qed.

(* The encoder receives an explicit scalar. This local format contract relates
   only that argument, the command plan, and the decoded bytes on success; it
   does not choose the transaction's scalar or promise protection/recovery. *)

Definition checked_boss_plan (encode:boss_generation_plan) image counter r :=
 option_map (fun next=>encode image next r) (boss_checked_generation (counter_value counter)).

Theorem checked_boss_plan_writer g sector encode read image counter r before plan result :
 boss_generation_format g sector encode read ->
 checked_boss_plan encode image counter r=Some plan ->
 erased_object_extent sector before r ->
 writer_execution g sector r true before plan result ->
 exists next,
 boss_checked_generation (counter_value counter)=Some next /\
 next=N.succ (counter_value counter) /\ plan=encode image next r /\
 (exists suffix,plan=map fst (writer_prefix result)++suffix) /\
 terminal_prefix (writer_prefix result) /\
 (writer_end result=WriterComplete -> exists decoded n,
   read (writer_flash result) (offset r)=Some (decoded,n) /\
   recovered_boss decoded=r /\ recovered_image decoded=image /\ counter_value n=next).
Proof.
 intros FORMAT PLAN ERASED RUN.
 unfold checked_boss_plan in PLAN.
 destruct (boss_checked_generation (counter_value counter)) as [next|] eqn:NEXT;
   simpl in PLAN;try discriminate.
 inversion PLAN;subst plan.
 destruct (writer_execution_prefix _ _ _ _ _ _ _ RUN) as [PREFIX TERMINAL].
 exists next;split;[reflexivity|]. split.
 - exact (proj2 (proj1 (boss_checked_generation_success _ _) NEXT)).
 - split;[reflexivity|]. split;[exact PREFIX|]. split;[exact TERMINAL|].
   exact (FORMAT image next r before result ERASED RUN).
Qed.

(* The logical image is a slot array, not Image.entries()'s live prefix.
   A dirty Data image has passed through write_slot, which trims empty trailing
   entries. This observation does not introduce another image or a free count. *)
Fixpoint boss_live_count (image:list compact_slot) : nat :=
 match image with
 | []=>0
 | slot::tail=>match boss_live_count tail,slot with
   | 0,None=>0 | n,_=>S n end
 end.
Lemma boss_live_count_bound image : boss_live_count image<=length image.
Proof.
 induction image as [|slot tail IH];[reflexivity|].
 cbn;destruct (boss_live_count tail);destruct slot;cbn in *;lia.
Qed.
Lemma boss_live_count_written image i entry : i<length image ->
 boss_live_count (image_replace image i (Some entry))=
 Nat.max (boss_live_count image) (S i).
Proof.
 revert i;induction image as [|slot tail IH];intros [|i] B;cbn in *;try lia.
 - destruct (boss_live_count tail);destruct slot;cbn;lia.
 - rewrite IH by lia.
   destruct (boss_live_count tail);destruct slot;cbn;lia.
Qed.

Inductive boss_size_result := BossLengthRejected | BossScratchRejected (total:nat)
 | BossSizeReady (total:nat).
(* Concrete page size is 256 on this path (produced by Pages/runtime).
   checked_mul(40), checked_add(32+8), checked_add(256-1), then mask.
   Division/multiplication expresses that power-of-two mask only after its
   checked addition. The scratch constant is storage.rs's 4096. *)
Definition boss_size_preflight word_max image : boss_size_result :=
 let entries:=boss_live_count image in
 let bytes:=entries*40 in
 if bytes<=?word_max then
   if bytes+40<=?word_max then
     if bytes+40+255<=?word_max then
       let total:=((bytes+40+255)/256)*256 in
       if total<=?4096 then BossSizeReady total else BossScratchRejected total
     else BossLengthRejected
   else BossLengthRejected
 else BossLengthRejected.
Lemma boss_size_preflight_ready word_max image total :
 boss_size_preflight word_max image=BossSizeReady total ->
 total=((boss_live_count image*40+40+255)/256)*256 /\
 boss_live_count image*40+40+255<=word_max /\ total<=4096.
Proof.
 unfold boss_size_preflight.
 repeat match goal with |- context[if ?b then _ else _]=>destruct b eqn:? end;
 intro H;try discriminate;inversion H;subst;repeat split;try reflexivity;
 apply Nat.leb_le;assumption.
Qed.
Lemma boss_size_preflight_capacity word_max image :
 1024*256<=word_max -> length image<=63 ->
 exists total,boss_size_preflight word_max image=BossSizeReady total /\ total<=2560.
Proof.
 intros WORD CAP.
 pose proof (boss_live_count_bound image) as COUNT.
 assert (M:boss_live_count image*40<=word_max) by lia.
 assert (A:boss_live_count image*40+40<=word_max) by lia.
 assert (B:boss_live_count image*40+40+255<=word_max) by lia.
 assert (D:(boss_live_count image*40+40+255)/256<=10).
 { assert (LT:(boss_live_count image*40+40+255)/256<11).
   { apply Nat.div_lt_upper_bound;lia. } lia. }
 unfold boss_size_preflight.
 rewrite (proj2 (Nat.leb_le _ _) M),(proj2 (Nat.leb_le _ _) A),
   (proj2 (Nat.leb_le _ _) B).
 assert (T:((boss_live_count image*40+40+255)/256)*256<=4096) by lia.
 rewrite (proj2 (Nat.leb_le _ _) T).
 eexists;split;[reflexivity|lia].
Qed.
