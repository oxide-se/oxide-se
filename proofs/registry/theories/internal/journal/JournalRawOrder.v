From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalFlashBridge JournalComplement JournalScan JournalIndex
 JournalWriteEntry JournalAppendSelection JournalRecoveryTrace JournalRequests JournalPhaseShape
 JournalReachableShape JournalProtocolAuthority JournalHistory JournalValidator PublicationPreparation PreparationOutcomes.
Import ListNotations.

(* A second observer of the SAME journal and SAME history, not a second state.
   During repair it uses phase_authority, never an unconditional FF suffix. *)
Definition raw_order sector page data_len j :=
 logged_invariant sector page data_len (fun _=>true) j.

Lemma checked_backup_raw sector page a data_len valid f :
 u32 a -> valid a=true -> backup_above_A sector a f ->
 checked_backup sector page data_len valid f=checked_backup sector page data_len (fun _=>true) f.
Proof.
 intros U VALID ABOVE. unfold checked_backup, validated_slot.
 destruct (decode_slot (flash_slot f sector) data_len (N.of_nat page)) as [id|] eqn:D; [|reflexivity].
 assert (ID : id=a).
 { eapply (validated_backup_only_requested_address (fun _=>true) a _ data_len (N.of_nat page) id U ABOVE).
   unfold validated_slot; rewrite D; reflexivity. }
 subst id; rewrite VALID; reflexivity.
Qed.

Lemma recovery_step_raw g sector page a data_len valid s s' :
 u32 a -> valid a=true -> backup_above_A sector a (flash_of s) ->
 recovery_step g sector page a data_len valid s s' ->
 recovery_step g sector page a data_len (fun _=>true) s s'.
Proof.
 intros U VALID ABOVE STEP. destruct STEP; try (constructor; assumption).
 - eapply inspect_valid; [exact H|]. rewrite <- (checked_backup_raw _ _ _ _ _ _ U VALID ABOVE); exact H0.
 - eapply inspect_invalid; [exact H|]. rewrite <- (checked_backup_raw _ _ _ _ _ _ U VALID ABOVE); exact H0.
Qed.
Lemma protocol_step_raw g sector page a data_len valid d s s' :
 u32 a -> valid a=true -> backup_above_A sector a (flash_of s) ->
 protocol_step g sector page a data_len valid d s s' ->
 protocol_step g sector page a data_len (fun _=>true) d s s'.
Proof.
 intros U VALID ABOVE STEP. destruct STEP as [s s' ROT|s s' REC].
 - apply from_rotation; exact ROT.
 - apply from_recovery; eapply recovery_step_raw; eauto.
Qed.

Lemma selected_raw_from_heads sector page data_len valid f h i a :
 observed sector page data_len (fun _=>true) f=hd_error h ->
 observed sector page data_len valid f=hd_error h ->
 selected sector page data_len valid f i a ->
 selected sector page data_len (fun _=>true) f i a.
Proof.
 intros RAW REAL SEL. unfold selected in *.
 assert (V : valid a=true) by (exact (proj2 (proj2 (latest_in_has_validated_slot _ _ _ _ _ _ SEL)))).
 unfold observed in RAW, REAL. rewrite SEL in REAL; simpl in REAL.
 destruct (latest_in_model (fun _=>true) data_len (N.of_nat page) (sector_bytes f 0 sector))
   as [[k b]|] eqn:R; simpl in RAW; [|congruence].
 assert (b=a) by congruence; subst b.
 pose proof (all_true_scan_raw _ _ _ _ _ _ R) as ORDER.
 pose proof (raw_latest_validated_selects _ _ _ _ _ _ valid ORDER V) as SAME.
 unfold latest_in_model in SEL; rewrite SEL in SAME; inversion SAME; subst k; reflexivity.
Qed.

Theorem journal_step_raw g sector page data_len valid s s' h :
 invariant sector page data_len valid s ->
 history_invariant sector page data_len valid h s ->
 history_invariant sector page data_len (fun _=>true) h s ->
 step g sector page data_len valid s s' ->
 step g sector page data_len (fun _=>true) s s'.
Proof.
 intros INV HIST RAW STEP. destruct STEP.
 - apply begin_append; [unfold candidate_valid in *; tauto|exact H0].
 - eapply begin_rotation; [unfold candidate_valid in *; tauto|exact H0|].
   exact (selected_raw_from_heads sector page data_len valid f h i a RAW HIST H1).
 - apply candidate_program; exact H.
 - apply acknowledge.
 - apply postwrite_readback_error.
 - apply boot_clean_latest.
 - apply reset_ready.
 - apply reset_before_program.
 - apply reset_before_ack.
 - apply reset_frozen.
 - apply advance_protocol; [exact H|exact H0|].
   destruct INV as [_ [[U [_ [_ V]]] [_ [[VF [AB REST]] OTHER]]]].
   eapply protocol_step_raw; eauto.
 - apply final_rotation_program; exact H.
 - apply return_from_latest.
 - apply reset_protocol.
 - apply reject_or_frozen_cleanup.
Qed.

Theorem logged_step_raw g sector page data_len valid j j' :
 logged_invariant sector page data_len valid j -> raw_order sector page data_len j ->
 logged_step g sector page data_len valid j j' ->
 logged_step g sector page data_len (fun _=>true) j j'.
Proof.
 intros [INV [HIST ACK]] [RI [RH RA]] STEP. destruct STEP.
 apply record_step. exact (journal_step_raw g sector page data_len valid s s' history INV HIST RH H).
Qed.
Theorem logged_step_preserves_raw g sector page data_len valid j j' :
 journal_geometry g sector page -> sector mod 8=0 ->
 logged_invariant sector page data_len valid j -> raw_order sector page data_len j ->
 logged_step g sector page data_len valid j j' -> raw_order sector page data_len j'.
Proof.
 intros G DIV I R STEP. exact (logged_step_preserves_invariant g sector page data_len (fun _=>true) G DIV j j' R
   (logged_step_raw g sector page data_len valid j j' I R STEP)).
Qed.
Theorem logged_trace_preserves_raw g sector page data_len valid j j' :
 journal_geometry g sector page -> sector mod 8=0 ->
 logged_invariant sector page data_len valid j -> raw_order sector page data_len j ->
 clos_refl_trans logged_state (logged_step g sector page data_len valid) j j' ->
 raw_order sector page data_len j'.
Proof.
 intros G DIV I R TRACE. revert I R; induction TRACE; intros I R.
 - exact (logged_step_preserves_raw g sector page data_len valid x y G DIV I R H).
 - exact R.
 - apply IHTRACE2; [eapply arbitrary_finite_history_preserves_invariant; eauto|apply IHTRACE1; assumption].
Qed.
Theorem reachable_journal_raw g sector page data_len valid j :
 journal_geometry g sector page -> sector mod 8=0 ->
 logged_reachable g sector page data_len valid j -> raw_order sector page data_len j.
Proof.
 intros G DIV [f [INIT TRACE]].
 assert (REACH : logged_reachable g sector page data_len valid (Logged (Boot f) [] [])).
 { exists f; split; [exact INIT|apply rt_refl]. }
 eapply logged_trace_preserves_raw; [exact G|exact DIV| | |exact TRACE].
 - eapply logged_reachable_invariant; eauto.
 - apply (logged_reachable_invariant g sector page data_len (fun _=>true) G DIV).
   exists f; split; [exact INIT|apply rt_refl].
Qed.

Theorem ready_raw_witness sector page data_len f h a id :
 raw_order sector page data_len (Logged (Ready f) h a) -> hd_error h=Some id ->
 exists index, raw_latest_witness (sector_bytes f 0 sector) data_len (N.of_nat page)
  (length (sector_bytes f 0 sector)/8) index id.
Proof.
 intros [_ [HIST ACK]] HEAD. cbn [history_invariant journal_control publications] in HIST.
 unfold observed in HIST; rewrite HEAD in HIST.
 destruct (latest_in_model (fun _=>true) data_len (N.of_nat page) (sector_bytes f 0 sector))
 as [[index found]|] eqn:SCAN; simpl in HIST; [|discriminate].
 inversion HIST; subst found. exists index; apply all_true_scan_raw; exact SCAN.
Qed.

Lemma raw_frame_ready sector page data_len f f' h a r :
 raw_order sector page data_len (Logged (Ready f) h a) ->
 PublicationPreparation.object_write_frame sector r f f' ->
 raw_order sector page data_len (Logged (Ready f') h a).
Proof. exact (PublicationPreparation.ready_object_write sector page data_len (fun _=>true) r f f' h a). Qed.

Theorem validator_gap_excluded index :
 ~ raw_latest_witness validator_gap_slots 8192 256 2 index 256.
Proof.
 intro RAW. pose proof (raw_latest_validated_selects _ _ _ _ _ _ (fun _=>true) RAW eq_refl) as SELECT.
 rewrite validator_gap_after in SELECT; discriminate.
Qed.

Lemma raw_writer_prefix g sector data_len span boss f plan result h a :
 raw_order sector 256 data_len (Logged (Ready f) h a) ->
 PreparationOutcomes.writer_execution g sector span boss f plan result ->
 raw_order sector 256 data_len (Logged (Ready (PreparationOutcomes.writer_flash result)) h a).
Proof.
 intros RAW RUN. eapply raw_frame_ready; [exact RAW|].
 eapply PreparationOutcomes.writer_execution_locality; [exact (proj1 (proj1 RAW))|exact RUN].
Qed.
