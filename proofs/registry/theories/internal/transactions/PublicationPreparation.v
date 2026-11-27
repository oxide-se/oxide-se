From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec PageOwnership RetentionCoverage
  PreparedAuthority CompactUpdates CompactImage CollectionRoots JournalHistory
  JournalReachableShape JournalPhaseShape JournalRecoveryTrace JournalProtocolAuthority
  JournalIndex JournalRequests.
Import ListNotations.

(* Coordinates are the existing journal-first view, not a second flash.
   This contract is for a successful writer on an already erased reservation.
   Recycling/neutralization is NOT a local write to that reservation. *)
Definition object_write_frame sector r (before after : flash) :=
  valid_flash after /\ forall x,
    ~ (2*sector + offset r <= x < 2*sector + offset r + span r) -> after x = before x.

Lemma object_write_keeps_journal sector r before after :
  object_write_frame sector r before after ->
  forall x, x < 2*sector -> after x = before x.
Proof. intros [_ FRAME] x X; apply FRAME; lia. Qed.

Lemma ready_object_write sector page data_len boss_ok r before after history acks :
  logged_invariant sector page data_len boss_ok (Logged (Ready before) history acks) ->
  object_write_frame sector r before after ->
  logged_invariant sector page data_len boss_ok (Logged (Ready after) history acks).
Proof.
  intros [[V [SH CLEAN]] [HEAD ACK]] W.
  pose proof (object_write_keeps_journal _ _ _ _ W) as FRAME.
  assert (BYTES : sector_bytes after 0 sector = sector_bytes before 0 sector).
  { unfold sector_bytes. apply map_ext_in. intros x X. apply in_seq in X. apply FRAME; lia. }
  split.
  - split; [exact (proj1 W)|]. split.
    + unfold JournalPhaseShape.shape in *; rewrite BYTES; exact SH.
    + intros i I. rewrite FRAME by lia. apply CLEAN; exact I.
  - split; [|exact ACK]. change (observed sector page data_len boss_ok after = hd_error history).
    unfold observed; rewrite BYTES; exact HEAD.
Qed.

Lemma free_object_write_preserves sector r live table before after :
  protected (needed 256 live) table -> free_range 256 table r ->
  object_write_frame sector r before after ->
  unchanged live (object_flash sector before) (object_flash sector after).
Proof.
  intros COVER FREE [_ FRAME] v a IN RANGE. unfold object_flash. apply FRAME.
  intros HIT. apply (covered_free_range_disjoint 256 live table r a ltac:(lia)
    COVER FREE ltac:(unfold contains; lia) v IN RANGE).
Qed.

Definition prepared_transaction_candidate (view : nat -> root_view) id ranges image index entry span s :=
  materialize_candidate (boss_extent (view id))
    (modified_transaction ranges image index entry span s).

(* Same preparation/protection operations as the successful transaction proof.
   Intermediate coverage is derived here, not supplied at the publication join. *)
Lemma transaction_candidate_context view marker old id ranges image index entry span s :
  idle_root view marker old s ->
  object_extents (view old) = image_dependencies ranges image ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges image index entry span s))
    (boss_extent (view id)) ->
  object_extents (view id) = image_dependencies ranges (image_replace image index (Some entry)) ->
  let changed := modified_transaction ranges image index entry span s in
  let prepared := prepared_transaction_candidate view id ranges image index entry span s in
  data_invariant changed /\ data_invariant prepared /\
  pending_preparation prepared = None /\
  protection_current prepared ++ attached_ranges prepared = root_extents (view id) /\
  physical_authority prepared = physical_authority s /\
  protected (needed 256 (root_extents (view old))) (protection_table (data_next DataBegin s)) /\
  protected (needed 256 (root_extents (view old))) (protection_table changed).
Proof.
  intros IDLE OLD RANGE FREE BFREE ENC changed prepared.
  destruct IDLE as [I [F [S [P [CUR [BASE [AUTH ACK]]]]]]].
  assert (BEGIN : data_invariant (data_next DataBegin s)).
  { apply data_command_preserves; [exact I|]. simpl; rewrite S; simpl; repeat split; auto; lia. }
  assert (COR : image_current_correspondence ranges image [boss_extent (view old)] (data_next DataBegin s)).
  { unfold image_current_correspondence; simpl. rewrite app_nil_r, CUR.
    unfold root_extents; rewrite OLD; reflexivity. }
  destruct (exact_member_preserves ranges image [boss_extent (view old)] index entry span
    (data_next DataBegin s) BEGIN eq_refl eq_refl FREE RANGE COR) as [MI MC].
  split; [exact MI|]. split.
  - apply materialize_candidate_preserves; try reflexivity; assumption.
  - split; [reflexivity|]. split.
    + change ((boss_extent (view id) ::
        (image_dependencies ranges (image_replace image index (Some entry)) ++ [])) ++ [] = root_extents (view id)).
      rewrite !app_nil_r. unfold root_extents; rewrite ENC; reflexivity.
    + split; [reflexivity|]. split.
      * intros p NEED. apply (proj1 (proj1 (proj1 BEGIN)) p).
        destruct NEED as [r [IN T]]. exists r; split; [|exact T].
        unfold required_ranges; simpl. repeat rewrite in_app_iff. rewrite AUTH. tauto.
      * intros p NEED. apply (proj1 (proj1 (proj1 MI)) p).
        destruct NEED as [r [IN T]]. exists r; split; [|exact T].
        unfold required_ranges. repeat rewrite in_app_iff.
        right; right; left. change (In r (physical_authority s)). rewrite AUTH; exact IN.
Qed.

(* Each successful service returns the SAME physical flash subsequently consumed
   by the journal.  The second field is local encode/decode coherence for the
   just-written BOSS, not conservation of any previous root. *)
Definition erased_object_extent sector (f : flash) r :=
  forall a, contains r a -> object_flash sector f a = 255%N.

Record successful_writer_contracts sector view (data_bytes : compact_entry -> nat -> N)
    (data_writer : flash -> extent -> compact_entry -> option flash)
    (boss_writer : flash -> nat -> list compact_slot -> option flash)
    (decode : flash -> nat -> option recovery_decoding) : Prop := {
  data_writer_frame : forall f r e f', erased_object_extent sector f r -> data_writer f r e = Some f' -> object_write_frame sector r f f';
  data_writer_encoding : forall f r e f', erased_object_extent sector f r -> data_writer f r e = Some f' ->
    forall a, contains r a -> object_flash sector f' a = data_bytes e (a - offset r);
  boss_writer_frame : forall f id image f', erased_object_extent sector f (boss_extent (view id)) -> boss_writer f id image = Some f' ->
    object_write_frame sector (boss_extent (view id)) f f';
  boss_writer_read : forall f id image f', erased_object_extent sector f (boss_extent (view id)) -> boss_writer f id image = Some f' ->
    decode (object_flash sector f') id = Some (RecoveryDecoding (boss_extent (view id)) image)
}.

Theorem transaction_preparation_on_common_flash sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer decode old id image index entry span s f data_flash prepared_flash history acks old_decoded :
  journal_idle sector 256 data_len boss_ok view marker old s (Logged (Ready f) history acks) ->
  object_extents (view old) = image_dependencies ranges image ->
  ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges image index entry span s))
    (boss_extent (view id)) ->
  erased_object_extent sector f span ->
  erased_object_extent sector data_flash (boss_extent (view id)) ->
  successful_writer_contracts sector view data_bytes data_writer boss_writer decode ->
  recovery_local_contracts view ranges decode ->
  data_writer f span entry = Some data_flash ->
  boss_writer data_flash id (image_replace image index (Some entry)) = Some prepared_flash ->
  decode (object_flash sector f) old = Some old_decoded ->
  let prepared := prepared_transaction_candidate view id ranges image index entry span s in
  data_invariant prepared /\ pending_preparation prepared = None /\
  protection_current prepared ++ attached_ranges prepared = root_extents (view id) /\
  protection_history_link view prepared (Logged (Ready prepared_flash) history acks) /\
  logged_invariant sector 256 data_len boss_ok (Logged (Ready prepared_flash) history acks) /\
  hd_error history = Some (N.of_nat old) /\
  decode (object_flash sector prepared_flash) old = Some old_decoded /\
  decode (object_flash sector prepared_flash) id =
    Some (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) /\
  unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector prepared_flash).
Proof.
  intros [IDLE [J [READY [HEAD LINK]]]] OLD RANGE FREE BFREE
    ERASED_DATA ERASED_BOSS [DW DE BW BR] [FORMAT LOCAL] DATA BOSS READ prepared.
  pose proof (BR _ _ _ _ ERASED_BOSS BOSS) as NEWREAD.
  assert (ENC : object_extents (view id) = image_dependencies ranges (image_replace image index (Some entry))).
  { symmetry; exact (proj2 (FORMAT _ _ _ NEWREAD)). }
  destruct (transaction_candidate_context view marker old id ranges image index entry span s
    IDLE OLD RANGE FREE BFREE ENC) as [MI [PI [P [CUR [AUTH [C0 C1]]]]]] .
  pose proof (DW _ _ _ _ ERASED_DATA DATA) as DFRAME. pose proof (BW _ _ _ _ ERASED_BOSS BOSS) as BFRAME.
  pose proof (free_object_write_preserves sector span _ _ _ _ C0 FREE DFRAME) as DKEEP.
  pose proof (free_object_write_preserves sector (boss_extent (view id)) _ _ _ _ C1 BFREE BFRAME) as BKEEP.
  assert (KEEP : unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector prepared_flash)).
  { intros r a IN HIT. rewrite (BKEEP r a IN HIT). exact (DKEEP r a IN HIT). }
  split; [exact PI|]. split; [exact P|]. split; [exact CUR|]. split.
  - unfold protection_history_link in *. unfold prepared. rewrite AUTH. exact LINK.
  - split.
    + eapply ready_object_write; [eapply ready_object_write; eauto|exact BFRAME].
    + split; [exact HEAD|]. split.
      * rewrite <- (LOCAL _ _ old KEEP); exact READ.
      * split; [eapply BR; [exact ERASED_BOSS|exact BOSS]|exact KEEP].
Qed.

(* A value returned AFTER the existing close/collect continuation.  This is not
   the append acknowledgement in JournalHistory.  Only the normal, installed
   mask continuation is represented by this function; panic has no return. *)
Inductive data_client_result := DataClientSuccess (root : nat) (image : list compact_slot).
Definition finish_data_client view marker id ranges image index entry span s :=
  let final := data_transaction view marker id ranges image index entry span s in
  (final, DataClientSuccess id (image_replace image index (Some entry))).

(* No later physical publication: this is a recovery-only trace, with arbitrary
   journal resets. The client receipt's compact image is preserved, and the
   recovered table is fresh, not the table carried before the reset. *)
Theorem client_success_recovery g sector data_len boss_ok view marker ranges decode
    id s f history acks decoded out pubs append_acks :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  journal_idle sector 256 data_len boss_ok view marker id s (Logged (Ready f) history acks) ->
  recovery_local_contracts view ranges decode ->
  decode (object_flash sector f) id = Some decoded ->
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
    (Logged (Ready f) history acks) (Logged (Ready out) pubs append_acks) ->
  decode (object_flash sector out) id = Some decoded /\
  journal_idle sector 256 data_len boss_ok view marker id
    (rebuild_decoded marker ranges decoded) (Logged (Ready out) pubs append_acks) /\
  data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
  data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)).
Proof.
  intros G DIV [IDLE [J [READY [HEAD LINK]]]] [FORMAT LOCAL] READ TRACE.
  destruct (recovery_trace_history _ _ _ _ _ _ _ TRACE) as [H [A T]].
  assert (JI : logged_invariant sector 256 data_len boss_ok (Logged (Ready out) pubs append_acks)).
  { eapply arbitrary_finite_history_preserves_invariant; eauto. }
  assert (FRAME : unchanged (root_extents (view id)) (object_flash sector f) (object_flash sector out)).
  { intros r a IN HIT. unfold object_flash.
    exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ (2*sector+a) G DIV J T ltac:(lia)). }
  assert (READOUT : decode (object_flash sector out) id = Some decoded).
  { rewrite <- (LOCAL _ _ id FRAME); exact READ. }
  destruct (decoded_reconstruction_opens_transaction view marker ranges id decoded (FORMAT _ _ _ READOUT))
    as [BACK [COR BEGIN]].
  split; [exact READOUT|]. split; [|exact BEGIN].
  apply idle_root_links_ready; [exact BACK|exact JI|]. change (pubs = history) in H. rewrite H; exact HEAD.
Qed.

Definition publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded :=
  (* SUCCESS: actual completed append, then existing RAM/close/collect program,
     then the distinct client result. No assumed prepared invariant or read. *)
  (forall out slot pubs append_acks,
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs append_acks) ->
    logged_step g sector 256 data_len boss_ok
      (Logged (AwaitAck out slot (N.of_nat id)) pubs append_acks)
      (Logged (Ready out) pubs (N.of_nat id :: append_acks)) ->
    let result := finish_data_client view marker id ranges image index entry span s in
    snd result = DataClientSuccess id (image_replace image index (Some entry)) /\
    journal_idle sector 256 data_len boss_ok view marker id (fst result)
      (Logged (Ready out) pubs (N.of_nat id :: append_acks)) /\
    decode (object_flash sector out) id = Some
      (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) /\
    (forall recovered hs ack,
      clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
        (Logged (Ready out) pubs (N.of_nat id :: append_acks)) (Logged (Ready recovered) hs ack) ->
      let decoded := RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)) in
      decode (object_flash sector recovered) id = Some decoded /\
      journal_idle sector 256 data_len boss_ok view marker id
        (rebuild_decoded marker ranges decoded) (Logged (Ready recovered) hs ack) /\
      data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
      data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)))) /\
  (* UNCERTAIN: the same prepared flash feeds arbitrary frozen cleanup and the
     existing recovery consumer. There is deliberately no client success here. *)
  (forall error_j commands,
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) ready error_j ->
    returned_error_control (journal_control error_j) ->
    let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
    data_calls commands (uncertain_return selected prepared) ->
    let frozen := execute_data commands (uncertain_return selected prepared) in
    data_invariant frozen /\ protection_frozen frozen = true /\
    protected (needed 256 (root_extents (view old) ++ root_extents (view id))) (protection_table frozen) /\
    (forall recovered pubs append_acks,
      clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
        (logged_after_reset error_j) (Logged (Ready recovered) pubs append_acks) ->
      exists chosen decoded,
        ((chosen = old /\ decoded = old_decoded) \/
         (chosen = id /\ decoded = RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)))) /\
        journal_idle sector 256 data_len boss_ok view marker chosen
          (rebuild_decoded marker ranges decoded) (Logged (Ready recovered) pubs append_acks) /\
        data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
        data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)))).

Theorem prepared_publication_client_or_uncertain g sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer decode old id image index entry span s f data_flash prepared_flash history acks old_decoded :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  journal_idle sector 256 data_len boss_ok view marker old s (Logged (Ready f) history acks) ->
  object_extents (view old) = image_dependencies ranges image -> ranges entry = [span] ->
  free_range 256 (protection_table (data_next DataBegin s)) span ->
  free_range 256 (protection_table (modified_transaction ranges image index entry span s))
    (boss_extent (view id)) ->
  erased_object_extent sector f span ->
  erased_object_extent sector data_flash (boss_extent (view id)) ->
  successful_writer_contracts sector view data_bytes data_writer boss_writer decode ->
  recovery_local_contracts view ranges decode ->
  data_writer f span entry = Some data_flash ->
  boss_writer data_flash id (image_replace image index (Some entry)) = Some prepared_flash ->
  decode (object_flash sector f) old = Some old_decoded ->
  let prepared := prepared_transaction_candidate view id ranges image index entry span s in
  let ready := Logged (Ready prepared_flash) history acks in
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded.
Proof.
  intros G DIV IDLE OLD RANGE FREE BFREE ERASED_DATA ERASED_BOSS WRITERS CONTRACT DATA BOSS READ prepared ready.
  destruct (transaction_preparation_on_common_flash sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer decode old id image index entry span s f data_flash prepared_flash history acks old_decoded
    IDLE OLD RANGE FREE BFREE ERASED_DATA ERASED_BOSS WRITERS CONTRACT DATA BOSS READ)
    as [PI [P [CUR [LINK [J [HEAD [READOLD [READNEW KEEP]]]]]]]].
  assert (ENC : object_extents (view id) = image_dependencies ranges (image_replace image index (Some entry))).
  { destruct CONTRACT as [FORMAT LOCAL]. symmetry; exact (proj2 (FORMAT _ _ _ READNEW)). }
  split.
  - intros out slot pubs append_acks TRACE APPEND_RETURN result.
    apply successful_trace_is_logged in TRACE.
    assert (AWAIT : logged_invariant sector 256 data_len boss_ok
      (Logged (AwaitAck out slot (N.of_nat id)) pubs append_acks)).
    { eapply arbitrary_finite_history_preserves_invariant; eauto. }
    assert (JI : logged_invariant sector 256 data_len boss_ok
      (Logged (Ready out) pubs (N.of_nat id :: append_acks))).
    { eapply logged_step_preserves_invariant; eauto. }
    assert (H : hd_error pubs = Some (N.of_nat id)).
    { exact (proj2 (proj1 (proj2 AWAIT))). }
    assert (NORMAL : journal_idle sector 256 data_len boss_ok view marker id (fst result)
      (Logged (Ready out) pubs (N.of_nat id :: append_acks))).
    { apply idle_root_links_ready; [|exact JI|exact H].
      apply data_transaction_idle with (old_id:=old); try assumption. exact (proj1 IDLE). }
    assert (READOUT : decode (object_flash sector out) id = Some
      (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)))).
    { destruct CONTRACT as [FORMAT LOCAL].
      assert (FRAME : unchanged (root_extents (view id))
        (object_flash sector prepared_flash) (object_flash sector out)).
      { intros r a IN HIT. unfold object_flash.
        exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ (2*sector+a) G DIV J TRACE ltac:(lia)). }
      rewrite <- (LOCAL _ _ id FRAME); exact READNEW. }
    split; [reflexivity|]. split; [exact NORMAL|]. split; [exact READOUT|].
    intros recovered hs ack REC decoded.
    eapply client_success_recovery; eauto.
  - intros error_j commands TRACE ERROR selected CALL frozen.
    assert (CURN : protection_current prepared ++ attached_ranges prepared = root_extents (view (N.to_nat (N.of_nat id)))).
    { rewrite Nat2N.id; exact CUR. }
    assert (R0 : decode (object_flash sector prepared_flash) (N.to_nat (N.of_nat old)) = Some old_decoded).
    { rewrite Nat2N.id; exact READOLD. }
    assert (R1 : decode (object_flash sector prepared_flash) (N.to_nat (N.of_nat id)) =
      Some (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)))).
    { rewrite Nat2N.id; exact READNEW. }
    destruct (uncertain_data_transaction_safety g sector data_len boss_ok view marker ranges decode
      prepared ready error_j commands (N.of_nat old) (N.of_nat id) old_decoded
      (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry)))
      G DIV J (proj1 PI) P HEAD LINK CURN TRACE ERROR CONTRACT R0 R1 CALL)
      as [[FI [FF [FT [FL COVER]]]] [ACK [PREFIX RESTART]]].
    split; [exact FI|]. split; [exact FF|]. split.
    + rewrite !Nat2N.id in COVER; exact COVER.
    + intros recovered pubs append_acks REC.
      destruct (RESTART recovered pubs append_acks REC)
        as [chosen [decoded [CHOICE [READBACK [FRAME [IDLEBACK [COR BEGIN]]]]]]].
      rewrite !Nat2N.id in CHOICE. exists chosen, decoded.
      split; [exact CHOICE|]. split; [exact IDLEBACK|exact BEGIN].
Qed.
