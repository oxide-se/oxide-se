From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority CompactImage
  CompactUpdates CollectionRoots JournalHistory JournalReachableShape JournalRequests
  JournalRecoveryTrace PublicationPreparation PreparationOutcomes BootReconstruction.
Import ListNotations.

Section Consumers.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable area_pages : nat.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8 = 0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.

Definition restart := boot_restart_post g sector data_len boss_ok view marker ranges decode topology area_pages.

Lemma ready_authority_boot f h a old d :
  logged_invariant sector 256 data_len boss_ok (Logged (Ready f) h a) ->
  hd_error h = Some (N.of_nat old) -> decode (object_flash sector f) old = Some d ->
  restart (fun id decoded => id = old /\ decoded = d) (Logged (Boot f) h a).
Proof.
  intros J HEAD READ.
  assert (R : recovery_logged_step g sector 256 data_len boss_ok
    (Logged (Ready f) h a) (Logged (Boot f) h a)).
  { split; [exact I|]. split; [exact I|].
    apply (record_step g sector 256 data_len boss_ok (Ready f) (Boot f)); apply reset_ready. }
  assert (B : logged_invariant sector 256 data_len boss_ok (Logged (Boot f) h a)).
  { eapply logged_step_preserves_invariant; eauto. exact (proj2 (proj2 R)). }
  eapply persistent_authority_repeated_boot; try eassumption; [exact I|].
  intros id decoded HEAD' READ'. simpl in HEAD', READ'.
  assert (id = old) by (apply Nat2N.inj; congruence). subst id; split; congruence.
Qed.

Lemma prepared_failure_boot old d h a reserved saved result :
  hd_error h = Some (N.of_nat old) ->
  preparation_failed_post g sector data_len boss_ok view marker ranges decode old d h a reserved saved result ->
  restart (fun id decoded => id = old /\ decoded = d) (Logged (Boot (writer_flash result)) h a).
Proof. intros HEAD [J [READ REST]]. eapply ready_authority_boot; eauto. Qed.

(* No final RAM coverage is an input. The head alternative is derived from the
   existing uncertain publication trace; physical framing preserves both reads. *)
Lemma uncertain_authority_boot j error_j old candidate old_decoded candidate_decoded :
  logged_invariant sector 256 data_len boss_ok j ->
  hd_error (publications j) = Some (N.of_nat old) ->
  decode (object_flash sector (control_image (journal_control j))) old = Some old_decoded ->
  decode (object_flash sector (control_image (journal_control j))) candidate = Some candidate_decoded ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat candidate)) j error_j ->
  returned_error_control (journal_control error_j) ->
  restart (fun id d => (id = old /\ d = old_decoded) \/ (id = candidate /\ d = candidate_decoded))
    (logged_after_reset error_j).
Proof.
  intros J HEAD OLD NEW TRACE ERROR.
  destruct (uncertain_trace_reset_boundary _ _ _ _ _ _ _ _ G DIV J TRACE)
    as [ERRINV [CHOICE [ACK FRAME]]].
  pose proof (returned_error_reset_step g sector 256 data_len boss_ok error_j ERROR) as RESET.
  assert (I : logged_invariant sector 256 data_len boss_ok (logged_after_reset error_j)).
  { eapply logged_step_preserves_invariant; eauto. }
  assert (REC : recovering_control (journal_control (logged_after_reset error_j))).
  { destruct error_j as [c h a]; destruct c; simpl in *; try exact Logic.I. }
  eapply persistent_authority_repeated_boot; try eassumption.
  intros id d HD RD.
  assert (FLASH : control_image (journal_control (logged_after_reset error_j)) = control_image (journal_control error_j)).
  { destruct error_j as [c h a]; destruct c; reflexivity. }
  rewrite FLASH in RD.
  assert (KEEP : unchanged (root_extents (view id))
    (object_flash sector (control_image (journal_control j)))
    (object_flash sector (control_image (journal_control error_j)))).
  { intros r a IN AT. apply FRAME; lia. }
  rewrite <- (recovery_locality_contract _ _ _ CONTRACT _ _ id KEEP) in RD.
  change (hd_error (publications error_j) = Some (N.of_nat id)) in HD.
  destruct CHOICE as [C|C].
  - rewrite HEAD in C. assert (id = old) by (apply Nat2N.inj; congruence).
    subst id; left; split; congruence.
  - assert (id = candidate) by (apply Nat2N.inj; congruence).
    subst id; right; split; congruence.
Qed.

(* The branch-level consumer is obtained from the existing complete preparation
   theorem. Successful writers also supply the stronger physical entry context
   needed for uncertain publication prefixes, without a prepared-state premise. *)
Theorem prepared_transaction_repeated_boot data_bytes data_writer boss_writer data_plan boss_plan
    old candidate image index entry r s f history acks old_decoded :
  journal_idle sector 256 data_len boss_ok view marker old s (Logged (Ready f) history acks) ->
  object_extents (view old) = image_dependencies ranges image -> ranges entry = [r] ->
  free_range 256 (protection_table (data_next DataBegin s)) r -> erased_object_extent sector f r ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  decode (object_flash sector f) old = Some old_decoded ->
  let dr := data_writer f r entry in
  match writer_end dr with
  | WriterComplete => forall
      (BF : free_range 256 (protection_table (modified_transaction ranges image index entry r s)) (boss_extent (view candidate)))
      (BE : erased_object_extent sector (writer_flash dr) (boss_extent (view candidate))),
      let br := boss_writer (writer_flash dr) candidate (image_replace image index (Some entry)) in
      match writer_end br with
      | WriterComplete =>
        publication_client_continuations g sector data_len boss_ok view marker ranges decode
          old candidate image index entry r s
          (prepared_transaction_candidate view candidate ranges image index entry r s)
          (Logged (Ready (writer_flash br)) history acks) old_decoded /\
        (forall error_j,
          clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat candidate))
            (Logged (Ready (writer_flash br)) history acks) error_j ->
          returned_error_control (journal_control error_j) ->
          restart (fun id d => (id = old /\ d = old_decoded) \/
            (id = candidate /\ d = RecoveryDecoding (boss_extent (view candidate)) (image_replace image index (Some entry))))
            (logged_after_reset error_j)) /\
        (forall out slot h a,
          clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat candidate))
            (Logged (Ready (writer_flash br)) history acks) (Logged (AwaitAck out slot (N.of_nat candidate)) h a) ->
          logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat candidate)) h a)
            (Logged (Ready out) h (N.of_nat candidate :: a)) ->
          restart (fun id d => id = candidate /\
            d = RecoveryDecoding (boss_extent (view candidate)) (image_replace image index (Some entry)))
            (Logged (Boot out) h (N.of_nat candidate :: a)))
      | _ => restart (fun id d => id = old /\ d = old_decoded) (Logged (Boot (writer_flash br)) history acks)
      end
  | _ => restart (fun id d => id = old /\ d = old_decoded) (Logged (Boot (writer_flash dr)) history acks)
  end.
Proof.
  intros IDLE OLD RANGE FREE ERASED WRITERS READ dr.
  pose proof (preparation_outcomes_transaction g sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer data_plan boss_plan decode old candidate image index entry r
    s f history acks old_decoded G DIV IDLE OLD RANGE FREE ERASED WRITERS CONTRACT READ) as ALL.
  cbn zeta in ALL. fold dr in ALL.
  destruct ALL as [DRUN [DKEEP REST]].
  assert (HEAD : hd_error history = Some (N.of_nat old)) by (exact (proj1 (proj2 (proj2 (proj2 IDLE))))).
  destruct (writer_end dr) eqn:DE; try (eapply prepared_failure_boot; eauto).
  intros BF BE br. specialize (REST BF BE). cbn zeta in REST. fold br in REST. destruct REST as [BRUN [BKEEP REST]].
  destruct (writer_end br) eqn:BRE; try (eapply prepared_failure_boot; eauto).
  split; [exact REST|]. split.
  - assert (DS : successful_data_writer data_writer f r entry = Some (writer_flash dr)).
    { unfold successful_data_writer, successful_observation. change (match writer_end dr with WriterComplete => Some (writer_flash dr) | _ => None end = Some (writer_flash dr)). rewrite DE; reflexivity. }
    assert (BS : successful_boss_writer boss_writer (writer_flash dr) candidate (image_replace image index (Some entry)) = Some (writer_flash br)).
    { unfold successful_boss_writer, successful_observation. change (match writer_end br with WriterComplete => Some (writer_flash br) | _ => None end = Some (writer_flash br)). rewrite BRE; reflexivity. }
    destruct (transaction_preparation_on_common_flash sector data_len boss_ok view marker ranges
      data_bytes (successful_data_writer data_writer) (successful_boss_writer boss_writer) decode
      old candidate image index entry r s f (writer_flash dr) (writer_flash br) history acks old_decoded
      IDLE OLD RANGE FREE BF ERASED BE (writer_success_codec _ _ _ _ _ _ _ _ _ WRITERS) CONTRACT DS BS READ)
      as [PI [P [CUR [LINK [JI [HD [OR [NR KEEP]]]]]]]].
    intros error_j TRACE ERROR. eapply uncertain_authority_boot; eauto.
  - intros out slot h a TRACE APPEND.
    destruct (proj1 REST out slot h a TRACE APPEND) as [CLIENT [IDLE' [READ' REC]]].
    eapply ready_authority_boot; [exact (proj1 (proj2 IDLE'))| |exact READ'].
    exact (proj1 (proj2 (proj2 (proj2 IDLE')))).
Qed.
End Consumers.
