From Stdlib Require Import List Arith NArith Lia Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import JournalRawOrder FreerGlobalDataTrace FreerAdmittedTrace
 FlashSpec RetentionCoverage PreparedAuthority CompactImage CompactUpdates CollectionRoots
 JournalHistory JournalReachableShape JournalRequests JournalRecoveryTrace PublicationPreparation
 PreparationOutcomes BootReconstruction TransactionBoundary PersistentBoundary DataEpisode FreerDataEpisode.
Import ListNotations.

Section Transport.
Variable g:geometry.
Variable sector:nat.
Variable data_len:N.
Variable valid:N->bool.
Variable view:nat->root_view.
Variable marker:extent.
Variable ranges:compact_entry->list extent.
Variable decode:flash->nat->option recovery_decoding.
Variable topology:recovery_decoding->bool.
Variable pages:nat.
Hypothesis G:journal_geometry g sector 256.
Hypothesis DIV:sector mod 8=0.
Hypothesis CONTRACT:recovery_local_contracts view ranges decode.
Local Notation Raw := (raw_order sector 256 data_len).
Local Notation Safe := (boundary_safe sector data_len valid view marker ranges decode pages).
Definition boundary_raw x := Raw (boundary_journal x).

Lemma journal_trace_both j j' :
 logged_invariant sector 256 data_len valid j -> Raw j ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid) j j' ->
 logged_invariant sector 256 data_len valid j' /\ Raw j'.
Proof. intros; eapply legacy_journal_trace_both; eauto. Qed.

Lemma successful_return_raw id ready out slot pubs acks :
 logged_invariant sector 256 data_len valid ready -> Raw ready ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid id)
  ready (Logged (AwaitAck out slot id) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot id) pubs acks)
  (Logged (Ready out) pubs (id::acks)) ->
 Raw (Logged (Ready out) pubs (id::acks)).
Proof. exact (legacy_successful_return_raw g sector data_len valid G DIV id ready out slot pubs acks). Qed.

Lemma publication_raw old id image index entry span s prepared ready e event next :
 logged_invariant sector 256 data_len valid ready -> Raw ready ->
 publication_execution g sector data_len valid view marker ranges old id image index entry span s prepared ready e event next ->
 boundary_raw next.
Proof. exact (legacy_publication_raw g sector data_len valid view marker ranges G DIV old id image index entry span s prepared ready e event next). Qed.

Lemma reserved_raw bytes dw bw dp bp old id d index entry span s f h a e event next :
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 Safe ((Logged (Ready f) h a,IdleBoundary old d s),e) -> Raw (Logged (Ready f) h a) ->
 ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
 erased_object_extent sector f span ->
 reserved_execution g sector data_len valid view marker ranges pages dw bw old id d index entry span s f h a e event next ->
 boundary_raw next.
Proof. exact (legacy_reserved_raw g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT bytes dw bw dp bp old id d index entry span s f h a e event next). Qed.

Lemma boundary_raw_preserves bytes dw bw dp bp x event y :
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 Safe x -> boundary_raw x ->
 boundary_step g sector data_len valid view marker ranges decode topology pages dw bw x event y -> boundary_raw y.
Proof. exact (legacy_boundary_raw_preserves g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT bytes dw bw dp bp x event y). Qed.

Theorem episode_raw_preserves x event y :
 Safe x -> boundary_raw x ->
 stationary_episode_step g sector data_len valid view marker ranges decode topology pages x event y -> boundary_raw y.
Proof.
 intros I R STEP. eapply FreerGlobalDataTrace.episode_raw_preserves; eauto.
Qed.

Theorem a11_trace_raw initial events final :
 Safe initial -> boundary_raw initial ->
 stationary_episode_trace g sector data_len valid view marker ranges decode topology pages initial events final ->
 Safe final /\ boundary_raw final.
Proof.
 intros I R TRACE. eapply episode_trace_raw; eauto.
Qed.

Theorem initialized_a11_trace_raw initial events final :
 Safe initial -> logged_reachable g sector 256 data_len valid (boundary_journal initial) ->
 stationary_episode_trace g sector data_len valid view marker ranges decode topology pages initial events final ->
 Safe final /\ boundary_raw final.
Proof.
 intros I REACH TRACE. eapply a11_trace_raw; [exact I| |exact TRACE].
 exact (reachable_journal_raw g sector 256 data_len valid _ G DIV REACH).
Qed.

Theorem admitted_a11_trace_raw bytes dw bw dp bp initial events final :
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 Safe initial -> logged_reachable g sector 256 data_len valid (boundary_journal initial) ->
 erased_episode_trace g sector data_len valid view marker ranges decode topology pages initial events final ->
 Safe final /\ boundary_raw final.
Proof.
 intros W I REACH TRACE. apply initialized_a11_trace_raw with (initial:=initial) (events:=events); auto.
 exact (erased_trace_refines g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT
   bytes dw bw dp bp W initial events final I TRACE).
Qed.

Theorem boot_raw_transport initial final :
 boot_invariant sector data_len valid view marker ranges decode pages initial ->
 Raw (boot_journal initial) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages) initial final ->
 Raw (boot_journal final).
Proof.
 intros I R T.
 destruct (boot_finite_trace g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT
  initial final I T) as [LAST PROJ].
 destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [_ [_ LOG]].
 exact (logged_trace_preserves_raw g sector 256 data_len valid _ _ G DIV (proj1 I) R LOG).
Qed.
End Transport.
