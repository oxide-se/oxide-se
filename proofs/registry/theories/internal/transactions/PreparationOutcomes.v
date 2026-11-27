From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import Types FlashSpec PageOwnership RetentionCoverage
  ScopeOwnership PreparedAuthority CompactImage CompactUpdates CollectionRoots
  JournalHistory JournalReachableShape JournalRequests PublicationPreparation.
Import ListNotations.

Record writer_command := WriterCommand { command_address : nat; command_bytes : list N }.
Inductive writer_termination := WriterComplete | WriterLocalError | WriterRetainError
  | WriterPhysicalError | WriterInterrupted.
(* An observation of a terminated execution, NOT a return value delivered after
   reset. The interrupted constructor has no continuation in writer_execution. *)
Record writer_observation := WriterObservation {
  writer_flash : flash;
  writer_prefix : list (writer_command * outcome);
  writer_end : writer_termination
}.
Definition command_in_reservation sector r c :=
  2*sector + offset r <= command_address c /\
  command_address c + length (command_bytes c) <= 2*sector + offset r + span r.

Inductive writer_execution g sector r (boss : bool) :
    flash -> list writer_command -> writer_observation -> Prop :=
| writer_completed f : writer_execution g sector r boss f [] (WriterObservation f [] WriterComplete)
| writer_local_error f plan :
    writer_execution g sector r boss f plan (WriterObservation f [] WriterLocalError)
| writer_retain_error f : boss = true ->
    writer_execution g sector r boss f [] (WriterObservation f [] WriterRetainError)
| writer_reset_between f plan :
    writer_execution g sector r boss f plan (WriterObservation f [] WriterInterrupted)
| writer_failed_command f c tail after :
    command_in_reservation sector r c ->
    program_step g f (command_address c) (command_bytes c) VerifyFailed after ->
    writer_execution g sector r boss f (c::tail)
      (WriterObservation after [(c,VerifyFailed)] WriterPhysicalError)
| writer_reset_command f c tail after :
    command_in_reservation sector r c ->
    program_step g f (command_address c) (command_bytes c) Reset after ->
    writer_execution g sector r boss f (c::tail)
      (WriterObservation after [(c,Reset)] WriterInterrupted)
| writer_successful_command f c tail after result :
    command_in_reservation sector r c ->
    program_step g f (command_address c) (command_bytes c) Success after ->
    writer_execution g sector r boss after tail result ->
    writer_execution g sector r boss f (c::tail)
      (WriterObservation (writer_flash result) ((c,Success)::writer_prefix result) (writer_end result)).

Lemma writer_command_frame g sector r c before after result :
  command_in_reservation sector r c ->
  program_step g before (command_address c) (command_bytes c) result after ->
  forall x, ~ (2*sector+offset r <= x < 2*sector+offset r+span r) -> after x = before x.
Proof.
  intros [LO HI] STEP x OUT. apply (program_locality _ _ _ _ _ _ STEP).
  destruct (Nat.lt_ge_cases x (command_address c)) as [LT|GE].
  - left; exact LT.
  - right. assert (LOW : 2*sector+offset r <= x) by lia.
    assert (UP : 2*sector+offset r+span r <= x).
    { apply Nat.nlt_ge. intro U; apply OUT; split; assumption. }
    exact (Nat.le_trans _ _ _ HI UP).
Qed.

Theorem writer_execution_locality g sector r boss before plan result :
  valid_flash before -> writer_execution g sector r boss before plan result ->
  object_write_frame sector r before (writer_flash result).
Proof.
  intros VALID RUN. induction RUN.
  - split; [exact VALID|intros; reflexivity].
  - split; [exact VALID|intros; reflexivity].
  - split; [exact VALID|intros; reflexivity].
  - split; [exact VALID|intros; reflexivity].
  - split; [eapply program_step_preserves_valid_flash; eauto|eapply writer_command_frame; eauto].
  - split; [eapply program_step_preserves_valid_flash; eauto|eapply writer_command_frame; eauto].
  - assert (V : valid_flash after) by (eapply program_step_preserves_valid_flash; eauto).
    destruct (IHRUN V) as [LAST FRAME]. split; [exact LAST|].
    intros x OUT. simpl. rewrite (FRAME x OUT). eapply writer_command_frame; eauto.
Qed.

(* The recorded list is a real prefix of the supplied command order. A Reset or
   VerifyFailed is terminal; successes before a local error remain in the log. *)
Definition terminal_prefix (events : list (writer_command * outcome)) :=
  Forall (fun e => snd e = Success) events \/
  exists successes c result, Forall (fun e => snd e = Success) successes /\
    result <> Success /\ events = successes ++ [(c,result)].
Theorem writer_execution_prefix g sector r boss before plan result :
  writer_execution g sector r boss before plan result ->
  (exists suffix, plan = map fst (writer_prefix result) ++ suffix) /\
  terminal_prefix (writer_prefix result).
Proof.
  intros RUN; induction RUN; simpl.
  - split; [exists []; reflexivity|left; constructor].
  - split; [exists plan; reflexivity|left; constructor].
  - split; [exists []; reflexivity|left; constructor].
  - split; [exists plan; reflexivity|left; constructor].
  - split; [exists tail; reflexivity|right; exists [], c, VerifyFailed; repeat split; try constructor; discriminate].
  - split; [exists tail; reflexivity|right; exists [], c, Reset; repeat split; try constructor; discriminate].
  - destruct IHRUN as [[suffix PLAN] LAST]. split; [exists suffix; simpl; congruence|].
    destruct LAST as [ALL|[successes [d [res [ALL [NE EQ]]]]]].
    + left; constructor; [reflexivity|exact ALL].
    + right; exists ((c,Success)::successes), d, res.
      split; [constructor; auto|]. split; [exact NE|simpl; congruence].
Qed.

Definition preparation_error_state end_ s := match end_ with
  | WriterPhysicalError => snapshot_error true s
  | WriterLocalError => snapshot_error false s
  | WriterRetainError => snapshot_retain_error s
  | WriterComplete | WriterInterrupted => s end.
Definition writer_returned_error end_ :=
  end_ = WriterLocalError \/ end_ = WriterRetainError \/ end_ = WriterPhysicalError.
Theorem preparation_error_state_preserves s p end_ :
  data_invariant s -> pending_preparation s = Some p -> writer_returned_error end_ ->
  data_invariant (preparation_error_state end_ s) /\
  pending_preparation (preparation_error_state end_ s) = None /\
  physical_authority (preparation_error_state end_ s) = physical_authority s /\
  acknowledged_authority (preparation_error_state end_ s) = acknowledged_authority s.
Proof.
  intros INV P [E|[E|E]]; subst end_; simpl.
  - split; [exact (proj1 (snapshot_error_preserves s p false INV P))|]. repeat split; reflexivity.
  - split; [apply snapshot_retain_error_preserves; exact INV|]. repeat split; reflexivity.
  - split; [exact (proj1 (snapshot_error_preserves s p true INV P))|]. repeat split; reflexivity.
Qed.

Definition data_reservation_state r s := data_next (DataReserve r) (data_next DataBegin s).
Definition boss_reservation_state (view : nat -> root_view) id ranges image index entry r s :=
  snapshot_reserve (boss_extent (view id)) (modified_transaction ranges image index entry r s).
Definition preparation_rollback saved end_ reserved :=
  data_next (DataClose [] saved false) (preparation_error_state end_ reserved).

Lemma preparation_entry_context view marker old ranges image index entry r s :
  idle_root view marker old s ->
  object_extents (view old) = image_dependencies ranges image -> ranges entry = [r] ->
  free_range 256 (protection_table (data_next DataBegin s)) r ->
  data_invariant (data_reservation_state r s) /\
  data_invariant (modified_transaction ranges image index entry r s) /\
  protected (needed 256 (root_extents (view old))) (protection_table (data_next DataBegin s)) /\
  protected (needed 256 (root_extents (view old)))
    (protection_table (modified_transaction ranges image index entry r s)).
Proof.
  intros [I [F [STACK [P [CUR [BASE [AUTH ACK]]]]]]] OLD RANGE FREE.
  assert (BEGIN : data_invariant (data_next DataBegin s)).
  { apply data_command_preserves; [exact I|]. simpl; rewrite STACK; simpl; repeat split; auto; lia. }
  assert (COR : image_current_correspondence ranges image [boss_extent (view old)] (data_next DataBegin s)).
  { unfold image_current_correspondence; simpl; rewrite app_nil_r, CUR.
    unfold root_extents; rewrite OLD; reflexivity. }
  destruct (exact_member_preserves ranges image [boss_extent (view old)] index entry r
    (data_next DataBegin s) BEGIN eq_refl eq_refl FREE RANGE COR) as [MI MC].
  split.
  - apply data_command_preserves; [exact BEGIN|]. simpl; repeat split; auto.
  - split; [exact MI|]. split.
    + intros p [v [IN T]]. apply (proj1 (proj1 (proj1 BEGIN)) p).
      exists v; split; [|exact T]. unfold required_ranges; simpl.
      repeat rewrite in_app_iff; rewrite AUTH; tauto.
    + intros p [v [IN T]]. apply (proj1 (proj1 (proj1 MI)) p).
      exists v; split; [|exact T]. unfold required_ranges; repeat rewrite in_app_iff.
      right; right; left. change (In v (physical_authority s)). rewrite AUTH; exact IN.
Qed.

Lemma preparation_error_rollback s p saved end_ :
  data_invariant s -> pending_preparation s = Some p ->
  protection_saved s = [saved] -> writer_returned_error end_ ->
  data_invariant (preparation_rollback saved end_ s) /\
  protection_current (preparation_rollback saved end_ s) = saved /\
  protection_saved (preparation_rollback saved end_ s) = [] /\
  physical_authority (preparation_rollback saved end_ s) = physical_authority s /\
  acknowledged_authority (preparation_rollback saved end_ s) = acknowledged_authority s /\
  (end_ = WriterPhysicalError ->
    protection_frozen (preparation_rollback saved end_ s) = true /\
    protection_table (preparation_rollback saved end_ s) = protection_table s).
Proof.
  intros INV P STACK ERROR.
  destruct (preparation_error_state_preserves s p end_ INV P ERROR) as [EI [EP [PH ACK]]].
  assert (SAVED : protection_saved (preparation_error_state end_ s) = [saved]).
  { destruct ERROR as [E|[E|E]]; subst end_; exact STACK. }
  split.
  - apply data_command_preserves; [exact EI|]. split; [exact EP|exact SAVED].
  - split; [reflexivity|]. split; [reflexivity|]. split; [exact PH|]. split; [exact ACK|].
    intro E; subst end_; split; reflexivity.
Qed.

(* Mask construction finishes before any table replacement. Failure is fatal
   only when the collect guard actually enabled the operation. *)
Definition preparation_collection old resolved s :=
  if collection_enabled true (Some old) (Some old) s then
    match resolved with
    | Some mask => install_collection 256 mask s
    | None => data_next DataFreeze s
    end
  else s.

Lemma preparation_collection_preserves view marker old saved end_ reserved p resolved :
  data_invariant reserved -> pending_preparation reserved = Some p ->
  protection_saved reserved = [saved] -> writer_returned_error end_ ->
  saved = root_extents (view old) ->
  protection_base reserved = marker :: root_extents (view old) ->
  physical_authority reserved = root_extents (view old) ->
  acknowledged_authority reserved = root_extents (view old) ->
  (forall mask, resolved = Some mask ->
    mask = collect_ranges view marker (Some old) (object_extents (view old)) []) ->
  let rolled := preparation_rollback saved end_ reserved in
  data_invariant (preparation_collection old resolved rolled) /\
  physical_authority (preparation_collection old resolved rolled) = root_extents (view old).
Proof.
  intros I P S E C B PH ACK MASK rolled.
  destruct (preparation_error_rollback reserved p saved end_ I P S E)
    as [RI [RC [RS [RP [RA RF]]]]].
  assert (PN : pending_preparation rolled = None) by reflexivity.
  assert (BOUND : collection_boundary view marker (Some old) (Some old)
    (object_extents (view old)) [] rolled).
  { unfold collection_boundary. split.
    - change (saved ++ [] = root_extents (view old)). rewrite app_nil_r; exact C.
    - split; [destruct E as [E|[E|E]]; subst end_; exact B|].
      split; [unfold rolled; rewrite RP; exact PH|].
      split; [unfold rolled; rewrite RA; exact ACK|].
      split; [reflexivity|]. unfold current_agrees; intros x EQ; inversion EQ; reflexivity. }
  pose proof (idle_collection_restores_data true view marker (Some old) (Some old)
    (object_extents (view old)) rolled resolved RI RS PN BOUND MASK) as CI.
  assert (PA : physical_authority rolled = root_extents (view old)) by (unfold rolled; rewrite RP; exact PH).
  unfold preparation_collection. unfold collection_return in CI.
  destruct (collection_enabled true (Some old) (Some old) rolled); [destruct resolved|];
    split; try exact CI; try exact PA.
  apply data_command_preserves; [exact RI|exact Logic.I].
Qed.

Definition prepublication_recovery_post g sector data_len boss_ok view marker ranges decode
    old old_decoded reached history acks :=
  forall out pubs append_acks,
    clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
      (Logged (Boot reached) history acks) (Logged (Ready out) pubs append_acks) ->
    decode (object_flash sector out) old = Some old_decoded /\
    journal_idle sector 256 data_len boss_ok view marker old
      (rebuild_decoded marker ranges old_decoded) (Logged (Ready out) pubs append_acks) /\
    data_caller DataBegin (rebuild_decoded marker ranges old_decoded) /\
    data_invariant (data_next DataBegin (rebuild_decoded marker ranges old_decoded)).

Lemma prepublication_recovery g sector data_len boss_ok view marker ranges decode old old_decoded reached history acks :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok (Logged (Ready reached) history acks) ->
  hd_error history = Some (N.of_nat old) ->
  recovery_local_contracts view ranges decode ->
  decode (object_flash sector reached) old = Some old_decoded ->
  prepublication_recovery_post g sector data_len boss_ok view marker ranges decode old old_decoded reached history acks.
Proof.
  intros G DIV J HEAD CONTRACT READ out pubs append_acks REC.
  pose proof CONTRACT as [FORMAT LOCAL].
  destruct (decoded_reconstruction_opens_transaction view marker ranges old old_decoded (FORMAT _ _ _ READ))
    as [IDLE [COR BEGIN]].
  assert (ENTRY : journal_idle sector 256 data_len boss_ok view marker old
    (rebuild_decoded marker ranges old_decoded) (Logged (Ready reached) history acks)).
  { apply idle_root_links_ready; assumption. }
  eapply client_success_recovery; [exact G|exact DIV|exact ENTRY|exact CONTRACT|exact READ|].
  eapply rt_trans; [apply rt_step|exact REC].
  split; [exact I|]. split; [exact I|].
  apply (record_step g sector 256 data_len boss_ok (Ready reached) (Boot reached) history acks).
  apply reset_ready.
Qed.

Definition preparation_failed_post g sector data_len boss_ok view marker ranges decode
    old old_decoded history acks reserved saved result :=
  logged_invariant sector 256 data_len boss_ok (Logged (Ready (writer_flash result)) history acks) /\
  decode (object_flash sector (writer_flash result)) old = Some old_decoded /\
  terminal_prefix (writer_prefix result) /\
  data_invariant reserved /\
  (writer_returned_error (writer_end result) ->
    let rolled := preparation_rollback saved (writer_end result) reserved in
    data_invariant rolled /\ protection_current rolled = saved /\
    protection_saved rolled = [] /\
    protected (needed 256 (root_extents (view old))) (protection_table rolled) /\
    (writer_end result = WriterPhysicalError -> protection_frozen rolled = true /\
      protection_table rolled = protection_table reserved) /\
    (forall commands, data_calls commands rolled ->
      data_invariant (execute_data commands rolled) /\
      physical_authority (execute_data commands rolled) = root_extents (view old)) /\
    (forall resolved,
      (forall mask, resolved = Some mask ->
        mask = collect_ranges view marker (Some old) (object_extents (view old)) []) ->
      data_invariant (preparation_collection old resolved rolled) /\
      physical_authority (preparation_collection old resolved rolled) = root_extents (view old))) /\
  prepublication_recovery_post g sector data_len boss_ok view marker ranges decode
    old old_decoded (writer_flash result) history acks.

Lemma writer_exit_composes g sector data_len boss_ok view marker ranges decode
    old old_decoded history acks before table r boss plan result reserved saved p :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok (Logged (Ready before) history acks) ->
  hd_error history = Some (N.of_nat old) ->
  recovery_local_contracts view ranges decode -> decode (object_flash sector before) old = Some old_decoded ->
  protected (needed 256 (root_extents (view old))) table -> free_range 256 table r ->
  data_invariant reserved -> pending_preparation reserved = Some p ->
  protection_saved reserved = [saved] -> physical_authority reserved = root_extents (view old) ->
  saved = root_extents (view old) ->
  protection_base reserved = marker :: root_extents (view old) ->
  acknowledged_authority reserved = root_extents (view old) ->
  writer_execution g sector r boss before plan result ->
  preparation_failed_post g sector data_len boss_ok view marker ranges decode
    old old_decoded history acks reserved saved result.
Proof.
  intros G DIV J HEAD CONTRACT READ COVER FREE INV P STACK AUTH SAVED BASE ACK RUN.
  pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 (proj1 J)) RUN) as FRAME.
  pose proof (ready_object_write _ _ _ _ _ _ _ _ _ J FRAME) as JNEW.
  pose proof (free_object_write_preserves _ _ _ _ _ _ COVER FREE FRAME) as KEEP.
  assert (READNEW : decode (object_flash sector (writer_flash result)) old = Some old_decoded).
  { destruct CONTRACT as [FORMAT LOCAL]. rewrite <- (LOCAL _ _ old KEEP); exact READ. }
  split; [exact JNEW|]. split; [exact READNEW|]. split.
  - exact (proj2 (writer_execution_prefix _ _ _ _ _ _ _ RUN)).
  - split; [exact INV|]. split.
    + intros ERROR rolled.
      destruct (preparation_error_rollback reserved p saved (writer_end result) INV P STACK ERROR)
        as [RI [RC [RS [RP [RA RF]]]]].
      assert (RAUTH : physical_authority rolled = root_extents (view old)) by (unfold rolled; rewrite RP; exact AUTH).
      split; [exact RI|]. split; [exact RC|]. split; [exact RS|]. split.
      * intros q [v [IN T]]. apply (proj1 (proj1 (proj1 RI)) q).
        exists v; split; [|exact T]. unfold required_ranges; repeat rewrite in_app_iff.
        right; right; left. change (In v (physical_authority rolled)). rewrite RAUTH; exact IN.
      * split; [exact RF|]. split.
        -- intros commands CALL. split.
           ++ apply data_execution_preserves; assumption.
           ++ rewrite (proj1 (data_execution_no_publication commands rolled)); exact RAUTH.
        -- intros resolved MASK. eapply preparation_collection_preserves; eauto.
    + eapply prepublication_recovery; eauto.
Qed.

(* The old option-valued service is now only a compatibility projection for the
   successful consumer. Failed/reset observations retain their reached flash and
   full command prefix in the primary interface. No continuation uses this
   projection after an interrupted observation. *)
Definition successful_observation result := match writer_end result with
  | WriterComplete => Some (writer_flash result) | _ => None end.
Definition successful_data_writer (writer : flash -> extent -> compact_entry -> writer_observation) := fun f r e => successful_observation (writer f r e).
Definition successful_boss_writer (writer : flash -> nat -> list compact_slot -> writer_observation) := fun f id image => successful_observation (writer f id image).

Record outcome_writer_contracts g sector view data_bytes
    (data_writer : flash -> extent -> compact_entry -> writer_observation)
    (boss_writer : flash -> nat -> list compact_slot -> writer_observation)
    (data_plan : flash -> extent -> compact_entry -> list writer_command)
    (boss_plan : flash -> nat -> list compact_slot -> list writer_command)
    (decode : flash -> nat -> option recovery_decoding) : Prop := {
  data_writer_execution : forall f r e,
    writer_execution g sector r false f (data_plan f r e) (data_writer f r e);
  boss_writer_execution : forall f id image,
    writer_execution g sector (boss_extent (view id)) true f (boss_plan f id image) (boss_writer f id image);
  writer_success_codec : successful_writer_contracts sector view data_bytes
    (successful_data_writer data_writer) (successful_boss_writer boss_writer) decode
}.

Theorem preparation_outcomes_transaction g sector data_len boss_ok view marker ranges
    data_bytes data_writer boss_writer data_plan boss_plan decode old id image index entry r
    s f history acks old_decoded :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  journal_idle sector 256 data_len boss_ok view marker old s (Logged (Ready f) history acks) ->
  object_extents (view old) = image_dependencies ranges image -> ranges entry = [r] ->
  free_range 256 (protection_table (data_next DataBegin s)) r ->
  erased_object_extent sector f r ->
  outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode ->
  recovery_local_contracts view ranges decode ->
  decode (object_flash sector f) old = Some old_decoded ->
  let data_result := data_writer f r entry in
  let saved := protection_current s ++ attached_ranges s in
  writer_execution g sector r false f (data_plan f r entry) data_result /\
  unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector (writer_flash data_result)) /\
  match writer_end data_result with
  | WriterComplete =>
      forall (FREE_BOSS : free_range 256
        (protection_table (modified_transaction ranges image index entry r s)) (boss_extent (view id)))
        (ERASED_BOSS : erased_object_extent sector (writer_flash data_result) (boss_extent (view id))),
      let boss_result := boss_writer (writer_flash data_result) id (image_replace image index (Some entry)) in
      writer_execution g sector (boss_extent (view id)) true (writer_flash data_result)
        (boss_plan (writer_flash data_result) id (image_replace image index (Some entry))) boss_result /\
      unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector (writer_flash boss_result)) /\
      match writer_end boss_result with
      | WriterComplete =>
          publication_client_continuations g sector data_len boss_ok view marker ranges decode
            old id image index entry r s
            (prepared_transaction_candidate view id ranges image index entry r s)
            (Logged (Ready (writer_flash boss_result)) history acks) old_decoded
      | _ => preparation_failed_post g sector data_len boss_ok view marker ranges decode
          old old_decoded history acks
          (boss_reservation_state view id ranges image index entry r s) saved boss_result
      end
  | _ => preparation_failed_post g sector data_len boss_ok view marker ranges decode
      old old_decoded history acks (data_reservation_state r s) saved data_result
  end.
Proof.
  intros G DIV IDLE OLD RANGE FREE ERASED [DRUN BRUN CODEC] CONTRACT READ data_result saved.
  pose proof IDLE as [ROOT [J [READY [HEAD LINK]]]].
  pose proof ROOT as [I [F [STACK [P [CUR [BASE [AUTH ACK]]]]]]].
  destruct (preparation_entry_context view marker old ranges image index entry r s ROOT OLD RANGE FREE)
    as [DI [MI [C0 C1]]].
  assert (D : writer_execution g sector r false f (data_plan f r entry) data_result) by apply DRUN.
  assert (DFRAME : object_write_frame sector r f (writer_flash data_result)).
  { apply (writer_execution_locality _ _ _ _ _ _ _ (proj1 (proj1 J)) D). }
  assert (DJ : logged_invariant sector 256 data_len boss_ok
    (Logged (Ready (writer_flash data_result)) history acks)).
  { eapply ready_object_write; eauto. }
  assert (DREAD : decode (object_flash sector (writer_flash data_result)) old = Some old_decoded).
  { pose proof (free_object_write_preserves _ _ _ _ _ _ C0 FREE DFRAME) as KEEP.
    destruct CONTRACT as [FORMAT LOCAL]. rewrite <- (LOCAL _ _ old KEEP); exact READ. }
  assert (DFAIL : preparation_failed_post g sector data_len boss_ok view marker ranges decode
    old old_decoded history acks (data_reservation_state r s) saved data_result).
  { eapply writer_exit_composes with (p:=Build_preparation ObjectPreparation r Reserved)
      (table:=protection_table (data_next DataBegin s)) (before:=f) (boss:=false) (plan:=data_plan f r entry); try eassumption; try reflexivity.
    - change (protection_saved s ++ [saved] = [saved]); rewrite STACK; reflexivity. }
  assert (DKEEP : unchanged (root_extents (view old)) (object_flash sector f)
    (object_flash sector (writer_flash data_result))) by (exact (free_object_write_preserves _ _ _ _ _ _ C0 FREE DFRAME)).
  split; [exact D|]. split; [exact DKEEP|]. destruct (writer_end data_result) eqn:DE; try exact DFAIL.
  intros FREE_BOSS ERASED_BOSS boss_result.
  assert (B : writer_execution g sector (boss_extent (view id)) true (writer_flash data_result)
    (boss_plan (writer_flash data_result) id (image_replace image index (Some entry))) boss_result) by apply BRUN.
  assert (BI : data_invariant (boss_reservation_state view id ranges image index entry r s)).
  { apply snapshot_reserve_preserves; try reflexivity; assumption. }
  assert (BFAIL : preparation_failed_post g sector data_len boss_ok view marker ranges decode
    old old_decoded history acks (boss_reservation_state view id ranges image index entry r s) saved boss_result).
  { eapply writer_exit_composes with (p:=Build_preparation BossPreparation (boss_extent (view id)) Reserved)
      (table:=protection_table (modified_transaction ranges image index entry r s))
      (before:=writer_flash data_result) (boss:=true)
      (plan:=boss_plan (writer_flash data_result) id (image_replace image index (Some entry))); try eassumption; try reflexivity.
    - change (protection_saved s ++ [saved] = [saved]); rewrite STACK; reflexivity. }
  assert (BKEEP : unchanged (root_extents (view old)) (object_flash sector (writer_flash data_result))
    (object_flash sector (writer_flash boss_result))).
  { eapply free_object_write_preserves; [exact C1|exact FREE_BOSS|].
    eapply writer_execution_locality; [exact (proj1 (proj1 DJ))|exact B]. }
  split; [exact B|]. split.
  { intros v a IN AT. rewrite (BKEEP v a IN AT). exact (DKEEP v a IN AT). }
  destruct (writer_end boss_result) eqn:BE; try exact BFAIL.
  eapply (prepared_publication_client_or_uncertain g sector data_len boss_ok view marker ranges
    data_bytes (successful_data_writer data_writer) (successful_boss_writer boss_writer) decode
    old id image index entry r s f (writer_flash data_result) (writer_flash boss_result) history acks old_decoded);
    try eassumption.
  - unfold successful_data_writer, successful_observation. change (match writer_end data_result with
      | WriterComplete => Some (writer_flash data_result) | _ => None end = Some (writer_flash data_result)).
    rewrite DE; reflexivity.
  - unfold successful_boss_writer, successful_observation. change (match writer_end boss_result with
      | WriterComplete => Some (writer_flash boss_result) | _ => None end = Some (writer_flash boss_result)).
    rewrite BE; reflexivity.
Qed.
