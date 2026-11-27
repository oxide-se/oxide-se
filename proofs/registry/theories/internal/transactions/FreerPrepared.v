From Stdlib Require Import List.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import PreparedAuthority ScopeOwnership
  RetentionCoverage PageOwnership FlashSpec FreerFlash FreerRetention CompactUpdates CompactImage.

Inductive PreparationAPI : interface :=
| WithdrawLoad : PreparationAPI unit.
Definition preparation_caller (s : protection_state) (A : Type) (e : PreparationAPI A) :=
  protection_frozen s = false /\ exists p,
    pending_preparation s = Some p /\ prep_kind p = LoadPreparation /\ prep_phase p = Written.
Definition preparation_callee (s : protection_state) (A : Type)
    (e : PreparationAPI A) (reply : A) : Prop := True.
Definition preparation_update (s : protection_state) (A : Type)
    (e : PreparationAPI A) (reply : A) : protection_state :=
  match pending_preparation s with
  | Some p => change_preparation s (Some (set_phase p Detached)) false (protection_table s) (protection_bits s) (protection_dirty s)
  | None => s
  end.
Definition preparation_contract := make_contract preparation_update preparation_caller preparation_callee.
Definition withdraw_load : impure PreparationAPI unit :=
  request_then WithdrawLoad (fun _ => local tt).
Lemma withdrawal_refines_step page s :
  preparation_caller s _ WithdrawLoad ->
  preparation_step page s (preparation_update s _ WithdrawLoad tt).
Proof.
  intros [F [p [P [K W]]]]. unfold preparation_update. rewrite P.
  eapply withdraw_load_context; eauto.
Qed.
Theorem composed_withdrawal_preserves page s s' :
  preparation_invariant page s -> preparation_caller s _ WithdrawLoad ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PreparationAPI)
    preparation_contract withdraw_load) s tt s' -> preparation_invariant page s'.
Proof.
  intros I C H. unfold withdraw_load in H. unroll_post H.
  destruct H0 as [middle [Hcall Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PreparationAPI)
    preparation_contract (local tt)) middle tt s') in Hlocal.
  unroll_post Hlocal. subst.
  eapply preparation_step_inductive; [exact I|].
  destruct x. apply withdrawal_refines_step; exact C.
Qed.
Theorem composed_preparation_erase g page initial bits dirty final f f' a outcome :
  page > 0 -> scope_invariant page initial ->
  preparation_trace page (enter_preparation initial bits dirty) final ->
  free_range page (protection_table final) {| offset := a; span := sector_size g |} ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (erase_reserved_sector a)) f outcome f' ->
  unchanged (required_ranges final) f f'.
Proof.
  intros P I T F H. apply erase_reserved_sector_post in H.
  eapply reachable_preparation_erase_preserves; eauto. exact (proj1 H).
Qed.

Theorem composed_withdrawal_preserves_common page s s' :
  protection_invariant page s -> preparation_caller s _ WithdrawLoad ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PreparationAPI)
    preparation_contract withdraw_load) s tt s' -> protection_invariant page s'.
Proof.
  intros I C H. unfold withdraw_load in H. unroll_post H.
  destruct H0 as [middle [Hcall Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PreparationAPI)
    preparation_contract (local tt)) middle tt s') in Hlocal.
  unroll_post Hlocal. subst.
  eapply protection_step_inductive; [exact I|].
  destruct x. apply withdrawal_refines_step; exact C.
Qed.
Theorem composed_protection_erase g page initial bits dirty final f f' a outcome :
  page > 0 -> scope_invariant page initial ->
  summary_sound bits (scope_pages initial) ->
  preparation_trace page (enter_with_summaries initial bits dirty) final ->
  free_range page (protection_table final) {| offset := a; span := sector_size g |} ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (erase_reserved_sector a)) f outcome f' ->
  unchanged (required_ranges final) f f'.
Proof.
  intros P I B T F H. apply erase_reserved_sector_post in H.
  eapply erase_preserves_covered_ranges; eauto.
  - exact (proj1 (proj1 (finite_protection_trace page _ _
      (enter_with_summaries_invariant page initial bits dirty I B) T))).
  - exact (proj1 H).
Qed.

(* DataReservation services use the same protection_state and its one table. *)
Inductive DataAPI : interface := DataDo : data_command -> DataAPI unit.
Definition data_api_caller s A (e : DataAPI A) :=
  match e with DataDo c => data_caller c s end.
Definition data_api_callee (s : protection_state) A (e : DataAPI A) (reply : A) : Prop := True.
Definition data_api_update s A (e : DataAPI A) (reply : A) :=
  match e with DataDo c => data_next c s end.
Definition data_contract := make_contract data_api_update data_api_caller data_api_callee.
Fixpoint data_program (commands : list data_command) : impure DataAPI unit :=
  match commands with
  | nil => local tt
  | cons c tail => request_then (DataDo c) (fun _ => data_program tail)
  end.
Lemma data_program_post commands s s' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure DataAPI)
    data_contract (data_program commands)) s tt s' ->
  s' = execute_data commands s.
Proof.
  revert s s'. induction commands as [|c tail IH]; intros s s' H; simpl in H.
  - unroll_post H. congruence.
  - unroll_post H. destruct H as [reply [middle [[Hcall EQ] Htail]]].
    subst middle. apply IH in Htail. exact Htail.
Qed.
Theorem composed_data_program_preserves commands s s' :
  data_invariant s -> data_calls commands s ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure DataAPI)
    data_contract (data_program commands)) s tt s' -> data_invariant s'.
Proof.
  intros I C H. apply data_program_post in H; subst.
  apply data_execution_preserves; assumption.
Qed.

(* Internal snapshot services and Data instructions observe the very same
   protection_state. Written is the successful-return continuation of the
   writer; lower Flash reset semantics must never invoke this continuation. *)
Inductive SnapshotAPI : interface :=
| SnapshotReserve : extent -> SnapshotAPI unit
| SnapshotWritten : SnapshotAPI unit
| SnapshotRehome : nat -> SnapshotAPI unit
| SnapshotInstall : list (list extent) -> nat -> SnapshotAPI unit
| SnapshotRetainError : SnapshotAPI unit
| SnapshotError : bool -> SnapshotAPI unit
| SnapshotData : data_command -> SnapshotAPI unit
| SnapshotRemember : nat -> SnapshotAPI unit.
Definition snapshot_api_caller s A (e : SnapshotAPI A) : Prop :=
  match e with
  | SnapshotReserve r => protection_frozen s = false /\ pending_preparation s = None /\
      free_range 256 (protection_table s) r
  | SnapshotWritten => protection_frozen s = false /\ exists p,
      pending_preparation s = Some p /\ prep_kind p = BossPreparation /\ prep_phase p = Reserved
  | SnapshotRehome lifetime => protection_frozen s = false /\ exists p,
      pending_preparation s = Some p /\ prep_kind p = BossPreparation /\ prep_phase p = Written /\
      lifetime <= length (protection_saved s)
  | SnapshotInstall prefix count => snapshot_install_caller prefix count s
  | SnapshotRetainError => exists p, pending_preparation s = Some p /\
      prep_kind p = BossPreparation /\ (prep_phase p = Written \/ prep_phase p = Detached)
  | SnapshotError _ => exists p, pending_preparation s = Some p /\ prep_kind p = BossPreparation /\ prep_phase p = Reserved
  | SnapshotData c => data_caller c s
  | SnapshotRemember _ => protection_frozen s=false /\ exists p,
      pending_preparation s=Some p /\ prep_kind p=BossPreparation /\ prep_phase p=Detached
  end.
Definition snapshot_api_callee (s : protection_state) A (e : SnapshotAPI A) (reply : A) : Prop := True.
Definition snapshot_api_update s A (e : SnapshotAPI A) (reply : A) :=
  match e with
  | SnapshotReserve r => snapshot_reserve r s
  | SnapshotWritten => snapshot_written s
  | SnapshotRehome lifetime => snapshot_rehome lifetime s
  | SnapshotInstall prefix count => snapshot_install_pending prefix count s
  | SnapshotRetainError => snapshot_retain_error s
  | SnapshotError frozen => snapshot_error frozen s
  | SnapshotData c => data_next c s
  | SnapshotRemember area_pages => match pending_preparation s with
      Some p=>remember_recovered_boss area_pages (prep_range p) s | None=>s end
  end.
Definition snapshot_contract := make_contract snapshot_api_update snapshot_api_caller snapshot_api_callee.
Theorem snapshot_service_preserves s A (e : SnapshotAPI A) (reply : A) :
  data_invariant s -> snapshot_api_caller s A e ->
  data_invariant (snapshot_api_update s A e reply).
Proof.
  intros INV CALL. destruct e; simpl in *.
  - destruct CALL as [F [P FREE]]. apply snapshot_reserve_preserves; assumption.
  - destruct CALL as [F [p [P [K W]]]]. eapply snapshot_written_preserves; eauto.
  - destruct CALL as [F [p [P [K [W L]]]]]. eapply snapshot_rehome_preserves; eauto.
  - apply snapshot_install_pending_preserves; assumption.
  - apply snapshot_retain_error_preserves; exact INV.
  - destruct CALL as [p [P [K W]]]. exact (proj1 (snapshot_error_preserves s p b INV P)).
  - apply data_command_preserves; assumption.
  - destruct CALL as [F [p [P [K D]]]]. rewrite P.
    apply validation_update_preserves_data;exact INV.
Qed.
Fixpoint snapshot_program (commands : list (SnapshotAPI unit)) : impure SnapshotAPI unit :=
  match commands with
  | nil => local tt
  | cons c tail => request_then c (fun _ => snapshot_program tail)
  end.
Fixpoint snapshot_calls (commands : list (SnapshotAPI unit)) s : Prop :=
  match commands with
  | nil => True
  | cons c tail => snapshot_api_caller s unit c /\
      snapshot_calls tail (snapshot_api_update s unit c tt)
  end.
Fixpoint snapshot_execute (commands : list (SnapshotAPI unit)) s :=
  match commands with
  | nil => s
  | cons c tail => snapshot_execute tail (snapshot_api_update s unit c tt)
  end.
Lemma snapshot_program_post commands s s' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
    snapshot_contract (snapshot_program commands)) s tt s' ->
  s' = snapshot_execute commands s.
Proof.
  revert s s'. induction commands as [|c tail IH]; intros s s' H; simpl in H.
  - unroll_post H. congruence.
  - unroll_post H. destruct H as [reply [middle [[CALL EQ] REST]]].
    subst middle. destruct reply. apply IH in REST; exact REST.
Qed.
Theorem composed_snapshot_data_preserves commands s s' :
  data_invariant s -> snapshot_calls commands s ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
    snapshot_contract (snapshot_program commands)) s tt s' -> data_invariant s'.
Proof.
  intros INV CALLS POST. apply snapshot_program_post in POST; subst s'.
  revert s INV CALLS. induction commands as [|c tail IH]; intros s INV CALLS; simpl in *.
  - exact INV.
  - destruct CALLS as [C CS]. apply IH; [eapply snapshot_service_preserves; eauto|exact CS].
Qed.

Lemma snapshot_program_executes commands s :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
   snapshot_contract (snapshot_program commands)) s tt (snapshot_execute commands s).
Proof.
 revert s;induction commands as [|cmd rest IH];intro s;cbn.
 - split;reflexivity.
 - exists tt,(snapshot_api_update s unit cmd tt);split;[split;reflexivity|apply IH].
Qed.

Definition snapshot_success_services prefix count r : list (SnapshotAPI unit) :=
  cons (SnapshotReserve r) (cons SnapshotWritten
    (cons (SnapshotRehome (length prefix)) (cons (SnapshotInstall prefix count) nil))).
Theorem snapshot_success_services_callers s prefix count r :
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> count > 0 ->
  protection_saved s = List.app prefix (List.repeat (List.app (protection_current s) (attached_ranges s)) count) ->
  snapshot_calls (snapshot_success_services prefix count r) s.
Proof.
  intros F P FREE N SHAPE. unfold snapshot_success_services.
  cbn [snapshot_calls snapshot_api_caller snapshot_api_update].
  split; [auto|]. split.
  - split; [reflexivity|]. exists (Build_preparation BossPreparation r Reserved).
    repeat split; reflexivity.
  - split.
    + split; [reflexivity|]. exists (Build_preparation BossPreparation r Written).
      repeat split; try reflexivity.
      change (length prefix <= length (protection_saved s)).
      rewrite SHAPE. rewrite List.length_app. rewrite List.repeat_length. apply PeanoNat.Nat.le_add_r.
    + split; [|exact I]. apply snapshot_install_caller_derived
        with (p:=Build_preparation BossPreparation r Written); try reflexivity; assumption.
Qed.

Lemma snapshot_data_callers commands s :
  data_calls commands s -> snapshot_calls (List.map SnapshotData commands) s.
Proof.
  revert s. induction commands as [|c tail IH]; intros s H; simpl in *; [exact I|].
  destruct H as [C T]; split; [exact C|apply IH; exact T].
Qed.
Definition snapshot_then_data_program prefix count r commands :=
  snapshot_program (List.app (snapshot_success_services prefix count r)
    (List.map SnapshotData commands)).
Theorem composed_snapshot_then_data prefix count r commands s s' :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) r -> count > 0 ->
  protection_saved s = List.app prefix (List.repeat (List.app (protection_current s) (attached_ranges s)) count) ->
  data_calls commands (snapshot_success prefix count r s) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
    snapshot_contract (snapshot_then_data_program prefix count r commands)) s tt s' ->
  data_invariant s'.
Proof.
  intros INV F P FREE POS SHAPE DATA POST. eapply composed_snapshot_data_preserves; [exact INV| |exact POST].
  pose proof (snapshot_success_services_callers s prefix count r F P FREE POS SHAPE)
    as [R [W [H [INSTALL END]]]].
  unfold snapshot_success_services. cbn [List.app snapshot_calls].
  split; [exact R|]. split; [exact W|]. split; [exact H|]. split; [exact INSTALL|].
  apply snapshot_data_callers. exact DATA.
Qed.

Inductive ExactImageAPI : interface :=
| ExactLocal : data_command -> ExactImageAPI unit
| ExactInstall : list compact_slot -> nat -> compact_entry -> ExactImageAPI unit.
Definition exact_api_caller kind ranges s A (op : ExactImageAPI A) : Prop :=
  match op with
  | ExactLocal c => data_caller c s
  | ExactInstall image index entry => data_caller DataAttach s /\
      data_slot_for kind image (entry_key kind entry) = Some index /\
      (exists root, image_current_correspondence ranges image root s) /\
      (exists p, pending_preparation s = Some p /\ ranges entry = cons (prep_range p) nil)
  end.
Definition exact_api_callee (s : protection_state) A (op : ExactImageAPI A) (reply : A) : Prop := True.
Definition exact_api_update ranges s A (op : ExactImageAPI A) (reply : A) :=
  match op with
  | ExactLocal c => data_next c s
  | ExactInstall image index entry => exact_attach ranges image index entry s
  end.
Definition exact_contract kind ranges :=
  make_contract (exact_api_update ranges) (exact_api_caller kind ranges) exact_api_callee.
Theorem exact_service_preserves kind ranges s A (op : ExactImageAPI A) (reply : A) :
  data_invariant s -> exact_api_caller kind ranges s A op ->
  data_invariant (exact_api_update ranges s A op reply).
Proof.
  intros INV CALL. destruct op; simpl in *.
  - apply data_command_preserves; assumption.
  - destruct CALL as [C [SEL [[root COR] [p [P RANGE]]]]].
    exact (proj1 (exact_attach_preserves ranges l root n c s p INV C P COR RANGE)).
Qed.
Fixpoint exact_service_program (ops : list (ExactImageAPI unit)) : impure ExactImageAPI unit :=
  match ops with nil => local tt | cons op tail => request_then op (fun _ => exact_service_program tail) end.
Fixpoint exact_service_execute ranges ops s :=
  match ops with nil => s | cons op tail => exact_service_execute ranges tail (exact_api_update ranges s unit op tt) end.
Fixpoint exact_service_calls kind ranges ops s : Prop :=
  match ops with nil => True | cons op tail => exact_api_caller kind ranges s unit op /\
    exact_service_calls kind ranges tail (exact_api_update ranges s unit op tt) end.
Fixpoint compile_exact commands image : list (ExactImageAPI unit) :=
  match commands with
  | nil => nil
  | cons c tail => cons (ExactLocal (DataReserve (edit_reservation c)))
      (cons (ExactLocal DataWritten)
        (cons (ExactInstall image (edit_index c) (edit_entry c))
          (compile_exact tail (image_replace image (edit_index c) (Some (edit_entry c))))))
  end.
Lemma exact_service_program_post kind ranges ops s s' :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ExactImageAPI)
    (exact_contract kind ranges) (exact_service_program ops)) s tt s' ->
  s' = exact_service_execute ranges ops s.
Proof.
  revert s s'. induction ops as [|op tail IH]; intros s s' H; simpl in H.
  - unroll_post H; congruence.
  - unroll_post H. destruct H as [reply [middle [[C EQ] REST]]].
    subst middle. destruct reply. apply IH in REST; exact REST.
Qed.
Lemma compiled_exact_execute ranges commands image s :
  exact_service_execute ranges (compile_exact commands image) s = execute_exact commands ranges image s.
Proof.
  revert image s. induction commands as [|c tail IH]; intros image s; simpl; [reflexivity|].
  apply IH.
Qed.
Theorem compiled_exact_callers kind ranges commands image root s :
  data_invariant s -> image_current_correspondence ranges image root s ->
  exact_calls kind ranges commands image s ->
  exact_service_calls kind ranges (compile_exact commands image) s.
Proof.
  revert image root s. induction commands as [|c tail IH]; intros image root s INV COR CALLS; simpl in CALLS; [exact I|].
  destruct CALLS as [F [P [FREE [RANGE [SEL REST]]]]].
  cbn [compile_exact exact_service_calls exact_api_caller exact_api_update].
  split; [simpl; auto|]. split.
  - split; [reflexivity|]. exists (Build_preparation ObjectPreparation (edit_reservation c) Reserved).
    repeat split; try reflexivity; intros; discriminate.
  - split.
    + split.
      * split; [reflexivity|]. exists (Build_preparation ObjectPreparation (edit_reservation c) Written).
        repeat split; reflexivity.
      * split; [exact SEL|]. split; [exists root; exact COR|].
        exists (Build_preparation ObjectPreparation (edit_reservation c) Written); split; [reflexivity|exact RANGE].
    + destruct (exact_member_preserves ranges image root (edit_index c) (edit_entry c)
        (edit_reservation c) s INV F P FREE RANGE COR) as [INV' COR'].
      apply IH with (root:=nil); assumption.
Qed.
Theorem composed_exact_edits kind ranges commands image root s s' :
  data_invariant s -> image_current_correspondence ranges image root s ->
  image_unique kind image -> exact_calls kind ranges commands image s ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ExactImageAPI)
    (exact_contract kind ranges) (exact_service_program (compile_exact commands image))) s tt s' ->
  data_invariant s' /\ image_current_correspondence ranges (edited_image commands image)
    (match commands with nil => root | _ => nil end) s' /\ image_unique kind (edited_image commands image).
Proof.
  intros INV COR U CALLS H. apply exact_service_program_post in H.
  rewrite compiled_exact_execute in H; subst s'. apply finite_exact_edits_preserve; assumption.
Qed.

(* Scratch construction can fail at any range resolution. The callee only
   specifies the successful enumeration, never protection or authority. *)
Inductive CollectionAPI : interface :=
| CollectScratch : CollectionAPI (option (list extent)).
Section CollectionContract.
Variable page : nat.
Variable initialized : bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable durable current : option nat.
Variable entries load : list extent.
Definition collection_api_caller s A (e : CollectionAPI A) :=
  collection_boundary view marker durable current entries load s.
Definition collection_api_callee (s : protection_state) A (e : CollectionAPI A) : A -> Prop :=
  match e with CollectScratch => fun resolved => forall ranges,
    resolved = Some ranges -> ranges = CollectionRoots.collect_ranges view marker current entries load end.
Definition collection_api_update s A (e : CollectionAPI A) : A -> protection_state :=
  match e with CollectScratch => fun resolved =>
    collection_return page initialized durable current resolved s end.
Definition collection_contract :=
  make_contract collection_api_update collection_api_caller collection_api_callee.
Definition collect_program : impure CollectionAPI (option (list extent)) :=
  request_then CollectScratch (fun result => local result).
Theorem collection_service_preserves s A (e : CollectionAPI A) reply :
  protection_invariant page s -> collection_api_caller s A e ->
  collection_api_callee s A e reply ->
  protection_invariant page (collection_api_update s A e reply).
Proof. destruct e; intros I C R; eapply collection_return_preserves; eauto. Qed.
Theorem composed_collection_preserves s result s' :
  protection_invariant page s -> collection_api_caller s _ CollectScratch ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CollectionAPI)
    collection_contract collect_program) s result s' -> protection_invariant page s'.
Proof.
  intros I C H. unfold collect_program in H. unroll_post H.
  destruct H0 as [middle [Hcall Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CollectionAPI)
    collection_contract (local x)) middle result s') in Hlocal.
  unroll_post Hlocal. subst.
  eapply collection_return_preserves; eauto.
Qed.
End CollectionContract.

(* Three separate internal effects over the existing witness. The Slot event
   must be supplied by JournalHistory's completed-candidate bridge; it is not
   a replacement for programming flash. Client acknowledgement is later. *)
Import ListNotations.
Inductive PublicationExitPhase := SlotCompleted | DurableRamWritten | ExternalAccepted.
Inductive PublicationExitAPI : interface :=
| ExitEffect : PublicationExitPhase -> PublicationExitAPI unit.
Section PublicationExitContract.
Variable marker : extent.
Variable candidate saved : list extent.
Definition exit_next phase s := match phase with
  | SlotCompleted => slot_publication candidate s
  | DurableRamWritten => durable_ram_update marker candidate s
  | ExternalAccepted => data_next (DataClose [] saved true) s end.
Definition exit_caller phase s := protection_frozen s = false /\
  pending_preparation s = None /\
  match phase with
  | SlotCompleted => protection_current s ++ attached_ranges s = candidate
  | DurableRamWritten => In marker (protection_base s)
  | ExternalAccepted => protection_saved s = [saved] end.
Definition exit_api_caller s A (e : PublicationExitAPI A) :=
  match e with ExitEffect phase => exit_caller phase s end.
Definition exit_api_callee (s : protection_state) A (e : PublicationExitAPI A) (reply : A) : Prop := True.
Definition exit_api_update s A (e : PublicationExitAPI A) (reply : A) :=
  match e with ExitEffect phase => exit_next phase s end.
Definition exit_contract := make_contract exit_api_update exit_api_caller exit_api_callee.
Fixpoint exit_program phases : impure PublicationExitAPI unit :=
  match phases with [] => local tt | phase :: tail =>
    request_then (ExitEffect phase) (fun _ => exit_program tail) end.
Fixpoint execute_exit phases s := match phases with [] => s | phase :: tail =>
  execute_exit tail (exit_next phase s) end.
Fixpoint exit_calls phases s := match phases with [] => True | phase :: tail =>
  exit_caller phase s /\ exit_calls tail (exit_next phase s) end.
Theorem exit_program_post phases s s' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    exit_contract (exit_program phases)) s tt s' -> s' = execute_exit phases s.
Proof.
  revert s s'. induction phases as [|c tail IH]; intros s s' H; simpl in H.
  - unroll_post H. congruence.
  - unroll_post H. destruct H as [reply [middle [[Hcall EQ] Htail]]].
    subst middle. apply IH in Htail. exact Htail.
Qed.
Theorem successful_exit_callers s :
  protection_frozen s = false -> pending_preparation s = None ->
  protection_saved s = [saved] -> In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = candidate ->
  exit_calls [SlotCompleted; DurableRamWritten; ExternalAccepted] s.
Proof. intros F P S M C. simpl. unfold exit_caller; simpl. repeat split; assumption. Qed.
Theorem composed_successful_close s s' :
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = candidate ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    exit_contract (exit_program [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    s tt s' -> protection_invariant 256 s'.
Proof.
  intros I F S P M C H. apply exit_program_post in H; subst s'.
  change (protection_invariant 256 (successful_external_close marker candidate saved s)).
  eapply successful_close_protects; eauto.
Qed.
End PublicationExitContract.

Theorem composed_successful_exit_collection view marker id saved s middle final initialized resolved :
  data_invariant s -> protection_frozen s = false -> protection_saved s = [saved] ->
  pending_preparation s = None -> In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = root_extents (view id) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    (exit_contract marker (root_extents (view id)) saved)
    (exit_program [SlotCompleted; DurableRamWritten; ExternalAccepted])) s tt middle ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CollectionAPI)
    (collection_contract 256 initialized view marker (Some id) (Some id)
      (object_extents (view id)) []) collect_program) middle resolved final ->
  protection_invariant 256 final.
Proof.
  intros I F S P M C EXIT COLLECT.
  apply exit_program_post in EXIT.
  change (middle = successful_external_close marker (root_extents (view id)) saved s) in EXIT.
  subst middle. eapply composed_collection_preserves; [| |exact COLLECT].
  - eapply successful_close_protects; eauto.
  - apply successful_close_boundary; exact C.
Qed.

Theorem composed_successful_close_restores_data marker candidate saved s s' :
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = candidate ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
    (exit_contract marker candidate saved)
    (exit_program [SlotCompleted; DurableRamWritten; ExternalAccepted]))
    s tt s' -> data_invariant s'.
Proof.
  intros I F S P M C H. apply exit_program_post in H; subst s'.
  change (data_invariant (successful_external_close marker candidate saved s)).
  eapply successful_close_restores_data; eauto.
Qed.

Inductive CandidateAPI : interface := InstallFinalBoss : CandidateAPI unit.
Definition candidate_caller s A (e : CandidateAPI A) :=
  protection_frozen s = false /\ exists p, pending_preparation s = Some p /\
    prep_kind p = BossPreparation /\ prep_phase p = Written.
Definition candidate_callee (s : protection_state) A (e : CandidateAPI A) (r : A) : Prop := True.
Definition candidate_update s A (e : CandidateAPI A) (r : A) := install_candidate s.
Definition candidate_contract := make_contract candidate_update candidate_caller candidate_callee.
Definition install_final_boss : impure CandidateAPI unit :=
  request_then InstallFinalBoss (fun _ => local tt).
Theorem candidate_service_preserves s :
  data_invariant s -> candidate_caller s _ InstallFinalBoss -> data_invariant (install_candidate s).
Proof. intros I [F [p [P [K W]]]]; eapply install_candidate_preserves; eauto. Qed.
Lemma final_boss_program_post s s' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CandidateAPI)
    candidate_contract install_final_boss) s tt s' -> s' = install_candidate s.
Proof.
  intros H; unfold install_final_boss in H; unroll_post H.
  destruct H0 as [middle [CALL LOCAL]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CandidateAPI)
    candidate_contract (local tt)) middle tt s') in LOCAL.
  unroll_post LOCAL. subst. reflexivity.
Qed.
Theorem composed_final_boss_preparation boss s written final :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) boss ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
    snapshot_contract (snapshot_program [SnapshotReserve boss; SnapshotWritten])) s tt written ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure CandidateAPI)
    candidate_contract install_final_boss) written tt final ->
  candidate_caller written _ InstallFinalBoss /\
  final = materialize_candidate boss s /\ data_invariant final.
Proof.
  intros I F P FREE RES INSTALL. apply snapshot_program_post in RES; subst written.
  apply final_boss_program_post in INSTALL; subst final. split.
  - split; [reflexivity|]. exists (Build_preparation BossPreparation boss Written).
    repeat split; reflexivity.
  - split; [reflexivity|]. apply materialize_candidate_preserves; assumption.
Qed.
Theorem final_boss_prepare_callers boss s :
  protection_frozen s = false -> pending_preparation s = None ->
  free_range 256 (protection_table s) boss ->
  snapshot_calls [SnapshotReserve boss; SnapshotWritten] s.
Proof.
  intros F P FREE. simpl. split; [auto|]. split; [|exact I].
  split; [reflexivity|]. exists (Build_preparation BossPreparation boss Reserved).
  repeat split; reflexivity.
Qed.

(* The authority observation is supplied by JournalHistory. Freeze precedes
   every cleanup effect; invariants are proved, never a callee guarantee. *)
Theorem composed_uncertain_cleanup candidate selected s commands final :
  protection_invariant 256 s -> pending_preparation s = None ->
  protection_current s ++ attached_ranges s = candidate ->
  (forall r, In r selected -> In r (physical_authority s ++ candidate)) ->
  data_calls commands (uncertain_return selected s) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure DataAPI)
    data_contract (data_program (DataFreeze :: commands)))
    (slot_publication selected s) tt final ->
  data_invariant final /\ protection_frozen final = true /\
  protection_table final = protection_table s /\
  physical_authority final = selected /\
  acknowledged_authority final = acknowledged_authority s /\
  protected (needed 256 (physical_authority s ++ candidate)) (protection_table final).
Proof.
  intros I P C SEL CALL POST. apply data_program_post in POST. subst final.
  exact (frozen_data_cleanup candidate selected s commands I P C SEL CALL).
Qed.

(* Successful ensure_protection after pages.reset. Retain is deliberately
   sequential: prefixes need not yet cover the whole recovered image. *)
Inductive RecoveryPagesAPI : interface :=
| RetainAtBoot : extent -> RecoveryPagesAPI unit.
Definition recovery_pages_caller (s : protection_state) A (e : RecoveryPagesAPI A) : Prop :=
  match e with RetainAtBoot r => offset r + span r <= 1024*256 end.
Definition recovery_pages_callee (s : protection_state) A (e : RecoveryPagesAPI A) (reply : A) : Prop := True.
Definition recovery_pages_update s A (e : RecoveryPagesAPI A) (reply : A) :=
  match e with RetainAtBoot r => recovery_retain r s end.
Definition recovery_pages_contract :=
  make_contract recovery_pages_update recovery_pages_caller recovery_pages_callee.
Fixpoint recovery_pages_program ranges : impure RecoveryPagesAPI unit := match ranges with
  | nil => local tt
  | cons r tail => request_then (RetainAtBoot r) (fun _ => recovery_pages_program tail) end.
Fixpoint recovery_pages_calls ranges s : Prop := match ranges with
  | nil => True
  | cons r tail => recovery_pages_caller s _ (RetainAtBoot r) /\
      recovery_pages_calls tail (recovery_retain r s) end.
Theorem recovery_pages_callers ranges s :
  Forall (fun r => offset r + span r <= 1024*256) ranges -> recovery_pages_calls ranges s.
Proof. intro B; revert s; induction B; intro s; simpl; auto. Qed.
Lemma recovery_pages_program_post ranges s final :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecoveryPagesAPI)
    recovery_pages_contract (recovery_pages_program ranges)) s tt final ->
  final = recovery_retains ranges s.
Proof.
  revert s final; induction ranges as [|r tail IH]; intros s final H; simpl in H.
  - unroll_post H. subst; reflexivity.
  - unroll_post H. match goal with E : exists _, _ |- _ =>
      destruct E as [reply [middle [[CALL EQ] REST]]] end.
    subst middle. apply IH in REST; exact REST.
Qed.
Theorem composed_reconstruction_opens_transaction view marker ranges id decoded final :
  decoded_root_agrees view ranges id decoded ->
  Forall (fun r => offset r + span r <= 1024*256)
    (marker :: recovered_boss decoded :: image_dependencies ranges (recovered_image decoded)) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecoveryPagesAPI)
    recovery_pages_contract
    (recovery_pages_program (marker :: recovered_boss decoded ::
      image_dependencies ranges (recovered_image decoded))))
    (recovered_ram marker (recovered_boss decoded)
      (image_dependencies ranges (recovered_image decoded))) tt final ->
  recovery_pages_calls (marker :: recovered_boss decoded ::
    image_dependencies ranges (recovered_image decoded))
    (recovered_ram marker (recovered_boss decoded) (image_dependencies ranges (recovered_image decoded))) /\
  idle_root view marker id final /\
  image_current_correspondence ranges (recovered_image decoded) [recovered_boss decoded] final /\
  data_caller DataBegin final /\ data_invariant (data_next DataBegin final).
Proof.
  intros FORMAT BOUNDS POST. apply recovery_pages_program_post in POST. subst final.
  split; [apply recovery_pages_callers; exact BOUNDS|].
  exact (decoded_reconstruction_opens_transaction view marker ranges id decoded FORMAT).
Qed.
