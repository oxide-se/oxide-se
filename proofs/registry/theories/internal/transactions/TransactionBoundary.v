From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec PageOwnership ScopeOwnership RetentionCoverage CompactImage
  CompactUpdates CollectionRoots PreparedAuthority JournalHistory JournalReachableShape
  JournalRecoveryTrace JournalRequests PublicationPreparation BootReconstruction BootTransaction.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export BossDecodingContract DecodedGeometryContract.
Import ListNotations.

(* A view of existing witnesses, not a transition system. The outer journal is
   the ONLY flash and history. Each alternative owns at most ONE protection
   witness. Reconstruction reuses boot_phase and drops operational RAM. *)
Inductive publication_boundary :=
| CandidatePrepared | SlotVisible | AppendReturned | DurableSynchronized.
Inductive transaction_phase :=
| IdleBoundary (id : nat) (decoded : recovery_decoding) (ram : protection_state)
| ClientBoundary (id : nat) (decoded : recovery_decoding) (ram : protection_state)
| OpenBoundary (image : list compact_slot) (root : list extent) (ram : protection_state)
| OperationBoundary (image : list compact_slot) (root : list extent) (ram : protection_state)
| PublishingBoundary (stage : publication_boundary) (id : nat)
    (decoded : recovery_decoding) (ram : protection_state)
(* Some [] represents Rust current=None. None denotes a legacy opaque cleanup
   whose root observer is not refined; it cannot justify a restoration skip.
   This witness is volatile and absent from Rebuilding/Fatal. *)
| FrozenBoundary (old candidate : N) (current : option (list extent)) (ram : protection_state)
| RebuildingBoundary (pc : boot_phase)
| FatalBoundary.
(* Frozen callers exclude allocating/attaching. Drop, freeze, unchanged and
   acceptance retain current; an opaque rollback lacks its concrete BOSS root. *)
Fixpoint opaque_preserves_current (commands:list data_command) :=
 match commands with []=>true | DataClose _ _ false :: _=>false
 | _::tail=>opaque_preserves_current tail end.
Definition opaque_frozen_root (current:option (list extent)) (commands:list data_command) :=
 match current with None=>None | Some root=>
   if opaque_preserves_current commands then Some root else None end.
Definition transaction_boundary := (logged_state * transaction_phase)%type.

Section Invariant.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable area_pages : nat.

Definition usable_boundary j id d ram :=
  journal_idle sector 256 data_len boss_ok view marker id ram j /\
  decoded_root_agrees view ranges id d /\
  image_current_correspondence ranges (recovered_image d) [recovered_boss d] ram.

Definition publication_boundary_invariant stage j id d ram :=
  protection_invariant 256 ram /\ protection_frozen ram = false /\
  pending_preparation ram = None /\ decoded_root_agrees view ranges id d /\
  image_current_correspondence ranges (recovered_image d) [recovered_boss d] ram /\
  protection_history_link view ram j /\
  match stage with
  | CandidatePrepared => data_invariant ram
  | SlotVisible => hd_error (publications j) = Some (N.of_nat id)
  | AppendReturned => hd_error (publications j) = Some (N.of_nat id) /\
      hd_error (acknowledgements j) = Some (N.of_nat id)
  | DurableSynchronized => hd_error (publications j) = Some (N.of_nat id) /\
      hd_error (acknowledgements j) = Some (N.of_nat id) /\
      protection_base ram = marker :: root_extents (view id) /\
      acknowledged_authority ram = root_extents (view id)
  end.

Definition common_invariant (state : transaction_boundary) :=
  let j := fst state in
  logged_invariant sector 256 data_len boss_ok j /\
  match snd state with
  | IdleBoundary id d ram => usable_boundary j id d ram
  | ClientBoundary id d ram => usable_boundary j id d ram /\
      hd_error (acknowledgements j) = Some (N.of_nat id)
  | OpenBoundary image root ram | OperationBoundary image root ram => data_invariant ram /\
      protection_frozen ram = false /\
      image_current_correspondence ranges image root ram /\ protection_history_link view ram j
  | PublishingBoundary stage id d ram => publication_boundary_invariant stage j id d ram
  | FrozenBoundary old candidate current ram => data_invariant ram /\ protection_frozen ram = true /\
      protection_history_link view ram j /\
      (hd_error (publications j) = Some old \/ hd_error (publications j) = Some candidate) /\
      protected (needed 256 (root_extents (view (N.to_nat old)) ++
        root_extents (view (N.to_nat candidate)))) (protection_table ram)
  | RebuildingBoundary pc =>
      boot_invariant sector data_len boss_ok view marker ranges decode area_pages (j,pc)
  | FatalBoundary => True
  end.

(* This is the missing representation input at a bare journal_idle boundary.
   It is provided by the decoder contract / exact-image producer, not by
   journal shape, offsets, or authentication alone. *)
Lemma idle_image j id d ram :
  journal_idle sector 256 data_len boss_ok view marker id ram j ->
  decoded_root_agrees view ranges id d ->
  usable_boundary j id d ram.
Proof.
  intros IDLE FORMAT. split; [exact IDLE|]. split; [exact FORMAT|].
  destruct FORMAT as [B E]. unfold image_current_correspondence.
  rewrite B, E. change (protection_current ram ++ attached_ranges ram = root_extents (view id)).
  destruct IDLE as [[_ [_ [_ [_ [C _]]]]] _]; exact C.
Qed.
Theorem journal_idle_common j id d ram :
  journal_idle sector 256 data_len boss_ok view marker id ram j ->
  decoded_root_agrees view ranges id d ->
  common_invariant (j,IdleBoundary id d ram).
Proof. intros I F. split; [exact (proj1 (proj2 I))|]. apply idle_image; assumption. Qed.

Theorem common_begin j id d ram :
  common_invariant (j,IdleBoundary id d ram) ->
  data_caller DataBegin ram /\
  common_invariant (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)).
Proof.
  intros [J [IDLE [FORMAT COR]]].
  destruct IDLE as [[I [F [S [P REST]]]] [JI [READY [HEAD LINK]]]].
  assert (CALL : data_caller DataBegin ram).
  { simpl. rewrite F, P, S; simpl; repeat split; auto; lia. }
  split; [exact CALL|]. split; [exact J|]. split.
  - apply data_command_preserves; assumption.
  - split; [reflexivity|]. split.
    + unfold image_current_correspondence in *; simpl; rewrite app_nil_r; exact COR.
    + apply local_data_keeps_history_link; exact LINK.
Qed.

Theorem completed_boot_common j id d ram :
  boot_invariant sector data_len boss_ok view marker ranges decode area_pages (j,Usable id d ram) ->
  common_invariant (j,IdleBoundary id d ram).
Proof.
  intros INV.
  destruct (boot_usable_opens sector data_len boss_ok view marker ranges decode area_pages j id d ram INV)
    as [IDLE [COR REST]].
  apply journal_idle_common; [exact IDLE|].
  destruct INV as [_ [_ [[READY [HEAD [READ FORMAT]]] RAM]]]; exact FORMAT.
Qed.

Theorem rebuilding_common j pc :
  boot_invariant sector data_len boss_ok view marker ranges decode area_pages (j,pc) ->
  common_invariant (j,RebuildingBoundary pc).
Proof. intros I; split; [exact (proj1 I)|exact I]. Qed.

(* Fatal is not reset. No ordinary service is enabled by this view. *)
Definition boundary_begin_caller (state : transaction_boundary) :=
  exists id d ram, snd state = IdleBoundary id d ram /\ data_caller DataBegin ram.
Theorem fatal_no_begin j : ~ boundary_begin_caller (j,FatalBoundary).
Proof. intros [id [d [ram [E _]]]]; discriminate. Qed.
Theorem reconstruction_no_begin j pc : ~ boundary_begin_caller (j,RebuildingBoundary pc).
Proof. intros [id [d [ram [E _]]]]; discriminate. Qed.
Theorem frozen_no_begin j old candidate current ram : ~ boundary_begin_caller (j,FrozenBoundary old candidate current ram).
Proof. intros [id [d [s [E _]]]]; discriminate. Qed.

(* Consumes the success conclusion, including its actual decoded candidate.
   The client-labelled boundary is not constructed from append success alone:
   the upstream continuation supplies the separate client result as well. *)
Theorem successful_continuation_common g old id image index entry span s prepared ready old_decoded
    out slot pubs acks :
  recovery_local_contracts view ranges decode ->
  publication_client_continuations g sector data_len boss_ok view marker ranges decode
    old id image index entry span s prepared ready old_decoded ->
  clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
  logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
    (Logged (Ready out) pubs (N.of_nat id :: acks)) ->
  let result := finish_data_client view marker id ranges image index entry span s in
  snd result = DataClientSuccess id (image_replace image index (Some entry)) /\
  common_invariant (Logged (Ready out) pubs (N.of_nat id :: acks),
    ClientBoundary id (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) (fst result)) /\
  common_invariant (Logged (Ready out) pubs (N.of_nat id :: acks),
    IdleBoundary id (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) (fst result)).
Proof.
  intros CONTRACT [SUCCESS FAILURE] TRACE ACK result.
  destruct (SUCCESS out slot pubs acks TRACE ACK) as [CLIENT [IDLE [READ REST]]].
  assert (USE : usable_boundary (Logged (Ready out) pubs (N.of_nat id :: acks)) id
    (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) (fst result)).
  { apply idle_image; [exact IDLE|]. eapply recovery_format_contract; eauto. }
  split; [exact CLIENT|]. split.
  - split; [exact (proj1 (proj2 IDLE))|]. split; [exact USE|reflexivity].
  - split; [exact (proj1 (proj2 IDLE))|exact USE].
Qed.

Theorem frozen_cleanup_common g old candidate s j error_j commands :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok j ->
  protection_invariant 256 s -> pending_preparation s = None ->
  hd_error (publications j) = Some old -> protection_history_link view s j ->
  protection_current s ++ attached_ranges s = root_extents (view (N.to_nat candidate)) ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok candidate) j error_j ->
  let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
  data_calls commands (uncertain_return selected s) ->
  common_invariant (error_j,FrozenBoundary old candidate None (execute_data commands (uncertain_return selected s))).
Proof.
  intros G DIV J I P HEAD LINK CUR TRACE selected CALL.
  destruct (uncertain_publication_then_cleanup g sector 256 data_len boss_ok view
    old candidate s j error_j commands G DIV J I P HEAD LINK CUR TRACE CALL)
    as [JI [CHOICE [ACK [DI [F [TABLE [L [A COVER]]]]]]]].
  split; [exact JI|]. split; [exact DI|]. split; [exact F|].
  split; [exact L|]. split; assumption.
Qed.

Theorem completed_slot_common g s j f index id history acks d :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok j ->
  logged_step g sector 256 data_len boss_ok j
    (Logged (AwaitAck f index (N.of_nat id)) history acks) ->
  protection_invariant 256 s -> protection_frozen s = false ->
  pending_preparation s = None ->
  protection_current s ++ attached_ranges s = root_extents (view id) ->
  decoded_root_agrees view ranges id d ->
  common_invariant (Logged (AwaitAck f index (N.of_nat id)) history acks,
    PublishingBoundary SlotVisible id d (slot_publication (root_extents (view id)) s)).
Proof.
  intros G DIV J STEP I F P CUR FORMAT.
  pose proof (logged_step_preserves_invariant g sector 256 data_len boss_ok G DIV _ _ J STEP) as JI.
  assert (HEAD : hd_error history = Some (N.of_nat id)).
  { exact (proj2 (proj1 (proj2 JI))). }
  split; [exact JI|]. unfold publication_boundary_invariant.
  split; [apply slot_publication_preserves; assumption|].
  split; [exact F|]. split; [exact P|]. split; [exact FORMAT|]. split.
  - unfold image_current_correspondence; simpl. rewrite CUR.
    destruct FORMAT as [B E]. rewrite B, E; reflexivity.
  - split; [|exact HEAD]. unfold protection_history_link; simpl.
    rewrite HEAD; simpl; rewrite Nat2N.id; reflexivity.
Qed.

(* This is the common consumer of the restart postcondition exported in EACH
   branch of prepared_transaction_repeated_boot. No post-reset RAM premise. *)
Theorem repeated_boot_common g topology allowed initial final :
  boot_restart_post g sector data_len boss_ok view marker ranges decode topology area_pages allowed initial ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology area_pages)
    (initial,Selecting) final ->
  common_invariant (boot_journal final,RebuildingBoundary (boot_pc final)) /\
  forall j id d ram, final = (j,Usable id d ram) ->
    allowed id d /\ common_invariant (j,IdleBoundary id d ram) /\
    data_caller DataBegin ram /\
    common_invariant (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)).
Proof.
  intros POST TRACE. destruct (POST final TRACE) as [INV [PUB [ACK [FRAME USE]]]].
  split.
  - apply rebuilding_common; exact INV.
  - intros j id d ram E; subst final.
    destruct (USE j id d ram eq_refl) as [A REST].
    pose proof (completed_boot_common j id d ram INV) as COMMON.
    split; [exact A|]. split; [exact COMMON|]. exact (common_begin j id d ram COMMON).
Qed.
Theorem rebuilding_trace_common g topology initial final :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  common_invariant (boot_journal initial,RebuildingBoundary (boot_pc initial)) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology area_pages)
    initial final ->
  common_invariant (boot_journal final,RebuildingBoundary (boot_pc final)).
Proof.
  intros G DIV CONTRACT [_ INV] TRACE.
  apply rebuilding_common.
  exact (proj1 (boot_finite_trace g sector data_len boss_ok view marker ranges decode topology area_pages
    G DIV CONTRACT initial final INV TRACE)).
Qed.

Theorem boot_stopped_common j :
  boot_invariant sector data_len boss_ok view marker ranges decode area_pages (j,Stopped) ->
  common_invariant (j,FatalBoundary).
Proof. intros I; split; [exact (proj1 I)|exact Logic.I]. Qed.
End Invariant.

(* A11.2: ghost evidence attached to the SAME boundary. Neither certificates
   nor receipts contain a second flash, page table, or physical history. *)
Record persistent_certificate := Certificate {
  certificate_id : nat;
  certificate_decoded : recovery_decoding
}.
Definition certificate_ranges ranges c :=
  recovered_boss (certificate_decoded c) ::
  image_dependencies ranges (recovered_image (certificate_decoded c)).
Record client_receipt := Receipt {
  receipt_event : nat; (* zero-based ordinal from the oldest physical event *)
  receipt_certificate : persistent_certificate
}.
(* Volatile controller metadata. No flash, page table, root or history copy. *)
Inductive finish_route := FinishAbort | FinishClean | FinishPublish.
Record operation_control := FullControl {
  abort_requested : bool;
  outer_live : bool;
  owns_outer : bool;
  owner_armed : bool;
  local_live : bool;
  local_taken : option bool;
  finish_selected : option finish_route;
  body_error_pending : bool
}.
(* Compatibility constructor for control prefixes with no body error. *)
Definition Control ab outer owns armed local taken selected :=
 FullControl ab outer owns armed local taken selected false.
Definition idle_control := Control false false false false false None None.
Definition control_begin (c:operation_control) := Control false true true true false None None.
Definition control_rejected_begin c := FullControl false (outer_live c) (owns_outer c)
  (owner_armed c) (local_live c) (local_taken c) (finish_selected c) (body_error_pending c).
Definition control_join c := FullControl (abort_requested c) true false false false None None false.
Definition control_abort c := FullControl true (outer_live c) (owns_outer c)
  (owner_armed c) (local_live c) (local_taken c) (finish_selected c) (body_error_pending c).
Definition control_open_local c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  (owner_armed c) true None None (body_error_pending c).
Definition control_take_local accept c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  (owner_armed c) false (Some accept) None (body_error_pending c).
Definition control_close_local c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  (owner_armed c) false None None (body_error_pending c).
Definition choose_finish c (dirty:bool) := if abort_requested c then FinishAbort
  else if dirty then FinishPublish else FinishClean.
Definition control_select dirty c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  (owner_armed c) (local_live c) (local_taken c) (Some (choose_finish c dirty)) (body_error_pending c).
(* outer.take() happens before completion; owner is disarmed only after a
   returned Ok(finalization), not on the publication error/early ? path. *)
Definition control_take_outer c := FullControl (abort_requested c) false (owns_outer c)
  (owner_armed c) (local_live c) (local_taken c) (finish_selected c) (body_error_pending c).
Definition control_disarm c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  false (local_live c) (local_taken c) (finish_selected c) (body_error_pending c).
Definition control_drop_owner c := control_disarm (control_take_outer c).
(* Delivery consumes the pending owned-finalization decision. This is ghost
   control provenance, not a new Rust field or a durable receipt. *)
Definition control_deliver c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
  (owner_armed c) (local_live c) (local_taken c) None false.
(* Produced only by an operational body failure, never by SelectFinish. *)
Definition control_body_error c := FullControl (abort_requested c) (outer_live c) (owns_outer c)
 (owner_armed c) (local_live c) (local_taken c) (finish_selected c) true.
Lemma local_success_preserves_abort c :
 abort_requested (control_close_local (control_take_local true c))=abort_requested c.
Proof. reflexivity. Qed.
Lemma abort_then_success_selects_abort c dirty :
 choose_finish (control_close_local (control_take_local true (control_abort c))) dirty=FinishAbort.
Proof. reflexivity. Qed.
Lemma clean_without_abort c : abort_requested c=false -> choose_finish c false=FinishClean.
Proof. intro H;unfold choose_finish;rewrite H;reflexivity. Qed.
Lemma dirty_without_abort c : abort_requested c=false -> choose_finish c true=FinishPublish.
Proof. intro H;unfold choose_finish;rewrite H;reflexivity. Qed.
Lemma consumed_local_stays_consumed c accept :
 local_live (control_close_local (control_take_local accept c))=false.
Proof. reflexivity. Qed.
Lemma failed_finalization_drop_is_noop c :
 outer_live (control_take_outer c)=false /\
 outer_live (control_drop_owner (control_take_outer c))=false /\
 owner_armed (control_drop_owner (control_take_outer c))=false.
Proof. repeat split;reflexivity. Qed.

(* A lineage is an observation of the existing scope stack, not another
   mutable stack. Its active prefix is selected by protection_saved's depth.
   OpeningRoot records the materialized current observed before the two opens;
   it is not yet permission to choose before_change. *)
Inductive scope_root_provenance :=
 | RootsUnknown | OpeningRoot (id:nat) | RootLineage (roots:list (option nat)).
(* Immutable local decoder interface, not another RAM image or history.
   The old decoder is the first projection; the second is the u32 read by Rust. *)
Definition read_counter (read:generation_decoder) f id := option_map snd (read f id).
Lemma decoded_counter_available sector decode read f id d :
 generation_decoding_matches sector decode read ->
 decode (object_flash sector f) id=Some d -> exists n,read_counter read f id=Some n.
Proof.
 intros MATCH READ;specialize (MATCH f id);rewrite READ in MATCH.
 unfold read_counter;destruct (read f id) as [[image n]|];[exists n;reflexivity|discriminate].
Qed.
(* Proof observation of the two allocator inputs in state.rs. The extent is
   the decoded durable BOSS, not current and not the last prepared snapshot. *)
Record allocation_runtime := AllocationRuntime {
 allocation_append : nat;
 allocation_latest : extent
}.
Definition allocation_from_decoded d :=
 AllocationRuntime (extent_end (recovered_boss d)) (recovered_boss d).
Definition read_allocation (read:generation_decoder) f id :=
 option_map (fun result=>allocation_from_decoded (fst result)) (read f id).

Record boundary_evidence := BoundaryEvidence {
  live_certificates : list persistent_certificate;
  client_receipts : list client_receipt;
  volatile_control : option operation_control;
  (* Volatile observation of Pages.page_size; None means no retained RAM. *)
  volatile_page_size : option nat;
  volatile_scope_roots : scope_root_provenance;
  (* None: no retained observation, not a claim that the Rust flag is false. *)
  volatile_runtime_initialized : option bool;
  counter_decoder : generation_decoder;
  volatile_counter : option decoded_counter;
  (* Known latest_registry offset; None forgets the RAM observation. *)
  volatile_latest_registry : option nat;
  volatile_allocation : option allocation_runtime
}.
Definition Evidence live receipts := BoundaryEvidence live receipts None (Some 256) (RootLineage []) None (fun _ _=>None) None None None.
Definition evidence_with_control e c := BoundaryEvidence (live_certificates e) (client_receipts e) c (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e) (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) (volatile_allocation e).
Definition forget_volatile_evidence e := BoundaryEvidence (live_certificates e) (client_receipts e) None None RootsUnknown None (counter_decoder e) None None None.
Definition recovered_page_evidence j id e := BoundaryEvidence (live_certificates e) (client_receipts e)
  (volatile_control e) (Some 256) (RootLineage []) (Some true) (counter_decoder e)
  (read_counter (counter_decoder e) (control_image (journal_control j)) id) (Some id)
  (read_allocation (counter_decoder e) (control_image (journal_control j)) id).
(* Mandatory destination evidence: persistent witnesses are retained, whereas
   reconstruction/fatal phases contain no volatile owner, latch or handles. *)
Definition phase_evidence phase e := BoundaryEvidence (live_certificates e) (client_receipts e)
 (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_control e end)
 (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_page_size e end)
 (match phase with RebuildingBoundary _ | FatalBoundary=>RootsUnknown | _=>volatile_scope_roots e end)
 (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_runtime_initialized e end)
 (counter_decoder e)
 (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_counter e end) (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_latest_registry e end)
 (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_allocation e end).
Lemma phase_evidence_live phase e : live_certificates (phase_evidence phase e)=live_certificates e.
Proof. destruct phase;reflexivity. Qed.
Lemma phase_evidence_receipts phase e : client_receipts (phase_evidence phase e)=client_receipts e.
Proof. destruct phase;reflexivity. Qed.
Lemma forget_volatile_evidence_idempotent e : forget_volatile_evidence (forget_volatile_evidence e)=forget_volatile_evidence e.
Proof. reflexivity. Qed.
Definition evidence_with_live e live := BoundaryEvidence live (client_receipts e) (volatile_control e) (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e) (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) (volatile_allocation e).
Definition certificate_valid sector view ranges decode j c :=
  decode (object_flash sector (control_image (journal_control j))) (certificate_id c) =
    Some (certificate_decoded c) /\
  decoded_root_agrees view ranges (certificate_id c) (certificate_decoded c).
(* Historical indexing only. The immutable certificate stores the observed
   incarnation; sound creation/delivery is proved by the operational consumers.
   No current decoding, current view or retained pages are required of a receipt.
   Keep the two parameters for source compatibility, deliberately unused. *)
Definition receipt_valid (_ : nat -> root_view)
    (_ : compact_entry -> list extent) history r :=
  exists newer older, history = newer ++ N.of_nat (certificate_id (receipt_certificate r)) :: older /\
    length older = receipt_event r.
Lemma receipt_valid_view_independent before after ranges history r :
 receipt_valid before ranges history r -> receipt_valid after ranges history r.
Proof. exact (fun H=>H). Qed.

Definition persistent_evidence sector view ranges decode j e :=
  Forall (certificate_valid sector view ranges decode j) (live_certificates e) /\
  (forall id, hd_error (publications j) = Some (N.of_nat id) ->
    exists c, In c (live_certificates e) /\ certificate_id c = id) /\
  Forall (receipt_valid view ranges (publications j)) (client_receipts e).
Definition boundary_certificate_link (state : transaction_boundary) e := match snd state with
  | IdleBoundary id d _ | ClientBoundary id d _ | PublishingBoundary _ id d _ =>
      In (Certificate id d) (live_certificates e)
  | _ => True end.
Definition enriched_invariant sector data_len boss_ok view marker ranges decode pages state e :=
  common_invariant sector data_len boss_ok view marker ranges decode pages state /\
  persistent_evidence sector view ranges decode (fst state) e /\ boundary_certificate_link state e.

Lemma recovered_page_evidence_invariant sector data_len valid view marker ranges decode pages state e j id :
 enriched_invariant sector data_len valid view marker ranges decode pages state e ->
 enriched_invariant sector data_len valid view marker ranges decode pages state (recovered_page_evidence j id e).
Proof.
 intros [COMMON [PERSIST LINK]]. split;[exact COMMON|]. split;[exact PERSIST|].
 destruct state as [journal phase];destruct phase;exact LINK.
Qed.

(* publication.rs installs latest_registry and mutation_counter after append,
   before closure/collection and delivery. These are RAM observations of the
   SAME decoded certificate; this operation creates no receipt. *)
Definition install_latest_range c e := BoundaryEvidence (live_certificates e)
  (client_receipts e) (volatile_control e) (volatile_page_size e)
  (volatile_scope_roots e) (volatile_runtime_initialized e) (counter_decoder e)
  (volatile_counter e) (Some (certificate_id c))
  (option_map (fun allocation=>AllocationRuntime (allocation_append allocation)
    (recovered_boss (certificate_decoded c))) (volatile_allocation e)).
Definition install_runtime_counter j c e := BoundaryEvidence (live_certificates e)
  (client_receipts e) (volatile_control e) (volatile_page_size e)
  (volatile_scope_roots e) (volatile_runtime_initialized e) (counter_decoder e)
  (read_counter (counter_decoder e) (control_image (journal_control j)) (certificate_id c))
  (volatile_latest_registry e) (volatile_allocation e).
Definition synchronize_publication j c e := install_runtime_counter j c (install_latest_range c e).
Inductive runtime_sync_point := BeforeRuntimeSync | LatestRangeWritten | RuntimeCounterWritten.
Definition runtime_sync_prefix point j c e := match point with
 | BeforeRuntimeSync=>e | LatestRangeWritten=>install_latest_range c e
 | RuntimeCounterWritten=>synchronize_publication j c e end.
Lemma runtime_sync_prefix_reset point j c e :
 forget_volatile_evidence (runtime_sync_prefix point j c e)=forget_volatile_evidence e.
Proof. destruct point;reflexivity. Qed.
Lemma runtime_sync_prefix_receipts point j c e :
 client_receipts (runtime_sync_prefix point j c e)=client_receipts e.
Proof. destruct point;reflexivity. Qed.
(* Delivery only consumes the owner and records the client observation. It
   never installs runtime metadata. observe_client is the historical composite
   adapter, retained for source compatibility with the complete suffix macros. *)
Definition deliver_published j c e := BoundaryEvidence (live_certificates e)
  (Receipt (pred (length (publications j))) c :: client_receipts e)
  (option_map (fun control=>control_deliver (control_disarm (control_take_outer control))) (volatile_control e))
  (volatile_page_size e) (RootLineage []) (volatile_runtime_initialized e)
  (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) (volatile_allocation e).
Definition observe_client j c e := deliver_published j c (synchronize_publication j c e).
Lemma synchronize_publication_no_receipt j c e :
 client_receipts (synchronize_publication j c e)=client_receipts e.
Proof. reflexivity. Qed.
Lemma synchronize_publication_reset j c e :
 forget_volatile_evidence (synchronize_publication j c e)=forget_volatile_evidence e.
Proof. reflexivity. Qed.
Lemma deliver_published_runtime_unchanged j c e :
 volatile_counter (deliver_published j c e)=volatile_counter e /\
 volatile_latest_registry (deliver_published j c e)=volatile_latest_registry e /\
 volatile_allocation (deliver_published j c e)=volatile_allocation e.
Proof. repeat split;reflexivity. Qed.

(* Internal control effects; storage operations remain the existing episodes.
   In the external initialized slice a mutation invalidates current (root=[]).
   A nonempty current root is the retained prestate; arbitrary root replacement
   is not a service of this controller. *)
Inductive controller_action :=
 | ArmOwned | RejectedBegin | JoinOuter | RequestAbort | OpenLocal | TakeLocal (accept:bool)
 | LocalClosed | SelectFinish | TakeOuter | DisarmOwner | DropOwner | DeliverOwned | ForgetControl
 | TakeBodyOuter | DeliverBodyError.
Definition phase_dirty phase := match phase with
 | OpenBoundary _ root _ => match root with []=>true | _=>false end
 | _=>false end.
Definition controller_caller action phase c : Prop := match action with
 | ArmOwned => match phase with IdleBoundary _ _ _ => True | _=>False end
 | RejectedBegin => match phase with OpenBoundary _ _ _ | OperationBoundary _ _ _ => True | _=>False end
 | JoinOuter => match phase with OpenBoundary _ _ _ => True | _=>False end
 | RequestAbort => match phase with OpenBoundary _ _ _ | OperationBoundary _ _ _ => outer_live c=true | _=>False end
 | OpenLocal => outer_live c=true /\ local_live c=false /\
      match phase with OperationBoundary _ _ _=>True|_=>False end
 | TakeLocal accept => local_live c=true /\
      match phase with OperationBoundary _ _ _=>True
       | FrozenBoundary _ _ (Some _) _=>accept=false /\ body_error_pending c=true /\ finish_selected c=None
       | _=>False end
 | LocalClosed => local_taken c<>None /\
      match phase with OpenBoundary _ _ _=>True
       | FrozenBoundary _ _ (Some _) _=>local_taken c=Some false /\ body_error_pending c=true /\ finish_selected c=None
       | _=>False end
 | SelectFinish => owns_outer c=true /\ owner_armed c=true /\ outer_live c=true /\
      local_live c=false /\ local_taken c=None /\
      match phase with OpenBoundary _ _ _=>body_error_pending c=false|_=>False end
 | TakeOuter => match phase with
      | OpenBoundary _ _ _ | FrozenBoundary _ _ _ _
      | PublishingBoundary CandidatePrepared _ _ _ =>
          finish_selected c<>None /\ outer_live c=true
      | _=>False end
 | DisarmOwner => outer_live c=false /\
      match phase with IdleBoundary _ _ _=>True|ClientBoundary _ _ _=>True|_=>False end
 | DropOwner => match phase with OpenBoundary _ _ _ | IdleBoundary _ _ _ | FrozenBoundary _ _ _ _ => owner_armed c=true /\ outer_live c=false | _=>False end
 | DeliverOwned => owner_armed c=false /\ outer_live c=false /\ finish_selected c<>None /\
      match phase with IdleBoundary _ _ _ | FrozenBoundary _ _ _ _=>True|_=>False end
 | TakeBodyOuter => body_error_pending c=true /\ finish_selected c=None /\
     outer_live c=true /\ local_live c=false /\ local_taken c=None /\
     match phase with OpenBoundary _ _ _ | FrozenBoundary _ _ _ _=>True|_=>False end
 | DeliverBodyError => body_error_pending c=true /\ finish_selected c=None /\
     owner_armed c=false /\ outer_live c=false /\
     match phase with IdleBoundary _ _ _=>True
       | FrozenBoundary _ _ _ ram=>protection_saved ram=[] | _=>False end
 | ForgetControl => match phase with RebuildingBoundary _=>True|FatalBoundary=>True|_=>False end
 end.
Definition controller_update action phase c : option operation_control := match action with
 | ArmOwned => Some (control_begin c)
 | RejectedBegin => Some (control_rejected_begin c) | JoinOuter => Some (control_join c)
 | RequestAbort => Some (control_abort c) | OpenLocal => Some (control_open_local c)
 | TakeLocal accept => Some (control_take_local accept c)
 | LocalClosed => Some (control_close_local c)
 | SelectFinish => Some (control_select (phase_dirty phase) c)
 | TakeOuter => Some (control_take_outer c)
 | DisarmOwner => Some (control_disarm c) | DropOwner => Some (control_drop_owner c)
 | DeliverOwned => Some (control_deliver c)
 | TakeBodyOuter => Some (control_take_outer c)
 | DeliverBodyError => Some (control_deliver c)
 | ForgetControl => None end.
Definition controller_read e := match volatile_control e with Some c=>c|None=>idle_control end.
Definition controller_root_update action phase origin := match action with
 | ArmOwned => match phase with IdleBoundary id _ _=>OpeningRoot id | _=>RootsUnknown end
 | OpenLocal => match origin with OpeningRoot id=>RootLineage [Some id;Some id] | _=>RootsUnknown end
 | ForgetControl=>RootsUnknown
 | _=>origin end.
Definition controller_evidence action phase e :=
 BoundaryEvidence (live_certificates e) (client_receipts e)
   (controller_update action phase (controller_read e)) (volatile_page_size e)
   (controller_root_update action phase (volatile_scope_roots e)) (volatile_runtime_initialized e) (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) (match phase with RebuildingBoundary _ | FatalBoundary=>None | _=>volatile_allocation e end).
Definition body_error_evidence e := evidence_with_control e (Some (control_body_error (controller_read e))).
Lemma body_error_evidence_live e : live_certificates (body_error_evidence e)=live_certificates e.
Proof. reflexivity. Qed.
Lemma body_error_evidence_receipts e : client_receipts (body_error_evidence e)=client_receipts e.
Proof. reflexivity. Qed.

Lemma controller_evidence_live action phase e :
 live_certificates (controller_evidence action phase e)=live_certificates e.
Proof. reflexivity. Qed.
Lemma controller_evidence_receipts action phase e :
 client_receipts (controller_evidence action phase e)=client_receipts e.
Proof. reflexivity. Qed.
Lemma controller_select_abort phase c : abort_requested c=true ->
 finish_selected (control_select (phase_dirty phase) c)=Some FinishAbort.
Proof. intro H;cbn;unfold choose_finish;rewrite H;reflexivity. Qed.
Lemma joined_cannot_finalize phase c : owns_outer c=false ->
 ~controller_caller SelectFinish phase c.
Proof. simpl;intros H [BAD _];congruence. Qed.
Lemma consumed_handle_cannot_take phase c accept : local_live c=false ->
 ~controller_caller (TakeLocal accept) phase c.
Proof. simpl;intros H [BAD _];congruence. Qed.

Lemma rejected_begin_clears_abort phase c :
 controller_update RejectedBegin phase c=Some (control_rejected_begin c) /\
 abort_requested (control_rejected_begin c)=false /\
 outer_live (control_rejected_begin c)=outer_live c.
Proof. repeat split;reflexivity. Qed.
Lemma clean_owned_selects_retained image boss ram :
 choose_finish (control_close_local (control_take_local true
   (control_open_local (control_begin idle_control))))
   (phase_dirty (OpenBoundary image [boss] ram))=FinishClean.
Proof. reflexivity. Qed.
Lemma changed_owned_selects_publication image ram :
 choose_finish (control_close_local (control_take_local true
   (control_open_local (control_begin idle_control))))
   (phase_dirty (OpenBoundary image [] ram))=FinishPublish.
Proof. reflexivity. Qed.

Lemma terminal_control_only_forget phase c action :
 (phase=FatalBoundary \/ exists pc,phase=RebuildingBoundary pc) ->
 controller_caller action phase c -> action=ForgetControl.
Proof.
 intros [EQ|[pc EQ]];subst phase;destruct action;simpl;intuition discriminate.
Qed.

(* Fresh boot RAM is described by its program counter, not the metadata
   carried before reset. initialized is already true during Retaining, but
   coverage and ordinary access are NOT asserted there. Stopped deliberately
   exposes no operational table: ensure_protection's invalidation is followed
   by the production recovery caller's expect/panic. *)
Definition boot_pages_size pc : option nat :=
 match pc with
 | Selecting | Decoding _ | Installing _ _ _ => Some 0
 | Retaining _ _ _ _ | Caching _ _ _ | Returning _ _ _ | Usable _ _ _ => Some 256
 | Stopped => None end.
Theorem retaining_pages_are_partial sector data_len valid view marker ranges decode pages
 j id d todo ram :
 boot_invariant sector data_len valid view marker ranges decode pages (j,Retaining id d todo ram) ->
 boot_pages_size (Retaining id d todo ram)=Some 256 /\
 (exists done,done++todo=decoded_ranges marker ranges d /\
   ram=recovery_retains done (decoded_fresh marker ranges d)) /\
 ordinary_access (j,Retaining id d todo ram)=False.
Proof. intros [_ [_ [LINK PARTIAL]]];split;[reflexivity|];split;[exact PARTIAL|reflexivity]. Qed.
Lemma recovered_metadata_matches_boot j id d ram e :
 volatile_page_size (recovered_page_evidence j id (forget_volatile_evidence e))=
 boot_pages_size (Usable id d ram) /\
 volatile_control (recovered_page_evidence j id (forget_volatile_evidence e))=None.
Proof. split;reflexivity. Qed.
Lemma reset_forgets_page_metadata e : volatile_page_size (forget_volatile_evidence e)=None.
Proof. reflexivity. Qed.


Definition active_snapshot_roots phase e : option (list (option nat)) :=
 let depth:=match phase with
 | OpenBoundary _ _ ram | OperationBoundary _ _ ram | PublishingBoundary _ _ _ ram
 | FrozenBoundary _ _ _ ram => Some (length (protection_saved ram))
 | IdleBoundary _ _ _ | ClientBoundary _ _ _ => Some 0
 | _=>None end in
 match depth,volatile_scope_roots e with
 | Some n,RootLineage roots => if n<=?length roots then Some (firstn n roots) else None
 | _,_=>None end.
Definition unresolved_snapshot (root:option nat) := match root with None=>true|Some _=>false end.
Lemma unknown_roots_do_not_select phase e : volatile_scope_roots e=RootsUnknown ->
 active_snapshot_roots phase e=None.
Proof. intro H;unfold active_snapshot_roots;rewrite H;destruct phase;reflexivity. Qed.
Lemma roots_are_not_dependencies id : unresolved_snapshot (Some id)=false /\
 unresolved_snapshot None=true.
Proof. split;reflexivity. Qed.

(* Projection equality cannot recover a concrete option, even with empty
   object dependencies on the materialized side. *)
Lemma snapshot_projection_loses_presence boss id deps :
 snapshot_dependencies boss (None,boss id::deps)=snapshot_dependencies boss (Some id,deps) /\
 (None:option nat)<>Some id.
Proof. split;[reflexivity|discriminate]. Qed.
Lemma usable_boot_roots_reconstructed j id e :
 volatile_scope_roots (recovered_page_evidence j id (forget_volatile_evidence e))=RootLineage [].
Proof. reflexivity. Qed.

(* state.rs::initialize_persistence_runtime_state writes this field, independently
   of Pages and of the physical marker. It is not performed by arbitrary Evidence. *)
Definition initialized_runtime_evidence e := BoundaryEvidence
 (live_certificates e) (client_receipts e) (volatile_control e)
 (volatile_page_size e) (volatile_scope_roots e) (Some true) (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) (volatile_allocation e).
Lemma initialize_runtime_observed e :
 volatile_runtime_initialized (initialized_runtime_evidence e)=Some true.
Proof. reflexivity. Qed.
Lemma reset_forgets_runtime e : volatile_runtime_initialized (forget_volatile_evidence e)=None.
Proof. reflexivity. Qed.
Lemma recovered_runtime_observed j id e : volatile_runtime_initialized (recovered_page_evidence j id e)=Some true.
Proof. reflexivity. Qed.

Lemma initialized_runtime_evidence_invariant sector data_len valid view marker ranges decode pages state e :
 enriched_invariant sector data_len valid view marker ranges decode pages state e ->
 enriched_invariant sector data_len valid view marker ranges decode pages state (initialized_runtime_evidence e).
Proof.
 intros [COMMON [PERSIST LINK]]. split;[exact COMMON|]. split;[exact PERSIST|].
 destruct state as [journal phase];destruct phase;exact LINK.
Qed.

(* Rust publication::write_snapshot reads a u32 runtime counter. This local
   expression does not install either the image generation or the runtime. *)
Definition boss_generation_max : N := 4294967295%N.
Definition boss_checked_generation (counter:N) : option N :=
 if (counter <? boss_generation_max)%N then Some (N.succ counter) else None.
Lemma boss_checked_generation_success counter next :
 boss_checked_generation counter=Some next <->
 (counter<boss_generation_max)%N /\ next=N.succ counter.
Proof.
 unfold boss_checked_generation;destruct (counter <? boss_generation_max)%N eqn:LT.
 - apply N.ltb_lt in LT;split;[intro E;inversion E;auto|intros [_ ->];reflexivity].
 - apply N.ltb_ge in LT;split;[discriminate|intros [BAD _];lia].
Qed.
Lemma boss_checked_generation_overflow counter :
 (counter<=boss_generation_max)%N ->
 (boss_checked_generation counter=None <-> counter=boss_generation_max).
Proof.
 intro BOUND;unfold boss_checked_generation.
 destruct (counter <? boss_generation_max)%N eqn:LT.
 - apply N.ltb_lt in LT;split;[discriminate|intro E;subst;lia].
 - apply N.ltb_ge in LT;split;[intro;lia|intro;reflexivity].
Qed.
Lemma boss_generation_boundary_cases :
 boss_checked_generation 4294967294%N=Some 4294967295%N /\
 boss_checked_generation 4294967295%N=None.
Proof. split;reflexivity. Qed.

Definition initialized_counter_evidence read counter e := BoundaryEvidence
 (live_certificates e) (client_receipts e) (volatile_control e)
 (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e)
 read (Some counter) (volatile_latest_registry e) (volatile_allocation e).
Lemma reset_forgets_counter e : volatile_counter (forget_volatile_evidence e)=None.
Proof. reflexivity. Qed.
Lemma recovered_counter_decoded j id e :
 volatile_counter (recovered_page_evidence j id (forget_volatile_evidence e))=
 read_counter (counter_decoder e) (control_image (journal_control j)) id.
Proof. reflexivity. Qed.
Lemma client_counter_installed j c e :
 volatile_counter (observe_client j c e)=
 read_counter (counter_decoder e) (control_image (journal_control j)) (certificate_id c).
Proof. reflexivity. Qed.

Lemma certified_decoding_read sector data_len valid view marker ranges decode pages j phase e id d :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,phase) e ->
 In (Certificate id d) (live_certificates e) ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d.
Proof.
 intros [_ [[ALL _] _]] MEMBER.
 apply Forall_forall with (x:=Certificate id d) in ALL;[exact (proj1 ALL)|exact MEMBER].
Qed.
Lemma generation_ready_read sector data_len valid view marker ranges decode pages j id d ram e :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,IdleBoundary id d ram) e ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d.
Proof. intro INV;eapply certified_decoding_read;[exact INV|exact (proj2 (proj2 INV))]. Qed.
Lemma generation_client_read sector data_len valid view marker ranges decode pages j id d ram e :
 enriched_invariant sector data_len valid view marker ranges decode pages (j,ClientBoundary id d ram) e ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d.
Proof. intro INV;eapply certified_decoding_read;[exact INV|exact (proj2 (proj2 INV))]. Qed.

(* Exact, local byte-dependence of the joint decoder. No global preservation
   of roots, journal selection or RAM is part of this format contract. *)
Lemma generation_journal_transport g sector data_len valid read j j' id d n :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 logged_invariant sector 256 data_len valid j ->
 generation_decoding_local sector read ->
 read (control_image (journal_control j)) id=Some (d,n) ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid) j j' ->
 read (control_image (journal_control j')) id=Some (d,n).
Proof.
 intros G DIV INV LOCAL READ RUN;eapply LOCAL;[exact READ|].
 intros r addr MEMBER AT;unfold object_flash.
 exact (logged_trace_frame_after_journal g sector 256 data_len valid j j' (2*sector+addr) G DIV INV RUN ltac:(lia)).
Qed.
Theorem client_counter_from_validation g sector data_len valid j j' id d n e :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 logged_invariant sector 256 data_len valid j ->
 generation_decoding_local sector (counter_decoder e) ->
 counter_decoder e (control_image (journal_control j)) id=Some (d,n) ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid) j j' ->
 volatile_counter (observe_client j' (Certificate id d) e)=Some n.
Proof.
 intros G DIV INV LOCAL READ RUN;rewrite client_counter_installed.
 unfold read_counter;simpl.
 rewrite (generation_journal_transport g sector data_len valid _ j j' id d n G DIV INV LOCAL READ RUN).
 reflexivity.
Qed.

Lemma initialized_counter_evidence_invariant sector data_len valid view marker ranges decode pages state e read counter :
 enriched_invariant sector data_len valid view marker ranges decode pages state e ->
 enriched_invariant sector data_len valid view marker ranges decode pages state
   (initialized_counter_evidence read counter e).
Proof.
 intros [COMMON [PERSIST LINK]]. split;[exact COMMON|]. split;[exact PERSIST|].
 destruct state as [journal phase];destruct phase;exact LINK.
Qed.

Lemma accepted_outer_root image root ram e old :
 active_snapshot_roots (OperationBoundary image root ram) e=Some [Some old;Some old] ->
 let accepted:=data_next (DataClose [physical_authority ram] (physical_authority ram) true) ram in
 let taken:=controller_evidence (TakeLocal true) (OperationBoundary image root ram) e in
 let closed:=controller_evidence LocalClosed (OpenBoundary image root accepted) taken in
 let selected:=controller_evidence SelectFinish (OpenBoundary image root accepted) closed in
 active_snapshot_roots (OpenBoundary image root accepted) selected=Some [Some old].
Proof.
 unfold active_snapshot_roots;cbn.
 destruct (volatile_scope_roots e) as [|id|roots];try discriminate.
 destruct (length (protection_saved ram)<=?length roots) eqn:BOUND;try discriminate.
 intro EQ;inversion EQ as [PREFIX].
 apply Nat.leb_le in BOUND.
 assert (DEPTH:length (protection_saved ram)=2).
 { apply (f_equal (@length (option nat))) in PREFIX.
   rewrite firstn_length, Nat.min_l in PREFIX by exact BOUND;exact PREFIX. }
 rewrite DEPTH in PREFIX.
 destruct roots as [|x [|y rest]];cbn in PREFIX;try discriminate.
 inversion PREFIX;reflexivity.
Qed.

(* Initialization and usable recovery produce the observation from the root
   actually selected. This does not identify an arbitrary current snapshot
   with latest_registry. Partial boot keeps no exported RAM observation. *)
Definition initialized_latest_evidence id e := BoundaryEvidence
 (live_certificates e) (client_receipts e) (volatile_control e)
 (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e)
 (counter_decoder e) (volatile_counter e) (Some id) None.
Lemma reset_forgets_latest e : volatile_latest_registry (forget_volatile_evidence e)=None.
Proof. reflexivity. Qed.
Lemma usable_boot_latest j id e : volatile_latest_registry (recovered_page_evidence j id e)=Some id.
Proof. reflexivity. Qed.
Lemma acknowledged_latest j c e : volatile_latest_registry (observe_client j c e)=Some (certificate_id c).
Proof. reflexivity. Qed.


Definition evidence_with_allocation e observation := BoundaryEvidence
 (live_certificates e) (client_receipts e) (volatile_control e)
 (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e)
 (counter_decoder e) (volatile_counter e) (volatile_latest_registry e) observation.

(* The write at storage.rs precedes Pages::reserve. Its argument is the range
   selected by the acquisition, never a caller-chosen replacement cursor. *)
Definition advance_allocation_evidence r e := BoundaryEvidence
 (live_certificates e) (client_receipts e) (volatile_control e)
 (volatile_page_size e) (volatile_scope_roots e) (volatile_runtime_initialized e)
 (counter_decoder e) (volatile_counter e) (volatile_latest_registry e)
 (option_map (fun a=>AllocationRuntime (extent_end r) (allocation_latest a))
   (volatile_allocation e)).
Lemma advance_allocation_observed r e a : volatile_allocation e=Some a ->
 volatile_allocation (advance_allocation_evidence r e)=
 Some (AllocationRuntime (extent_end r) (allocation_latest a)).
Proof. intro H;cbn;now rewrite H. Qed.
Lemma reset_forgets_allocation e :
 volatile_allocation (forget_volatile_evidence e)=None.
Proof. reflexivity. Qed.
Lemma recovered_allocation_decoded j id e d n :
 counter_decoder e (control_image (journal_control j)) id=Some (d,n) ->
 volatile_allocation (recovered_page_evidence j id (forget_volatile_evidence e))=
 Some (allocation_from_decoded d).
Proof. intro H;cbn [recovered_page_evidence forget_volatile_evidence volatile_allocation counter_decoder].
 unfold read_allocation;now rewrite H. Qed.

Definition initialized_allocation_evidence j id e :=
 evidence_with_allocation e
   (read_allocation (counter_decoder e) (control_image (journal_control j)) id).
Lemma allocation_from_same_decoder sector decode j id e d :
 generation_decoding_matches sector decode (counter_decoder e) ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d ->
 read_allocation (counter_decoder e) (control_image (journal_control j)) id=
 Some (allocation_from_decoded d).
Proof.
 intros MATCH READ;specialize (MATCH (control_image (journal_control j)) id).
 rewrite READ in MATCH;unfold read_allocation.
 destruct (counter_decoder e (control_image (journal_control j)) id) as [[decoded n]|];
   cbn in MATCH |- *;inversion MATCH;reflexivity.
Qed.
Lemma allocation_recovered_after_reset sector decode j id e d :
 generation_decoding_matches sector decode (counter_decoder e) ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d ->
 volatile_allocation (recovered_page_evidence j id (forget_volatile_evidence e))=
 Some (allocation_from_decoded d).
Proof. intros MATCH READ;apply allocation_from_same_decoder with (sector:=sector) (decode:=decode);assumption. Qed.
