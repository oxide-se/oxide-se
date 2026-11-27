From Stdlib Require Import List Arith NArith Lia Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage ScopeOwnership CompactImage CompactUpdates
  CollectionRoots PreparedAuthority JournalHistory JournalRequests JournalReachableShape JournalRecoveryTrace
  PublicationPreparation PreparationOutcomes BootReconstruction BootTransaction TransactionBoundary
  PersistentBoundary DataEpisode PublicationResetWitness JournalAppendAuthority FreerPrepared FreerPublicationReturn FreerPersistentBoundary FreerDataEpisode IncarnationBoundary RecycledWriter JournalRawOrder NeutralizationBoundary RawNeutralizationBoundary AllocationAdmission FreerAllocationAdmission RecyclingErase RecyclingEraseBoundary RecyclingSearch Neutralization.
Import ListNotations.

(* An execution boundary plus its existing ghost evidence. No new flash, table,
   image, journal or physical history is stored in this pairing. *)
Definition recycling_cursor_evidence result r e :=
 evidence_with_allocation e (match neutral_end_ result with
 | NeutralSuccess=>volatile_allocation (advance_allocation_evidence r e)
 | _=>volatile_allocation e end).

Definition execution_boundary := (transaction_boundary * boundary_evidence)%type.
(* Three observable RAM prefixes of storage::reserve_persistent_span_sized.
   The physical commands are already over. This is a projection of the SAME
   boundary, not a second execution relation or an atomicity assumption. *)
Inductive acquisition_ram_point := EffectsDone | CursorAdvanced | ReservationDone.
Definition acquisition_ram_prefix point boss r s e := match point with
 | EffectsDone=>(s,e)
 | CursorAdvanced=>(s,advance_allocation_evidence r e)
 | ReservationDone=>(reservation_state boss r s,advance_allocation_evidence r e)
 end.
Definition acquisition_ram_reset point boss r s e j : execution_boundary :=
 let reached:=acquisition_ram_prefix point boss r s e in
 ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence (snd reached)).
Lemma acquisition_ram_reset_same point boss r s e j :
 acquisition_ram_reset point boss r s e j=
 ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e).
Proof. destruct point;reflexivity. Qed.
Lemma acquisition_ram_prefix_effects point boss r s e :
 live_certificates (snd (acquisition_ram_prefix point boss r s e))=live_certificates e /\
 client_receipts (snd (acquisition_ram_prefix point boss r s e))=client_receipts e.
Proof. destruct point;split;reflexivity. Qed.

Definition boundary_journal (x : execution_boundary) := fst (fst x).
Definition boundary_receipts (x : execution_boundary) := client_receipts (snd x).
Definition emitted_receipts (event : option client_receipt) :=
  match event with None => [] | Some r => [r] end.

(* RAM control is absent at every interrupted/stopped boundary. This is
   separate from the persistent certificates and from numeric reconstruction. *)
Definition terminal_control_absent (x:execution_boundary) : Prop :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary => volatile_control (snd x)=None
 | _ => True end.
Definition terminal_roots_absent (x:execution_boundary) : Prop :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary => volatile_scope_roots (snd x)=RootsUnknown
 | _=>True end.
Lemma phase_evidence_roots j phase e :
 terminal_roots_absent ((j,phase),phase_evidence phase e).
Proof. destruct phase;cbn;auto. Qed.
Lemma phase_evidence_boundary_roots boundary e :
 terminal_roots_absent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary as [j phase];apply phase_evidence_roots. Qed.

Definition terminal_allocation_absent (x:execution_boundary) : Prop :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary => volatile_allocation (snd x)=None
 | _=>True end.
Lemma phase_evidence_allocation j phase e :
 terminal_allocation_absent ((j,phase),phase_evidence phase e).
Proof. destruct phase;cbn;auto. Qed.
Lemma phase_evidence_boundary_allocation boundary e :
 terminal_allocation_absent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary as [j phase];apply phase_evidence_allocation. Qed.

Lemma phase_evidence_terminal j phase e :
 terminal_control_absent ((j,phase),phase_evidence phase e).
Proof. destruct phase;cbn;auto. Qed.

Lemma phase_evidence_boundary boundary e :
 terminal_control_absent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary as [j phase];apply phase_evidence_terminal. Qed.

Lemma phase_evidence_idle id d ram e : phase_evidence (IdleBoundary id d ram) e=e.
Proof. destruct e;reflexivity. Qed.
Lemma phase_evidence_client id d ram e : phase_evidence (ClientBoundary id d ram) e=e.
Proof. destruct e;reflexivity. Qed.
Lemma phase_evidence_open image root ram e : phase_evidence (OpenBoundary image root ram) e=e.
Proof. destruct e;reflexivity. Qed.
Lemma phase_evidence_operation image root ram e : phase_evidence (OperationBoundary image root ram) e=e.
Proof. destruct e;reflexivity. Qed.
Lemma phase_evidence_publishing stage id d ram e : phase_evidence (PublishingBoundary stage id d ram) e=e.
Proof. destruct e;reflexivity. Qed.
Lemma phase_evidence_frozen old candidate current ram e : phase_evidence (FrozenBoundary old candidate current ram) e=e.
Proof. destruct e;reflexivity. Qed.
#[export] Hint Rewrite phase_evidence_idle phase_evidence_client phase_evidence_open phase_evidence_operation phase_evidence_publishing phase_evidence_frozen forget_volatile_evidence_idempotent : control_evidence.

(* Volatile observation, separate from coverage. During reconstruction the
   boot program counter owns the fresh table; no pre-reset metadata is reused. *)
Definition page_metadata_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary => volatile_page_size (snd x)=None
 | _ => volatile_page_size (snd x)=Some 256 end.
Lemma phase_page_metadata j phase e : volatile_page_size e=Some 256 ->
 page_metadata_coherent ((j,phase),phase_evidence phase e).
Proof. intro M;destruct phase;cbn;auto. Qed.
Lemma boundary_page_metadata boundary e : volatile_page_size e=Some 256 ->
 page_metadata_coherent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_page_metadata. Qed.

(* Runtime state is independent of Pages metadata. During boot the existing
   boot phases record installation; ordinary evidence is exported only at resume. *)
Definition runtime_metadata_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary => volatile_runtime_initialized (snd x)=None
 | _ => volatile_runtime_initialized (snd x)=Some true end.
Lemma phase_runtime_metadata j phase e : volatile_runtime_initialized e=Some true ->
 runtime_metadata_coherent ((j,phase),phase_evidence phase e).
Proof. intro M;destruct phase;cbn;auto. Qed.
Lemma boundary_runtime_metadata boundary e : volatile_runtime_initialized e=Some true ->
 runtime_metadata_coherent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_runtime_metadata. Qed.

Definition counter_metadata_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary=>volatile_counter (snd x)=None
 | _=>exists n,volatile_counter (snd x)=Some n end.
Lemma phase_counter_metadata j phase e : (exists n,volatile_counter e=Some n) ->
 counter_metadata_coherent ((j,phase),phase_evidence phase e).
Proof. intro M;destruct phase;cbn;auto. Qed.
Lemma boundary_counter_metadata boundary e : (exists n,volatile_counter e=Some n) ->
 counter_metadata_coherent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_counter_metadata. Qed.

Definition allocation_metadata_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary=>volatile_allocation (snd x)=None
 | _=>exists n,volatile_allocation (snd x)=Some n end.
Lemma phase_allocation_metadata j phase e : (exists n,volatile_allocation e=Some n) ->
 allocation_metadata_coherent ((j,phase),phase_evidence phase e).
Proof. intro M;destruct phase;cbn;auto. Qed.
Lemma boundary_allocation_metadata boundary e : (exists n,volatile_allocation e=Some n) ->
 allocation_metadata_coherent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_allocation_metadata. Qed.

(* Provenance postcondition on the existing transitions, not a new machine. *)
Definition counter_origin sector (decode:flash -> nat -> option recovery_decoding) before (after:execution_boundary) :=
 volatile_counter (snd after)=before \/ volatile_counter (snd after)=None \/
 exists id d,decode (object_flash sector (control_image (journal_control (boundary_journal after)))) id=Some d /\
 volatile_counter (snd after)=read_counter (counter_decoder (snd after))
   (control_image (journal_control (boundary_journal after))) id.
Lemma phase_counter_origin sector decode j phase e :
 counter_origin sector decode (volatile_counter e) ((j,phase),phase_evidence phase e).
Proof. destruct phase;unfold counter_origin;cbn;auto. Qed.
Lemma boundary_counter_origin sector decode boundary e :
 counter_origin sector decode (volatile_counter e) (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_counter_origin. Qed.

Lemma phase_counter_origin_same sector decode before j phase e :
 volatile_counter e=before -> counter_origin sector decode before ((j,phase),phase_evidence phase e).
Proof. intro EQ;rewrite <- EQ;apply phase_counter_origin. Qed.
Lemma boundary_counter_origin_same sector decode before boundary e :
 volatile_counter e=before -> counter_origin sector decode before (boundary,phase_evidence (snd boundary) e).
Proof. intro EQ;rewrite <- EQ;apply boundary_counter_origin. Qed.

(* latest_registry is a runtime observation, not current and not a second
   physical history. Unknown is forgotten at reset; initialization/recovery and
   completed append summaries are its only producers. *)
Definition latest_metadata_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | RebuildingBoundary _ | FatalBoundary=>volatile_latest_registry (snd x)=None
 | _=>exists id,volatile_latest_registry (snd x)=Some id end.
Lemma phase_latest_metadata j phase e : (exists id,volatile_latest_registry e=Some id) ->
 latest_metadata_coherent ((j,phase),phase_evidence phase e).
Proof. intro M;destruct phase;cbn;auto. Qed.
Lemma boundary_latest_metadata boundary e : (exists id,volatile_latest_registry e=Some id) ->
 latest_metadata_coherent (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_latest_metadata. Qed.
Definition latest_at_head (x:execution_boundary) :=
 option_map N.of_nat (volatile_latest_registry (snd x))=hd_error (publications (boundary_journal x)).
(* Runtime authority is synchronized at ordinary call boundaries. During
   uncertain append or recovery no such RAM equality is asserted. *)
Definition ordinary_latest_coherent (x:execution_boundary) :=
 match snd (fst x) with
 | IdleBoundary _ _ _ | ClientBoundary _ _ _ | OpenBoundary _ _ _
 | OperationBoundary _ _ _ | PublishingBoundary CandidatePrepared _ _ _
 | PublishingBoundary DurableSynchronized _ _ _=>latest_at_head x
 | _=>True end.
Lemma ordinary_latest_phase j phase e :
 ordinary_latest_coherent ((j,phase),e) ->
 ordinary_latest_coherent ((j,phase),phase_evidence phase e).
Proof. destruct phase;try (destruct stage);cbn;auto. Qed.

Definition latest_origin before (x:execution_boundary) :=
 volatile_latest_registry (snd x)=before \/ volatile_latest_registry (snd x)=None \/ latest_at_head x.
Lemma phase_latest_origin j phase e :
 latest_origin (volatile_latest_registry e) ((j,phase),phase_evidence phase e).
Proof. destruct phase;unfold latest_origin;cbn;auto. Qed.
Lemma boundary_latest_origin boundary e :
 latest_origin (volatile_latest_registry e) (boundary,phase_evidence (snd boundary) e).
Proof. destruct boundary;apply phase_latest_origin. Qed.
Lemma phase_latest_origin_same before j phase e : volatile_latest_registry e=before ->
 latest_origin before ((j,phase),phase_evidence phase e).
Proof. intro EQ;rewrite <-EQ;apply phase_latest_origin. Qed.
Lemma boundary_latest_origin_same before boundary e : volatile_latest_registry e=before ->
 latest_origin before (boundary,phase_evidence (snd boundary) e).
Proof. intro EQ;rewrite <-EQ;apply boundary_latest_origin. Qed.

(* Typed internal controller service. Its callee supplies no safety invariant. *)
Inductive ControllerAPI : interface :=
 | ControllerCommand : controller_action -> ControllerAPI unit
 | EnsureProtectionProbe : ControllerAPI bool
 | BeforeChangeProbe : ControllerAPI bool
 | RuntimeInitializedProbe : ControllerAPI bool
 | NextGenerationProbe : ControllerAPI (option N).
Definition controller_service_caller (x:execution_boundary) A (call:ControllerAPI A) :=
 match call with ControllerCommand action=>
 controller_caller action (snd (fst x)) (controller_read (snd x))
 | NextGenerationProbe=>exists n,volatile_counter (snd x)=Some n
 | RuntimeInitializedProbe=>exists b,volatile_runtime_initialized (snd x)=Some b
 | EnsureProtectionProbe=>True
 | BeforeChangeProbe=>exists roots,active_snapshot_roots (snd (fst x)) (snd x)=Some roots /\
   match snd (fst x) with OperationBoundary _ _ ram=>protection_frozen ram=false | _=>False end end.
Definition controller_service_callee (x:execution_boundary) A (call:ControllerAPI A) : A->Prop :=
 match call with ControllerCommand _=>fun _=>True
 | NextGenerationProbe=>fun answer=>exists n,volatile_counter (snd x)=Some n /\
     answer=boss_checked_generation (counter_value n)
 | RuntimeInitializedProbe=>fun answer=>volatile_runtime_initialized (snd x)=Some answer
 | EnsureProtectionProbe=>fun answer=>answer=
   match volatile_page_size (snd x) with Some n=>negb (Nat.eqb n 0) | None=>false end
 | BeforeChangeProbe=>fun answer=>match active_snapshot_roots (snd (fst x)) (snd x) with
   | Some roots=>answer=existsb unresolved_snapshot roots | None=>False end end.
Definition controller_service_update (x:execution_boundary) A (call:ControllerAPI A) : A->execution_boundary :=
 match call with ControllerCommand action=>fun _=>
 (fst x,controller_evidence action (snd (fst x)) (snd x))
 | EnsureProtectionProbe=>fun _=>x
 | BeforeChangeProbe=>fun _=>x | RuntimeInitializedProbe=>fun _=>x | NextGenerationProbe=>fun _=>x end.
Definition controller_contract := make_contract controller_service_update controller_service_caller controller_service_callee.
Definition controller_program action : impure ControllerAPI unit :=
 request_then (ControllerCommand action) (fun _=>local tt).
Lemma controller_program_post action x result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
  controller_contract (controller_program action)) x result final ->
 result=tt /\ final=(fst x,controller_evidence action (snd (fst x)) (snd x)).
Proof.
 intro RUN;unfold controller_program in RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[OK UPDATE] REST]]];subst middle.
 unroll_post REST;destruct REST as [R S];subst result final;split;reflexivity.
Qed.

Definition ensure_protection_probe : impure ControllerAPI bool :=
 request_then EnsureProtectionProbe (fun answer=>local answer).
Lemma ensure_protection_probe_ready x : volatile_page_size (snd x)=Some 256 ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract ensure_protection_probe) x true x.
Proof.
 intro M;unfold ensure_protection_probe;simpl.
 exists true,x;split;[split;[change (true=match volatile_page_size (snd x) with Some n=>negb (Nat.eqb n 0) | None=>false end);rewrite M;reflexivity|reflexivity]|].
 split;reflexivity.
Qed.
Lemma ensure_protection_probe_result x answer final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract ensure_protection_probe) x answer final ->
 answer=match volatile_page_size (snd x) with Some n=>negb (Nat.eqb n 0) | None=>false end /\ final=x.
Proof.
 intro RUN;unfold ensure_protection_probe in RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[R S] T]]];subst middle.
 unroll_post T;destruct T as [A B];subst answer final;auto.
Qed.

Definition runtime_initialized_probe : impure ControllerAPI bool :=
 request_then RuntimeInitializedProbe (fun answer=>local answer).
Lemma runtime_initialized_probe_ready x : volatile_runtime_initialized (snd x)=Some true ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract runtime_initialized_probe) x true x.
Proof.
 intro R;unfold runtime_initialized_probe;simpl.
 exists true,x;split;[split;[exact R|reflexivity]|split;reflexivity].
Qed.
Lemma runtime_initialized_probe_result x answer final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract runtime_initialized_probe) x answer final ->
 volatile_runtime_initialized (snd x)=Some answer /\ final=x.
Proof.
 intro RUN;unfold runtime_initialized_probe in RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[R S] T]]];subst middle.
 unroll_post T;destruct T as [A B];subst answer final;auto.
Qed.

Definition next_generation_probe : impure ControllerAPI (option N) :=
 request_then NextGenerationProbe (fun answer=>local answer).
Lemma next_generation_probe_ready x n : volatile_counter (snd x)=Some n ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract next_generation_probe) x (boss_checked_generation (counter_value n)) x.
Proof.
 intro R;unfold next_generation_probe;simpl.
 exists (boss_checked_generation (counter_value n)),x;split.
 - split;[exists n;auto|reflexivity].
 - split;reflexivity.
Qed.
Lemma next_generation_probe_result x answer final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract next_generation_probe) x answer final ->
 (exists n,volatile_counter (snd x)=Some n /\ answer=boss_checked_generation (counter_value n)) /\ final=x.
Proof.
 intro RUN;unfold next_generation_probe in RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[R S] T]]];subst middle.
 unroll_post T;destruct T as [A B];subst answer final;auto.
Qed.

Definition before_change_probe : impure ControllerAPI bool :=
 request_then BeforeChangeProbe (fun answer=>local answer).
Lemma before_change_probe_known j image root ram e roots :
 active_snapshot_roots (OperationBoundary image root ram) e=Some roots ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((j,OperationBoundary image root ram),e) (existsb unresolved_snapshot roots)
   ((j,OperationBoundary image root ram),e).
Proof.
 intro ROOTS;unfold before_change_probe;simpl.
 exists (existsb unresolved_snapshot roots),((j,OperationBoundary image root ram),e).
 split;[split;[change (match active_snapshot_roots (OperationBoundary image root ram) e with Some rs=>existsb unresolved_snapshot roots=existsb unresolved_snapshot rs|None=>False end);rewrite ROOTS;reflexivity|reflexivity]|].
 split;reflexivity.
Qed.
Lemma before_change_unknown_no_call x :
 active_snapshot_roots (snd (fst x)) (snd x)=None ->
 ~controller_service_caller x bool BeforeChangeProbe.
Proof. intros UNKNOWN [rs [E _]];rewrite UNKNOWN in E;discriminate. Qed.
Lemma before_change_probe_result x answer final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe) x answer final ->
 exists roots,active_snapshot_roots (snd (fst x)) (snd x)=Some roots /\
 answer=existsb unresolved_snapshot roots /\ final=x.
Proof.
 intro RUN;unfold before_change_probe in RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[R S] T]]];subst middle.
 unroll_post T;destruct T as [A B];subst answer final.
 cbn in R;destruct (active_snapshot_roots (snd (fst x)) (snd x)) as [rs|] eqn:E;[exists rs;auto|contradiction].
Qed.

(* Area/page rejection precedes before_change and ensure_protection in Rust.
   Only the later length check consumes the initialized short path. *)
Inductive operation_payload_rejection sector f h a image root ram e : Prop :=
| operation_bad_area area_len req cursor available page final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector area_len req cursor f) (check_payload_area available page))
   ram false final -> operation_payload_rejection sector f h a image root ram e
| operation_bad_length area_len req cursor word_max bytes final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) false
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract ensure_protection_probe)
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) true
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector area_len req cursor f) (check_payload_length word_max bytes))
   ram None final -> operation_payload_rejection sector f h a image root ram e.
Lemma payload_rejection_controlled sector f h a image root ram e :
 volatile_page_size e=Some 256 ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract before_change_probe)
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) false
   ((Logged (Ready f) h a,OperationBoundary image root ram),e) ->
 returned_payload_rejection sector ram f ->
 operation_payload_rejection sector f h a image root ram e.
Proof.
 intros META BEFORE REJECT;destruct REJECT.
 - eapply operation_bad_length;[exact BEFORE|apply ensure_protection_probe_ready;exact META|exact H].
 - eapply operation_bad_area;exact H.
Qed.

(* Read-only entry/prepass of write_registry_data_objects. No transaction is
   opened here. None abstracts a RETURNED comparison error, not a reset. *)
Inductive pair_prepass_result :=
 | PairEntryRejected | PairComparisonError (index:nat) | PairSelected (indices:list nat).
Inductive PairPrepassAPI : interface := PairCompare : nat -> PairPrepassAPI (option bool).
Definition pair_prepass_update (_:unit) A (_:PairPrepassAPI A) (_:A) := tt.
Definition pair_prepass_caller count (_:unit) A (op:PairPrepassAPI A) :=
 match op with PairCompare i=>i<count end.
Definition pair_prepass_callee (compare:nat->option bool) (_:unit) A (op:PairPrepassAPI A) : A->Prop :=
 match op with PairCompare i=>fun answer=>answer=compare i end.
Definition pair_prepass_contract count compare :=
 make_contract pair_prepass_update (pair_prepass_caller count) (pair_prepass_callee compare).
Definition pair_prepass_program count same : impure PairPrepassAPI pair_prepass_result :=
 match count with
 | 1 => request_then (PairCompare 0) (fun first=>local
     (match first with None=>PairComparisonError 0 | Some equal=>PairSelected (if equal then [] else [0]) end))
 | 2 => request_then (PairCompare 0) (fun first=>match first with
     | None=>local (PairComparisonError 0)
     | Some equal=>if same then local (PairSelected (changed_pair true equal false))
       else request_then (PairCompare 1) (fun second=>local
         (match second with None=>PairComparisonError 1
          | Some equal_second=>PairSelected (changed_pair false equal equal_second) end)) end)
 | _=>local PairEntryRejected end.
Definition pair_prepass_compute count same (compare:nat->option bool) :=
 match count with
 | 1 => match compare 0 with None=>PairComparisonError 0
         | Some equal=>PairSelected (if equal then [] else [0]) end
 | 2 => match compare 0 with None=>PairComparisonError 0
         | Some equal=>if same then PairSelected (changed_pair true equal false)
           else match compare 1 with None=>PairComparisonError 1
                | Some equal_second=>PairSelected (changed_pair false equal equal_second) end end
 | _=>PairEntryRejected end.
Definition pair_prepass_return result : option bool := match result with
 | PairEntryRejected | PairComparisonError _=>Some false
 | PairSelected []=>Some true | PairSelected (_::_)=>None end.
Lemma pair_prepass_execution count same compare result :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
   (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
 result=pair_prepass_compute count same compare.
Proof.
 destruct count as [|[|[|count]]].
 - intro RUN;simpl in RUN;unroll_post RUN;exact (eq_sym (proj1 RUN)).
 - intro RUN;simpl in RUN;unroll_post RUN.
   destruct RUN as [reply [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst reply.
   unroll_post REST;exact (eq_sym (proj1 REST)).
 - destruct same.
   + intro RUN;simpl in RUN;unroll_post RUN.
     destruct RUN as [reply [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst reply.
     destruct (compare 0);unroll_post REST;exact (eq_sym (proj1 REST)).
   + intro RUN;simpl in RUN;unroll_post RUN.
     destruct RUN as [reply [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst reply.
     destruct (compare 0) as [equal|].
     * simpl in REST;unroll_post REST.
       destruct REST as [reply [middle [[EQ STATE] LAST]]];subst middle;cbn in EQ;subst reply.
       unroll_post LAST;exact (eq_sym (proj1 LAST)).
     * unroll_post REST;exact (eq_sym (proj1 REST)).
 - intro RUN;simpl in RUN;unroll_post RUN;exact (eq_sym (proj1 RUN)).
Qed.
Definition prepass_same count same := match count with 2=>same|_=>false end.
Definition prepass_equal_first (compare:nat->option bool) := match compare 0 with Some b=>b|None=>false end.
Definition prepass_equal_second count same (compare:nat->option bool) :=
 match count with 1=>true|_=>if same then false else match compare 1 with Some b=>b|None=>false end end.
Lemma pair_prepass_selected count same compare indices :
 pair_prepass_compute count same compare=PairSelected indices ->
 indices=changed_pair (prepass_same count same) (prepass_equal_first compare)
   (prepass_equal_second count same compare).
Proof.
 destruct count as [|[|[|count]]];cbn [pair_prepass_compute];try discriminate.
 - destruct (compare 0) as [[]|] eqn:F;intro EQ;inversion EQ;subst;
   unfold prepass_equal_first,prepass_equal_second,prepass_same;rewrite F;reflexivity.
 - destruct (compare 0) as [first|] eqn:F;[destruct same|];try discriminate.
   + intro EQ;inversion EQ;subst;unfold prepass_equal_first,prepass_equal_second,prepass_same;rewrite F;reflexivity.
   + destruct (compare 1) as [second|] eqn:S;try discriminate.
     intro EQ;inversion EQ;subst;unfold prepass_equal_first,prepass_equal_second,prepass_same;rewrite F;rewrite S;reflexivity.
Qed.
Lemma pair_prepass_duplicate_skips_second first left right :
 left 0=first -> right 0=first ->
 pair_prepass_compute 2 true left=pair_prepass_compute 2 true right.
Proof. intros L R;cbn [pair_prepass_compute];rewrite L;rewrite R;reflexivity. Qed.
Lemma pair_prepass_first_error_stops same compare : compare 0=None ->
 pair_prepass_compute 2 same compare=PairComparisonError 0.
Proof. intro ERR;cbn [pair_prepass_compute];rewrite ERR;reflexivity. Qed.

(* Ordinary delivery consumes the pending decision in a separate controller
   step. DisarmOwner/DropOwner preserve it; neither is a delivery. *)
Inductive operation_exit :=
 | ReturnedPublished (receipt:client_receipt)
 | ReturnedOrdinary (route:finish_route)
 | ReturnedEntry (success:bool)
 | ReturnedBodyError
 | InterruptedReset | InterruptedFatal.
Definition ordinary_result route := match route with
 | FinishClean=>RetainedResult | FinishAbort=>AbortedResult | FinishPublish=>FinalizationError end.
Definition exit_observation (exit:operation_exit) : option finalization_result :=
 match exit with
 | ReturnedPublished _ => Some RetainedResult
 | ReturnedOrdinary route => Some (ordinary_result route)
 | ReturnedEntry success=>Some (if success then RetainedResult else FinalizationError)
 | ReturnedBodyError=>Some FinalizationError
 | InterruptedReset | InterruptedFatal => None end.
(* Delivery observations include the outer-handle condition already required
   by DeliverOwned/DeliverBodyError. This is a proof observer, not an added
   Rust test; the existing delivery producers discharge it from their callers. *)
Definition delivered_owner_closed (e:boundary_evidence) :=
 outer_live (controller_read e)=false /\ owner_armed (controller_read e)=false.
Lemma published_owner_closed j c e : delivered_owner_closed (observe_client j c e).
Proof.
 unfold delivered_owner_closed,controller_read,observe_client,deliver_published,synchronize_publication;
 cbn;destruct (volatile_control e);split;reflexivity.
Qed.
Definition edge_exit (x:execution_boundary) (event:option client_receipt)
 (y:execution_boundary) : option operation_exit :=
 match event with
 | Some receipt => Some (ReturnedPublished receipt)
 | None => match snd (fst y) with
   | FatalBoundary => Some InterruptedFatal
   | RebuildingBoundary _ => Some InterruptedReset
   | IdleBoundary _ _ _ | FrozenBoundary _ _ _ _ =>
     match finish_selected (controller_read (snd x)),finish_selected (controller_read (snd y)) with
     | Some route,None => if owner_armed (controller_read (snd x)) then None
                          else if owner_armed (controller_read (snd y)) then None
                          else if outer_live (controller_read (snd y)) then None else Some (ReturnedOrdinary route)
     | None,None=>if body_error_pending (controller_read (snd x)) then
         if body_error_pending (controller_read (snd y)) then None
         else if owner_armed (controller_read (snd x)) then None
         else if owner_armed (controller_read (snd y)) then None
         else if outer_live (controller_read (snd y)) then None else Some ReturnedBodyError
       else None
     | _,_=>None end
   | _=>None end end.
Lemma published_edge_exit x receipt y :
 edge_exit x (Some receipt) y=Some (ReturnedPublished receipt).
Proof. reflexivity. Qed.
Lemma reset_edge_exit x j pc e :
 edge_exit x None ((j,RebuildingBoundary pc),e)=Some InterruptedReset.
Proof. reflexivity. Qed.
Lemma fatal_edge_exit x j e :
 edge_exit x None ((j,FatalBoundary),e)=Some InterruptedFatal.
Proof. reflexivity. Qed.

Lemma recycled_extent_mapping g sector fuel recognize f t req round alignment pages start r count :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 erase_geometry g sector r count ->
 extent_end (block_pages (recycle_lo r) (useful_pages r))<=pages*256.
Proof.
 intros SEARCH [_ [_ [_ [_ [_ LENGTH]]]]].
 pose proof (reusable_search_extent_bound _ _ _ _ _ _ _ _ _ _ _ SEARCH) as BOUND.
 unfold extent_end,block_pages;cbn;nia.
Qed.

Section Trace.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Variable data_bytes : compact_entry -> nat -> N.
Variable data_writer : flash -> extent -> compact_entry -> writer_observation.
Variable boss_writer : flash -> nat -> list compact_slot -> writer_observation.
Variable data_plan : flash -> extent -> compact_entry -> list writer_command.
Variable boss_plan : flash -> nat -> list compact_slot -> list writer_command.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8=0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.
Hypothesis WRITERS : outcome_writer_contracts g sector view data_bytes data_writer boss_writer data_plan boss_plan decode.

Definition boundary_safe (x : execution_boundary) :=
  enriched_invariant sector data_len boss_ok view marker ranges decode pages (fst x) (snd x).
(* Recovery uses the certificates carried by THIS boundary, rather than a
   fresh global format assertion at each decoding step. These consumers are
   used below by boundary_step_preserves and boundary_history_extension.
   Their inferred signatures do not contain CONTRACT or WRITERS. *)
Theorem boundary_boot_prefix_safe initial final e :
  boundary_safe ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) ->
  (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) initial final ->
  boundary_safe ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (e)) /\
  publications (boot_journal final)=publications (boot_journal initial).
Proof.
  intros INV LOCAL RUN.
  exact (certified_boot_trace g sector data_len boss_ok view marker ranges decode topology pages
    initial final e G DIV INV LOCAL RUN).
Qed.

Theorem boundary_boot_objects_preserved initial final e :
  boundary_safe ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) ->
  (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) initial final ->
  forall address, 2*sector<=address ->
    control_image (journal_control (boot_journal final)) address =
    control_image (journal_control (boot_journal initial)) address.
Proof.
  intros INV LOCAL RUN. induction RUN; intros address OUT.
  - pose proof (boot_projection g sector data_len boss_ok view marker ranges decode topology pages
      x y (proj2 (proj1 INV)) H) as LOG.
    destruct (recovery_trace_history _ _ _ _ _ _ _ LOG) as [_ [_ PHYSICAL]].
    exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ _ G DIV (proj1 (proj1 INV)) PHYSICAL OUT).
  - reflexivity.
  - pose proof (proj1 (boundary_boot_prefix_safe _ _ _ INV LOCAL RUN1)) as MID.
    rewrite (IHRUN2 MID address OUT). exact (IHRUN1 INV address OUT).
Qed.

Theorem boundary_reset_prefix_safe j phase e :
  boundary_safe ((j,phase),e) ->
  logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
  boundary_safe ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence (e)).
Proof.
  intros INV RUN. exact (incarnation_reset_boundary g sector data_len boss_ok view marker ranges decode pages
    j phase e G DIV INV RUN).
Qed.

(* Compatibility supplier for the still fixed-view writer episodes. It uses
   only the locality field and the live certificate's existing correspondence.
   No historical receipt is decoded and no final correspondence is assumed. *)
Lemma boundary_live_readers x : boundary_safe x ->
  forall c, In c (live_certificates (snd x)) -> incarnation_reader_local ranges decode c.
Proof.
  intros [_ [EV _]] c IN.
  pose proof (proj1 (Forall_forall _ _) (proj1 EV) c IN) as [_ [BOSS OBJECTS]].
  unfold incarnation_reader_local. intros before after READ FRAME.
  assert (KEEP:unchanged (root_extents (view (certificate_id c))) before after).
  { unfold root_extents. rewrite <- BOSS, <- OBJECTS. exact FRAME. }
  rewrite <- (recovery_locality_contract _ _ _ CONTRACT _ _ _ KEEP). exact READ.
Qed.

Definition prepared_evidence old id d index entry e :=
  evidence_with_live e [Certificate old d;Certificate id (RecoveryDecoding (boss_extent (view id))
    (image_replace (recovered_image d) index (Some entry)))].
Definition old_evidence old d e := evidence_with_live e [Certificate old d].
Definition collected_failure old d reserved saved result resolved e : execution_boundary :=
  ((Logged (Ready (writer_flash result)) (publications (fst reserved)) (acknowledgements (fst reserved)),
     failure_phase old d resolved (preparation_rollback saved (writer_end result) (snd reserved))),
    phase_evidence (failure_phase old d resolved (preparation_rollback saved (writer_end result) (snd reserved))) (old_evidence old d e)).

(* These are executions of a publication suffix, not assertions about its
   invariant. In particular there is no constructor with a safe destination
   or a selected-authority premise. *)
Inductive publication_execution old id image index entry span s prepared ready e :
    option client_receipt -> execution_boundary -> Prop :=
| publication_client out slot pubs acks final :
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id (protection_current s++attached_ranges s))
      (client_finish_program id (image_replace image index (Some entry)) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
      (prepared_transaction_candidate view id ranges image index entry span s)
      (ClientReturned (DataClientSuccess id (image_replace image index (Some entry)))) final ->
    publication_execution old id image index entry span s prepared ready e
      (Some (Receipt (pred (length pubs)) (Certificate id (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))))))
      ((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id
        (RecoveryDecoding (boss_extent (view id)) (image_replace image index (Some entry))) final),
       client_return_evidence view (Logged (Ready out) pubs (N.of_nat id::acks))
         (ClientReturned (DataClientSuccess id (image_replace image index (Some entry)))) e)
| publication_stopped out slot pubs acks final :
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id (protection_current s++attached_ranges s))
      (client_finish_program id (image_replace image index (Some entry)) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
      (prepared_transaction_candidate view id ranges image index entry span s) ClientStopped final ->
    publication_execution old id image index entry span s prepared ready e None
      ((Logged (Ready out) pubs (N.of_nat id::acks),FatalBoundary),forget_volatile_evidence (e))
| publication_error error_j commands :
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id)) ready error_j ->
    returned_error_control (journal_control error_j) ->
    data_calls commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) prepared) ->
    publication_execution old id image index entry span s prepared ready e None
      ((error_j,FrozenBoundary (N.of_nat old) (N.of_nat id) None
        (execute_data commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) prepared))),e)
| publication_cut cut :
    publication_reset_prefix g sector data_len boss_ok (N.of_nat id) ready cut ->
    publication_execution old id image index entry span s prepared ready e None
      ((cut,RebuildingBoundary Selecting),forget_volatile_evidence (e))
| publication_after_append_cut out slot pubs acks :
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    publication_execution old id image index entry span s prepared ready e None
      ((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence (e))
| publication_ram_prefix_cut out slot pubs acks phases suffix partial :
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
      (exit_contract marker (root_extents (view id)) (protection_current s++attached_ranges s))
      (exit_program phases)) prepared tt partial ->
    publication_execution old id image index entry span s prepared ready e None
      ((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence (e))
| publication_collect_prefix_cut out slot pubs acks closed resolved partial :
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len boss_ok (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len boss_ok (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
      (exit_contract marker (root_extents (view id)) (protection_current s++attached_ranges s))
      (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) prepared tt closed ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id (protection_current s++attached_ranges s))
      collection_service_prefix) closed resolved partial ->
    publication_execution old id image index entry span s prepared ready e None
      ((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence (e)).

Lemma publication_execution_control old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 terminal_control_absent next.
Proof. intro RUN;destruct RUN;exact I || reflexivity. Qed.

Lemma publication_execution_roots old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 terminal_roots_absent next.
Proof. intro RUN;destruct RUN;exact I || reflexivity. Qed.

Lemma publication_execution_pages old id image index entry span s prepared ready e event next :
 volatile_page_size e=Some 256 ->
 publication_execution old id image index entry span s prepared ready e event next ->
 page_metadata_coherent next.
Proof. intros M RUN;destruct RUN;cbn;auto. Qed.

Lemma publication_execution_runtime old id image index entry span s prepared ready e event next :
 volatile_runtime_initialized e=Some true ->
 publication_execution old id image index entry span s prepared ready e event next ->
 runtime_metadata_coherent next.
Proof. intros M RUN;destruct RUN;cbn;auto. Qed.

Lemma publication_execution_safe old id image index entry span s prepared ready decoded e event next :
  publication_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready decoded e ->
  publication_execution old id image index entry span s prepared ready e event next ->
  boundary_safe next /\ boundary_receipts next=emitted_receipts event++client_receipts e.
Proof.
  intros PUB RUN. destruct RUN.
  - pose proof (episode_client_finish g sector data_len boss_ok view marker ranges decode topology pages G DIV CONTRACT
      old id image index entry span s prepared ready decoded e out slot pubs acks final _ PUB H H0 H1) as [R [INV REST]].
    split; [exact INV|reflexivity].
  - pose proof (episode_client_finish g sector data_len boss_ok view marker ranges decode topology pages G DIV CONTRACT
      old id image index entry span s prepared ready decoded e out slot pubs acks final _ PUB H H0 H1) as [F [INV REST]].
    split; [exact INV|reflexivity].
  - destruct PUB as [P [C [S [ERR REST]]]].
    split; [exact (proj1 (ERR _ _ H H0 H1))|reflexivity].
  - destruct PUB as [P [C [S [ERR [CUT REST]]]]].
    split; [exact (proj1 (proj2 (proj2 (CUT _ H))))|reflexivity].
  - destruct PUB as [P [C [S REST]]].
    split; [exact (proj1 (S _ _ _ _ H H0 _ (rt_refl _ _ _)))|reflexivity].
  - destruct (episode_exit_prefix_reset g sector data_len boss_ok view marker ranges decode topology pages
      old id image index entry span s prepared ready decoded e out slot pubs acks phases suffix partial PUB H H0 H1 H2) as [RAM BOOT].
    split; [exact (proj1 (BOOT _ (rt_refl _ _ _)))|reflexivity].
  - destruct (episode_collection_prefix_reset g sector data_len boss_ok view marker ranges decode topology pages
      old id image index entry span s prepared ready decoded e out slot pubs acks closed resolved partial PUB H H0 H1 H2) as [RAM [COLLECT BOOT]].
    split; [exact (proj1 (BOOT _ (rt_refl _ _ _)))|reflexivity].
Qed.

Lemma publication_execution_allocation old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 terminal_allocation_absent next.
Proof. intro RUN;destruct RUN;exact I || reflexivity. Qed.



(* Resource guards are local inputs. Writer observations and reached flash
   are computed by the same services as A8; no invariant is a constructor input. *)
Inductive reserved_execution old id d index entry span s f h a e :
    option client_receipt -> execution_boundary -> Prop :=
| data_error resolved :
    writer_returned_error (writer_end (data_writer f span entry)) ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    reserved_execution old id d index entry span s f h a e None
      (collected_failure old d (Logged (Ready f) h a,data_reservation_state span s)
        (protection_current s++attached_ranges s) (data_writer f span entry) resolved (advance_allocation_evidence span e))
| data_reset : writer_end (data_writer f span entry)=WriterInterrupted ->
    reserved_execution old id d index entry span s f h a e None
      ((Logged (Boot (writer_flash (data_writer f span entry))) h a,RebuildingBoundary Selecting),forget_volatile_evidence (old_evidence old d e))
| boss_error resolved :
    writer_end (data_writer f span entry)=WriterComplete ->
    free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)) ->
    erased_object_extent sector (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_returned_error (writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))) ->
    (forall mask, resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    range_numeric (1024*256) (boss_extent (view id)) ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    reserved_execution old id d index entry span s f h a e None
      (collected_failure old d (Logged (Ready f) h a,boss_reservation_state view id ranges (recovered_image d) index entry span s)
        (protection_current s++attached_ranges s)
        (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))) resolved (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e)))
| boss_reset :
    writer_end (data_writer f span entry)=WriterComplete ->
    free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)) ->
    erased_object_extent sector (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterInterrupted ->
    range_numeric (1024*256) (boss_extent (view id)) ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    reserved_execution old id d index entry span s f h a e None
      ((Logged (Boot (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a,
        RebuildingBoundary Selecting),forget_volatile_evidence (old_evidence old d e))
| prepared_execution event next :
    writer_end (data_writer f span entry)=WriterComplete ->
    free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s)) (boss_extent (view id)) ->
    erased_object_extent sector (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterComplete ->
    publication_execution old id (recovered_image d) index entry span s
      (prepared_transaction_candidate view id ranges (recovered_image d) index entry span s)
      (Logged (Ready (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a)
      (prepared_evidence old id d index entry (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e))) event next ->
    range_numeric (1024*256) (boss_extent (view id)) ->
    runtime_erased_admission sector pages (advance_allocation_evidence span e)
      (modified_transaction ranges (recovered_image d) index entry span s)
      (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
    reserved_execution old id d index entry span s f h a e event next.

Lemma reserved_execution_control old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 terminal_control_absent next.
Proof.
 intro RUN;destruct RUN;try reflexivity.
 - unfold collected_failure;apply phase_evidence_terminal.
 - unfold collected_failure;apply phase_evidence_terminal.
 - eapply publication_execution_control;eauto.
Qed.

Lemma reserved_execution_roots old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 terminal_roots_absent next.
Proof.
 intro RUN;destruct RUN;try reflexivity.
 - unfold collected_failure;apply phase_evidence_roots.
 - unfold collected_failure;apply phase_evidence_roots.
 - eapply publication_execution_roots;eauto.
Qed.

Lemma reserved_execution_allocation old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 terminal_allocation_absent next.
Proof.
 intro RUN;destruct RUN;try reflexivity.
 - unfold collected_failure;apply phase_evidence_allocation.
 - unfold collected_failure;apply phase_evidence_allocation.
 - eapply publication_execution_allocation;eauto.
Qed.

Lemma reserved_execution_safe old id d index entry span s f h a e event next :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
  erased_object_extent sector f span ->
  reserved_execution old id d index entry span s f h a e event next ->
  boundary_safe next /\ boundary_receipts next=emitted_receipts event++client_receipts e.
Proof.
  intros INV RANGE FREE ERASED RUN.
  destruct (enriched_data_episode_freer g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT data_bytes data_writer boss_writer data_plan boss_plan
    old id d index entry span s f h a e INV RANGE FREE ERASED WRITERS) as [POST DELIVERY].
  unfold data_episode_post in POST. destruct POST as [EXEC [FRAME CASE]].
  destruct RUN.
  - destruct H as [H|[H|H]]; rewrite H in CASE;
      split; try reflexivity; exact (proj1 (proj2 CASE) resolved ltac:(unfold writer_returned_error;auto) H0).
  - rewrite H in CASE. split; [exact (proj1 (proj2 (proj2 CASE) _ (rt_refl _ _ _)))|reflexivity].
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]].
    destruct H2 as [H2|[H2|H2]]; rewrite H2 in CASE;
      split; try reflexivity; exact (proj1 (proj2 CASE) resolved ltac:(unfold writer_returned_error;auto) H3).
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]]. rewrite H2 in CASE.
    split; [exact (proj1 (proj2 (proj2 CASE) _ (rt_refl _ _ _)))|reflexivity].
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]]. rewrite H2 in CASE.
    eapply publication_execution_safe with (e:=prepared_evidence old id d index entry (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e)));[exact CASE|exact H3].
Qed.

Section NumericReserved.
Variable word_max:nat.
Hypothesis NUM_MARK:range_numeric word_max marker.
Hypothesis NUM_DECODE:decoded_numeric_contract word_max ranges decode.
Hypothesis NUM_CAP:1024*256<=word_max.

Lemma publication_execution_numeric old id image index entry span s prepared ready e event next :
 state_numeric word_max prepared ->
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> phase_numeric word_max marker ranges (snd (fst next)).
Proof.
 intros NUM RUN FINAL;destruct RUN;try exact I.
 - eapply enriched_client_numeric;[exact NUM_MARK|exact NUM_DECODE|exact FINAL].
 - apply numeric_frozen_commands;[|reflexivity|exact H1].
   unfold uncertain_return;eapply data_numeric_preserves;[|exact I|exact I].
   apply numeric_slot;[exact NUM|].
   exact (selected_numeric word_max sector view ranges decode error_j e NUM_DECODE (proj1 (proj2 FINAL))).
Qed.

Theorem reserved_execution_numeric old id d index entry span s f h a e event next :
 boundary_safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 state_numeric word_max s -> range_numeric (1024*256) span ->
 ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
 erased_object_extent sector f span ->
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next /\ phase_numeric word_max marker ranges (snd (fst next)).
Proof.
 intros INIT NUM ADMIT RANGE FREE BLANK RUN.
 pose proof (proj1 (reserved_execution_safe _ _ _ _ _ _ _ _ _ _ _ _ _ INIT RANGE FREE BLANK RUN)) as FINAL.
 assert (RNUM:range_numeric word_max span) by (eapply range_numeric_monotone;eauto).
 assert (SAVED:Forall (range_numeric word_max) (protection_current s++attached_ranges s)).
 { apply Forall_app;split;[exact (proj1 NUM)|exact (proj1 (proj2 NUM))]. }
 assert (CHANGED:state_numeric word_max (modified_transaction ranges (recovered_image d) index entry span s)).
 { apply numeric_exact_member with (root:=[recovered_boss d]);try assumption.
   - apply numeric_begin_unconditionally;exact NUM.
   - reflexivity.
   - unfold image_current_correspondence;cbn;rewrite app_nil_r.
     exact (proj2 (proj2 (proj2 (proj1 INIT)))). }
 split;[exact FINAL|]. destruct RUN;try exact I.
 - apply numeric_failure_phase,numeric_rollback;[|exact SAVED].
   change (state_numeric word_max (reservation_state false span (data_next DataBegin s))).
   apply numeric_reservation;[apply numeric_begin_unconditionally;exact NUM|exact RNUM].
 - apply numeric_failure_phase,numeric_rollback;[|exact SAVED].
   change (state_numeric word_max (reservation_state true (boss_extent (view id))
     (modified_transaction ranges (recovered_image d) index entry span s))).
   apply numeric_reservation;[exact CHANGED|eapply range_numeric_monotone;eauto].
 - eapply publication_execution_numeric;[|exact H3|exact FINAL].
   apply numeric_materialize;[exact CHANGED|eapply range_numeric_monotone;eauto].
Qed.
End NumericReserved.

Lemma frozen_boundary_cleanup j old candidate current next_current ram e commands :
  boundary_safe ((j,FrozenBoundary old candidate current ram),e) -> data_calls commands ram ->
  boundary_safe ((j,FrozenBoundary old candidate next_current (execute_data commands ram)),e).
Proof.
  intros [[JI [DI [FR [LINK [CHOICE COVER]]]]] [EV CERT]] CALL.
  pose proof (data_execution_preserves commands ram DI CALL) as NEXT.
  pose proof (data_execution_refines commands ram DI CALL) as TRACE.
  destruct (frozen_preparation_trace_keeps_storage 256 _ _ FR TRACE) as [FR' [TABLE AUTH]].
  destruct (data_execution_no_publication commands ram) as [PH ACK].
  split; [|split; [exact EV|exact I]]. split; [exact JI|].
  split; [exact NEXT|]. split; [exact FR'|]. split.
  - unfold protection_history_link in *. rewrite PH. exact LINK.
  - split; [exact CHOICE|]. rewrite TABLE. exact COVER.
Qed.

Lemma reserved_execution_pages old id d index entry span s f h a e event next :
 volatile_page_size e=Some 256 ->
 reserved_execution old id d index entry span s f h a e event next ->
 page_metadata_coherent next.
Proof.
 intros M RUN;destruct RUN;try reflexivity;
 try (unfold collected_failure;apply phase_page_metadata;exact M).
 eapply publication_execution_pages;[|eassumption];exact M.
Qed.

Lemma reserved_execution_runtime old id d index entry span s f h a e event next :
 volatile_runtime_initialized e=Some true ->
 reserved_execution old id d index entry span s f h a e event next ->
 runtime_metadata_coherent next.
Proof.
 intros M RUN;destruct RUN;try reflexivity;
 try (unfold collected_failure;apply phase_runtime_metadata;exact M).
 eapply publication_execution_runtime;[|eassumption];exact M.
Qed.

(* Exact acquisition lineage of the historical macro. No destination
   observation is an argument of this theorem. *)
Lemma publication_execution_allocation_value old id image index entry span s prepared ready e event next a :
 volatile_allocation e=Some a ->
 publication_execution old id image index entry span s prepared ready e event next ->
 volatile_allocation (snd next)=None \/ volatile_allocation (snd next)=Some a \/
 volatile_allocation (snd next)=Some (AllocationRuntime (allocation_append a) (boss_extent (view id))).
Proof.
 intros OBS RUN;destruct RUN;cbn;try (left;reflexivity);try (right;left;exact OBS).
 rewrite OBS;right;right;reflexivity.
Qed.
Lemma phase_allocation_value phase e :
 volatile_allocation (phase_evidence phase e)=None \/
 volatile_allocation (phase_evidence phase e)=volatile_allocation e.
Proof. destruct phase;cbn;auto. Qed.
Lemma reserved_execution_allocation_value old id d index entry span s f h a e event next source :
 volatile_allocation e=Some source ->
 reserved_execution old id d index entry span s f h a e event next ->
 volatile_allocation (snd next)=None \/
 volatile_allocation (snd next)=Some (AllocationRuntime (extent_end span) (allocation_latest source)) \/
 volatile_allocation (snd next)=Some (AllocationRuntime (extent_end (boss_extent (view id))) (allocation_latest source)) \/
 volatile_allocation (snd next)=Some (AllocationRuntime (extent_end (boss_extent (view id))) (boss_extent (view id))).
Proof.
 intros OBS RUN;destruct RUN;try (left;reflexivity).
 - unfold collected_failure;cbn [snd].
   match goal with |- context[phase_evidence ?phase ?ev] =>
   destruct (phase_allocation_value phase ev) as [N|S] end;[left;exact N|].
   rewrite S;cbn;rewrite OBS;auto.
 - unfold collected_failure;cbn [snd].
   match goal with |- context[phase_evidence ?phase ?ev] =>
   destruct (phase_allocation_value phase ev) as [N|S] end;[left;exact N|].
   rewrite S;cbn;rewrite OBS;auto.
 - match goal with RUN:publication_execution _ _ _ _ _ _ _ _ _ ?ev _ _ |- _ =>
   assert (O:volatile_allocation ev=Some (AllocationRuntime (extent_end (boss_extent (view id))) (allocation_latest source)))
     by (cbn;rewrite OBS;reflexivity);
   pose proof (publication_execution_allocation_value _ _ _ _ _ _ _ _ _ _ _ _ _ O RUN) as OUT end.
   tauto.
Qed.

Inductive boundary_step : execution_boundary -> option client_receipt -> execution_boundary -> Prop :=
| run_reserved old id d index entry span s f h a e event next :
    ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
    erased_object_extent sector f span ->
    reserved_execution old id d index entry span s f h a e event next ->
    range_numeric (1024*256) span ->
    runtime_erased_admission sector pages e (data_next DataBegin s) f span ->
    boundary_step ((Logged (Ready f) h a,IdleBoundary old d s),e) event next
| frozen_continue j old candidate current ram e commands : data_calls commands ram ->
    boundary_step ((j,FrozenBoundary old candidate current ram),e) None
      ((j,FrozenBoundary old candidate (opaque_frozen_root current commands) (execute_data commands ram)),e)
| client_resume j id d ram e :
    boundary_step ((j,ClientBoundary id d ram),e) None ((j,IdleBoundary id d ram),e)
| reset_boundary j phase e :
    logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
    boundary_step ((j,phase),e) None ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e)
| run_boot initial final e :
    clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) initial final ->
    boundary_step ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) None
      ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence e)
| boot_resume j id d ram e :
    boundary_step ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence (e)) None ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e))
| boot_stop j e :
    boundary_step ((j,RebuildingBoundary Stopped),forget_volatile_evidence (e)) None ((j,FatalBoundary),forget_volatile_evidence e).

Lemma boundary_step_pages x event y : page_metadata_coherent x ->
 boundary_step x event y -> page_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;cbn in M |- *;try assumption;try reflexivity.
 eapply reserved_execution_pages;[exact M|eassumption].
Qed.

Lemma boundary_step_runtime x event y : runtime_metadata_coherent x ->
 boundary_step x event y -> runtime_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;cbn in M |- *;try assumption;try reflexivity.
 eapply reserved_execution_runtime;[exact M|eassumption].
Qed.

Lemma boundary_step_control x event y : boundary_step x event y -> terminal_control_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity.
 eapply reserved_execution_control;eauto.
Qed.

Lemma boundary_step_roots x event y : boundary_step x event y -> terminal_roots_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity.
 eapply reserved_execution_roots;eauto.
Qed.

Lemma boundary_step_allocation x event y : boundary_step x event y -> terminal_allocation_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity.
 eapply reserved_execution_allocation;eauto.
Qed.

Theorem boundary_step_preserves x event y :
  boundary_safe x -> boundary_step x event y ->
  boundary_safe y /\ boundary_receipts y=emitted_receipts event++boundary_receipts x.
Proof.
  intros INV STEP. destruct STEP.
  - eapply reserved_execution_safe; eauto.
  - split; [eapply frozen_boundary_cleanup; eauto|reflexivity].
  - split; [exact (proj1 (enriched_client_next sector data_len boss_ok view marker ranges decode pages _ _ _ _ _ INV))|reflexivity].
  - split; [eapply boundary_reset_prefix_safe; eauto|reflexivity].
  - split; [|reflexivity].
    exact (proj1 (boundary_boot_prefix_safe _ _ _ INV (boundary_live_readers _ INV) H)).
  - split; [apply recovered_page_evidence_invariant;exact (proj1 (enriched_boot_usable sector data_len boss_ok view marker ranges decode pages _ _ _ _ _ INV))|reflexivity].
  - split; [eapply enriched_boot_fatal; exact INV|reflexivity].
Qed.

Lemma publication_execution_counter_source old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 counter_decoder (snd next)=counter_decoder e.
Proof. intro RUN;destruct RUN;reflexivity. Qed.
Lemma reserved_execution_counter_source old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 counter_decoder (snd next)=counter_decoder e.
Proof.
 intro RUN;destruct RUN;try reflexivity.
 match goal with RUN:publication_execution _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
 apply publication_execution_counter_source in RUN;exact RUN end.
Qed.
Lemma boundary_step_counter_source x event y : boundary_step x event y ->
 counter_decoder (snd y)=counter_decoder (snd x).
Proof. intro RUN;destruct RUN;try reflexivity;eapply reserved_execution_counter_source;eassumption. Qed.
Lemma latest_idle_head j id d ram e : boundary_safe ((j,IdleBoundary id d ram),e) ->
 hd_error (publications j)=Some (N.of_nat id).
Proof. intro INV;exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INV))))))). Qed.
Lemma latest_client_head j id d ram e : boundary_safe ((j,ClientBoundary id d ram),e) ->
 hd_error (publications j)=Some (N.of_nat id).
Proof. intro INV;exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj1 INV)))))))). Qed.

Lemma publication_execution_latest old id image index entry span s prepared ready e event next :
 (exists n,volatile_latest_registry e=Some n) ->
 publication_execution old id image index entry span s prepared ready e event next ->
 latest_metadata_coherent next.
Proof. intros M RUN;destruct RUN;cbn;auto;try (eexists;reflexivity). Qed.
Lemma reserved_execution_latest old id d index entry span s f h a e event next :
 (exists n,volatile_latest_registry e=Some n) ->
 reserved_execution old id d index entry span s f h a e event next ->
 latest_metadata_coherent next.
Proof.
 intros M RUN;destruct RUN;try reflexivity;
 try (unfold collected_failure;apply phase_latest_metadata;exact M).
 match goal with RUN:publication_execution ?a ?b ?c ?d ?f ?h ?i ?j ?k ?l ?m ?n |- _ =>
 exact (publication_execution_latest a b c d f h i j k l m n M RUN) end.
Qed.
Lemma boundary_step_latest x event y : latest_metadata_coherent x ->
 boundary_step x event y -> latest_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;cbn in M |- *;try exact M;try reflexivity;try (eexists;reflexivity).
 eapply reserved_execution_latest;eassumption.
Qed.
Lemma publication_execution_latest_origin old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> latest_origin (volatile_latest_registry e) next.
Proof.
 intros RUN INV;destruct RUN;unfold latest_origin;cbn;try tauto.
 right;right;unfold latest_at_head;cbn;symmetry;apply latest_client_head in INV;exact INV.
Qed.
Lemma reserved_execution_latest_origin old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next -> latest_origin (volatile_latest_registry e) next.
Proof.
 intros RUN INV;destruct RUN;try (unfold latest_origin;cbn;tauto);
 try (unfold collected_failure;
   match goal with |- latest_origin _ ((?j,?phase),phase_evidence ?phase ?ev) =>
    exact (phase_latest_origin j phase ev) end).
 match goal with RUN:publication_execution ?a ?b ?c ?d ?f ?h ?i ?j ?k ?l ?m ?n |- _ =>
 exact (publication_execution_latest_origin a b c d f h i j k l m n RUN INV) end.
Qed.
Lemma boundary_step_latest_origin x event y : boundary_safe x ->
 boundary_step x event y -> latest_origin (volatile_latest_registry (snd x)) y.
Proof.
 intros INV RUN;pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;try (unfold latest_origin;cbn;tauto).
 - eapply reserved_execution_latest_origin;eassumption.
 - right;right;unfold latest_at_head;cbn;symmetry;apply latest_idle_head in NEXT;exact NEXT.
Qed.

Lemma publication_execution_ordinary_latest old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> ordinary_latest_coherent next.
Proof.
 intros RUN NEXT;destruct RUN;try exact I.
 cbn [ordinary_latest_coherent latest_at_head boundary_journal];cbn.
 symmetry;apply latest_client_head in NEXT;exact NEXT.
Qed.
Lemma reserved_execution_ordinary_latest old id d index entry span s f h a e event next :
 latest_at_head ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next -> ordinary_latest_coherent next.
Proof.
 intros COHERENT RUN NEXT;destruct RUN;try exact I.
 - unfold collected_failure;apply ordinary_latest_phase.
   unfold failure_phase;repeat match goal with
   | |- context[if ?test then _ else _] => destruct test
   | |- context[match ?opt with Some _=>_ | None=>_ end] => destruct opt
   end;exact I || exact COHERENT.
 - unfold collected_failure;apply ordinary_latest_phase.
   unfold failure_phase;repeat match goal with
   | |- context[if ?test then _ else _] => destruct test
   | |- context[match ?opt with Some _=>_ | None=>_ end] => destruct opt
   end;exact I || exact COHERENT.
 - eapply publication_execution_ordinary_latest;eassumption.
Qed.
Lemma boundary_step_ordinary_latest x event y :
 ordinary_latest_coherent x -> boundary_safe x ->
 boundary_step x event y -> ordinary_latest_coherent y.
Proof.
 intros COHERENT INV RUN;pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact COHERENT;try exact I.
 - eapply reserved_execution_ordinary_latest;try eassumption.
   exact COHERENT.
 - cbn [ordinary_latest_coherent latest_at_head boundary_journal];cbn.
   symmetry;apply latest_idle_head in NEXT;exact NEXT.
Qed.

Lemma decoded_allocation_available f id read d :
 generation_decoding_matches sector decode read ->
 decode (object_flash sector f) id=Some d ->
 exists a,read_allocation read f id=Some a.
Proof.
 intros MATCH READ;exists (allocation_from_decoded d).
 specialize (MATCH f id);rewrite READ in MATCH;unfold read_allocation.
 destruct (read f id) as [[decoded n]|];cbn in MATCH |- *;inversion MATCH;reflexivity.
Qed.
Lemma publication_execution_allocation_known old id image index entry span s prepared ready e event next :
 (exists n,volatile_allocation e=Some n) ->
 publication_execution old id image index entry span s prepared ready e event next ->
 allocation_metadata_coherent next.
Proof.
 intros M RUN;destruct RUN;cbn;try exact M;try reflexivity.
 all: destruct M as [n EQ];rewrite EQ;cbn;eauto.
Qed.
Lemma reserved_execution_allocation_known old id d index entry span s f h a e event next :
 (exists n,volatile_allocation e=Some n) ->
 reserved_execution old id d index entry span s f h a e event next ->
 allocation_metadata_coherent next.
Proof.
 intros M RUN;destruct RUN;try reflexivity;
 try (unfold collected_failure;apply phase_allocation_metadata;cbn;destruct M as [n EQ];rewrite EQ;eexists;reflexivity).
 match goal with RUN:publication_execution ?a ?b ?c ?d ?f ?h ?i ?j ?k ?l ?m ?n |- _ =>
 eapply (publication_execution_allocation_known a b c d f h i j k l m n);[|exact RUN] end.
 cbn;destruct M as [n EQ];rewrite EQ;eexists;reflexivity.
Qed.
Lemma boundary_step_allocation_known x event y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 allocation_metadata_coherent x -> boundary_safe x ->
 boundary_step x event y -> allocation_metadata_coherent y.
Proof.
 intros MATCH M INV RUN.
 pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;cbn in M |- *;try exact M;try reflexivity.
 - eapply reserved_execution_allocation_known;eassumption.
 - eapply decoded_allocation_available;[exact MATCH|].
   apply generation_ready_read in NEXT;exact NEXT.
Qed.

Lemma publication_execution_counter old id image index entry span s prepared ready e event next :
 generation_decoding_matches sector decode (counter_decoder e) ->
 (exists n,volatile_counter e=Some n) ->
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> counter_metadata_coherent next.
Proof.
 intros MATCH M RUN INV;destruct RUN;cbn;try exact M;try reflexivity.
 eapply decoded_counter_available;[exact MATCH|].
 apply generation_client_read in INV;exact INV.
Qed.
Lemma reserved_execution_counter old id d index entry span s f h a e event next :
 generation_decoding_matches sector decode (counter_decoder e) ->
 (exists n,volatile_counter e=Some n) ->
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next -> counter_metadata_coherent next.
Proof.
 intros MATCH M RUN INV;destruct RUN;try reflexivity;
 try (unfold collected_failure;apply phase_counter_metadata;exact M).
 match goal with RUN:publication_execution ?a ?b ?c ?d ?f ?h ?i ?j ?k ?l ?m ?n |- _ =>
 exact (publication_execution_counter a b c d f h i j k l m n MATCH M RUN INV) end.
Qed.
Lemma boundary_step_counter x event y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 counter_metadata_coherent x -> boundary_safe x ->
 boundary_step x event y -> counter_metadata_coherent y.
Proof.
 intros MATCH M INV RUN.
 pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;cbn in M |- *;try exact M;try reflexivity.
 - eapply reserved_execution_counter;[exact MATCH|exact M|eassumption|exact NEXT].
 - eapply decoded_counter_available;[exact MATCH|].
   apply generation_ready_read in NEXT;exact NEXT.
Qed.

Lemma publication_execution_counter_origin old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> counter_origin sector decode (volatile_counter e) next.
Proof.
 intros RUN INV;destruct RUN;unfold counter_origin;cbn;try tauto.
 right;right;eexists;eexists;split.
 - apply generation_client_read in INV;exact INV.
 - reflexivity.
Qed.
Lemma reserved_execution_counter_origin old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next -> counter_origin sector decode (volatile_counter e) next.
Proof.
 intros RUN INV;destruct RUN;try (unfold counter_origin;cbn;tauto);
 try (unfold collected_failure;
   match goal with |- counter_origin _ _ _ ((?j,?phase),phase_evidence ?phase ?ev) =>
    exact (phase_counter_origin sector decode j phase ev) end).
 match goal with RUN:publication_execution ?a ?b ?c ?d ?f ?h ?i ?j ?k ?l ?m ?n |- _ =>
 exact (publication_execution_counter_origin a b c d f h i j k l m n RUN INV) end.
Qed.
Lemma boundary_step_counter_origin x event y :
 boundary_safe x -> boundary_step x event y -> counter_origin sector decode (volatile_counter (snd x)) y.
Proof.
 intros INV RUN;pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;try (unfold counter_origin;cbn;tauto).
 - eapply reserved_execution_counter_origin;[eassumption|exact NEXT].
 - unfold counter_origin;right;right;eexists;eexists;split.
   + apply generation_ready_read in NEXT;exact NEXT.
   + reflexivity.
Qed.

Theorem boundary_step_numeric word_max x event y :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode -> 1024*256<=word_max ->
 boundary_safe x -> phase_numeric word_max marker ranges (snd (fst x)) ->
 boundary_step x event y ->
 boundary_safe y /\ phase_numeric word_max marker ranges (snd (fst y)).
Proof.
 intros MARK DEC CAP INIT NUM RUN.
 pose proof (proj1 (boundary_step_preserves _ _ _ INIT RUN)) as FINAL.
 split;[exact FINAL|]. destruct RUN.
 - exact (proj2 (reserved_execution_numeric word_max MARK DEC CAP _ _ _ _ _ _ _ _ _ _ _ _ _
     INIT NUM H3 H H0 H1 H2)).
 - apply numeric_frozen_commands;[exact NUM| |exact H].
   exact (proj1 (proj2 (proj2 (proj1 INIT)))).
 - exact NUM.
 - exact I.
 - eapply boot_numeric_from_local_decoding;[exact MARK|exact DEC|exact (proj2 (proj1 FINAL))].
 - exact (proj2 NUM).
 - exact I.
Qed.

(* Events are newest first, like the existing logical receipt list. *)
Inductive boundary_trace : execution_boundary -> list client_receipt -> execution_boundary -> Prop :=
| trace_nil x : boundary_trace x [] x
| trace_cons x event y events z : boundary_step x event y -> boundary_trace y events z ->
    boundary_trace x (events++emitted_receipts event) z.

Theorem finite_data_trace_safe initial events final :
  boundary_safe initial -> boundary_trace initial events final ->
  boundary_safe final /\ boundary_receipts final=events++boundary_receipts initial.
Proof.
  intros INIT TRACE. induction TRACE.
  - split; [exact INIT|reflexivity].
  - destruct (boundary_step_preserves _ _ _ INIT H) as [MID RECEIPTS].
    destruct (IHTRACE MID) as [LAST HISTORY]. split; [exact LAST|].
    rewrite HISTORY. rewrite RECEIPTS. rewrite app_assoc. reflexivity.
Qed.

Theorem finite_trace_receipts_valid initial events final :
  boundary_safe initial -> boundary_trace initial events final ->
  Forall (receipt_valid view ranges (publications (boundary_journal final)))
    (events++boundary_receipts initial).
Proof.
  intros INV TRACE. destruct (finite_data_trace_safe _ _ _ INV TRACE) as [SAFE EQ].
  rewrite <- EQ. exact (proj2 (proj2 (proj1 (proj2 SAFE)))).
Qed.

Theorem usable_trace_opens initial events j id d ram e :
  boundary_safe initial -> boundary_trace initial events ((j,IdleBoundary id d ram),e) ->
  data_caller DataBegin ram /\
  boundary_safe ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e).
Proof.
  intros INV TRACE. pose proof (proj1 (finite_data_trace_safe _ _ _ INV TRACE)) as SAFE.
  destruct (common_begin sector data_len boss_ok view marker ranges decode pages _ _ _ _ (proj1 SAFE)) as [CALL NEXT].
  split; [exact CALL|]. split; [exact NEXT|]. split; [exact (proj1 (proj2 SAFE))|exact I].
Qed.

(* Internal prefixes are not erased by the macro edge: at EVERY reachable idle
   frontier the full A8/A11.3 outcome-and-prefix specification is available.
   This includes incomplete journal prefixes and boot prefixes with no Ready. *)
Theorem finite_trace_internal_prefixes initial events f h a old d ram e id index entry span :
  boundary_safe initial -> boundary_trace initial events ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  data_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    data_writer boss_writer data_plan boss_plan old id d index entry span ram f h a e /\
  data_episode_delivery g sector data_len boss_ok view marker ranges decode topology pages
    data_writer boss_writer old id d index entry span ram f h a e.
Proof.
  intros INV TRACE RANGE FREE ERASED.
  eapply enriched_data_episode_freer; eauto. exact (proj1 (finite_data_trace_safe _ _ _ INV TRACE)).
Qed.

Theorem trace_append x events y more z :
  boundary_trace x events y -> boundary_trace y more z -> boundary_trace x (more++events) z.
Proof.
  intros T U. induction T.
  - rewrite app_nil_r; exact U.
  - rewrite app_assoc. eapply trace_cons; eauto.
Qed.

(* Composition witnesses consume operational edges, never intermediate safety. *)
Theorem two_successes_compose x r1 j1 id1 d1 ram1 e1 r2 y :
  boundary_step x (Some r1) ((j1,ClientBoundary id1 d1 ram1),e1) ->
  boundary_step ((j1,IdleBoundary id1 d1 ram1),e1) (Some r2) y ->
  boundary_trace x [r2;r1] y.
Proof.
  intros A B. change (boundary_trace x ([r2]++[r1]) y).
  eapply trace_cons with (event:=Some r1); [exact A|]. change (boundary_trace ((j1,ClientBoundary id1 d1 ram1),e1) ([r2]++[]) y).
  eapply trace_cons with (event:=None); [apply client_resume|]. change (boundary_trace ((j1,IdleBoundary id1 d1 ram1),e1) ([]++[r2]) y).
  eapply trace_cons with (event:=Some r2); [exact B|apply trace_nil].
Qed.
Theorem reset_boot_next_compose j phase e f h a id d ram event y :
  logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (logged_after_reset j,Selecting) (Logged (Ready f) h a,Usable id d ram) ->
  boundary_step ((Logged (Ready f) h a,IdleBoundary id d ram),recovered_page_evidence (Logged (Ready f) h a) id (forget_volatile_evidence e)) event y ->
  boundary_trace ((j,phase),e) (emitted_receipts event) y.
Proof.
  intros RESET BOOT NEXT.
  rewrite <- (app_nil_r (emitted_receipts event)). eapply trace_cons with (event:=None); [apply reset_boundary; exact RESET|].
  rewrite <- (app_nil_r (emitted_receipts event)). eapply trace_cons with (event:=None); [apply (run_boot (logged_after_reset j,Selecting) (Logged (Ready f) h a,Usable id d ram) (forget_volatile_evidence e)); exact BOOT|].
  rewrite <- (app_nil_r (emitted_receipts event)). eapply trace_cons with (event:=None); [apply boot_resume|].
  change (boundary_trace ((Logged (Ready f) h a,IdleBoundary id d ram),recovered_page_evidence (Logged (Ready f) h a) id (forget_volatile_evidence e)) ([]++emitted_receipts event) y).
  eapply trace_cons; [exact NEXT|apply trace_nil].
Qed.
Definition selected_live (x : execution_boundary) c :=
  In c (live_certificates (snd x)) /\
  hd_error (publications (boundary_journal x))=Some (N.of_nat (certificate_id c)).

Lemma selected_certificate_membership x c :
  boundary_safe x -> certificate_valid sector view ranges decode (boundary_journal x) c ->
  hd_error (publications (boundary_journal x))=Some (N.of_nat (certificate_id c)) -> selected_live x c.
Proof.
  intros [CORE [EV LINK]] [READ FMT] HEAD.
  destruct (proj1 (proj2 EV) (certificate_id c) HEAD) as [c' [IN ID]].
  assert (VALID : certificate_valid sector view ranges decode (boundary_journal x) c').
  { eapply Forall_forall; [exact (proj1 EV)|exact IN]. }
  destruct VALID as [READ' FMT']. rewrite ID in READ'.
  assert (certificate_decoded c'=certificate_decoded c) by congruence.
  assert (c'=c) by (destruct c,c'; simpl in *; congruence).
  subst c'; split; assumption.
Qed.

Lemma idle_selected_unique f h a old d ram e c :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
  selected_live ((Logged (Ready f) h a,IdleBoundary old d ram),e) c -> c=Certificate old d.
Proof.
  intros [[JI [IDLE [FMT COR]]] [EV IN]] [C HEAD].
  pose proof (proj1 (proj2 (proj2 (proj2 IDLE)))) as OLD.
  change (hd_error h=Some (N.of_nat old)) in OLD.
  change (hd_error h=Some (N.of_nat (certificate_id c))) in HEAD.
  assert (ID : certificate_id c=old) by (apply Nat2N.inj; congruence).
  assert (V : certificate_valid sector view ranges decode (Logged (Ready f) h a) c).
  { eapply Forall_forall; [exact (proj1 EV)|exact C]. }
  assert (V' : certificate_valid sector view ranges decode (Logged (Ready f) h a) (Certificate old d)).
  { eapply Forall_forall; [exact (proj1 EV)|exact IN]. }
  destruct V as [R F], V' as [R' F']. simpl in R', R. rewrite ID in R.
  assert (certificate_decoded c=d) by congruence. destruct c; simpl in *; congruence.
Qed.

Lemma publication_execution_logged old id image index entry span s prepared ready e event next :
  publication_execution old id image index entry span s prepared ready e event next ->
  clos_refl_trans logged_state (logged_step g sector 256 data_len boss_ok) ready (boundary_journal next).
Proof.
  intro RUN; destruct RUN; cbn [boundary_journal fst].
  - eapply rt_trans; [eapply successful_trace_is_logged; exact H|apply rt_step; exact H0].
  - eapply rt_trans; [eapply successful_trace_is_logged; exact H|apply rt_step; exact H0].
  - exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ H))).
  - destruct H as [before [PREFIX [BEFORE [STEP DEST]]]].
    eapply rt_trans; [exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX)))|apply rt_step; exact STEP].
  - eapply rt_trans; [eapply successful_trace_is_logged; exact H|].
    eapply rt_trans; [apply rt_step; exact H0|]. apply rt_step; apply record_step; apply reset_ready.
  - eapply rt_trans; [eapply successful_trace_is_logged; exact H|].
    eapply rt_trans; [apply rt_step; exact H0|]. apply rt_step; apply record_step; apply reset_ready.
  - eapply rt_trans; [eapply successful_trace_is_logged; exact H|].
    eapply rt_trans; [apply rt_step; exact H0|]. apply rt_step; apply record_step; apply reset_ready.
Qed.

Lemma reserved_history_extension old id d index entry span ram f h a e event next :
  reserved_execution old id d index entry span ram f h a e event next ->
  exists prefix, publications (boundary_journal next)=prefix++h.
Proof.
  intro RUN. destruct RUN; try (exists [];reflexivity).
  pose proof (publication_execution_logged _ _ _ _ _ _ _ _ _ _ _ _ H3) as LOG.
  exact (logged_history_extension _ _ _ _ _ _ _ LOG).
Qed.

Lemma publication_execution_reads old id image index entry span s prepared ready decoded e event next c :
  publication_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    old id image index entry span s prepared ready decoded e ->
  In c (live_certificates e) ->
  publication_execution old id image index entry span s prepared ready e event next ->
  certificate_valid sector view ranges decode (boundary_journal next) c.
Proof.
  intros [PREP REST] IN RUN.
  assert (C : certificate_valid sector view ranges decode ready c).
  { eapply Forall_forall; [exact (proj1 (proj1 (proj2 PREP)))|exact IN]. }
  assert (FRAME : forall x, 2*sector<=x -> control_image (journal_control (boundary_journal next)) x=control_image (journal_control ready) x).
  { intros x X. eapply logged_trace_frame_after_journal; eauto.
    - exact (proj1 (proj1 PREP)).
    - eapply publication_execution_logged; exact RUN. }
  exact (proj1 (certificate_frame sector view ranges decode DIV CONTRACT ready (boundary_journal next) c C FRAME)).
Qed.

Lemma reserved_execution_old_read old id d index entry span s f h a e event next :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
  erased_object_extent sector f span ->
  reserved_execution old id d index entry span s f h a e event next ->
  certificate_valid sector view ranges decode (boundary_journal next) (Certificate old d).
Proof.
  intros INV RANGE FREE ERASED RUN.
  pose proof (enriched_data_episode g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT data_bytes data_writer boss_writer data_plan boss_plan old id d index entry span s f h a e
    INV RANGE FREE ERASED WRITERS) as POST.
  pose proof (proj1 (proj2 (proj2 (proj1 INV)))) as FMT.
  unfold data_episode_post in POST. destruct POST as [EXEC [FRAME CASE]].
  destruct RUN.
  - destruct H as [H|[H|H]]; rewrite H in CASE;
      split; try exact FMT; exact (proj1 (proj2 (proj1 CASE))).
  - rewrite H in CASE. split; try exact FMT; exact (proj1 (proj2 (proj1 CASE))).
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]].
    destruct H2 as [H2|[H2|H2]]; rewrite H2 in CASE;
      split; try exact FMT; exact (proj1 (proj2 (proj1 CASE))).
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]]. rewrite H2 in CASE.
    split; try exact FMT; exact (proj1 (proj2 (proj1 CASE))).
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]]. rewrite H2 in CASE.
    eapply publication_execution_reads with (e:=prepared_evidence old id d index entry (advance_allocation_evidence (boss_extent (view id)) (advance_allocation_evidence span e))); [exact CASE|simpl; auto|exact H3].
Qed.
Lemma boundary_history_extension x event y :
  boundary_safe x -> boundary_step x event y ->
  exists prefix, publications (boundary_journal y)=prefix++publications (boundary_journal x).
Proof.
  intros INV STEP. destruct STEP.
  - eapply reserved_history_extension; exact H2.
  - exists []; reflexivity.
  - exists []; reflexivity.
  - exists []; reflexivity.
  - destruct (boundary_boot_prefix_safe _ _ _ INV (boundary_live_readers _ INV) H) as [LAST PUB].
    exists []; exact PUB.
  - exists []; reflexivity.
  - exists []; reflexivity.
Qed.
Theorem global_history_extension initial events final :
  boundary_safe initial -> boundary_trace initial events final ->
  exists prefix, publications (boundary_journal final)=prefix++publications (boundary_journal initial).
Proof.
  intros INV TRACE. induction TRACE.
  - exists []; reflexivity.
  - destruct (boundary_history_extension _ _ _ INV H) as [p P].
    destruct (IHTRACE (proj1 (boundary_step_preserves _ _ _ INV H))) as [q Q].
    exists (q++p). rewrite Q. rewrite P. rewrite app_assoc. reflexivity.
Qed.

Lemma no_publication_step_selected x event y c :
  boundary_safe x -> selected_live x c -> boundary_step x event y ->
  publications (boundary_journal y)=publications (boundary_journal x) ->
  selected_live y c.
Proof.
  intros INV SEL STEP HIST.
  pose proof (proj1 (boundary_step_preserves _ _ _ INV STEP)) as NEXT.
  destruct STEP.
  - pose proof (idle_selected_unique _ _ _ _ _ _ _ _ INV SEL) as SAME; subst c.
    apply selected_certificate_membership; [exact NEXT| |].
    + eapply reserved_execution_old_read; eauto.
    + rewrite HIST. exact (proj2 SEL).
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
  - split; [exact (proj1 SEL)|rewrite HIST; exact (proj2 SEL)].
Qed.

(* The no-later-publication condition constrains the physical event history,
   not the selected image or the destination invariant. *)
Definition publication_free_step x y := exists event,
  boundary_step x event y /\ publications (boundary_journal y)=publications (boundary_journal x).
Theorem no_later_publication_preserves_certificate x y c :
  boundary_safe x -> selected_live x c ->
  clos_refl_trans execution_boundary publication_free_step x y ->
  boundary_safe y /\ selected_live y c.
Proof.
  intros INV SEL TRACE. induction TRACE.
  - destruct H as [event [STEP HIST]]. split.
    + exact (proj1 (boundary_step_preserves _ _ _ INV STEP)).
    + eapply no_publication_step_selected; eauto.
  - split; assumption.
  - destruct (IHTRACE1 INV SEL) as [MID SELECTED]. apply IHTRACE2; assumption.
Qed.

Lemma selected_usable_identity j chosen decoded ram e c :
  boundary_safe ((j,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (e)) ->
  selected_live ((j,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (e)) c ->
  chosen=certificate_id c /\ decoded=certificate_decoded c /\ data_caller DataBegin ram.
Proof.
  intros SAFE SEL.
  destruct (enriched_boot_usable sector data_len boss_ok view marker ranges decode pages _ _ _ _ _ SAFE)
    as [IDLE [FOUND [CALL NEXT]]].
  destruct j as [ctrl h a].
  destruct (proj1 (proj2 (proj2 (proj1 (proj2 (proj1 IDLE)))))) as [f READY].
  cbn in READY; subst ctrl.
  pose proof (idle_selected_unique _ _ _ _ _ _ _ _ IDLE SEL) as E.
  subst c; split; [reflexivity|]. split; [reflexivity|exact CALL].
Qed.

Theorem global_success_recovered initial events j id d ram e final_j chosen decoded restored final_e :
  boundary_safe initial -> boundary_trace initial events ((j,ClientBoundary id d ram),e) ->
  clos_refl_trans execution_boundary publication_free_step ((j,ClientBoundary id d ram),e)
    ((final_j,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (final_e)) ->
  chosen=id /\ decoded=d /\ data_caller DataBegin restored.
Proof.
  intros INIT TRACE QUIET.
  pose proof (proj1 (finite_data_trace_safe _ _ _ INIT TRACE)) as SAFE.
  assert (SEL : selected_live ((j,ClientBoundary id d ram),e) (Certificate id d)).
  { split; [exact (proj2 (proj2 SAFE))|].
    exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj1 SAFE)))))))). }
  destruct (no_later_publication_preserves_certificate _ _ _ SAFE SEL QUIET) as [FINAL SAME].
  exact (selected_usable_identity _ _ _ _ _ _ FINAL SAME).
Qed.

(* An uncertain episode keeps two certificates, but only the journal head is
   selected. Later physical publication is deliberately excluded from this
   episode-relative corollary, not from the global trace relation. *)
Theorem global_uncertain_no_hybrid initial events j phase old before candidate after receipts
    jf chosen decoded ram ef :
  boundary_safe initial ->
  boundary_trace initial events ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) ->
  publications (boundary_journal initial) <> [] ->
  clos_refl_trans execution_boundary publication_free_step
    ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts)
    ((jf,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (ef)) ->
  ((chosen=old /\ decoded=before) \/ (chosen=candidate /\ decoded=after)) /\ data_caller DataBegin ram.
Proof.
  intros INIT TRACE NONEMPTY QUIET.
  pose proof (proj1 (finite_data_trace_safe _ _ _ INIT TRACE)) as SAFE.
  destruct (global_history_extension _ _ _ INIT TRACE) as [prefix EXT].
  assert (NONEMPTY' : publications j<>[]).
  { change (publications j=prefix++publications (boundary_journal initial)) in EXT.
    intro EMPTY. rewrite EMPTY in EXT. symmetry in EXT. apply app_eq_nil in EXT; tauto. }
  destruct (publications j) as [|head tail] eqn:PUBLICATIONS; [contradiction|].
  assert (HEAD : hd_error (publications j)=Some (N.of_nat (N.to_nat head))).
  { rewrite PUBLICATIONS. rewrite N2Nat.id. reflexivity. }
  destruct (proj1 (proj2 (proj1 (proj2 SAFE))) _ HEAD) as [c [IN CID]].
  assert (SEL : selected_live ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) c).
  { split; [exact IN|rewrite CID;exact HEAD]. }
  pose proof (proj1 SEL) as MEMBER.
  destruct (no_later_publication_preserves_certificate _ _ _ SAFE SEL QUIET) as [FINAL SAME].
  destruct (selected_usable_identity _ _ _ _ _ _ FINAL SAME) as [ID [IMAGE CALL]].
  split; [|exact CALL]. simpl in MEMBER. destruct MEMBER as [C|[C|NO]]; [left|right|contradiction]; subst c; split; assumption.
Qed.
Definition actual_client_delivery (r : client_receipt) :=
  exists id image saved initial final,
    receipt_certificate r=Certificate id (RecoveryDecoding (boss_extent (view id)) image) /\
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id saved)
      (client_finish_program id image [SlotCompleted;DurableRamWritten;ExternalAccepted]))
      initial (ClientReturned (DataClientSuccess id image)) final.
Lemma publication_emission_is_delivery old id image index entry span s prepared ready e event next :
  publication_execution old id image index entry span s prepared ready e event next ->
  forall r, event=Some r -> actual_client_delivery r.
Proof.
  intros RUN r EQ. destruct RUN; try discriminate.
  inversion EQ; subst r. exists id,(image_replace image index (Some entry)),
    (protection_current s++attached_ranges s),
    (prepared_transaction_candidate view id ranges image index entry span s),final.
  split; [reflexivity|exact H1].
Qed.
Lemma reserved_emission_is_delivery old id d index entry span s f h a e event next :
  reserved_execution old id d index entry span s f h a e event next ->
  forall r, event=Some r -> actual_client_delivery r.
Proof.
  intros RUN r EQ. destruct RUN; try discriminate.
  eapply publication_emission_is_delivery; eauto.
Qed.
Theorem boundary_emission_is_delivery x event y :
  boundary_step x event y -> forall r, event=Some r -> actual_client_delivery r.
Proof. intros RUN r EQ; destruct RUN; try discriminate; eapply reserved_emission_is_delivery; eauto. Qed.
Lemma publication_receipt_owner_closed old id image index entry span s prepared ready e event next :
 publication_execution old id image index entry span s prepared ready e event next ->
 forall receipt,event=Some receipt -> delivered_owner_closed (snd next).
Proof.
 intros RUN receipt EQ;destruct RUN;try discriminate.
 apply published_owner_closed.
Qed.
Lemma reserved_receipt_owner_closed old id d index entry span s f h a e event next :
 reserved_execution old id d index entry span s f h a e event next ->
 forall receipt,event=Some receipt -> delivered_owner_closed (snd next).
Proof. intros RUN receipt EQ;destruct RUN;try discriminate;eapply publication_receipt_owner_closed;eauto. Qed.
Lemma boundary_receipt_owner_closed x event y :
 boundary_step x event y -> forall receipt,event=Some receipt -> delivered_owner_closed (snd y).
Proof. intros RUN receipt EQ;destruct RUN;try discriminate;eapply reserved_receipt_owner_closed;eauto. Qed.

Theorem trace_emissions_are_deliveries initial events final :
  boundary_trace initial events final -> Forall actual_client_delivery events.
Proof.
  intro TRACE; induction TRACE.
  - constructor.
  - apply Forall_app; split; [exact IHTRACE|].
    destruct event; [constructor; [eapply boundary_emission_is_delivery; eauto|constructor]|constructor].
Qed.

Theorem unchanged_history_is_publication_free initial events final :
  boundary_safe initial -> boundary_trace initial events final ->
  publications (boundary_journal final)=publications (boundary_journal initial) ->
  clos_refl_trans execution_boundary publication_free_step initial final.
Proof.
  intros INV TRACE. induction TRACE; intro SAME; [apply rt_refl|].
  pose proof (proj1 (boundary_step_preserves _ _ _ INV H)) as MID.
  destruct (boundary_history_extension _ _ _ INV H) as [p P].
  destruct (global_history_extension _ _ _ MID TRACE) as [q Q].
  assert (L : length p=0 /\ length q=0).
  { pose proof (f_equal (@length N) SAME) as L. rewrite Q in L. rewrite P in L.
    repeat rewrite length_app in L. lia. }
  destruct L as [LP LQ]. apply length_zero_iff_nil in LP; apply length_zero_iff_nil in LQ. subst p q.
  eapply rt_trans; [apply rt_step; exists event; split; [exact H|exact P]|].
  apply IHTRACE; assumption.
Qed.

Theorem global_idle_before_publication initial events j id d ram e next_j chosen decoded restored next_e later :
  boundary_safe initial -> boundary_trace initial events ((j,IdleBoundary id d ram),e) ->
  boundary_trace ((j,IdleBoundary id d ram),e) later ((next_j,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (next_e)) ->
  publications next_j=publications j ->
  chosen=id /\ decoded=d /\ data_caller DataBegin restored.
Proof.
  intros INIT PREFIX SUFFIX HIST.
  pose proof (proj1 (finite_data_trace_safe _ _ _ INIT PREFIX)) as SAFE.
  assert (SEL : selected_live ((j,IdleBoundary id d ram),e) (Certificate id d)).
  { split; [exact (proj2 (proj2 SAFE))|]. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 SAFE))))))). }
  pose proof (unchanged_history_is_publication_free _ _ _ SAFE SUFFIX HIST) as QUIET.
  destruct (no_later_publication_preserves_certificate _ _ _ SAFE SEL QUIET) as [FINAL SAME].
  exact (selected_usable_identity _ _ _ _ _ _ FINAL SAME).
Qed.

Theorem global_client_durability initial events j id d ram e next_j chosen decoded restored next_e later :
  boundary_safe initial -> boundary_trace initial events ((j,ClientBoundary id d ram),e) ->
  boundary_trace ((j,ClientBoundary id d ram),e) later ((next_j,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (next_e)) ->
  publications next_j=publications j ->
  chosen=id /\ decoded=d /\ data_caller DataBegin restored.
Proof.
  intros INIT PREFIX SUFFIX HIST.
  eapply global_success_recovered; [exact INIT|exact PREFIX|].
  eapply unchanged_history_is_publication_free; [exact (proj1 (finite_data_trace_safe _ _ _ INIT PREFIX))|exact SUFFIX|exact HIST].
Qed.

Theorem fixed_writers_trace_safety f h a old decoded ram evidence events final :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old decoded ram),evidence) ->
  boundary_trace ((Logged (Ready f) h a,IdleBoundary old decoded ram),evidence) events final ->
  boundary_safe final /\
  boundary_receipts final=events++client_receipts evidence /\
  Forall (receipt_valid view ranges (publications (boundary_journal final))) (boundary_receipts final) /\
  Forall actual_client_delivery events.
Proof.
  intros INIT TRACE. destruct (finite_data_trace_safe _ _ _ INIT TRACE) as [SAFE RECEIPTS].
  split; [exact SAFE|]. split; [exact RECEIPTS|]. split.
  - exact (proj2 (proj2 (proj1 (proj2 SAFE)))).
  - apply trace_emissions_are_deliveries with (initial:=((Logged (Ready f) h a,IdleBoundary old decoded ram),evidence)) (final:=final); exact TRACE.
Qed.
(* Nonempty witness schemas are built from reserved operational executions,
   not from boundary invariants or the existence of a successful result. *)
Theorem two_reserved_successes_witness old id1 d0 index1 entry1 span1 s0 f0 h0 a0 e0
    r1 f1 h1 a1 d1 s1 e1 id2 index2 entry2 span2 r2 final :
  ranges entry1=[span1] -> free_range 256 (protection_table (data_next DataBegin s0)) span1 ->
  erased_object_extent sector f0 span1 ->
  reserved_execution old id1 d0 index1 entry1 span1 s0 f0 h0 a0 e0 (Some r1)
    ((Logged (Ready f1) h1 a1,ClientBoundary id1 d1 s1),e1) ->
  ranges entry2=[span2] -> free_range 256 (protection_table (data_next DataBegin s1)) span2 ->
  erased_object_extent sector f1 span2 ->
  reserved_execution id1 id2 d1 index2 entry2 span2 s1 f1 h1 a1 e1 (Some r2) final ->
  range_numeric (1024*256) span1 -> range_numeric (1024*256) span2 ->
  runtime_erased_admission sector pages e0 (data_next DataBegin s0) f0 span1 ->
  runtime_erased_admission sector pages e1 (data_next DataBegin s1) f1 span2 ->
  boundary_trace ((Logged (Ready f0) h0 a0,IdleBoundary old d0 s0),e0) [r2;r1] final.
Proof.
  intros R1 F1 E1 X1 R2 F2 E2 X2 N1 N2 AD1 AD2.
  eapply two_successes_compose.
  - exact (run_reserved old id1 d0 index1 entry1 span1 s0 f0 h0 a0 e0 (Some r1) _ R1 F1 E1 X1 N1 AD1).
  - exact (run_reserved id1 id2 d1 index2 entry2 span2 s1 f1 h1 a1 e1 (Some r2) _ R2 F2 E2 X2 N2 AD2).
Qed.
Theorem reset_then_reserved_witness j phase e f h a old d ram id index entry span event final :
  logged_step g sector 256 data_len boss_ok j (logged_after_reset j) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (logged_after_reset j,Selecting) (Logged (Ready f) h a,Usable old d ram) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  reserved_execution old id d index entry span ram f h a (recovered_page_evidence (Logged (Ready f) h a) old (forget_volatile_evidence e)) event final ->
  range_numeric (1024*256) span ->
  runtime_erased_admission sector pages (recovered_page_evidence (Logged (Ready f) h a) old (forget_volatile_evidence e)) (data_next DataBegin ram) f span ->
  boundary_trace ((j,phase),e) (emitted_receipts event) final.
Proof. intros RESET BOOT R F E RUN NUM AD. eapply reset_boot_next_compose; eauto. eapply run_reserved; eauto. Qed.
Theorem publication_cut_boot_witness old id d index entry span ram f h a e cut final :
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  writer_end (data_writer f span entry)=WriterComplete ->
  free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span ram)) (boss_extent (view id)) ->
  erased_object_extent sector (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
  writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterComplete ->
  publication_reset_prefix g sector data_len boss_ok (N.of_nat id)
    (Logged (Ready (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a) cut ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) (cut,Selecting) final ->
  range_numeric (1024*256) span -> range_numeric (1024*256) (boss_extent (view id)) ->
  runtime_erased_admission sector pages e (data_next DataBegin ram) f span ->
  runtime_erased_admission sector pages (advance_allocation_evidence span e)
    (modified_transaction ranges (recovered_image d) index entry span ram)
    (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
  boundary_trace ((Logged (Ready f) h a,IdleBoundary old d ram),e) []
    ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence (prepared_evidence old id d index entry e)).
Proof.
  intros RANGE FREE ERASED D BF BE B CUT BOOT NUM BNUM AD BAD.
  replace ([] : list client_receipt) with ([]++emitted_receipts None) by reflexivity.
  eapply trace_cons with (event:=None).
  - eapply run_reserved; [exact RANGE|exact FREE|exact ERASED| |exact NUM|exact AD].
    eapply prepared_execution; [exact D|exact BF|exact BE|exact B| |exact BNUM|exact BAD]. apply publication_cut; exact CUT.
  - replace ([] : list client_receipt) with ([]++emitted_receipts None) by reflexivity.
    eapply trace_cons with (event:=None); [apply (run_boot (cut,Selecting) final _);exact BOOT|apply trace_nil].
Qed.

Definition boundary_objects x := object_flash sector (control_image (journal_control (boundary_journal x))).
Lemma reserved_execution_old_bytes old id d index entry span s f h a e event next :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
  erased_object_extent sector f span ->
  reserved_execution old id d index entry span s f h a e event next ->
  unchanged (root_extents (view old)) (object_flash sector f) (boundary_objects next).
Proof.
  intros INV RANGE FREE ERASED RUN.
  pose proof (enriched_data_episode g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT data_bytes data_writer boss_writer data_plan boss_plan old id d index entry span s f h a e
    INV RANGE FREE ERASED WRITERS) as POST.
  unfold data_episode_post in POST. destruct POST as [EXEC [FRAME CASE]].
  destruct RUN; try exact FRAME.
  - rewrite H in CASE. specialize (CASE H0 H1). exact (proj1 (proj2 CASE)).
  - rewrite H in CASE. specialize (CASE H0 H1). exact (proj1 (proj2 CASE)).
  - rewrite H in CASE. specialize (CASE H0 H1). destruct CASE as [EXEC2 [FRAME2 CASE]]. rewrite H2 in CASE.
    pose proof (publication_execution_logged _ _ _ _ _ _ _ _ _ _ _ _ H3) as LOG.
    assert (KEEP : forall x, 2*sector<=x -> control_image (journal_control (boundary_journal next)) x=
      writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))) x).
    { intros x X. exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ _ G DIV (proj1 (proj1 (proj1 CASE))) LOG X). }
    intros r addr IN AT. unfold boundary_objects,object_flash. rewrite (KEEP (2*sector+addr) ltac:(lia)). exact (FRAME2 r addr IN AT).
Qed.
(* Historical service composition exposes the same physical marker frame. *)
Lemma reserved_execution_marker old id d index entry span s f h a e event next :
 boundary_safe ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
 erased_object_extent sector f span ->
 reserved_execution old id d index entry span s f h a e event next ->
 unchanged [marker] (object_flash sector f) (boundary_objects next).
Proof.
 intros INV RANGE FREE ERASED RUN.
 pose proof (enriched_data_episode g sector data_len boss_ok view marker ranges decode topology pages
   G DIV CONTRACT data_bytes data_writer boss_writer data_plan boss_plan old id d index entry span s f h a e
   INV RANGE FREE ERASED WRITERS) as POST.
 destruct POST as [EXEC [OLD_FRAME CASE]].
 pose proof INV as [[JI [IDLE [FMT COR]]] EVIDENCE].
 pose proof (proj1 IDLE) as ROOT.
 pose proof ROOT as [DI [NF [STACK [P [CUR [BASE [AUTH ACK]]]]]]].
 destruct (preparation_entry_context view marker old ranges (recovered_image d) index entry span s
   ROOT (eq_sym (proj2 FMT)) RANGE FREE) as [RES [MOD OTHER]].
 assert (VALID:valid_flash f) by exact (proj1 (proj1 JI)).
 assert (DFRAME:unchanged [marker] (object_flash sector f)
   (object_flash sector (writer_flash (data_writer f span entry)))).
 { eapply pending_writer_marker_frame with (s:=data_reservation_state span s)
     (p:=Build_preparation ObjectPreparation span Reserved);try eassumption;try reflexivity.
   change (In marker (protection_base s));rewrite BASE;simpl;auto. }
 assert (DVALID:valid_flash (writer_flash (data_writer f span entry))).
 { exact (proj1 (writer_execution_locality _ _ _ _ _ _ _ VALID EXEC)). }
 assert (BFRAME:free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span s))
   (boss_extent (view id)) ->
   unchanged [marker] (object_flash sector f)
   (object_flash sector (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id
      (image_replace (recovered_image d) index (Some entry)))))).
 { intro BF.
   pose proof (free_writer_marker_frame g sector marker
     (modified_transaction ranges (recovered_image d) index entry span s) (boss_extent (view id)) true
     (writer_flash (data_writer f span entry))
     (boss_plan (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))
     (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))
     MOD ltac:(change (In marker (protection_base s));rewrite BASE;simpl;auto) BF DVALID
     (boss_writer_execution _ _ _ _ _ _ _ _ _ WRITERS _ _ _)) as KEEP.
   intros r addr IN AT;rewrite (KEEP r addr IN AT);exact (DFRAME r addr IN AT). }
 destruct RUN;try exact DFRAME;try (apply BFRAME;assumption).
 rewrite H in CASE;specialize (CASE H0 H1);destruct CASE as [EXEC2 [FRAME2 CASE]];rewrite H2 in CASE.
 pose proof (publication_execution_logged _ _ _ _ _ _ _ _ _ _ _ _ H3) as LOG.
 intros r addr IN AT;unfold boundary_objects,object_flash.
 rewrite (logged_trace_frame_after_journal _ _ _ _ _ _ _ (2*sector+addr) G DIV (proj1 (proj1 (proj1 CASE))) LOG ltac:(lia)).
 exact (BFRAME H0 r addr IN AT).
Qed.
Lemma boundary_step_marker x event y :
 boundary_safe x -> boundary_step x event y ->
 unchanged [marker] (boundary_objects x) (boundary_objects y).
Proof.
 intros INV RUN;destruct RUN;try (intros r addr IN AT;reflexivity).
 - eapply reserved_execution_marker;eauto.
 - destruct j as [ctrl pubs acks];destruct ctrl;intros r addr IN AT;reflexivity.
 - intros r addr IN AT;unfold boundary_objects,object_flash.
   apply (boundary_boot_objects_preserved _ _ _ INV (boundary_live_readers _ INV) H);lia.
Qed.

Lemma boundary_selected_bytes x event y c :
  boundary_safe x -> selected_live x c -> boundary_step x event y ->
  unchanged (certificate_ranges ranges c) (boundary_objects x) (boundary_objects y).
Proof.
  intros INV SEL STEP. destruct STEP.
  - pose proof (idle_selected_unique _ _ _ _ _ _ _ _ INV SEL) as EQ; subst c.
    pose proof (proj1 (proj2 (proj2 (proj1 INV)))) as [BOSS OBJECTS].
    unfold certificate_ranges; simpl. rewrite BOSS. rewrite OBJECTS.
    eapply reserved_execution_old_bytes; eauto.
  - unfold unchanged; intros; reflexivity.
  - unfold unchanged; intros; reflexivity.
  - destruct j as [ctrl h a]; destruct ctrl; unfold unchanged; intros; reflexivity.
  - intros r address IN AT. unfold boundary_objects, object_flash.
    apply (boundary_boot_objects_preserved _ _ _ INV (boundary_live_readers _ INV) H); lia.
  - unfold unchanged; intros; reflexivity.
  - unfold unchanged; intros; reflexivity.
Qed.
Theorem no_later_publication_preserves_objects x y c :
  boundary_safe x -> selected_live x c ->
  clos_refl_trans execution_boundary publication_free_step x y ->
  unchanged (certificate_ranges ranges c) (boundary_objects x) (boundary_objects y).
Proof.
  intros INV SEL TRACE. induction TRACE.
  - destruct H as [event [STEP HIST]]. eapply boundary_selected_bytes; eauto.
  - unfold unchanged; intros; reflexivity.
  - destruct (no_later_publication_preserves_certificate _ _ _ INV SEL TRACE1) as [MID C].
    intros r addr IN AT. rewrite (IHTRACE2 MID C r addr IN AT). exact (IHTRACE1 INV SEL r addr IN AT).
Qed.
Theorem completed_unacknowledged_episode_witness old id d index entry span ram f h a e
    before after slot history acks :
  ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
  erased_object_extent sector f span ->
  writer_end (data_writer f span entry)=WriterComplete ->
  free_range 256 (protection_table (modified_transaction ranges (recovered_image d) index entry span ram)) (boss_extent (view id)) ->
  erased_object_extent sector (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
  writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))=WriterComplete ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok (N.of_nat id))
    (Logged (Ready (writer_flash (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry))))) h a)
    (Logged (Writing before slot (N.of_nat id)) history acks) ->
  program_step g before (8*slot/256*256) (candidate_buffer 256 before slot (N.of_nat id)) Success after ->
  candidate_completed after slot (N.of_nat id)=true ->
  range_numeric (1024*256) span -> range_numeric (1024*256) (boss_extent (view id)) ->
  runtime_erased_admission sector pages e (data_next DataBegin ram) f span ->
  runtime_erased_admission sector pages (advance_allocation_evidence span e)
    (modified_transaction ranges (recovered_image d) index entry span ram)
    (writer_flash (data_writer f span entry)) (boss_extent (view id)) ->
  boundary_trace ((Logged (Ready f) h a,IdleBoundary old d ram),e) []
    ((Logged (Boot after) (N.of_nat id::history) acks,RebuildingBoundary Selecting),forget_volatile_evidence (prepared_evidence old id d index entry e)).
Proof.
  intros R F E D BF BE B PREFIX PROGRAM COMPLETE NUM BNUM AD BAD.
  apply (publication_cut_boot_witness old id d index entry span ram f h a e
    (Logged (Boot after) (N.of_nat id::history) acks)
    (Logged (Boot after) (N.of_nat id::history) acks,Selecting)); try assumption.
  - eapply completed_program_publication_cut; eauto.
  - apply rt_refl.
Qed.

Theorem published_cut_recovers_exact initial events cut old id d index entry e final_j chosen decoded ram :
  boundary_safe initial ->
  boundary_trace initial events ((cut,RebuildingBoundary Selecting),forget_volatile_evidence (prepared_evidence old id d index entry e)) ->
  hd_error (publications cut)=Some (N.of_nat id) ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages)
    (cut,Selecting) (final_j,Usable chosen decoded ram) ->
  chosen=id /\ decoded=RecoveryDecoding (boss_extent (view id)) (image_replace (recovered_image d) index (Some entry)) /\
  data_caller DataBegin ram.
Proof.
  intros INIT TRACE HEAD BOOT.
  pose proof (proj1 (finite_data_trace_safe _ _ _ INIT TRACE)) as CUT.
  pose proof (proj1 (enriched_boot_transport g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT (cut,Selecting) (final_j,Usable chosen decoded ram) _ CUT BOOT)) as FINAL.
  destruct (boot_finite_trace g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT _ _ (proj2 (proj1 CUT)) BOOT) as [LAST PROJ].
  destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [PUB REST].
  apply (selected_usable_identity final_j chosen decoded ram (prepared_evidence old id d index entry e)
    (Certificate id (RecoveryDecoding (boss_extent (view id)) (image_replace (recovered_image d) index (Some entry))))).
  - exact FINAL.
  - split; [simpl; auto|]. change (hd_error (publications final_j)=Some (N.of_nat id)).
    change (publications final_j=publications cut) in PUB. rewrite PUB. exact HEAD.
Qed.

Theorem initialized_history_nonempty f h a old d ram e :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary old d ram),e) -> h<>[].
Proof.
  intro INV. pose proof (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 INV))))))) as HEAD.
  change (hd_error h=Some (N.of_nat old)) in HEAD. intro E; subst h; discriminate.
Qed.
Theorem initialized_uncertain_no_hybrid f h a root initial_decoded initial_ram initial_e events
    j phase old before candidate after receipts jf chosen decoded ram ef later :
  boundary_safe ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) ->
  boundary_trace ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) events
    ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) ->
  boundary_trace ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) later
    ((jf,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (ef)) ->
  publications jf=publications j ->
  ((chosen=old /\ decoded=before) \/ (chosen=candidate /\ decoded=after)) /\ data_caller DataBegin ram.
Proof.
  intros INIT PREFIX SUFFIX HIST.
  eapply global_uncertain_no_hybrid; [exact INIT|exact PREFIX| |].
  - exact (initialized_history_nonempty _ _ _ _ _ _ _ INIT).
  - eapply unchanged_history_is_publication_free;
      [exact (proj1 (finite_data_trace_safe _ _ _ INIT PREFIX))|exact SUFFIX|exact HIST].
Qed.

Theorem global_client_objects_stable initial events j id d ram e later final :
  boundary_safe initial -> boundary_trace initial events ((j,ClientBoundary id d ram),e) ->
  boundary_trace ((j,ClientBoundary id d ram),e) later final ->
  publications (boundary_journal final)=publications j ->
  unchanged (certificate_ranges ranges (Certificate id d))
    (object_flash sector (control_image (journal_control j))) (boundary_objects final).
Proof.
  intros INIT PREFIX SUFFIX HIST.
  pose proof (proj1 (finite_data_trace_safe _ _ _ INIT PREFIX)) as SAFE.
  assert (SEL : selected_live ((j,ClientBoundary id d ram),e) (Certificate id d)).
  { split; [exact (proj2 (proj2 SAFE))|].
    exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj1 SAFE)))))))). }
  apply (no_later_publication_preserves_objects ((j,ClientBoundary id d ram),e) final (Certificate id d)); [exact SAFE|exact SEL|].
  eapply unchanged_history_is_publication_free; eauto.
Qed.
Theorem failed_preparation_has_no_publication old id d index entry span ram f h a e event next :
  reserved_execution old id d index entry span ram f h a e event next ->
  (writer_end (data_writer f span entry)<>WriterComplete \/
   writer_end (boss_writer (writer_flash (data_writer f span entry)) id (image_replace (recovered_image d) index (Some entry)))<>WriterComplete) ->
  event=None /\ publications (boundary_journal next)=h /\ boundary_receipts next=client_receipts e.
Proof.
  intros RUN FAILED. destruct RUN; try (split; [reflexivity|split;reflexivity]).
  destruct FAILED; contradiction.
Qed.
Lemma publication_execution_allocation_origin old id image index entry span s prepared ready e event next :
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode e ->
 publication_execution old id image index entry span s prepared ready e event next ->
 boundary_safe next -> allocation_range_origin sector pages decode (snd next).
Proof.
 intros GEO ORIGIN RUN SAFE;destruct RUN;try exact ORIGIN;try apply allocation_origin_forget.
 eapply allocation_origin_observe;[exact GEO|].
 exact (generation_client_read _ _ _ _ _ _ _ _ _ _ _ _ _ SAFE).
Qed.
Lemma reserved_execution_allocation_origin old id d index entry span s f h a e event next :
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode e ->
 reserved_execution old id d index entry span s f h a e event next ->
 boundary_safe next -> allocation_range_origin sector pages decode (snd next).
Proof.
 intros GEO ORIGIN RUN SAFE;destruct RUN;try apply allocation_origin_forget.
 - unfold collected_failure;cbn [snd];apply allocation_origin_phase.
   apply allocation_origin_advance;exact ORIGIN.
 - unfold collected_failure;cbn [snd];apply allocation_origin_phase.
   apply allocation_origin_advance;apply allocation_origin_advance;exact ORIGIN.
 - eapply publication_execution_allocation_origin;[exact GEO| |eassumption|exact SAFE].
   apply allocation_origin_advance;apply allocation_origin_advance;exact ORIGIN.
Qed.
Lemma boundary_step_allocation_origin x event y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode (snd x) -> boundary_safe x ->
 boundary_step x event y -> allocation_range_origin sector pages decode (snd y).
Proof.
 intros MATCH GEO ORIGIN INV RUN.
 pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact ORIGIN;try apply allocation_origin_forget.
 - eapply reserved_execution_allocation_origin;eassumption.
 - intros a OBS;eapply allocation_origin_decoded;[exact MATCH|exact GEO| |exact OBS].
   exact (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ NEXT).
Qed.

Lemma publication_execution_append_bound old id image index entry span s prepared ready e event next :
 allocation_append_bound pages e ->
 publication_execution old id image index entry span s prepared ready e event next ->
 allocation_append_bound pages (snd next).
Proof.
 intros B RUN;destruct RUN;try exact B;try apply allocation_append_forget.
 apply allocation_append_observe;exact B.
Qed.
Lemma reserved_execution_append_bound old id d index entry span s f h a e event next :
 extent_end span<=pages*256 ->
 reserved_execution old id d index entry span s f h a e event next ->
 allocation_append_bound pages (snd next).
Proof.
 intros B RUN;destruct RUN;try apply allocation_append_forget.
 - unfold collected_failure;cbn [snd];apply allocation_append_phase;apply allocation_append_advance;exact B.
 - unfold collected_failure;cbn [snd];apply allocation_append_phase;apply allocation_append_advance.
   match goal with A:runtime_erased_admission _ _ _ _ _ _ |- _ =>
     exact (proj1 (runtime_erased_advance_bounded _ _ _ _ _ _ _ (Nat.le_refl _) A)) end.
 - eapply publication_execution_append_bound;[|eassumption].
   apply allocation_append_advance.
   match goal with A:runtime_erased_admission _ _ _ _ _ _ |- _ =>
     exact (proj1 (runtime_erased_advance_bounded _ _ _ _ _ _ _ (Nat.le_refl _) A)) end.
Qed.
Lemma boundary_step_append_bound x event y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 decoded_allocation_geometry pages decode -> allocation_append_bound pages (snd x) ->
 boundary_safe x -> boundary_step x event y -> allocation_append_bound pages (snd y).
Proof.
 intros MATCH GEO B INV RUN;pose proof (proj1 (boundary_step_preserves _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact B;try apply allocation_append_forget.
 - eapply reserved_execution_append_bound;[|eassumption].
   match goal with A:runtime_erased_admission _ _ _ _ _ _ |- _ =>
     exact (proj1 (runtime_erased_advance_bounded _ _ _ _ _ _ _ (Nat.le_refl _) A)) end.
 - intros a OBS;eapply allocation_append_decoded;[exact MATCH|exact GEO| |exact OBS].
   exact (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ NEXT).
Qed.

End Trace.

(* The outer trace quantifies the observed writer services PER EDGE. In
   particular retrying identical input can have a different physical outcome.
   This is the union of the preceding operational relations on the SAME state,
   not a new storage machine or a second copy of any witness. *)
(* Observers are indices of the EXISTING episode relation. They are not a
   second flash, journal or RAM witness. A writer's output observer is computed
   from its reached bytes and decoder result. *)
Section LegacyRawTransport.
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
Definition legacy_boundary_raw x := Raw (boundary_journal x).

Lemma legacy_journal_trace_both j j' :
 logged_invariant sector 256 data_len valid j -> Raw j ->
 clos_refl_trans logged_state (logged_step g sector 256 data_len valid) j j' ->
 logged_invariant sector 256 data_len valid j' /\ Raw j'.
Proof. intros J R T; split; [eapply arbitrary_finite_history_preserves_invariant; eauto|].
 exact (logged_trace_preserves_raw g sector 256 data_len valid j j' G DIV J R T). Qed.

Lemma legacy_successful_return_raw id ready out slot pubs acks :
 logged_invariant sector 256 data_len valid ready -> Raw ready ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid id)
  ready (Logged (AwaitAck out slot id) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot id) pubs acks)
  (Logged (Ready out) pubs (id::acks)) ->
 Raw (Logged (Ready out) pubs (id::acks)).
Proof.
 intros J R T S. apply successful_trace_is_logged in T.
 destruct (legacy_journal_trace_both _ _ J R T) as [JA RA].
 exact (logged_step_preserves_raw g sector 256 data_len valid _ _ G DIV JA RA S).
Qed.

Lemma legacy_publication_raw old id image index entry span s prepared ready e event next :
 logged_invariant sector 256 data_len valid ready -> Raw ready ->
 publication_execution g sector data_len valid view marker ranges old id image index entry span s prepared ready e event next ->
 legacy_boundary_raw next.
Proof.
 intros J R RUN. destruct RUN; unfold legacy_boundary_raw,boundary_journal; simpl.
 - eapply legacy_successful_return_raw; eauto.
 - eapply legacy_successful_return_raw; eauto.
 - destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ H) as [_ [_ T]].
   exact (proj2 (legacy_journal_trace_both _ _ J R T)).
 - destruct H as [before [T [CONTROL [STEP DEST]]]].
   destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ T) as [_ [_ LOG]].
   destruct (legacy_journal_trace_both _ _ J R LOG) as [JB RB].
   exact (logged_step_preserves_raw g sector 256 data_len valid _ _ G DIV JB RB STEP).
 - change (Raw (Logged (Ready out) pubs (N.of_nat id::acks))). eapply legacy_successful_return_raw; eauto.
 - change (Raw (Logged (Ready out) pubs (N.of_nat id::acks))). eapply legacy_successful_return_raw; eauto.
 - change (Raw (Logged (Ready out) pubs (N.of_nat id::acks))). eapply legacy_successful_return_raw; eauto.
Qed.

Lemma legacy_reserved_raw bytes dw bw dp bp old id d index entry span s f h a e event next :
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 Safe ((Logged (Ready f) h a,IdleBoundary old d s),e) -> Raw (Logged (Ready f) h a) ->
 ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin s)) span ->
 erased_object_extent sector f span ->
 reserved_execution g sector data_len valid view marker ranges pages dw bw old id d index entry span s f h a e event next ->
 legacy_boundary_raw next.
Proof.
 intros W INITIAL RAW RANGE FREE ERASED RUN.
 pose proof (enriched_data_episode g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT
  bytes dw bw dp bp old id d index entry span s f h a e INITIAL RANGE FREE ERASED W) as POST.
 unfold data_episode_post in POST. destruct POST as [DRUN [KEEP CASE]].
 pose proof (proj1 (proj1 INITIAL)) as JI.
 pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 (proj1 JI)) DRUN) as DFRAME.
 pose proof (raw_frame_ready _ _ _ _ _ _ _ _ RAW DFRAME) as DRAW.
 pose proof (ready_object_write _ _ _ _ _ _ _ _ _ JI DFRAME) as DJ.
 destruct RUN; unfold legacy_boundary_raw,boundary_journal; simpl.
 - exact DRAW.
 - exact DRAW.
 - rewrite H in CASE; specialize (CASE H0 H1); destruct CASE as [BRUN REST].
   pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 DFRAME) BRUN) as BF.
   exact (raw_frame_ready _ _ _ _ _ _ _ _ DRAW BF).
 - rewrite H in CASE; specialize (CASE H0 H1); destruct CASE as [BRUN REST].
   pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 DFRAME) BRUN) as BF.
   exact (raw_frame_ready _ _ _ _ _ _ _ _ DRAW BF).
 - rewrite H in CASE; specialize (CASE H0 H1); destruct CASE as [BRUN REST].
   pose proof (writer_execution_locality _ _ _ _ _ _ _ (proj1 DFRAME) BRUN) as BF.
   eapply legacy_publication_raw; [exact (ready_object_write _ _ _ _ _ _ _ _ _ DJ BF)|
    exact (raw_frame_ready _ _ _ _ _ _ _ _ DRAW BF)|exact H3].
Qed.

Lemma legacy_boundary_raw_preserves bytes dw bw dp bp x event y :
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 Safe x -> legacy_boundary_raw x ->
 boundary_step g sector data_len valid view marker ranges decode topology pages dw bw x event y -> legacy_boundary_raw y.
Proof.
 intros W INITIAL RAW STEP. destruct STEP; try exact RAW.
 - eapply legacy_reserved_raw; eauto.
 - exact (logged_step_preserves_raw g sector 256 data_len valid _ _ G DIV (proj1 (proj1 INITIAL)) RAW H).
 - destruct (boot_finite_trace g sector data_len valid view marker ranges decode topology pages G DIV CONTRACT
    initial final (proj2 (proj1 INITIAL)) H) as [LAST PROJ].
   destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [_ [_ LOG]].
   exact (logged_trace_preserves_raw g sector 256 data_len valid _ _ G DIV (proj1 (proj1 INITIAL)) RAW LOG).
Qed.

End LegacyRawTransport.

Section CertifiedSuffix.
Variable g:geometry.
Variable sector:nat.
Variable data_len:N.
Variable valid:N->bool.
Variable view:nat->root_view.
Variable marker:extent.
Variable ranges:compact_entry->list extent.
Variable decode:flash->nat->option recovery_decoding.
Variable pages:nat.
Hypothesis G:journal_geometry g sector 256.
Hypothesis DIV:sector mod 8=0.

Lemma certified_append_evidence ready id d s e out slot pubs acks :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 logged_invariant sector 256 data_len valid (Logged (Ready out) pubs (N.of_nat id::acks)) /\
 persistent_evidence sector view ranges decode (Logged (Ready out) pubs (N.of_nat id::acks)) e /\
 hd_error pubs=Some (N.of_nat id).
Proof.
 intros [[JI CORE] [EV IN]] LOCAL TRACE ACK.
 pose proof (successful_trace_is_logged _ _ _ _ _ _ _ _ TRACE) as LOG.
 assert (MID:logged_invariant sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)).
 { eapply arbitrary_finite_history_preserves_invariant;eauto. }
 assert (HEAD:hd_error pubs=Some (N.of_nat id)) by (exact (proj2 (proj1 (proj2 MID)))).
 assert (FULL:clos_refl_trans logged_state (logged_step g sector 256 data_len valid) ready
   (Logged (Ready out) pubs (N.of_nat id::acks))) by (eapply rt_trans;[exact LOG|apply rt_step;exact ACK]).
 destruct (certified_journal_transport g sector data_len valid view ranges decode ready
   (Logged (Ready out) pubs (N.of_nat id::acks)) e (N.of_nat id) G DIV JI EV LOCAL
   (ex_intro _ (Certificate id d) (conj IN eq_refl)) FULL (or_intror HEAD)) as [J E].
 auto.
Qed.

(* Append success establishes the synchronized boundary before collection or
   delivery. In particular the current receipt list is unchanged. *)
Theorem certified_runtime_sync ready id d s e out slot pubs acks :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 In marker (protection_base s) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 let j:=Logged (Ready out) pubs (N.of_nat id::acks) in
 enriched_invariant sector data_len valid view marker ranges decode pages
   (j,PublishingBoundary DurableSynchronized id d
     (durable_ram_update marker (root_extents (view id)) (slot_publication (root_extents (view id)) s)))
   (synchronize_publication j (Certificate id d) e).
Proof.
 intros INV LOCAL MARK RUN ACK j.
 pose proof INV as [[JI [PI [F [P [FMT [COR [LINK DI]]]]]]] [EV IN]].
 destruct (certified_append_evidence ready id d s e out slot pubs acks INV LOCAL RUN ACK) as [J [E HEAD]].
 assert (CUR:protection_current s++attached_ranges s=root_extents (view id)).
 { unfold image_current_correspondence in COR;destruct FMT as [B OB];rewrite B OB in COR;exact COR. }
 apply enriched_durable_sync;[|exact MARK].
 split.
 - split;[exact J|]. split;[apply slot_publication_preserves;assumption|].
   split;[exact F|]. split;[exact P|]. split;[exact FMT|]. split.
   + unfold image_current_correspondence;cbn;rewrite CUR.
     destruct FMT as [B OB];rewrite B OB;reflexivity.
   + split.
     * unfold protection_history_link;cbn;rewrite HEAD;cbn;rewrite Nat2N.id;reflexivity.
     * split;[exact HEAD|reflexivity].
 - split;[exact E|exact IN].
Qed.

Theorem certified_client_return ready id d s e saved out slot pubs acks final :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 protection_saved s=[saved] -> In marker (protection_base s) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
   (client_finish_contract view marker id saved)
   (client_finish_program id (recovered_image d) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
   s (ClientReturned (DataClientSuccess id (recovered_image d))) final ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id d final)
   (observe_client (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id d)
     (evidence_with_live e [Certificate id d])).
Proof.
 intros INV LOCAL STACK MARK TRACE ACK POST.
 pose proof INV as [[JI [PI [F [P [FMT [COR [LINK DI]]]]]]] [EV IN]].
 destruct (certified_append_evidence ready id d s e out slot pubs acks INV LOCAL TRACE ACK) as [J [E HEAD]].
 assert (CUR:protection_current s++attached_ranges s=root_extents (view id)).
 { unfold image_current_correspondence in COR;destruct FMT as [B OB];rewrite B in COR;rewrite OB in COR;exact COR. }
 pose proof (client_success_only_after_close_collection view marker id (recovered_image d) saved s final _ POST) as [_ FINAL].
 subst final.
 assert (IDLE:journal_idle sector 256 data_len valid view marker id (finish_collected view marker id saved s)
   (Logged (Ready out) pubs (N.of_nat id::acks))).
 { apply idle_root_links_ready;[eapply finish_collected_idle;eauto|exact J|exact HEAD]. }
 eapply receipt_extension_wellformed;[|simpl;auto|exact HEAD].
 split.
 - split;[exact J|]. split;[apply idle_image;assumption|reflexivity].
 - split;[|unfold boundary_certificate_link;simpl;auto]. split.
   + constructor;[apply (proj1 (Forall_forall _ _) (proj1 E) (Certificate id d) IN)|constructor].
   + split;[|exact (proj2 (proj2 E))]. intros chosen H.
     change (hd_error pubs=Some (N.of_nat chosen)) in H.
     assert (chosen=id) by (apply Nat2N.inj;congruence);subst;simpl;eauto.
Qed.
Lemma certified_append_fatal ready id d s e out slot pubs acks :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Ready out) pubs (N.of_nat id::acks),FatalBoundary) e.
Proof.
 intros INV LOCAL TRACE ACK.
 destruct (certified_append_evidence ready id d s e out slot pubs acks INV LOCAL TRACE ACK) as [J [E HEAD]].
 split;[split;[exact J|exact I]|split;[exact E|exact I]].
Qed.
Lemma certified_append_cut ready id d s e out slot pubs acks :
 enriched_invariant sector data_len valid view marker ranges decode pages
   (ready,PublishingBoundary CandidatePrepared id d s) e ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 enriched_invariant sector data_len valid view marker ranges decode pages
   (Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting) e.
Proof.
 intros INV LOCAL TRACE ACK.
 eapply incarnation_reset_boundary with (phase:=FatalBoundary) (j:=Logged (Ready out) pubs (N.of_nat id::acks));[exact G|exact DIV| |].
 - exact (certified_append_fatal ready id d s e out slot pubs acks INV LOCAL TRACE ACK).
 - apply record_step;apply reset_ready.
Qed.
End CertifiedSuffix.

(* Read-only rollback services. The flash is an input observer of the unique
   journal, not another mutable store. Error/panic are terminal observations;
   an interrupted prefix never executes the remaining continuation. *)
Definition root_address (root:list extent) := option_map offset (hd_error root).
Inductive RestoreObservation := RestoreReadFailed | RestorePanicked | RestoreValidationFailed | RestoreValidated.
Inductive RestoreAPI : interface :=
| RestoreRead : RestoreAPI (option (list N))
| RestoreInspect : list N -> RestoreAPI bool
| RestoreValidate : list N -> RestoreAPI bool.
Definition restore_update (_:unit) A (_:RestoreAPI A) (_:A) := tt.
Definition restore_caller (_:unit) A (_:RestoreAPI A) := True.
Definition restore_callee (read:option (list N)) (inspect validate:list N->bool)
 (_:unit) A (op:RestoreAPI A) : A->Prop :=
 match op with RestoreRead => fun reply=>reply=read
 | RestoreInspect bytes=>fun reply=>reply=inspect bytes
 | RestoreValidate bytes=>fun reply=>reply=validate bytes end.
Definition restore_contract read inspect validate := make_contract restore_update restore_caller (restore_callee read inspect validate).
Definition restore_probe : impure RestoreAPI RestoreObservation :=
 request_then RestoreRead (fun reply=>match reply with
 | None=>local RestoreReadFailed
 | Some bytes=>request_then (RestoreInspect bytes) (fun ok=>if ok then
     request_then (RestoreValidate bytes) (fun valid=>local (if valid then RestoreValidated else RestoreValidationFailed))
     else local RestorePanicked) end).
Lemma restore_probe_outcome read inspect validate outcome :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
   (restore_contract read inspect validate) restore_probe) tt outcome tt ->
 outcome=match read with None=>RestoreReadFailed | Some bytes=>
   if inspect bytes then (if validate bytes then RestoreValidated else RestoreValidationFailed)
   else RestorePanicked end.
Proof.
 intro RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [reply [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst reply.
 destruct read as [bytes|];unroll_post REST.
 - destruct REST as [ok [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst ok.
   destruct (inspect bytes);unroll_post REST.
   + destruct REST as [ok [middle [[EQ STATE] REST]]];subst middle;cbn in EQ;subst ok.
     symmetry;exact (proj1 REST).
   + symmetry;exact (proj1 REST).
 - symmetry;exact (proj1 REST).
Qed.
Inductive RestoreCut := BeforeSnapshotRead | AfterSnapshotRead | BeforeImageCopy | DuringImageCopy.
Definition restore_cut_reached (read:option (list N)) (inspect validate:list N->bool) cut := match cut with
 | BeforeSnapshotRead=>True
 | AfterSnapshotRead=>exists bytes,read=Some bytes
 | BeforeImageCopy | DuringImageCopy=>exists bytes,read=Some bytes /\ inspect bytes=true /\ validate bytes=true
 end.

(* Local rejection services: providers decide numeric/format/read predicates,
   never a transaction invariant. No storage update is part of these checks. *)
Inductive external_check := CompareContents | ReadArea | PageGeometry | DataLength
 | BossLength | ScratchCapacity | GenerationCapacity | ReusableSearchExhausted
 | PreparedReference | EntryAddress | EntryFields.
Inductive CheckAPI : interface := RunCheck : external_check -> CheckAPI bool.
Definition check_update (_:unit) A (_:CheckAPI A) (_:A) := tt.
Definition check_caller (_:unit) A (_:CheckAPI A) := True.
Definition check_callee (provider:external_check->bool) (_:unit) A (op:CheckAPI A) : A->Prop :=
 match op with RunCheck which=>fun reply=>reply=provider which end.
Definition check_contract provider := make_contract check_update check_caller (check_callee provider).
Definition check_program which : impure CheckAPI bool := request_then (RunCheck which) (fun reply=>local reply).
Lemma check_program_result provider which reply :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
   (check_contract provider) (check_program which)) tt reply tt -> reply=provider which.
Proof.
 intro RUN;simpl in RUN;unroll_post RUN.
 destruct RUN as [r [u [[E U] REST]]];subst u;cbn in E;subst r.
 unroll_post REST;symmetry;exact (proj1 REST).
Qed.

(* Local post-write checks only; these contracts specify a response, never
   protection, rollback or absence of earlier physical effects. *)
Inductive prepared_local_rejection kind image key r : Prop :=
| missing_attachment_slot : data_slot_for kind image key=None ->
    prepared_local_rejection kind image key r
| rejected_prepared_reference (provider:extent->external_check->bool) :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
      (check_contract (provider r)) (check_program PreparedReference)) tt false tt ->
    prepared_local_rejection kind image key r
| rejected_entry_conversion index (provider:extent->external_check->bool) which :
    data_slot_for kind image key=Some index ->
    (which=EntryAddress \/ which=EntryFields) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
      (check_contract (provider r)) (check_program which)) tt false tt ->
    prepared_local_rejection kind image key r.

Section ArbitraryEpisodes.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8=0.
Local Notation Safe valid view := (boundary_safe sector data_len valid view marker ranges decode pages).

(* Same state update as forgetting a retained handle: no release, no writer,
   no dirty/current mutation. Its use here is a successful responsibility
   transfer to an entry already present, not a simulated writer error. *)
Definition identical_attach_state := snapshot_retain_error.
Lemma identical_attachment_safe valid view j image root s e :
 Safe valid view ((j,OperationBoundary image root s),e) ->
 Safe valid view ((j,OperationBoundary image root (identical_attach_state s)),e).
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]].
 split;[|split;[exact EV|exact I]]. split;[exact JI|].
 split;[apply snapshot_retain_error_preserves;exact DI|].
 split;[exact F|]. split;[exact COR|exact LINK].
Qed.

(* The token is detached from cleanup responsibility; its range remains
   owned in the single page table. Remember only updates authentication bits. *)
Definition rehome_cached lifetime s :=
 match pending_preparation s with
 | Some p => remember_recovered_boss pages (prep_range p) (snapshot_rehome lifetime s)
 | None => s
 end.
Lemma rehome_cached_safe valid view j image root s e p lifetime :
 Safe valid view ((j,OpenBoundary image root s),e) ->
 pending_preparation s=Some p -> lifetime<=length (protection_saved s) ->
 Safe valid view ((j,OpenBoundary image root (rehome_cached lifetime s)),e).
Proof.
 intros [[JI [DI [F [COR LINK]]]] [EV CERT]] P DEPTH.
 unfold rehome_cached;rewrite P.
 split;[|split;[exact EV|exact I]]. split;[exact JI|].
 split;[apply validation_update_preserves_data;
   eapply snapshot_rehome_preserves; eauto|].
 unfold snapshot_rehome;rewrite P.
 split;[exact F|]. split;[exact COR|exact LINK].
Qed.

Inductive episode_step : (N->bool) -> (nat->root_view) -> execution_boundary -> option client_receipt ->
                        (N->bool) -> (nat->root_view) -> execution_boundary -> Prop :=
| execute_services valid view bytes dw bw dp bp x event y :
    recovery_local_contracts view ranges decode ->
    outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
    boundary_step g sector data_len valid view marker ranges decode topology pages dw bw x event y ->
    episode_step valid view x event valid view y
| consume_pending valid view f h a old previous image root s e p boss plan result validate :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    incarnation_reader_local ranges decode (Certificate old previous) ->
    validator_accepts_decoded sector decode validate ->
    pending_writer_run g sector s p boss f plan result ->
    prep_kind p=(if boss then BossPreparation else ObjectPreparation) ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
      (validate (writer_flash result)) view
      (writer_exit_boundary old image root s h a result,phase_evidence (snd (writer_exit_boundary old image root s h a result)) (selected_evidence old previous e))
| consume_decoded valid view f h a old previous image root s e p plan result validate id fresh :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    contains (prep_range p) id -> contains (boss_extent (view old)) old ->
    (forall after, unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector after) ->
      decode (object_flash sector f) old=decode (object_flash sector after) old) ->
    validator_accepts_decoded sector decode validate ->
    pending_writer_run g sector s p true f plan result -> writer_end result=WriterComplete ->
    decode (object_flash sector (writer_flash result)) id=Some fresh ->
    recovered_boss fresh=prep_range p -> recovered_image fresh=image -> prep_kind p=BossPreparation ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
      (validate (writer_flash result)) (install_decoded_view view ranges id fresh)
      (writer_exit_boundary old image root s h a result,phase_evidence (snd (writer_exit_boundary old image root s h a result)) (evidence_with_live e [Certificate old previous;Certificate id fresh]))
| attach_pending valid view j image root s e p index entry :
    pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
    ranges entry=[prep_range p] ->
    episode_step valid view ((j,OpenBoundary image root s),e) None valid view
      ((j,OpenBoundary (image_replace image index (Some entry)) []
        (exact_attach ranges image index entry (data_next DataWritten s))),e)
| reset_episode valid view j phase e :
    logged_step g sector 256 data_len valid j (logged_after_reset j) ->
    episode_step valid view ((j,phase),e) None valid view ((logged_after_reset j,RebuildingBoundary Selecting),forget_volatile_evidence e)
| boot_episode valid view initial final e :
    (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages) initial final ->
    episode_step valid view ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) None valid view
      ((boot_journal final,RebuildingBoundary (boot_pc final)),forget_volatile_evidence e)
| resume_episode valid view j id d ram e :
    episode_step valid view ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence (e)) None valid view
      ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e))
| begin_episode valid view j id d ram e :
    episode_step valid view ((j,IdleBoundary id d ram),e) None valid view
      ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e)
| acquire_erased valid view f h a image root s e r boss :
    pending_preparation s=None -> erased_admission sector s f r ->
    mapped_erased_admission sector pages s f r ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,OpenBoundary image root (reservation_state boss r s)),advance_allocation_evidence r e)
| acquire_recycled valid view f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) -> incarnation_reader_local ranges decode (Certificate old previous) ->
    recognizer_local sector recognize -> validator_accepts_decoded sector decode validate -> pending_preparation s=None ->
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
    erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
      (validate (neutral_flash result)) view
      (recycling_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)) boss,phase_evidence (snd (recycling_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)) boss)) (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e)))
| cleanup_episode valid view j old candidate current ram e commands :
    data_calls commands ram ->
    episode_step valid view ((j,FrozenBoundary old candidate current ram),e) None valid view
      ((j,FrozenBoundary old candidate (opaque_frozen_root current commands) (execute_data commands ram)),e)
| install_prepared valid view j image s e p id d :
    pending_preparation s=Some p -> prep_kind p=BossPreparation -> prep_phase p=Written ->
    In (Certificate id d) (live_certificates e) ->
    recovered_boss d=prep_range p -> recovered_image d=image ->
    episode_step valid view ((j,OpenBoundary image [] s),e) None valid view
      ((j,PublishingBoundary CandidatePrepared id d (install_candidate s)),e)
| return_prepared valid view ready id d s e saved out slot pubs acks final :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    protection_saved s=[saved] -> In marker (protection_base s) ->
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id saved)
      (client_finish_program id (recovered_image d) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
      s (ClientReturned (DataClientSuccess id (recovered_image d))) final ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e)
      (Some (Receipt (pred (length pubs)) (Certificate id d))) valid view
      ((Logged (Ready out) pubs (N.of_nat id::acks),ClientBoundary id d final),
       observe_client (Logged (Ready out) pubs (N.of_nat id::acks)) (Certificate id d)
         (evidence_with_live e [Certificate id d]))
| fail_prepared valid view ready id d s e old error_j commands :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    hd_error (publications ready)=Some old ->
    clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len valid (N.of_nat id)) ready error_j ->
    returned_error_control (journal_control error_j) ->
    data_calls commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s) ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) None valid view
      ((error_j,FrozenBoundary old (N.of_nat id) (opaque_frozen_root (Some [recovered_boss d]) commands)
        (execute_data commands (uncertain_return (optional_root view (option_map N.to_nat (hd_error (publications error_j)))) s))),e)
| stop_prepared valid view ready id d s e saved out slot pubs acks final :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    protection_saved s=[saved] -> In marker (protection_base s) ->
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id saved)
      (client_finish_program id (recovered_image d) [SlotCompleted;DurableRamWritten;ExternalAccepted]))
      s ClientStopped final ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) None valid view
      ((Logged (Ready out) pubs (N.of_nat id::acks),FatalBoundary),forget_volatile_evidence (e))
| cut_prepared valid view ready id d s e cut :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    publication_reset_prefix g sector data_len valid (N.of_nat id) ready cut ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) None valid view
      ((cut,RebuildingBoundary Selecting),forget_volatile_evidence (e))
| cut_exit_prepared valid view ready id d s e saved out slot pubs acks phases suffix partial :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    protection_saved s=[saved] -> In marker (protection_base s) ->
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    phases++suffix=[SlotCompleted;DurableRamWritten;ExternalAccepted] ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
      (exit_contract marker (root_extents (view id)) saved) (exit_program phases)) s tt partial ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) None valid view
      ((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence (e))
| cut_collection_prepared valid view ready id d s e saved out slot pubs acks closed resolved partial :
    (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
    protection_saved s=[saved] -> In marker (protection_base s) ->
    clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
      ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
    logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
      (Logged (Ready out) pubs (N.of_nat id::acks)) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PublicationExitAPI)
      (exit_contract marker (root_extents (view id)) saved)
      (exit_program [SlotCompleted;DurableRamWritten;ExternalAccepted])) s tt closed ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ClientFinishAPI)
      (client_finish_contract view marker id saved) collection_service_prefix) closed resolved partial ->
    episode_step valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) None valid view
      ((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence (e))
| resume_client_episode valid view j id d s e :
    episode_step valid view ((j,ClientBoundary id d s),e) None valid view ((j,IdleBoundary id d s),e)

| drop_unattached_episode valid view j image root s e p :
    pending_preparation s=Some p ->
    episode_step valid view ((j,OpenBoundary image root s),e) None valid view
      ((j,OpenBoundary image root (data_next DataDrop s)),e)
| rollback_external_episode valid view f h a image root s e old d resolved :
    rollback_structure marker s -> pending_preparation s=None ->
    hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
    (forall mask,resolved=Some mask ->
      mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (normal_external_rollback s)))) (e))

| rollback_prepared_episode valid view f h a id candidate s e old previous resolved :
    rollback_structure marker s -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    episode_step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) None valid view
      ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)))) (e))

| reject_data_arity valid view j id d s e count :
    count=0 \/ 2<count ->
    episode_step valid view ((j,IdleBoundary id d s),e) None valid view ((j,IdleBoundary id d s),e)

| restore_failed_episode valid view f h a image root s e old read inspect validate outcome :
    pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
    rollback_structure marker s -> root<>[boss_extent (view old)] ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract (read (object_flash sector f) old) inspect validate) restore_probe) tt outcome tt ->
    (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed) ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))

| restore_cut_episode valid view f h a image root s e old read inspect validate cut :
    pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
    rollback_structure marker s -> root<>[boss_extent (view old)] ->
    restore_cut_reached (read (object_flash sector f) old) inspect validate cut ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e))
| restore_panic_episode valid view f h a image root s e old (read:flash->nat->option (list N)) (diagnostics:list N->bool) bytes :
    pending_preparation s=None -> hd_error h=Some (N.of_nat old) ->
    rollback_structure marker s -> root<>[boss_extent (view old)] ->
    read (object_flash sector f) old=Some bytes -> diagnostics bytes=false ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))

| cut_recycled_before_reserve valid view f h a old previous image root s e recognize magic fuel req round alignment start r count result validate :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) -> incarnation_reader_local ranges decode (Certificate old previous) ->
    recognizer_local sector recognize -> validator_accepts_decoded sector decode validate -> pending_preparation s=None ->
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
    erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
    neutral_end_ result=NeutralSuccess ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
      (validate (neutral_flash result)) view
      ((Logged (Boot (neutral_flash result)) h a,RebuildingBoundary Selecting),forget_volatile_evidence (selected_evidence old previous e))

| restore_prepared_failed_episode valid view f h a id candidate s e old read inspect validate outcome :
    rollback_structure marker s -> hd_error h=Some (N.of_nat old) -> id<>old ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract (read (object_flash sector f) old) inspect validate) restore_probe) tt outcome tt ->
    (outcome=RestoreReadFailed \/ outcome=RestoreValidationFailed \/ outcome=RestorePanicked) ->
    episode_step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) None valid view
      ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence (e))
| restore_prepared_cut_episode valid view f h a id candidate s e old read inspect validate cut :
    rollback_structure marker s -> hd_error h=Some (N.of_nat old) -> id<>old ->
    restore_cut_reached (read (object_flash sector f) old) inspect validate cut ->
    episode_step valid view ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared id candidate s),e) None valid view
      ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence (e))

| entry_check_rejected valid view j id d s e provider :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
      (check_contract provider) (check_program CompareContents)) tt false tt ->
    episode_step valid view ((j,IdleBoundary id d s),e) None valid view ((j,IdleBoundary id d s),e)
| admission_check_rejected valid view f h a image root s e old previous provider which resolved :
    which<>CompareContents ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CheckAPI)
      (check_contract provider) (check_program which)) tt false tt ->
    pending_preparation s=None -> rollback_structure marker s -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old previous resolved (normal_external_rollback s)))) (e))
| drop_checked_failure valid view j image root s e p initialized word_max err :
    pending_preparation s=Some p -> protection_frozen s=false ->
    range_check initialized word_max (prep_range p)=Some err ->
    episode_step valid view ((j,OpenBoundary image root s),e) None valid view ((j,FatalBoundary),forget_volatile_evidence (e))
| writer_drop_checked_failure valid view f h a old previous image root s e p plan result validate initialized word_max err :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    incarnation_reader_local ranges decode (Certificate old previous) -> validator_accepts_decoded sector decode validate ->
    pending_writer_run g sector s p false f plan result -> prep_kind p=ObjectPreparation ->
    writer_end result=WriterLocalError -> range_check initialized word_max (prep_range p)=Some err ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) None
      (validate (writer_flash result)) view
      ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))

| outer_pair_accepted valid view f h a old d s e ia ib ea eb ra rb pa pb wa wb validate same eq_a eq_b :
    raw_order sector 256 data_len (Logged (Ready f) h a) ->
    incarnation_reader_local ranges decode (Certificate old d) -> validator_accepts_decoded sector decode validate ->
    changed_pair same eq_a eq_b=[0;1] ->
    erased_admission sector (outer_local_begin s) f ra ->
    writer_execution g sector ra false f pa wa -> writer_end wa=WriterComplete -> ranges ea=[ra] ->
    erased_admission sector (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) (writer_flash wa) rb ->
    writer_execution g sector rb false (writer_flash wa) pb wb -> writer_end wb=WriterComplete -> ranges eb=[rb] ->
    runtime_erased_admission sector pages e (outer_local_begin s) f ra ->
    runtime_erased_admission sector pages (advance_allocation_evidence ra e)
      (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) (writer_flash wa) rb ->
    episode_step valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) None
      (validate (writer_flash wb)) view
      ((Logged (Ready (writer_flash wb)) h a,
        OpenBoundary (image_replace (image_replace (recovered_image d) ia (Some ea)) ib (Some eb)) []
          (pair_accept ranges (recovered_image d) ia ib ea eb ra rb s)),selected_evidence old d (advance_allocation_evidence rb (advance_allocation_evidence ra e)))
| unchanged_pair_episode valid view j old d s e same eq_a eq_b :
    changed_pair same eq_a eq_b=[] ->
    episode_step valid view ((j,IdleBoundary old d s),e) None valid view ((j,IdleBoundary old d s),e)

| operation_first_episode valid view f h a old d s e index entry r plan result validate :
    raw_order sector 256 data_len (Logged (Ready f) h a) ->
    incarnation_reader_local ranges decode (Certificate old d) -> validator_accepts_decoded sector decode validate ->
    erased_admission sector (outer_local_begin s) f r ->
    writer_execution g sector r false f plan result -> writer_end result=WriterComplete -> ranges entry=[r] ->
    runtime_erased_admission sector pages e (outer_local_begin s) f r ->
    episode_step valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) None
      (validate (writer_flash result)) view
      ((Logged (Ready (writer_flash result)) h a,OperationBoundary
        (image_replace (recovered_image d) index (Some entry)) []
        (exact_member ranges (recovered_image d) index entry r (outer_local_begin s))),selected_evidence old d (advance_allocation_evidence r e))
| operation_reserve_episode valid view j image root s e r :
    pending_preparation s=None ->
    erased_admission sector s (control_image (journal_control j)) r ->
    mapped_erased_admission sector pages s (control_image (journal_control j)) r ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OperationBoundary image root (reservation_state false r s)),advance_allocation_evidence r e)
| operation_writer_episode valid view f h a old previous image root s e p plan result validate :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    incarnation_reader_local ranges decode (Certificate old previous) -> validator_accepts_decoded sector decode validate ->
    pending_writer_run g sector s p false f plan result -> prep_kind p=ObjectPreparation ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None
      (validate (writer_flash result)) view
      (operation_writer_exit old image root s h a result,phase_evidence (snd (operation_writer_exit old image root s h a result)) (selected_evidence old previous e))
| operation_cancel_episode valid view f h a image root s e old d read inspect validate :
    operation_rollback_structure marker s -> pending_preparation s=None ->
    hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect validate) restore_probe) tt RestoreValidated tt ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),e)
| operation_restore_fatal valid view j image root s e read inspect validate outcome :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect validate) restore_probe) tt outcome tt -> outcome<>RestoreValidated ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view ((j,FatalBoundary),forget_volatile_evidence (e))

| frozen_scope_close valid view j old candidate current s e views saved read inspect check :
    data_caller (DataClose views saved false) s ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect check) restore_probe) tt RestoreValidated tt ->
    episode_step valid view ((j,FrozenBoundary old candidate current s),e) None valid view
      ((j,FrozenBoundary old candidate None (data_next (DataClose views saved false) s)),e)
| frozen_scope_stop valid view j old candidate current s e read inspect check outcome :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
      (restore_contract read inspect check) restore_probe) tt outcome tt -> outcome<>RestoreValidated ->
    episode_step valid view ((j,FrozenBoundary old candidate current s),e) None valid view ((j,FatalBoundary),forget_volatile_evidence (e))

| operation_drop_checked_failure valid view f h a old previous image root s e p plan result validate initialized word_max err :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    incarnation_reader_local ranges decode (Certificate old previous) -> validator_accepts_decoded sector decode validate ->
    pending_writer_run g sector s p false f plan result -> prep_kind p=ObjectPreparation ->
    writer_end result=WriterLocalError -> range_check initialized word_max (prep_range p)=Some err ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None
      (validate (writer_flash result)) view
      ((Logged (Ready (writer_flash result)) h a,FatalBoundary),forget_volatile_evidence (selected_evidence old previous e))

| operation_acquire_recycled valid view f h a old previous image root s e recognize magic fuel req round alignment start r count result validate :
    raw_order sector 256 data_len (Logged (Ready f) h a) -> hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) -> incarnation_reader_local ranges decode (Certificate old previous) ->
    recognizer_local sector recognize -> validator_accepts_decoded sector decode validate -> pending_preparation s=None ->
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundRecyclable r ->
    erase_geometry g sector r count -> recycling_run g sector recognize magic r count f result ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None
      (validate (neutral_flash result)) view
      (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)),phase_evidence (snd (operation_acquisition_boundary old image root s h a result (block_pages (recycle_lo r) (useful_pages r)))) (selected_evidence old previous (recycling_cursor_evidence result (block_pages (recycle_lo r) (useful_pages r)) e)))
| operation_begin_episode valid view j old d s e :
    episode_step valid view ((j,IdleBoundary old d s),e) None valid view
      ((j,OperationBoundary (recovered_image d) [recovered_boss d] (outer_local_begin s)),e)
| operation_attach_episode valid view j image root s e p index entry :
    pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
    ranges entry=[prep_range p] ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OperationBoundary (image_replace image index (Some entry)) []
        (exact_attach ranges image index entry (data_next DataWritten s))),e)
| operation_accept_episode valid view j image root s e :
    operation_rollback_structure marker s -> pending_preparation s=None ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OpenBoundary image root
        (data_next (DataClose [physical_authority s] (physical_authority s) true) s)),e)

| operation_clean_cancel_episode valid view f h a image root s e old d :
    operation_rollback_structure marker s -> pending_preparation s=None ->
    hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
    image=recovered_image d -> root=[recovered_boss d] ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] (operation_cancel s)),e)

| controller_episode valid view j phase e action :
    controller_caller action phase (controller_read e) ->
    episode_step valid view ((j,phase),e) None valid view
      ((j,phase),controller_evidence action phase e)
| clean_retained_episode valid view f h a old d s e resolved :
    rollback_structure marker s -> pending_preparation s=None ->
    hd_error h=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
    finish_selected (controller_read e)=Some FinishClean ->
    (forall mask,resolved=Some mask -> mask=collect_ranges view marker (Some old) (object_extents (view old)) []) ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d] s),e) None valid view
      ((Logged (Ready f) h a,failure_phase old d resolved (clean_external_close s)),phase_evidence (snd ((Logged (Ready f) h a,failure_phase old d resolved (clean_external_close s)))) (e))

| operation_prepared_rejected valid view j image root s e p kind key :
    pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
    prepared_local_rejection kind image key (prep_range p) ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OperationBoundary image root s),body_error_evidence e)
| operation_rejected_token_drop valid view j image root s e p :
    pending_preparation s=Some p -> body_error_pending (controller_read e)=true ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OperationBoundary image root (data_next DataDrop s)),e)

(* Observe the returned error of the very writer whose reached flash/state is
   this boundary. This is not a phase-only inference and executes no command. *)
| operation_writer_error_observed valid view old image root s e p f h a plan result :
    pending_preparation s=Some p ->
    writer_execution g sector (prep_range p) false f plan result ->
    (writer_end result=WriterLocalError \/ writer_end result=WriterRetainError \/ writer_end result=WriterPhysicalError) ->
    (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
     outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
    episode_step valid view (operation_writer_exit old image root s h a result,e) None valid view
      (operation_writer_exit old image root s h a result,
       phase_evidence (snd (operation_writer_exit old image root s h a result)) (body_error_evidence e))

| frozen_body_scope valid view j old candidate current s e views id read inspect check :
    data_caller (DataClose views (root_extents (view id)) false) s ->
    (root_address current=root_address [boss_extent (view id)] \/
     (root_address current<>root_address [boss_extent (view id)] /\
      post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RestoreAPI)
       (restore_contract read inspect check) restore_probe) tt RestoreValidated tt)) ->
    episode_step valid view ((j,FrozenBoundary old candidate (Some current) s),e) None valid view
      ((j,FrozenBoundary old candidate (Some [boss_extent (view id)])
         (data_next (DataClose views (root_extents (view id)) false) s)),e)


(* Return from the executed acquisition, before any token/writer exists. *)
| operation_acquisition_error_observed valid view old image root s e f h a
    recognize magic r count result :
    pending_preparation s=None ->
    recycling_run g sector recognize magic r count f result ->
    neutral_end_ result=NeutralError ->
    (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
     outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
    episode_step valid view
      (operation_acquisition_boundary old image root s h a result
        (block_pages (recycle_lo r) (useful_pages r)),e) None valid view
      (operation_acquisition_boundary old image root s h a result
        (block_pages (recycle_lo r) (useful_pages r)),body_error_evidence e)
| operation_search_rejected valid view f h a image root s e fuel recognize req round alignment start reply :
    pending_preparation s=None ->
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=reply ->
    (reply=SearchMiss \/ reply=SearchError) ->
    (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
     outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)


| operation_numeric_rejected valid view f h a image root s e :
    pending_preparation s=None ->
    operation_payload_rejection sector f h a image root s e ->
    (body_error_pending (controller_read e)=false /\ local_live (controller_read e)=true /\
     outer_live (controller_read e)=true /\ finish_selected (controller_read e)=None) ->
    episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
      ((Logged (Ready f) h a,OperationBoundary image root s),body_error_evidence e)
| before_change_checked valid view j image root ram e :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
      controller_contract before_change_probe)
      ((j,OperationBoundary image root ram),e) false ((j,OperationBoundary image root ram),e) ->
    episode_step valid view ((j,OperationBoundary image root ram),e) None valid view
      ((j,OperationBoundary image root ram),e)
| acquisition_search_interrupted valid view f h a image root s e fuel shape verify req round alignment start target fatal phase :
    (phase=OperationBoundary image root s \/ phase=OpenBoundary image root s) ->
    pending_preparation s=None ->
    reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
      f (protection_table s) req round alignment pages start target ->
    recognition_interruption shape verify f target fatal ->
    episode_step valid view ((Logged (Ready f) h a,phase),e) None valid view
      (if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
       else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e))

| operation_identical_attachment valid view j image root s e p index entry :
    pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
    ranges entry=[prep_range p] -> nth_error image index=Some (Some entry) ->
    episode_step valid view ((j,OperationBoundary image root s),e) None valid view
      ((j,OperationBoundary image root (identical_attach_state s)),e)

| prepared_rehome_cache valid view j image root s e p lifetime :
    pending_preparation s=Some p -> prep_kind p=BossPreparation ->
    prep_phase p=Written -> lifetime<=length (protection_saved s) ->
    episode_step valid view ((j,OpenBoundary image root s),e) None valid view
      ((j,OpenBoundary image root (rehome_cached lifetime s)),e)
| prepared_image_setter valid view f h a image s e p counter next decoded encoded :
    pending_preparation s=Some p -> prep_kind p=BossPreparation -> prep_phase p=Detached ->
    volatile_counter e=Some counter ->
    boss_checked_generation (counter_value counter)=Some next ->
    counter_decoder e f (offset (prep_range p))=Some (decoded,encoded) ->
    recovered_boss decoded=prep_range p -> recovered_image decoded=image ->
    counter_value encoded=next ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None valid view
      ((Logged (Ready f) h a,OpenBoundary image [] (image_generation_set next s)),e)
| install_detached_address valid view f h a image s e p old previous fresh base checked raw :
    hd_error h=Some (N.of_nat old) ->
    In (Certificate old previous) (live_certificates e) ->
    decoding_address_contract decode ->
    pending_preparation s=Some p -> prep_kind p=BossPreparation -> prep_phase p=Detached ->
    decode (object_flash sector f) (offset (prep_range p))=Some fresh ->
    recovered_boss fresh=prep_range p -> recovered_image fresh=image ->
    rust_absolute_address checked base (offset (prep_range p))=Some (Some raw) ->
    raw=(base+N.of_nat (offset (prep_range p)))%N ->
    episode_step valid view ((Logged (Ready f) h a,OpenBoundary image [] s),e) None valid
      (install_decoded_view view ranges (offset (prep_range p)) fresh)
      ((Logged (Ready f) h a,PublishingBoundary CandidatePrepared (offset (prep_range p)) fresh
         (install_candidate_observed s)),
        evidence_with_live e [Certificate old previous;Certificate (offset (prep_range p)) fresh])

.

(* Consume the executed SnapshotAPI program, rather than a destination
   safety certificate. The resulting token is Detached, never re-labelled. *)
Lemma prepared_rehome_cache_post valid view j image root s e p lifetime cached :
 pending_preparation s=Some p -> prep_kind p=BossPreparation ->
 prep_phase p=Written -> lifetime<=length (protection_saved s) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure SnapshotAPI)
   snapshot_contract (snapshot_program [SnapshotRehome lifetime;SnapshotRemember pages]))
   s tt cached ->
 episode_step valid view ((j,OpenBoundary image root s),e) None valid view
   ((j,OpenBoundary image root cached),e).
Proof.
 intros P KIND PHASE DEPTH RUN;apply snapshot_program_post in RUN;subst cached.
 replace (snapshot_execute [SnapshotRehome lifetime;SnapshotRemember pages] s)
   with (rehome_cached lifetime s).
 - eapply prepared_rehome_cache;eauto.
 - unfold rehome_cached;rewrite P.
   cbn [snapshot_execute snapshot_api_update];unfold snapshot_rehome;rewrite P;reflexivity.
Qed.

(* Both callers execute the same read-only search. Keep the old producer
   as a compatibility lemma; the existing episode relation is generalized. *)
Lemma operation_search_interrupted valid view f h a image root s e fuel shape verify req round alignment start target fatal :
 pending_preparation s=None ->
 reusable_call_prefix sector fuel (header_returned shape verify) (header_reply shape verify)
   f (protection_table s) req round alignment pages start target ->
 recognition_interruption shape verify f target fatal ->
 episode_step valid view ((Logged (Ready f) h a,OperationBoundary image root s),e) None valid view
   (if fatal then ((Logged (Ready f) h a,FatalBoundary),forget_volatile_evidence e)
    else ((Logged (Boot f) h a,RebuildingBoundary Selecting),forget_volatile_evidence e)).
Proof. intros; eapply acquisition_search_interrupted; eauto. Qed.

(* Compatibility producer: the old slot rejection is still an actual branch. *)
Lemma operation_attach_rejected valid view j image root s e p kind key :
 pending_preparation s=Some p -> prep_kind p=ObjectPreparation -> prep_phase p=Written ->
 data_slot_for kind image key=None ->
 episode_step valid view ((j,OperationBoundary image root s),e) None valid view
   ((j,OperationBoundary image root s),body_error_evidence e).
Proof.
 intros P KIND WRITTEN SLOT;eapply operation_prepared_rejected;try eassumption.
 apply missing_attachment_slot;exact SLOT.
Qed.

Lemma episode_step_control vi oi x event vf of_ y :
 episode_step vi oi x event vf of_ y -> terminal_control_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity;
 try apply phase_evidence_terminal;try apply phase_evidence_boundary.
 - eapply boundary_step_control;exact H1.
 - destruct phase;try exact I;destruct action;simpl in H;try solve [tauto];reflexivity.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite H1;exact I.
 - destruct fatal;reflexivity.
Qed.

Lemma episode_step_roots vi oi x event vf of_ y :
 episode_step vi oi x event vf of_ y -> terminal_roots_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity;
 try apply phase_evidence_roots;try apply phase_evidence_boundary_roots.
 - eapply boundary_step_roots;exact H1.
 - destruct phase;try exact I;destruct action;simpl in H;try solve [tauto];reflexivity.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite H1;exact I.
 - destruct fatal;reflexivity.
Qed.

Lemma episode_step_allocation vi oi x event vf of_ y :
 episode_step vi oi x event vf of_ y -> terminal_allocation_absent y.
Proof.
 intro RUN;destruct RUN;try exact I;try reflexivity;
 try apply phase_evidence_allocation;try apply phase_evidence_boundary_allocation.
 - eapply boundary_step_allocation;exact H1.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;rewrite H1;exact I.
 - destruct fatal;reflexivity.
Qed.

Inductive episode_trace : (N->bool) -> (nat->root_view) -> execution_boundary -> list client_receipt ->
                         (N->bool) -> (nat->root_view) -> execution_boundary -> Prop :=
| episodes_nil valid view x : episode_trace valid view x [] valid view x
| episodes_cons vi oi x event vm om y events vf of_ z :
    episode_step vi oi x event vm om y -> episode_trace vm om y events vf of_ z ->
    episode_trace vi oi x (events++emitted_receipts event) vf of_ z.

Theorem episode_trace_roots vi oi initial events vf of_ final :
 terminal_roots_absent initial ->
 episode_trace vi oi initial events vf of_ final -> terminal_roots_absent final.
Proof.
 intros INIT RUN;induction RUN;[exact INIT|].
 apply IHRUN;eapply episode_step_roots;eauto.
Qed.

Theorem episode_trace_allocation_reset vi oi initial events vf of_ final :
 terminal_allocation_absent initial ->
 episode_trace vi oi initial events vf of_ final -> terminal_allocation_absent final.
Proof.
 intros INIT RUN;induction RUN;[exact INIT|].
 apply IHRUN;eapply episode_step_allocation;eauto.
Qed.

(* Marked prefixes of episode_trace. The silent constructor cannot cross a
   delivery or an interruption, and there is no constructor after [operation_end].
   Cleanup may disarm the owner, but after that point only a terminal delivery
   or interruption is allowed; a new operation cannot extend this finalization.
   This stores no second state, flash, table, or history. *)
Inductive operation_execution : (N->bool) -> (nat->root_view) -> execution_boundary ->
 list client_receipt -> (N->bool) -> (nat->root_view) -> execution_boundary -> operation_exit -> Prop :=
| operation_end vi oi x event vf of_ y exit :
    episode_step vi oi x event vf of_ y -> edge_exit x event y=Some exit ->
    operation_execution vi oi x (emitted_receipts event) vf of_ y exit
| operation_internal vi oi x event vm om y events vf of_ z exit :
    episode_step vi oi x event vm om y -> edge_exit x event y=None ->
    owner_armed (controller_read (snd x))=true ->
    operation_execution vm om y events vf of_ z exit ->
    operation_execution vi oi x (events++emitted_receipts event) vf of_ z exit
| operation_already_fatal valid view j e : volatile_control e=None ->
    operation_execution valid view ((j,FatalBoundary),e) [] valid view ((j,FatalBoundary),e) InterruptedFatal
| operation_already_reset valid view j pc e : volatile_control e=None ->
    operation_execution valid view ((j,RebuildingBoundary pc),e) [] valid view ((j,RebuildingBoundary pc),e) InterruptedReset
| operation_entry_return valid view j id d ram e count same compare result success :
    outer_live (controller_read e)=false -> owner_armed (controller_read e)=false ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure PairPrepassAPI)
      (pair_prepass_contract count compare) (pair_prepass_program count same)) tt result tt ->
    pair_prepass_return result=Some success ->
    operation_execution valid view ((j,IdleBoundary id d ram),e) [] valid view
      ((j,IdleBoundary id d ram),e) (ReturnedEntry success).

Lemma episode_receipt_owner_closed vi oi x event vf of_ y :
 episode_step vi oi x event vf of_ y ->
 forall receipt,event=Some receipt -> delivered_owner_closed (snd y).
Proof.
 intros RUN receipt EQ;destruct RUN;try discriminate.
 - eapply boundary_receipt_owner_closed;eauto.
 - apply published_owner_closed.
Qed.
Lemma ordinary_edge_owner_closed x event y exit :
 edge_exit x event y=Some exit ->
 (match exit with ReturnedOrdinary _ | ReturnedBodyError=>True | _=>False end) ->
 delivered_owner_closed (snd y).
Proof.
 intros EDGE RETURN;destruct event;[inversion EDGE;subst;contradiction|].
 unfold edge_exit in EDGE;destruct (snd (fst y));try (inversion EDGE;subst;contradiction).
 all: destruct (finish_selected (controller_read (snd x)));
      destruct (finish_selected (controller_read (snd y)));try discriminate;
      repeat match type of EDGE with context[if ?b then _ else _]=>destruct b eqn:? end;
      try discriminate;split;assumption.
Qed.
Theorem operation_execution_owner_closed vi oi x events vf of_ y exit :
 operation_execution vi oi x events vf of_ y exit ->
 exit_observation exit<>None -> delivered_owner_closed (snd y).
Proof.
 intros RUN;induction RUN;intro RETURN.
 - destruct exit;try (cbn in RETURN;contradiction).
   + eapply episode_receipt_owner_closed;[exact H|].
     destruct event;[inversion H0;reflexivity|].
     unfold edge_exit in H0;destruct (snd (fst y));try discriminate;
       destruct (finish_selected (controller_read (snd x)));
       destruct (finish_selected (controller_read (snd y)));try discriminate;
       repeat match type of H0 with context[if ?b then _ else _]=>destruct b end;discriminate.
   + eapply ordinary_edge_owner_closed;[exact H0|exact I].
   + destruct event;unfold edge_exit in H0;try discriminate;
       destruct (snd (fst y));try discriminate;
       destruct (finish_selected (controller_read (snd x)));
       destruct (finish_selected (controller_read (snd y)));try discriminate;
       repeat match type of H0 with context[if ?b then _ else _]=>destruct b end;discriminate.
   + eapply ordinary_edge_owner_closed;[exact H0|exact I].
 - exact (IHRUN RETURN).
 - contradiction.
 - contradiction.
 - split;assumption.
Qed.

Lemma operation_execution_trace vi oi x events vf of_ y exit :
 operation_execution vi oi x events vf of_ y exit ->
 episode_trace vi oi x events vf of_ y.
Proof.
 intro RUN;induction RUN.
 - change (episode_trace vi oi x ([]++emitted_receipts event) vf of_ y).
   eapply episodes_cons;[exact H|constructor].
 - eapply episodes_cons;eauto.
 - constructor.
 - constructor.
 - constructor.
Qed.
Lemma silent_edge_no_receipt x event y : edge_exit x event y=None -> event=None.
Proof. destruct event;[discriminate|reflexivity]. Qed.
Lemma operation_execution_receipts vi oi x events vf of_ y exit :
 operation_execution vi oi x events vf of_ y exit ->
 events=match exit with ReturnedPublished r=>[r]|_=>[] end.
Proof.
 intro RUN;induction RUN.
 - destruct event as [r|].
   + inversion H0;reflexivity.
   + unfold edge_exit in H0;destruct (snd (fst y));
     try (destruct (finish_selected (controller_read (snd x))));
     try (destruct (finish_selected (controller_read (snd y))));
     try (destruct (body_error_pending (controller_read (snd x))));
     try (destruct (body_error_pending (controller_read (snd y))));
     try (destruct (owner_armed (controller_read (snd x))));
     try (destruct (owner_armed (controller_read (snd y))));
     try (destruct (outer_live (controller_read (snd y))));inversion H0;reflexivity.
 - apply silent_edge_no_receipt in H0;subst event;cbn;rewrite app_nil_r;exact IHRUN.

 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.

(* Chronological observations of marked operations, independently of the
   reverse-chronological durable receipts. Extending the execution only appends
   observations; no subsequent phase is queried to reclassify an old return. *)
Definition append_operation_observation history exit :=
 match exit_observation exit with Some result=>history++[result]|None=>history end.
Lemma delivered_observation_survives history exit result :
 exit_observation exit=Some result ->
 append_operation_observation history exit=history++[result].
Proof. intro EQ;unfold append_operation_observation;rewrite EQ;reflexivity. Qed.
Lemma owner_return_cannot_be_silent (x y:execution_boundary) :
 owner_armed (controller_read (snd x))=true ->
 owner_armed (controller_read (snd y))=false ->
 ~ (owner_armed (controller_read (snd y))=owner_armed (controller_read (snd x))).
Proof. intros BEFORE AFTER EQ;congruence. Qed.
Lemma operation_execution_one_receipt vi oi x events vf of_ y exit :
 operation_execution vi oi x events vf of_ y exit -> length events<=1.
Proof.
 intro RUN;rewrite (operation_execution_receipts _ _ _ _ _ _ _ _ RUN).
 destruct exit;cbn;lia.
Qed.
Lemma reset_has_no_observation history :
 append_operation_observation history InterruptedReset=history.
Proof. reflexivity. Qed.

Lemma episode_step_pages vi oi x event vf of_ y :
 page_metadata_coherent x -> episode_step vi oi x event vf of_ y ->
 page_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;
 try (eapply boundary_step_pages;[exact M|eassumption]);
 try (apply boundary_page_metadata;exact M);
 try (apply phase_page_metadata;exact M);
 cbn in M |- *;try assumption;try reflexivity.
 all: try (unfold operation_writer_exit;apply boundary_page_metadata;exact M).
 all: try (unfold operation_acquisition_boundary;apply boundary_page_metadata;exact M).
 all: try (destruct fatal;reflexivity).
 all: try (destruct phase;exact M).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);cbn in M |- *;assumption || reflexivity.
Qed.
Theorem episode_trace_pages vi oi initial events vf of_ final :
 page_metadata_coherent initial -> episode_trace vi oi initial events vf of_ final ->
 page_metadata_coherent final.
Proof.
 intros M TRACE;induction TRACE;[exact M|].
 apply IHTRACE. eapply episode_step_pages;eassumption.
Qed.

Lemma episode_step_runtime vi oi x event vf of_ y :
 runtime_metadata_coherent x -> episode_step vi oi x event vf of_ y ->
 runtime_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;
 try (eapply boundary_step_runtime;[exact M|eassumption]);
 try (apply boundary_runtime_metadata;exact M);
 try (apply phase_runtime_metadata;exact M);
 cbn in M |- *;try assumption;try reflexivity.
 all: try (unfold operation_writer_exit;apply boundary_runtime_metadata;exact M).
 all: try (unfold operation_acquisition_boundary;apply boundary_runtime_metadata;exact M).
 all: try (destruct fatal;reflexivity).
 all: try (destruct phase;exact M).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);cbn in M |- *;assumption || reflexivity.
Qed.
Theorem episode_trace_runtime vi oi initial events vf of_ final :
 runtime_metadata_coherent initial -> episode_trace vi oi initial events vf of_ final ->
 runtime_metadata_coherent final.
Proof.
 intros M TRACE;induction TRACE;[exact M|].
 apply IHTRACE. eapply episode_step_runtime;eassumption.
Qed.

(* The reset entry has no runtime observation. Usable exports a fresh one
   justified by the actual boot_runtime edge, not by pre-reset evidence. *)
Theorem boot_runtime_handoff valid view initial j id d ram e :
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (initial,Selecting) (j,Usable id d ram) ->
 (exists jr ir dr,
   clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
     (initial,Selecting) (jr,Installing ir dr TopologyChecked) /\
   boot_step g sector data_len valid marker ranges decode topology pages
     (jr,Installing ir dr TopologyChecked) (jr,Installing ir dr RuntimeInstalled) /\
   clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
     (jr,Installing ir dr RuntimeInstalled) (j,Usable id d ram)) /\
 episode_trace valid view ((initial,RebuildingBoundary Selecting),forget_volatile_evidence e) []
   valid view ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e)) /\
 runtime_metadata_coherent
   ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e)).
Proof.
 intros LOCAL BOOT. split.
 - exact (usable_boot_initialized g sector data_len valid view marker ranges decode topology pages
     initial j id d ram BOOT).
 - split;[|reflexivity].
   change (episode_trace valid view
     ((initial,RebuildingBoundary Selecting),forget_volatile_evidence e) ([]++[])
     valid view ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e))).
   eapply episodes_cons with (event:=None);[exact (boot_episode valid view
     (initial,Selecting) (j,Usable id d ram) e LOCAL BOOT)|].
   change (episode_trace valid view
     ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence e) ([]++[])
     valid view ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e))).
   eapply episodes_cons with (event:=None);[exact (resume_episode valid view j id d ram e)|constructor].
Qed.
Corollary episode_trace_runtime_forgotten vi oi initial events vf of_ j pc e :
 runtime_metadata_coherent initial ->
 episode_trace vi oi initial events vf of_ ((j,RebuildingBoundary pc),e) ->
 volatile_runtime_initialized e=None.
Proof. intros M RUN;exact (episode_trace_runtime _ _ _ _ _ _ _ M RUN). Qed.

Theorem episode_trace_control vi oi initial events vf of_ final :
 terminal_control_absent initial ->
 episode_trace vi oi initial events vf of_ final -> terminal_control_absent final.
Proof.
 intros INIT RUN;induction RUN;[exact INIT|].
 apply IHRUN;exact (episode_step_control _ _ _ _ _ _ _ H).
Qed.

Corollary episode_trace_reset_forgets vi oi initial events vf of_ j pc e :
 terminal_control_absent initial ->
 episode_trace vi oi initial events vf of_ ((j,RebuildingBoundary pc),e) ->
 volatile_control e=None /\ controller_read e=idle_control.
Proof.
 intros INIT RUN;pose proof (episode_trace_control _ _ _ _ _ _ _ INIT RUN) as EMPTY.
 change (volatile_control e=None) in EMPTY;split;[exact EMPTY|].
 unfold controller_read;rewrite EMPTY;reflexivity.
Qed.

Lemma controller_program_episode valid view x action result final :
 controller_service_caller x _ (ControllerCommand action) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract (controller_program action)) x result final ->
 episode_step valid view x None valid view final.
Proof.
 intros CALL RUN;apply controller_program_post in RUN;destruct RUN as [R FINAL];subst final.
 destruct x as [[j phase] e];apply controller_episode;exact CALL.
Qed.

Lemma episode_step_safe vi oi x event vf of_ y : Safe vi oi x ->
  episode_step vi oi x event vf of_ y ->
  Safe vf of_ y /\ boundary_receipts y=emitted_receipts event++boundary_receipts x.
Proof.
 intros INV RUN; destruct RUN.
 - exact (boundary_step_preserves g sector data_len valid view marker ranges decode topology pages
     bytes dw bw dp bp G DIV H H0 _ _ _ INV H1).
 - split; [exact (proj1 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p boss plan result validate G DIV INV H H0 H1 H2 H3 H4))|reflexivity].
 - destruct H6 as [[P BLANK] WRITE].
   destruct (prepared_incarnation_from_reserved_writer g sector data_len valid view marker ranges decode pages
     f h a old image root s e p true plan result id fresh validate INV H H0 P H2 H3 H4 H5 WRITE H8 H9 H10)
     as [prior [NE [NEXT [KEEP COVER]]]].
   assert (EQ:prior=previous).
   { pose proof (proj1 (Forall_forall _ _) (proj1 (proj1 (proj2 INV))) (Certificate old previous) H1) as [READ FMT].
     pose proof (Forall_inv (proj1 (proj1 (proj2 NEXT)))) as [READ' FMT'].
     simpl in READ,READ'.
     assert (PH:physical_authority s=root_extents (view old)).
     { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 INV))))) as LINK.
       unfold protection_history_link in LINK; simpl in LINK; rewrite H0 in LINK; simpl in LINK; rewrite Nat2N.id in LINK; exact LINK. }
     assert (FRAME:unchanged (root_extents (view old)) (object_flash sector f) (object_flash sector (writer_flash result))).
     { intros r addr IN AT; apply (KEEP r addr); [|exact AT]. unfold protected_roots; repeat rewrite in_app_iff; rewrite PH; tauto. }
     rewrite (H4 _ FRAME) in READ; congruence. }
   subst prior. split; [eapply writer_exit_phase; eauto|reflexivity].
 - split; [eapply reserved_exact_attachment; eauto|reflexivity].
 - split; [eapply boundary_reset_prefix_safe; eauto|reflexivity].
 - split; [exact (proj1 (boundary_boot_prefix_safe g sector data_len valid view marker ranges decode topology pages
     G DIV _ _ _ INV H H0))|reflexivity].
 - split; [apply recovered_page_evidence_invariant;exact (proj1 (enriched_boot_usable sector data_len valid view marker ranges decode pages _ _ _ _ _ INV))|reflexivity].
 - destruct (common_begin sector data_len valid view marker ranges decode pages _ _ _ _ (proj1 INV)) as [CALL NEXT].
   split; [split; [exact NEXT|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - pose proof INV as [[JI [DI [FR [COR LINK]]]] [EV CERT]].
   destruct (erased_admission_guards _ _ _ _ H0) as [FREE BLANK].
   split;[eapply reservation_state_open;[exact INV|exact H|exact FREE]|reflexivity].
 - split; [exact (proj1 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8))|reflexivity].
 - split;[eapply frozen_boundary_cleanup;eauto|reflexivity].
 - split;[eapply install_certified_candidate;eauto|reflexivity].
 - split;[eapply certified_client_return;eauto|reflexivity].
 - split;[eapply certified_uncertain_cleanup;eauto|reflexivity].
 - split;[eapply certified_append_fatal;eauto|reflexivity].
 - split;[eapply certified_publication_reset;eauto|reflexivity].
 - split;[eapply certified_append_cut;eauto|reflexivity].
 - split;[eapply certified_append_cut;eauto|reflexivity].
 - split;[exact (proj1 (enriched_client_next sector data_len valid view marker ranges decode pages _ _ _ _ _ INV))|reflexivity].
 - split;[eapply certified_drop_pending;eauto|reflexivity].
 - split;[eapply certified_normal_rollback;eauto|reflexivity].
 - split;[eapply certified_prepared_rollback;eauto|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - assert (RESET:logged_step g sector 256 data_len valid (Logged (Ready f) h a) (Logged (Boot f) h a)) by (apply record_step;apply reset_ready).
   split;[exact (boundary_reset_prefix_safe g sector data_len valid view marker ranges decode pages
     G DIV (Logged (Ready f) h a) (OpenBoundary image root s) e INV RESET)|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - pose proof (proj1 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8)) as RESERVED.
   unfold recycling_acquisition_boundary in RESERVED;rewrite H9 in RESERVED.
   assert (RESET:logged_step g sector 256 data_len (validate (neutral_flash result))
     (Logged (Ready (neutral_flash result)) h a) (Logged (Boot (neutral_flash result)) h a)) by (apply record_step;apply reset_ready).
   split;[exact (boundary_reset_prefix_safe g sector data_len (validate (neutral_flash result)) view marker ranges decode pages
     G DIV (Logged (Ready (neutral_flash result)) h a) _ _ RESERVED RESET)|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - assert (RESET:logged_step g sector 256 data_len valid (Logged (Ready f) h a) (Logged (Boot f) h a)) by (apply record_step;apply reset_ready).
   split;[exact (boundary_reset_prefix_safe g sector data_len valid view marker ranges decode pages
     G DIV (Logged (Ready f) h a) (PublishingBoundary CandidatePrepared id candidate s) e INV RESET)|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[eapply certified_normal_rollback;eauto|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - pose proof (proj1 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4)) as NEXT.
   unfold writer_exit_boundary in NEXT;rewrite H6 in NEXT.
   split;[split;[split;[exact (proj1 (proj1 NEXT))|exact I]|split;[exact (proj1 (proj2 NEXT))|exact I]]|reflexivity].
 - split;[exact (proj1 (certified_outer_pair g sector data_len valid view marker ranges decode pages
     f h a old d s e ia ib ea eb ra rb pa pb wa wb validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H3) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H4 H5 H6
     ltac:(destruct (erased_admission_guards _ _ _ _ H7) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H8 H9 H10))|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact (proj1 (certified_operation_first g sector data_len valid view marker ranges decode pages
     f h a old d s e index entry r plan result validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H3 H4 H5))|reflexivity].
 - split;[exact (reservation_state_open sector data_len valid view marker ranges decode pages
    j image root s e r false INV H (proj1 (erased_admission_guards _ _ _ _ H0)))|reflexivity].
 - pose proof (proj1 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4)) as NEXT.
   split;[apply operation_phase_safe;exact NEXT|unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);reflexivity].
 - split;[exact (proj1 (proj2 (certified_operation_cancel sector data_len valid view marker ranges decode pages
     f h a image root s e old d INV H H0 H1 H2)))|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - split;[exact (frozen_boundary_cleanup sector data_len valid view marker ranges decode pages j old candidate current None s e [DataClose views saved false] INV (conj H I))|reflexivity].
 - split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity].
 - pose proof (proj1 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4)) as NEXT.
   unfold writer_exit_boundary in NEXT;rewrite H6 in NEXT.
   split;[split;[split;[exact (proj1 (proj1 NEXT))|exact I]|split;[exact (proj1 (proj2 NEXT))|exact I]]|reflexivity].
 - pose proof (proj1 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8)) as NEXT.
   split;[apply operation_phase_safe;exact NEXT|reflexivity].
 - split;[exact (proj1 (certified_operation_begin sector data_len valid view marker ranges decode pages j old d s e INV))|reflexivity].
 - split;[exact (reserved_exact_attachment sector data_len valid view marker ranges decode pages j image root s e p index entry INV H H0 H2)|reflexivity].
 - split;[exact (proj2 (certified_local_accept sector data_len valid view marker ranges decode pages
    j image root s e (physical_authority s) INV (proj1 H) H0))|reflexivity].
 - split;[exact (proj1 (proj2 (certified_operation_cancel sector data_len valid view marker ranges decode pages
     f h a image root s e old d INV H H0 H1 H2)))|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[eapply certified_clean_retained;eauto|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact (certified_drop_pending sector data_len valid view marker ranges decode pages j image root s e p INV H)|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact (frozen_boundary_cleanup sector data_len valid view marker ranges decode pages j old candidate (Some current) (Some [boss_extent (view id)]) s e [DataClose views (root_extents (view id)) false] INV (conj H I))|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact INV|reflexivity].
 - split;[exact INV|reflexivity].
 - destruct fatal;split;[split;[split;[exact (proj1 (proj1 INV))|exact I]|split;[exact (proj1 (proj2 INV))|exact I]]|reflexivity| |reflexivity].
   exact (boundary_reset_prefix_safe g sector data_len valid view marker ranges decode pages
     G DIV (Logged (Ready f) h a) phase e INV
     ltac:(apply record_step;apply reset_ready)).
 - split;[apply identical_attachment_safe;exact INV|reflexivity].
 - split;[eapply rehome_cached_safe;eauto|reflexivity].

 - split;[exact INV|reflexivity].

 - split;[eapply install_detached_decoded;eauto|reflexivity].

Qed.

Lemma episode_step_counter_source vi oi x event vf of_ y :
 episode_step vi oi x event vf of_ y -> counter_decoder (snd y)=counter_decoder (snd x).
Proof.
 intro RUN;destruct RUN;
 try (eapply boundary_step_counter_source;eassumption);try reflexivity.
 all: try (destruct fatal;reflexivity).
 all: try (unfold operation_writer_exit,operation_acquisition_boundary;reflexivity).
Qed.
Lemma episode_step_counter vi oi x event vf of_ y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 counter_metadata_coherent x -> Safe vi oi x ->
 episode_step vi oi x event vf of_ y -> counter_metadata_coherent y.
Proof.
 intros MATCH M INV RUN.
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;
 try (eapply boundary_step_counter;eassumption);
 try (apply boundary_counter_metadata;exact M);
 try (apply phase_counter_metadata;exact M);
 cbn in M |- *;try exact M;try reflexivity.
 all: try (eapply decoded_counter_available;[exact MATCH|apply generation_ready_read in NEXT;exact NEXT]).
 all: try (eapply decoded_counter_available;[exact MATCH|apply generation_client_read in NEXT;exact NEXT]).
 all: try (unfold operation_writer_exit;apply boundary_counter_metadata;exact M).
 all: try (unfold operation_acquisition_boundary;apply boundary_counter_metadata;exact M).
 all: try (destruct fatal;reflexivity).
 all: try (destruct phase;exact M).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);cbn in M |- *;assumption || reflexivity.
Qed.
Theorem episode_trace_counter vi oi initial events vf of_ final :
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 counter_metadata_coherent initial -> Safe vi oi initial ->
 episode_trace vi oi initial events vf of_ final ->
 counter_metadata_coherent final /\ counter_decoder (snd final)=counter_decoder (snd initial).
Proof.
 intros MATCH M INV RUN;induction RUN;[auto|].
 pose proof (episode_step_counter_source _ _ _ _ _ _ _ H) as SOURCE.
 destruct (IHRUN ltac:(rewrite SOURCE;exact MATCH)
   (episode_step_counter _ _ _ _ _ _ _ MATCH M INV H)
   (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H))) as [COHERENT SAME].
 split;[exact COHERENT|congruence].
Qed.

Lemma episode_step_allocation_known vi oi x event vf of_ y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 allocation_metadata_coherent x -> Safe vi oi x ->
 episode_step vi oi x event vf of_ y -> allocation_metadata_coherent y.
Proof.
 intros MATCH M INV RUN.
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;
 try (eapply boundary_step_allocation_known;eassumption);
 try (apply boundary_allocation_metadata;exact M);
 try (apply phase_allocation_metadata;exact M);
 cbn in M |- *;try exact M;try reflexivity.
 all: try (eapply decoded_allocation_available;[exact MATCH|apply generation_ready_read in NEXT;exact NEXT]).
 all: try (eapply decoded_allocation_available;[exact MATCH|apply generation_client_read in NEXT;exact NEXT]).
 all: try (unfold operation_writer_exit;apply boundary_allocation_metadata;exact M).
 all: try (unfold operation_acquisition_boundary;apply boundary_allocation_metadata;exact M).
 all: try (destruct fatal;reflexivity).
 all: try (destruct phase;cbn in M |- *;exact M || reflexivity).
 all: try (destruct M as [n EQ];cbn in EQ;rewrite EQ;eexists;reflexivity).
 all: try (unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,
   recycling_cursor_evidence;destruct (neutral_end_ result);cbn in *;
   try reflexivity;destruct M as [n EQ];rewrite EQ;eexists;reflexivity).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);cbn in M |- *;assumption || reflexivity.
Qed.
Lemma episode_step_allocation_origin vi oi x event vf of_ y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode (snd x) -> Safe vi oi x ->
 episode_step vi oi x event vf of_ y -> allocation_range_origin sector pages decode (snd y).
Proof.
 intros MATCH GEO ORIGIN INV RUN.
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact ORIGIN;try apply allocation_origin_forget;
 try (eapply boundary_step_allocation_origin;eassumption);
 try (apply allocation_origin_phase;exact ORIGIN);
 try (apply allocation_origin_advance;exact ORIGIN);
 try (apply allocation_origin_advance;apply allocation_origin_advance;exact ORIGIN).
 all: try (eapply allocation_origin_observe;[exact GEO|exact (generation_client_read _ _ _ _ _ _ _ _ _ _ _ _ _ NEXT)]).
 all: try (intros actual OBS;eapply allocation_origin_decoded;[exact MATCH|exact GEO|exact (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ NEXT)|exact OBS]).
 all: try (destruct fatal;apply allocation_origin_forget).
 all: try (destruct phase;exact ORIGIN || apply allocation_origin_forget).
 all: try (unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);
   apply allocation_origin_phase;exact ORIGIN).
 all: try (unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,
   recycling_cursor_evidence;destruct (neutral_end_ result);cbn [snd];
   try apply allocation_origin_forget;try exact ORIGIN;
   try (apply allocation_origin_phase;exact ORIGIN);
   try (apply allocation_origin_phase;apply allocation_origin_advance;exact ORIGIN)).
 all: destruct phase;try exact ORIGIN;intros actual OBS;discriminate.
Qed.
Lemma episode_step_append_bound vi oi x event vf of_ y :
 generation_decoding_matches sector decode (counter_decoder (snd x)) ->
 decoded_allocation_geometry pages decode -> allocation_append_bound pages (snd x) ->
 Safe vi oi x -> episode_step vi oi x event vf of_ y -> allocation_append_bound pages (snd y).
Proof.
 intros MATCH GEO B INV RUN;pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact B;try apply allocation_append_forget;
 try (eapply boundary_step_append_bound;eassumption);
 try (apply allocation_append_phase;exact B).
 all: try (apply allocation_append_observe;exact B).
 all: try (intros actual OBS;eapply allocation_append_decoded;[exact MATCH|exact GEO|exact (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ NEXT)|exact OBS]).
 all: try (apply allocation_append_advance;
   match goal with A:mapped_erased_admission _ _ _ _ _ |- _ => exact (mapped_erased_admission_bound _ _ _ _ _ A)
   | A:runtime_erased_admission _ _ _ _ _ _ |- _ => exact (proj1 (runtime_erased_advance_bounded _ _ _ _ _ _ _ (Nat.le_refl _) A)) end).
 all: try (destruct fatal;apply allocation_append_forget).
 all: try (destruct phase;exact B || apply allocation_append_forget).
 all: try (unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);
   apply allocation_append_phase;exact B).
 all: try (assert (MAPPED:extent_end (block_pages (recycle_lo r) (useful_pages r))<=pages*256)
     by (eapply recycled_extent_mapping;eassumption);
   unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,
   recycling_cursor_evidence;destruct (neutral_end_ result);cbn [snd];
   try apply allocation_append_forget;try exact B;
   try (apply allocation_append_phase;exact B);
   try (apply allocation_append_phase;apply allocation_append_advance;exact MAPPED)).
Qed.
Theorem episode_trace_append_bound vi oi initial events vf of_ final :
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_allocation_geometry pages decode -> allocation_append_bound pages (snd initial) ->
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 allocation_append_bound pages (snd final).
Proof.
 intros MATCH GEO B INV RUN;induction RUN;[exact B|].
 apply IHRUN;[rewrite (episode_step_counter_source _ _ _ _ _ _ _ H);exact MATCH| |].
 - eapply episode_step_append_bound;eassumption.
 - exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)).
Qed.

Theorem episode_trace_allocation_origin vi oi initial events vf of_ final :
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_allocation_geometry pages decode ->
 allocation_range_origin sector pages decode (snd initial) -> Safe vi oi initial ->
 episode_trace vi oi initial events vf of_ final ->
 allocation_range_origin sector pages decode (snd final).
Proof.
 intros MATCH GEO ORIGIN INV RUN;induction RUN;[exact ORIGIN|].
 apply IHRUN;[rewrite (episode_step_counter_source _ _ _ _ _ _ _ H);exact MATCH| |].
 - eapply episode_step_allocation_origin;eassumption.
 - exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)).
Qed.

Theorem episode_trace_allocation_known vi oi initial events vf of_ final :
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 allocation_metadata_coherent initial -> Safe vi oi initial ->
 episode_trace vi oi initial events vf of_ final ->
 allocation_metadata_coherent final /\ counter_decoder (snd final)=counter_decoder (snd initial).
Proof.
 intros MATCH M INV RUN;induction RUN;[auto|].
 pose proof (episode_step_counter_source _ _ _ _ _ _ _ H) as SOURCE.
 destruct (IHRUN ltac:(rewrite SOURCE;exact MATCH)
   (episode_step_allocation_known _ _ _ _ _ _ _ MATCH M INV H)
   (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H))) as [COHERENT SAME].
 split;[exact COHERENT|congruence].
Qed.

(* One transported property: present on ordinary boundaries, forgotten on
   reset/fatal, with a decoded durable range and a separately bounded probe
   cursor. No identity between these two offsets is asserted. *)
Definition allocation_transport x :=
 allocation_metadata_coherent x /\
 allocation_range_origin sector pages decode (snd x) /\
 allocation_append_bound pages (snd x).
Theorem episode_trace_allocation_transport vi oi initial events vf of_ final :
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_allocation_geometry pages decode -> allocation_transport initial ->
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 allocation_transport final.
Proof.
 intros MATCH GEO [KNOWN [ORIGIN BOUND]] INV RUN;split.
 - exact (proj1 (episode_trace_allocation_known _ _ _ _ _ _ _ MATCH KNOWN INV RUN)).
 - split;[eapply episode_trace_allocation_origin|eapply episode_trace_append_bound];eassumption.
Qed.

Lemma episode_step_latest vi oi x event vf of_ y :
 latest_metadata_coherent x -> episode_step vi oi x event vf of_ y ->
 latest_metadata_coherent y.
Proof.
 intros M RUN;destruct RUN;
 try (eapply boundary_step_latest;[exact M|eassumption]);
 try (apply boundary_latest_metadata;exact M);
 try (apply phase_latest_metadata;exact M);
 cbn in M |- *;try assumption;try reflexivity;try (eexists;reflexivity).
 all: try (unfold operation_writer_exit;apply boundary_latest_metadata;exact M).
 all: try (unfold operation_acquisition_boundary;apply boundary_latest_metadata;exact M).
 all: try (destruct fatal;reflexivity).
 all: try (destruct phase;exact M).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);cbn in M |- *;assumption || reflexivity.
Qed.
Theorem episode_trace_latest vi oi initial events vf of_ final :
 latest_metadata_coherent initial -> episode_trace vi oi initial events vf of_ final ->
 latest_metadata_coherent final.
Proof. intros M RUN;induction RUN;[exact M|]. apply IHRUN;eapply episode_step_latest;eassumption. Qed.

Lemma episode_step_ordinary_latest vi oi x event vf of_ y :
 ordinary_latest_coherent x -> Safe vi oi x ->
 episode_step vi oi x event vf of_ y -> ordinary_latest_coherent y.
Proof.
 intros COHERENT INV RUN;pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;try exact COHERENT;try exact I;
 try (eapply boundary_step_ordinary_latest;eassumption);
 try (apply ordinary_latest_phase;exact COHERENT).
 all: try (cbn [ordinary_latest_coherent latest_at_head boundary_journal];cbn;
   symmetry;apply latest_idle_head in NEXT;exact NEXT).
 all: try (cbn [ordinary_latest_coherent latest_at_head boundary_journal];cbn;
   symmetry;apply latest_client_head in NEXT;exact NEXT).
 all: try (destruct fatal;exact I).
 all: try (destruct phase;try destruct stage;exact COHERENT || exact I).
 all: try (unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);
   apply ordinary_latest_phase;exact COHERENT || exact I).
 all: try (unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary,
   recycling_cursor_evidence;destruct (neutral_end_ result);
   apply ordinary_latest_phase;exact COHERENT || exact I).
 all: apply ordinary_latest_phase;unfold failure_phase;
 repeat match goal with
 | |- context[if ?test then _ else _] => destruct test
 | |- context[match ?opt with Some _=>_ | None=>_ end] => destruct opt
 end;exact I || exact COHERENT.
Qed.
Theorem episode_trace_ordinary_latest vi oi initial events vf of_ final :
 ordinary_latest_coherent initial -> Safe vi oi initial ->
 episode_trace vi oi initial events vf of_ final -> ordinary_latest_coherent final.
Proof.
 intros COHERENT INV RUN;induction RUN;[exact COHERENT|].
 apply IHRUN;[eapply episode_step_ordinary_latest;eassumption|].
 exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)).
Qed.

Lemma episode_step_latest_origin vi oi x event vf of_ y :
 Safe vi oi x -> episode_step vi oi x event vf of_ y ->
 latest_origin (volatile_latest_registry (snd x)) y.
Proof.
 intros INV RUN;pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;try (eapply boundary_step_latest_origin;eassumption);
 try (eapply boundary_latest_origin_same;reflexivity);try (eapply phase_latest_origin_same;reflexivity);
 try (unfold latest_origin;cbn;tauto).
 all: try (right;right;unfold latest_at_head;cbn;symmetry;apply latest_idle_head in NEXT;exact NEXT).
 all: try (right;right;unfold latest_at_head;cbn;symmetry;apply latest_client_head in NEXT;exact NEXT).
 all: try (unfold operation_writer_exit;eapply boundary_latest_origin_same;reflexivity).
 all: try (unfold operation_acquisition_boundary;eapply boundary_latest_origin_same;reflexivity).
 all: try (destruct fatal;unfold latest_origin;cbn;tauto).
 all: try (destruct phase;unfold latest_origin;cbn;tauto).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);unfold latest_origin;cbn;tauto.
Qed.

Lemma episode_step_counter_origin vi oi x event vf of_ y :
 Safe vi oi x -> episode_step vi oi x event vf of_ y ->
 counter_origin sector decode (volatile_counter (snd x)) y.
Proof.
 intros INV RUN;pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV RUN)) as NEXT.
 destruct RUN;try (eapply boundary_step_counter_origin;eassumption);
 try (eapply boundary_counter_origin_same;reflexivity);try (eapply phase_counter_origin_same;reflexivity);
 try (unfold counter_origin;cbn;tauto).
 all: try (unfold counter_origin;right;right;eexists;eexists;split;
   [apply generation_ready_read in NEXT;exact NEXT|reflexivity]).
 all: try (unfold counter_origin;right;right;eexists;eexists;split;
   [apply generation_client_read in NEXT;exact NEXT|reflexivity]).
 all: try (unfold operation_writer_exit;eapply boundary_counter_origin_same;reflexivity).
 all: try (unfold operation_acquisition_boundary;eapply boundary_counter_origin_same;reflexivity).
 all: try (destruct fatal;unfold counter_origin;cbn;tauto).
 all: try (destruct phase;unfold counter_origin;cbn;tauto).
 all: unfold operation_writer_exit,writer_exit_boundary in *;
   destruct (writer_end result);unfold counter_origin;cbn;tauto.
Qed.
Theorem episode_trace_counter_origin vi oi initial events vf of_ final :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 volatile_counter (snd final)=volatile_counter (snd initial) \/
 volatile_counter (snd final)=None \/
 exists vm om installed prefix suffix id d,
 episode_trace vi oi initial prefix vm om installed /\
 episode_trace vm om installed suffix vf of_ final /\
 decode (object_flash sector (control_image (journal_control (boundary_journal installed)))) id=Some d /\
 volatile_counter (snd final)=read_counter (counter_decoder (snd installed))
   (control_image (journal_control (boundary_journal installed))) id.
Proof.
 intros INV RUN;induction RUN;[left;reflexivity|].
 destruct (IHRUN (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H))) as [SAME|[NONE|FRESH]].
 - destruct (episode_step_counter_origin _ _ _ _ _ _ _ INV H) as [OLD|[NONE|[id [d [READ INSTALLED]]]]].
   + left;congruence.
   + right;left;congruence.
   + right;right;exists vm,om,y,(emitted_receipts event),events,id,d.
     split.
     * change (episode_trace vi oi x ([]++emitted_receipts event) vm om y).
       eapply episodes_cons;[exact H|constructor].
     * split;[exact RUN|]. split;[exact READ|congruence].
 - right;left;exact NONE.
 - destruct FRESH as [v [o [installed [prefix [suffix [id [d [PRE [POST [READ VALUE]]]]]]]]]].
   right;right;exists v,o,installed,(prefix++emitted_receipts event),suffix,id,d.
   split;[eapply episodes_cons;eassumption|]. auto.
Qed.

Definition historical_delivery r := exists delivery_view, actual_client_delivery delivery_view marker r.
Lemma episode_emission vi oi x event vf of_ y : Safe vi oi x ->
 episode_step vi oi x event vf of_ y -> forall r, event=Some r -> historical_delivery r.
Proof.
 intros INV RUN r EQ; destruct RUN; try discriminate.
 - exists view; eapply boundary_emission_is_delivery; eauto.
 - inversion EQ;subst r. exists view.
   exists id,(recovered_image d),saved,s,final. split;[|exact H4].
   pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INV)))))) as FMT.
   destruct d as [boss image];simpl in *;destruct FMT as [B OB]. simpl in B;subst boss;reflexivity.
Qed.

Theorem a11_external_reserved_data_safety vi oi initial events vf of_ final :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 Safe vf of_ final /\ boundary_receipts final=events++boundary_receipts initial /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall historical_delivery events.
Proof.
 intros INIT TRACE; induction TRACE.
 - split; [exact INIT|]. split; [reflexivity|]. split; [exact (proj2 (proj2 (proj1 (proj2 INIT))))|constructor].
 - destruct (episode_step_safe _ _ _ _ _ _ _ INIT H) as [MID OBS].
   destruct (IHTRACE MID) as [LAST [RECEIPTS [VALID DELIVERED]]].
   split; [exact LAST|]. split; [rewrite RECEIPTS; rewrite OBS; rewrite app_assoc;reflexivity|].
   split; [exact VALID|]. apply Forall_app; split; [exact DELIVERED|].
   destruct event as [receipt|];[constructor;[exact (episode_emission _ _ _ _ _ _ _ INIT H receipt eq_refl)|constructor]|constructor].
Qed.

(* A completed boot supplies the counter read with its decoded BOSS. No
   counter from before reset appears in the premises. *)
Theorem boot_counter_reconstructed valid view initial j id d ram e :
 Safe valid view ((initial,RebuildingBoundary Selecting),forget_volatile_evidence e) ->
 generation_decoding_matches sector decode (counter_decoder e) ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (initial,Selecting) (j,Usable id d ram) ->
 exists n,
 counter_decoder e (control_image (journal_control j)) id=Some (d,n) /\
 volatile_counter (recovered_page_evidence j id (forget_volatile_evidence e))=Some n /\
 episode_trace valid view ((initial,RebuildingBoundary Selecting),forget_volatile_evidence e) []
   valid view ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e)) /\
 Safe valid view ((j,IdleBoundary id d ram),recovered_page_evidence j id (forget_volatile_evidence e)) /\
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages)
   (initial,Selecting) (j,Installing id d TopologyChecked) /\
 boot_step g sector data_len valid marker ranges decode topology pages
   (j,Installing id d TopologyChecked) (j,Installing id d RuntimeInstalled).
Proof.
 intros INIT MATCH LOCAL RUN.
 destruct (boot_runtime_handoff valid view initial j id d ram e LOCAL RUN) as [_ [PATH _]].
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT PATH)) as SAFE.
 pose proof (generation_ready_read sector data_len valid view marker ranges decode pages
   j id d ram _ SAFE) as READ.
 specialize (MATCH (control_image (journal_control j)) id);rewrite READ in MATCH.
 destruct (counter_decoder e (control_image (journal_control j)) id) as [[dd n]|] eqn:FULL;
   cbn in MATCH;try discriminate;inversion MATCH;subst dd.
 exists n;split;[reflexivity|]. split.
 - cbn;unfold read_counter;rewrite FULL;reflexivity.
 - split;[exact PATH|]. split;[exact SAFE|].
   exact (usable_boot_counter_origin g sector data_len valid marker ranges decode topology pages
     initial j id d ram RUN).
Qed.

Lemma lift_boundary_trace valid view bytes dw bw dp bp initial events final :
 recovery_local_contracts view ranges decode ->
 outcome_writer_contracts g sector view bytes dw bw dp bp decode ->
 boundary_trace g sector data_len valid view marker ranges decode topology pages dw bw initial events final ->
 episode_trace valid view initial events valid view final.
Proof.
 intros C W RUN; induction RUN; [apply episodes_nil|].
 eapply episodes_cons; [eapply execute_services; eauto|exact IHRUN].
Qed.

Lemma episode_step_history vi oi x event vf of_ y : Safe vi oi x ->
 episode_step vi oi x event vf of_ y ->
 exists prefix, publications (boundary_journal y)=prefix++publications (boundary_journal x).
Proof.
 intros INV RUN; destruct RUN.
 - eapply boundary_history_extension; eauto.
 - exists []; unfold boundary_journal; simpl; unfold writer_exit_boundary; destruct (writer_end result); reflexivity.
 - exists []; unfold boundary_journal; simpl; unfold writer_exit_boundary; destruct (writer_end result); reflexivity.
 - exists []; reflexivity.
 - exists []; reflexivity.
 - exists []; exact (proj2 (boundary_boot_prefix_safe g sector data_len valid view marker ranges decode topology pages
     G DIV _ _ _ INV H H0)).
 - exists []; reflexivity.
 - exists []; reflexivity.
 - exists []; reflexivity.
 - exists []; unfold boundary_journal; simpl; unfold recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result); reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - eapply logged_history_extension. eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - eapply logged_history_extension. exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ H1))).
 - eapply logged_history_extension. eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - eapply logged_history_extension. destruct H0 as [before [PREFIX [BEFORE [STEP DEST]]]].
   eapply rt_trans;[exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX)))|apply rt_step;exact STEP].
 - eapply logged_history_extension. eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - eapply logged_history_extension. eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];unfold boundary_journal,operation_writer_exit,writer_exit_boundary;simpl;destruct (writer_end result);reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];unfold boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - exists [];reflexivity.
 - destruct fatal;exists [];reflexivity.
 - exists [];reflexivity.

 - exists [];reflexivity.

 - exists [];reflexivity.

 - exists [];reflexivity.

Qed.
Lemma episode_history_extension vi oi initial events vf of_ final :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 exists prefix, publications (boundary_journal final)=prefix++publications (boundary_journal initial).
Proof.
 intros INIT RUN; induction RUN; [exists [];reflexivity|].
 destruct (episode_step_safe _ _ _ _ _ _ _ INIT H) as [MID OBS].
 destruct (episode_step_history _ _ _ _ _ _ _ INIT H) as [p P].
 destruct (IHRUN MID) as [q Q]. exists (q++p); rewrite Q; rewrite P; rewrite app_assoc; reflexivity.
Qed.

Theorem episode_trace_latest_without_publication vi oi initial events vf of_ final :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ final ->
 publications (boundary_journal final)=publications (boundary_journal initial) ->
 (volatile_latest_registry (snd initial)=None \/ latest_at_head initial) ->
 volatile_latest_registry (snd final)=None \/ latest_at_head final.
Proof.
 intros INV RUN;induction RUN;intros SAME START;[auto|].
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)) as MID.
 destruct (episode_step_history _ _ _ _ _ _ _ INV H) as [first FIRST].
 destruct (episode_history_extension _ _ _ _ _ _ _ MID RUN) as [later LATER].
 assert (EMPTY:first=[] /\ later=[]).
 { rewrite LATER in SAME;rewrite FIRST in SAME.
   apply (f_equal (@length N)) in SAME;repeat rewrite app_length in SAME.
   destruct first,later;cbn in SAME;split;try reflexivity;lia. }
 destruct EMPTY as [-> ->];cbn in FIRST,LATER.
 destruct (episode_step_latest_origin _ _ _ _ _ _ _ INV H) as [SAME_RAM|[LOST|NEW]].
 - apply IHRUN;[exact MID|exact LATER|].
   destruct START as [LOST|START];[left;congruence|right].
   unfold latest_at_head in *;rewrite SAME_RAM;rewrite FIRST;exact START.
 - apply IHRUN;[exact MID|exact LATER|left;exact LOST].
 - apply IHRUN;[exact MID|exact LATER|right;exact NEW].
Qed.

Theorem idle_trace_open_latest vi oi f h a old d ram e events vf of_ ff aa image roots s ev :
 Safe vi oi ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 volatile_latest_registry e=Some old ->
 episode_trace vi oi ((Logged (Ready f) h a,IdleBoundary old d ram),e) events vf of_
   ((Logged (Ready ff) h aa,OpenBoundary image roots s),ev) ->
 volatile_latest_registry ev=Some old.
Proof.
 intros INIT LATEST RUN.
 assert (HEAD:hd_error h=Some (N.of_nat old)).
 { apply latest_idle_head in INIT;exact INIT. }
 assert (START:latest_at_head ((Logged (Ready f) h a,IdleBoundary old d ram),e)).
 { unfold latest_at_head;cbn;rewrite LATEST;cbn;congruence. }
 destruct (episode_trace_latest_without_publication _ _ _ _ _ _ _ INIT RUN eq_refl (or_intror START))
   as [LOST|END].
 - assert (M:latest_metadata_coherent ((Logged (Ready f) h a,IdleBoundary old d ram),e)).
   { cbn;exists old;exact LATEST. }
   pose proof (episode_trace_latest _ _ _ _ _ _ _ M RUN) as PRESENT.
   cbn in LOST,PRESENT;destruct PRESENT as [id PRESENT];congruence.
 - unfold latest_at_head in END;cbn in END;rewrite HEAD in END.
   destruct (volatile_latest_registry ev) as [id|] eqn:E;cbn in END;try discriminate.
   inversion END;assert (id=old) by lia;subst;reflexivity.
Qed.

Lemma selected_live_unique valid view x c d : Safe valid view x ->
 selected_live x c -> selected_live x d -> c=d.
Proof.
 intros [_ [EV _]] [IC HC] [ID HD].
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) c IC) as [RC FC].
 pose proof (proj1 (Forall_forall _ _) (proj1 EV) d ID) as [RD FD].
 assert (certificate_id c=certificate_id d) by (apply Nat2N.inj; congruence).
 assert (certificate_decoded c=certificate_decoded d) by (rewrite H in RC; congruence).
 destruct c,d; simpl in *; congruence.
Qed.
Lemma episode_step_selected vi oi x event vf of_ y c :
 Safe vi oi x -> selected_live x c -> episode_step vi oi x event vf of_ y ->
 publications (boundary_journal y)=publications (boundary_journal x) ->
 selected_live y c /\ unchanged (certificate_ranges ranges c) (boundary_objects sector x) (boundary_objects sector y).
Proof.
 intros INV SEL RUN HIST; destruct RUN.
 - split.
   + eapply no_publication_step_selected; eauto.
   + eapply boundary_selected_bytes; eauto.
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique; [exact INV|exact SEL|split; [exact H1|exact H0]]. }
   subst c. destruct (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p boss plan result validate G DIV INV H H0 H1 H2 H3 H4) as [NEXT [KEEP RAW]].
   split; [split; [simpl;auto|rewrite HIST;exact H0]|].
   unfold boundary_objects, boundary_journal; simpl. unfold writer_exit_boundary; destruct (writer_end result); exact KEEP.
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique; [exact INV|exact SEL|split; [exact H1|exact H0]]. }
   subst c. split; [split; [simpl;auto|rewrite HIST;exact H0]|].
   destruct H6 as [[P BLANK] WRITE].
   pose proof (pending_writer_preserves_roots _ _ _ _ _ _ _ _ (proj1 (proj2 (proj1 INV))) P
     (proj1 (proj1 (proj1 (proj1 INV)))) WRITE) as KEEP.
   pose proof (proj1 (Forall_forall _ _) (proj1 (proj1 (proj2 INV))) (Certificate old previous) H1) as [_ [B O]].
   assert (PH:physical_authority s=root_extents (view old)).
   { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 INV))))) as LINK.
     unfold protection_history_link in LINK; simpl in LINK; rewrite H0 in LINK; simpl in LINK;rewrite Nat2N.id in LINK; exact LINK. }
   unfold boundary_objects,boundary_journal; simpl. unfold writer_exit_boundary; rewrite H7; simpl.
   unfold certificate_ranges; simpl in B,O |- *. rewrite B; rewrite O.
   intros r addr IN AT; apply (KEEP r addr); [|exact AT].
   unfold protected_roots; repeat rewrite in_app_iff;rewrite PH;tauto.
 - split; [exact SEL|intros kept addr IN AT;reflexivity].
 - split; [split; [exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   destruct j as [ctrl h a];destruct ctrl;intros kept addr IN AT;reflexivity.
 - split; [split; [exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT; unfold boundary_objects,object_flash.
   apply (boundary_boot_objects_preserved g sector data_len valid view marker ranges decode topology pages
     G DIV _ _ _ INV H H0); lia.
 - split; [exact SEL|intros kept addr IN AT;reflexivity].
 - split; [exact SEL|intros kept addr IN AT;reflexivity].
 - split; [exact SEL|intros ext addr IN AT;reflexivity].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique; [exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c. destruct (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8) as [NEXT [KEEP REST]].
   split;[split;[simpl;auto|rewrite HIST;exact H0]|].
   unfold boundary_objects,boundary_journal; simpl;unfold recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result);exact KEEP.
 - split;[exact SEL|intros ext addr IN AT;reflexivity].
 - split;[exact SEL|intros ext addr IN AT;reflexivity].
 - assert (LOG:clos_refl_trans logged_state (logged_step g sector 256 data_len valid) ready
       (Logged (Ready out) pubs (N.of_nat id::acks))).
   { eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3]. }
   destruct (certified_append_evidence g sector data_len valid view marker ranges decode pages G DIV
     ready id d s e out slot pubs acks INV H H2 H3) as [J [EV HEAD]].
   split.
   + eapply selected_certificate_membership.
     * eapply certified_client_return;eauto.
     * apply (proj1 (Forall_forall _ _) (proj1 EV) c (proj1 SEL)).
     * rewrite HIST;exact (proj2 SEL).
   + intros r addr IN AT;unfold boundary_objects,object_flash.
     eapply logged_trace_frame_after_journal;eauto;try exact (proj1 (proj1 INV));lia.
 - split;[split;[exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ H1))).
 - split;[split;[exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - split;[split;[exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   destruct H0 as [before [PREFIX [BEFORE [STEP DEST]]]].
   eapply rt_trans;[exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX)))|apply rt_step;exact STEP].
 - split;[split;[exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - split;[split;[exact (proj1 SEL)|rewrite HIST;exact (proj2 SEL)]|].
   intros r addr IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c. pose proof (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8) as [NEXT [KEEP REST]].
   split;[split;[simpl;auto|exact H0]|exact KEEP].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c. pose proof (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4) as [NEXT [KEEP ORDER]].
   split;[split;[simpl;auto|exact H0]|exact KEEP].
 - assert (ID:c=Certificate old d).
   { eapply selected_live_unique;[exact INV|exact SEL|].
     split;[exact (proj2 (proj2 INV))|].
     pose proof (proj1 (proj2 (proj1 INV))) as IDLE.
     exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
   subst c;split;[split;[simpl;auto|exact (proj2 SEL)]|].
   exact (proj1 (proj2 (certified_outer_pair g sector data_len valid view marker ranges decode pages
     f h a old d s e ia ib ea eb ra rb pa pb wa wb validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H3) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H4 H5 H6
     ltac:(destruct (erased_admission_guards _ _ _ _ H7) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H8 H9 H10))).
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - assert (ID:c=Certificate old d).
   { eapply selected_live_unique;[exact INV|exact SEL|].
     split;[exact (proj2 (proj2 INV))|].
     pose proof (proj1 (proj2 (proj1 INV))) as IDLE.
     exact (proj1 (proj2 (proj2 (proj2 IDLE)))). }
   subst c;split;[split;[simpl;auto|exact (proj2 SEL)]|].
   exact (proj1 (proj2 (proj2 (certified_operation_first g sector data_len valid view marker ranges decode pages
     f h a old d s e index entry r plan result validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H3 H4 H5)))).
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c. pose proof (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4) as [NEXT [KEEP ORDER]].
   split;[unfold selected_live,boundary_journal,operation_writer_exit,writer_exit_boundary;simpl;
     destruct (writer_end result);split;simpl;auto|].
   unfold boundary_objects,boundary_journal,operation_writer_exit,writer_exit_boundary;destruct (writer_end result);exact KEEP.
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c. pose proof (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4) as [NEXT [KEEP ORDER]].
   split;[split;[simpl;auto|exact H0]|exact KEEP].
 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H1|exact H0]]. }
   subst c;pose proof (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8) as [NEXT [KEEP REST]].
   split.
   + unfold selected_live,boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result);split;simpl;auto.
   + unfold boundary_objects,boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result);exact KEEP.
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros r addr IN AT;reflexivity].
 - split;[exact SEL|intros r addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].
 - destruct fatal;split;[exact SEL|intros kept addr IN AT;reflexivity|exact SEL|intros kept addr IN AT;reflexivity].
 - split;[exact SEL|intros kept addr IN AT;reflexivity].

 - split;[exact SEL|intros ext addr IN AT;reflexivity].

 - split;[exact SEL|intros ext addr IN AT;reflexivity].

 - assert (EQ:c=Certificate old previous).
   { eapply selected_live_unique;[exact INV|exact SEL|split;[exact H0|exact H]]. }
   subst c;split;[split;[simpl;auto|exact H]|intros ext addr IN AT;reflexivity].

Qed.
Theorem episode_no_publication_transport vi oi initial events vf of_ final c :
 Safe vi oi initial -> selected_live initial c -> episode_trace vi oi initial events vf of_ final ->
 publications (boundary_journal final)=publications (boundary_journal initial) ->
 Safe vf of_ final /\ selected_live final c /\
 unchanged (certificate_ranges ranges c) (boundary_objects sector initial) (boundary_objects sector final).
Proof.
 intros INIT SEL RUN; induction RUN; intro HIST.
 - split;[exact INIT|]. split;[exact SEL|intros kept addr IN AT;reflexivity].
 - pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INIT H)) as MID.
   destruct (episode_step_history _ _ _ _ _ _ _ INIT H) as [p P].
   destruct (episode_history_extension _ _ _ _ _ _ _ MID RUN) as [q Q].
   assert (L:length p=0 /\ length q=0).
   { pose proof (f_equal (@length N) HIST) as L;rewrite Q in L; rewrite P in L;repeat rewrite length_app in L;lia. }
   destruct L as [LP LQ];apply length_zero_iff_nil in LP;apply length_zero_iff_nil in LQ;subst p q.
   destruct (episode_step_selected _ _ _ _ _ _ _ _ INIT SEL H P) as [SELECT KEEP].
   destruct (IHRUN MID SELECT Q) as [LAST [CHOSEN BYTES]].
   split;[exact LAST|]. split;[exact CHOSEN|].
   intros r addr IN AT;rewrite (BYTES r addr IN AT);exact (KEEP r addr IN AT).
Qed.

Theorem episode_success_durable vi oi initial events vm om j id d ram e later vf of_ jf chosen decoded restored ef :
 Safe vi oi initial -> episode_trace vi oi initial events vm om ((j,ClientBoundary id d ram),e) ->
 episode_trace vm om ((j,ClientBoundary id d ram),e) later vf of_ ((jf,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (ef)) ->
 publications jf=publications j ->
 chosen=id /\ decoded=d /\ data_caller DataBegin restored /\
 unchanged (certificate_ranges ranges (Certificate id d))
  (object_flash sector (control_image (journal_control j))) (object_flash sector (control_image (journal_control jf))).
Proof.
 intros INIT PREFIX SUFFIX HIST.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT PREFIX)) as SAFE.
 assert (SEL:selected_live ((j,ClientBoundary id d ram),e) (Certificate id d)).
 { split;[exact (proj2 (proj2 SAFE))|]. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 (proj1 SAFE)))))))). }
 destruct (episode_no_publication_transport _ _ _ _ _ _ _ _ SAFE SEL SUFFIX HIST) as [LAST [SAME KEEP]].
 destruct (selected_usable_identity sector data_len vf of_ marker ranges decode pages _ _ _ _ _ _ LAST SAME)
   as [ID [IMAGE CALL]]. auto.
Qed.
Theorem episode_before_publication vi oi initial events vm om j id d ram e later vf of_ jf chosen decoded restored ef :
 Safe vi oi initial -> episode_trace vi oi initial events vm om ((j,IdleBoundary id d ram),e) ->
 episode_trace vm om ((j,IdleBoundary id d ram),e) later vf of_ ((jf,RebuildingBoundary (Usable chosen decoded restored)),forget_volatile_evidence (ef)) ->
 publications jf=publications j -> chosen=id /\ decoded=d /\ data_caller DataBegin restored.
Proof.
 intros INIT PREFIX SUFFIX HIST.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT PREFIX)) as SAFE.
 assert (SEL:selected_live ((j,IdleBoundary id d ram),e) (Certificate id d)).
 { split;[exact (proj2 (proj2 SAFE))|]. exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj2 (proj1 SAFE))))))). }
 destruct (episode_no_publication_transport _ _ _ _ _ _ _ _ SAFE SEL SUFFIX HIST) as [LAST [SAME KEEP]].
 exact (selected_usable_identity sector data_len vf of_ marker ranges decode pages _ _ _ _ _ _ LAST SAME).
Qed.
Theorem episode_next_begin vi oi initial events vf of_ j id d ram e :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ ((j,IdleBoundary id d ram),e) ->
 data_caller DataBegin ram /\ Safe vf of_ ((j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)),e).
Proof.
 intros INIT RUN.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT RUN)) as SAFE.
 destruct (common_begin sector data_len vf of_ marker ranges decode pages _ _ _ _ (proj1 SAFE)) as [CALL NEXT].
 split;[exact CALL|]. split;[exact NEXT|]. split;[exact (proj1 (proj2 SAFE))|exact I].
Qed.
Theorem episodes_append vi oi x events vm om y more vf of_ z :
 episode_trace vi oi x events vm om y -> episode_trace vm om y more vf of_ z ->
 episode_trace vi oi x (more++events) vf of_ z.
Proof.
 intros T U;induction T;[rewrite app_nil_r;exact U|].
 rewrite app_assoc;eapply episodes_cons;eauto.
Qed.


Theorem episode_prefixes vi oi initial events vf of_ f h a old d ram e id index entry span bytes dw bw dp bp :
 recovery_local_contracts of_ ranges decode ->
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ ((Logged (Ready f) h a,IdleBoundary old d ram),e) ->
 ranges entry=[span] -> free_range 256 (protection_table (data_next DataBegin ram)) span ->
 erased_object_extent sector f span -> outcome_writer_contracts g sector of_ bytes dw bw dp bp decode ->
 data_episode_post g sector data_len vf of_ marker ranges decode topology pages dw bw dp bp old id d index entry span ram f h a e /\
 data_episode_delivery g sector data_len vf of_ marker ranges decode topology pages dw bw old id d index entry span ram f h a e.
Proof.
 intros C INIT RUN RANGE FREE BLANK W.
 eapply enriched_data_episode_freer; eauto.
 exact (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT RUN)).
Qed.

Theorem episode_uncertain_no_hybrid vi oi f h a root initial_decoded initial_ram initial_e events
 vm om j phase old before candidate after receipts later vf of_ jf chosen decoded ram ef :
 Safe vi oi ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) ->
 episode_trace vi oi ((Logged (Ready f) h a,IdleBoundary root initial_decoded initial_ram),initial_e) events
   vm om ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) ->
 episode_trace vm om ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) later
   vf of_ ((jf,RebuildingBoundary (Usable chosen decoded ram)),forget_volatile_evidence (ef)) ->
 publications jf=publications j ->
 ((chosen=old /\ decoded=before) \/ (chosen=candidate /\ decoded=after)) /\ data_caller DataBegin ram.
Proof.
 intros INIT PREFIX SUFFIX HIST.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT PREFIX)) as SAFE.
 pose proof (initialized_history_nonempty sector data_len vi oi marker ranges decode pages _ _ _ _ _ _ _ INIT) as NONEMPTY.
 destruct (episode_history_extension _ _ _ _ _ _ _ INIT PREFIX) as [prefix EXT].
 assert (N:publications j<>[]).
 { change (publications j=prefix++h) in EXT. intro EMPTY;rewrite EMPTY in EXT.
   symmetry in EXT;apply app_eq_nil in EXT;tauto. }
 destruct (publications j) as [|head tail] eqn:PUBLICATIONS; [contradiction|].
 assert (HEAD:hd_error (publications j)=Some (N.of_nat (N.to_nat head))).
 { rewrite PUBLICATIONS;rewrite N2Nat.id;reflexivity. }
 destruct (proj1 (proj2 (proj1 (proj2 SAFE))) _ HEAD) as [c [IN CID]].
 assert (SEL:selected_live ((j,phase),Evidence [Certificate old before;Certificate candidate after] receipts) c).
 { split;[exact IN|rewrite CID;exact HEAD]. }
 assert (HIST' : publications jf=publications j) by congruence.
 destruct (episode_no_publication_transport _ _ _ _ _ _ _ _ SAFE SEL SUFFIX HIST') as [LAST [SAME KEEP]].
 destruct (selected_usable_identity sector data_len vf of_ marker ranges decode pages _ _ _ _ _ _ LAST SAME)
  as [ID [IMAGE CALL]].
 split;[|exact CALL]. simpl in IN;destruct IN as [C|[C|NO]];[left|right|contradiction];subst c;split;assumption.
Qed.

Theorem two_episode_returns_witness valid view bytes1 dw1 bw1 dp1 bp1 bytes2 dw2 bw2 dp2 bp2
 x r1 j1 id1 d1 ram1 e1 r2 final :
 recovery_local_contracts view ranges decode ->
 outcome_writer_contracts g sector view bytes1 dw1 bw1 dp1 bp1 decode ->
 outcome_writer_contracts g sector view bytes2 dw2 bw2 dp2 bp2 decode ->
 boundary_step g sector data_len valid view marker ranges decode topology pages dw1 bw1
  x (Some r1) ((j1,ClientBoundary id1 d1 ram1),e1) ->
 boundary_step g sector data_len valid view marker ranges decode topology pages dw2 bw2
  ((j1,IdleBoundary id1 d1 ram1),e1) (Some r2) final ->
 episode_trace valid view x [r2;r1] valid view final.
Proof.
 intros C W1 W2 X1 X2.
 change (episode_trace valid view x ([r2]++emitted_receipts (Some r1)) valid view final).
 eapply episodes_cons;[eapply execute_services;[exact C|exact W1|exact X1]|].
 change (episode_trace valid view ((j1,ClientBoundary id1 d1 ram1),e1) ([r2]++emitted_receipts None) valid view final).
 eapply episodes_cons with (event:=None).
 - eapply execute_services;[exact C|exact W1|apply client_resume].
 - change (episode_trace valid view ((j1,IdleBoundary id1 d1 ram1),e1) ([]++emitted_receipts (Some r2)) valid view final).
   eapply episodes_cons;[eapply execute_services;[exact C|exact W2|exact X2]|apply episodes_nil].
Qed.


Lemma certified_boot_raw valid view initial final e :
 Safe valid view ((boot_journal initial,RebuildingBoundary (boot_pc initial)),forget_volatile_evidence (e)) ->
 raw_order sector 256 data_len (boot_journal initial) ->
 (forall c, In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 clos_refl_trans boot_state (boot_step g sector data_len valid marker ranges decode topology pages) initial final ->
 raw_order sector 256 data_len (boot_journal final).
Proof.
 intros INV RAW LOCAL RUN; induction RUN.
 - pose proof (boot_projection g sector data_len valid view marker ranges decode topology pages
     x y (proj2 (proj1 INV)) H) as PROJ.
   destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [_ [_ LOG]].
   exact (logged_trace_preserves_raw g sector 256 data_len valid _ _ G DIV (proj1 (proj1 INV)) RAW LOG).
 - exact RAW.
 - apply IHRUN2; [exact (proj1 (boundary_boot_prefix_safe g sector data_len valid view marker ranges decode topology pages
     G DIV _ _ _ INV LOCAL RUN1))|exact (IHRUN1 INV RAW)].
Qed.
Theorem episode_raw_preserves vi oi x event vf of_ y :
 Safe vi oi x -> raw_order sector 256 data_len (boundary_journal x) ->
 episode_step vi oi x event vf of_ y -> raw_order sector 256 data_len (boundary_journal y).
Proof.
 intros INV RAW RUN; destruct RUN.
 - eapply legacy_boundary_raw_preserves; eauto.
 - destruct H4 as [[P BLANK] WRITE].
   pose proof (raw_writer_prefix _ _ _ _ _ _ _ _ _ _ H WRITE) as R.
   unfold boundary_journal; simpl;unfold writer_exit_boundary;destruct (writer_end result);exact R.
 - destruct H6 as [[P BLANK] WRITE].
   pose proof (raw_writer_prefix _ _ _ _ _ _ _ _ _ _ H WRITE) as R.
   unfold boundary_journal; simpl;unfold writer_exit_boundary;destruct (writer_end result);exact R.
 - exact RAW.
 - exact (logged_step_preserves_raw g sector 256 data_len valid _ _ G DIV (proj1 (proj1 INV)) RAW H).
 - eapply certified_boot_raw; eauto.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact (proj1 (proj2 (proj2 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate boss
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8)))).
 - exact RAW.
 - exact RAW.
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ H1))).
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   destruct H0 as [before [PREFIX [BEFORE [STEP DEST]]]].
   eapply rt_trans;[exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX)))|apply rt_step;exact STEP].
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - eapply logged_trace_preserves_raw;[exact G|exact DIV|exact (proj1 (proj1 INV))|exact RAW|].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - pose proof (proj1 (proj2 (proj2 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8)))) as ORDER.
   unfold recycling_acquisition_boundary in ORDER;rewrite H9 in ORDER;exact ORDER.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - pose proof (proj2 (proj2 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4))) as ORDER.
   unfold writer_exit_boundary in ORDER;rewrite H6 in ORDER;exact ORDER.
 - exact (proj2 (proj2 (certified_outer_pair g sector data_len valid view marker ranges decode pages
     f h a old d s e ia ib ea eb ra rb pa pb wa wb validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H3) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H4 H5 H6
     ltac:(destruct (erased_admission_guards _ _ _ _ H7) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H8 H9 H10))).
 - exact RAW.
 - exact (proj2 (proj2 (proj2 (certified_operation_first g sector data_len valid view marker ranges decode pages
     f h a old d s e index entry r plan result validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H3 H4 H5)))).
 - exact RAW.
 - pose proof (proj2 (proj2 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4))) as ORDER.
   unfold boundary_journal,operation_writer_exit,writer_exit_boundary in *;destruct (writer_end result);exact ORDER.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - pose proof (proj2 (proj2 (pending_writer_consumes g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e p false plan result validate G DIV INV H H0 H1 H2 H3 H4))) as ORDER.
   unfold writer_exit_boundary in ORDER;rewrite H6 in ORDER;exact ORDER.
 - pose proof (proj1 (proj2 (proj2 (recycling_certified_acquisition g sector data_len valid view marker ranges decode pages
     f h a old previous image root s e recognize magic fuel req round alignment start r count result validate false
     G DIV INV H H0 H1 H2 H3 H4 H5 H6 H7 H8)))) as ORDER.
   unfold boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary in *;
     destruct (neutral_end_ result);exact ORDER.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - exact RAW.
 - destruct fatal;exact RAW.
 - exact RAW.

 - exact RAW.

 - exact RAW.

 - exact RAW.

Qed.
Theorem episode_trace_raw vi oi initial events vf of_ final :
 Safe vi oi initial -> raw_order sector 256 data_len (boundary_journal initial) ->
 episode_trace vi oi initial events vf of_ final ->
 Safe vf of_ final /\ raw_order sector 256 data_len (boundary_journal final).
Proof.
 intros INV RAW RUN;induction RUN;[split;assumption|].
 apply IHRUN.
 - exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)).
 - eapply episode_raw_preserves;eauto.
Qed.

(* Control facts, not a second storage invariant. These facts originate at
   DataBegin and survive the actual allocation/writer/install updates. *)
Definition external_structure (x:execution_boundary) :=
 match snd (fst x) with
 | OpenBoundary _ _ s | PublishingBoundary _ _ _ s =>
     exists saved, protection_saved s=[saved] /\ In marker (protection_base s)
 | OperationBoundary _ _ s =>
     exists saved, protection_saved s=[saved;saved] /\ In marker (protection_base s)
 | _ => True
 end.
Lemma episode_external_structure vi oi x event vf of_ y :
 Safe vi oi x -> external_structure x -> episode_step vi oi x event vf of_ y -> external_structure y.
Proof.
 intros INV STRUCT RUN;destruct RUN.
 - destruct H1;try exact I.
   match goal with X:context[reserved_execution] |- _ => destruct X end.
   + unfold collected_failure,external_structure; simpl;unfold failure_phase.
     destruct resolved;repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
   + exact I.
   + unfold collected_failure,external_structure; simpl;unfold failure_phase.
     destruct resolved;repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
   + exact I.
   + match goal with X:context[publication_execution] |- _ => destruct X end;exact I.
 - destruct H4 as [[P BLANK] WRITE].
   destruct STRUCT as [saved [STACK MARK]]. unfold writer_exit_boundary;destruct (writer_end result);try exact I.
   + exists saved;unfold snapshot_written;rewrite P;split;assumption.
   + exists saved;cbn [snapshot_error];unfold data_next;rewrite ?P;destruct (protection_frozen s);split;assumption.
   + exists saved;split;assumption.
 - destruct STRUCT as [saved [STACK MARK]].
   unfold writer_exit_boundary;rewrite H7;exists saved.
   destruct H6 as [[P BLANK] WRITE]. unfold snapshot_written;rewrite P;split;assumption.
 - destruct STRUCT as [saved [STACK MARK]]. exists saved.
   unfold exact_attach,data_next;rewrite H;simpl;split;assumption.
 - exact I.
 - exact I.
 - exact I.
 - pose proof (proj1 (proj1 (proj2 (proj1 INV)))) as [DI [F [STACK [P [CUR [BASE REST]]]]]].
   exists (protection_current ram++attached_ranges ram);split.
   + simpl;rewrite STACK;reflexivity.
   + change (In marker (protection_base ram));rewrite BASE;simpl;auto.
 - destruct STRUCT as [saved [STACK MARK]]. exists saved;destruct boss;split;assumption.
 - destruct STRUCT as [saved [STACK MARK]]. unfold recycling_acquisition_boundary,neutral_open_boundary;
     destruct (neutral_end_ result);try exact I. exists saved;destruct boss;split;assumption.
 - exact I.
 - destruct STRUCT as [saved [STACK MARK]]. exists saved.
   unfold install_candidate,data_next;rewrite H;simpl;split;assumption.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - destruct STRUCT as [saved [STACK MARK]]. exists saved;split;assumption.
 - unfold external_structure,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - unfold external_structure,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact STRUCT.
 - unfold external_structure,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact I.
 - exact I.
 - exists (protection_current s++attached_ranges s);split;[reflexivity|].
   pose proof (proj1 (proj1 (proj2 (proj1 INV)))) as [DI [F [STACK [P [CUR [BASE REST]]]]]].
   change (In marker (protection_base s));rewrite BASE;simpl;auto.
 - exact I.
 - pose proof (proj1 (proj2 (certified_operation_first g sector data_len valid view marker ranges decode pages
     f h a old d s e index entry r plan result validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H3 H4 H5))) as [STACK [BASE ACK]].
   exists (physical_authority (exact_member ranges (recovered_image d) index entry r (outer_local_begin s))).
   split;[exact STACK|rewrite BASE;simpl;auto].
 - exact STRUCT.
 - destruct STRUCT as [saved [STACK MARK]];destruct H4 as [[P BLANK] WRITE].
   unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);try exact I;
     exists saved;unfold snapshot_written,snapshot_error,snapshot_retain_error,data_next;
     rewrite ?P;split;assumption.
 - exists (physical_authority s);split;[reflexivity|destruct H as [STACK [BASE ACK]];simpl;rewrite BASE;simpl;auto].
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);try exact I;exact STRUCT.
 - destruct (proj2 (certified_operation_begin sector data_len valid view marker ranges decode pages j old d s e INV)) as [STACK [BASE ACK]].
   exists (physical_authority (outer_local_begin s));split;[exact STACK|rewrite BASE;simpl;auto].
 - destruct STRUCT as [saved [STACK MARK]];exists saved;unfold exact_attach,data_next;rewrite H;simpl;split;assumption.
 - exists (physical_authority s);split;[reflexivity|destruct H as [STACK [BASE ACK]];simpl;rewrite BASE;simpl;auto].
 - exists (physical_authority s);split;[reflexivity|destruct H as [STACK [BASE ACK]];simpl;rewrite BASE;simpl;auto].
 - exact STRUCT.
 - unfold external_structure,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact STRUCT.
 - destruct STRUCT as [saved [STACK MARK]]. exists saved;unfold data_next;split;assumption.
 - exact STRUCT.
 - exact I.
 - exact STRUCT.
 - exact STRUCT.
 - exact STRUCT.
 - exact STRUCT.
 - destruct fatal;exact I.
 - exact STRUCT.

 - unfold rehome_cached;rewrite H;unfold snapshot_rehome;rewrite H;exact STRUCT.

 - exact STRUCT.

 - unfold install_candidate_observed,install_candidate,data_next;rewrite H2;simpl.
   destruct STRUCT as [saved [STACK MARK]];exists saved;split;assumption.

Qed.
Theorem episode_trace_external_structure vi oi initial events vf of_ final :
 Safe vi oi initial -> external_structure initial -> episode_trace vi oi initial events vf of_ final ->
 external_structure final.
Proof.
 intros INV STRUCT TRACE;induction TRACE;[exact STRUCT|].
 apply IHTRACE;[exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H))|].
 eapply episode_external_structure;eauto.
Qed.

(* Physical producer shared by the historical single/pair shortcuts. *)
Lemma idle_member_marker valid view f h a old d s e index entry r plan result :
 Safe valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) ->
 free_range 256 (protection_table (outer_local_begin s)) r -> ranges entry=[r] ->
 writer_execution g sector r false f plan result ->
 unchanged [marker] (object_flash sector f) (object_flash sector (writer_flash result)) /\
 data_invariant (exact_member ranges (recovered_image d) index entry r (outer_local_begin s)) /\
 In marker (protection_base (exact_member ranges (recovered_image d) index entry r (outer_local_begin s))).
Proof.
 intros INV FREE RANGE WRITE.
 destruct (certified_operation_begin sector data_len valid view marker ranges decode pages
   (Logged (Ready f) h a) old d s e INV) as [INNER [STACK [BASE ACK]]].
 destruct (proj2 (proj1 INNER)) as [DI [NF [COR LINK]]].
 assert (P:pending_preparation (outer_local_begin s)=None).
 { reflexivity. }
 split.
 - eapply free_writer_marker_frame;[exact DI|rewrite BASE;simpl;auto|exact FREE| |exact WRITE].
   exact (proj1 (proj1 (proj1 (proj1 INV)))).
 - split.
   + exact (proj1 (exact_member_preserves ranges (recovered_image d) [recovered_boss d]
       index entry r (outer_local_begin s) DI NF P FREE RANGE COR)).
   + change (In marker (protection_base (outer_local_begin s)));rewrite BASE;simpl;auto.
Qed.

Lemma episode_step_marker_frame vi oi x event vf of_ y :
 Safe vi oi x -> external_structure x -> episode_step vi oi x event vf of_ y ->
 unchanged [marker] (boundary_objects sector x) (boundary_objects sector y).
Proof.
 intros INV STRUCT RUN;destruct RUN;try (intros kept address IN AT;reflexivity).
 all: try solve [eapply boundary_step_marker; eauto].
 all: try solve [match goal with W:pending_writer_run _ _ ?s ?p ?boss ?f ?plan ?result |- _ =>
   destruct STRUCT as [saved [STACK BASE]];
   destruct W as [[P BLANK] WRITE];
   pose proof (pending_writer_marker_frame g sector marker s p boss f plan result
     (proj1 (proj2 (proj1 INV))) BASE P (proj1 (proj1 (proj1 (proj1 INV)))) WRITE) as KEEP;
   unfold boundary_objects,boundary_journal,operation_writer_exit,writer_exit_boundary;
   destruct (writer_end result);exact KEEP end].
 all: try solve [match goal with W:recycling_run _ _ ?recognize ?magic ?r ?count ?f ?result,
   S:reusable_search _ ?fuel _ _ (protection_table ?s) ?req ?round ?alignment ?pages ?start=FoundRecyclable _,
   L:recognizer_local _ _, E:erase_geometry _ _ _ _ |- _ =>
   destruct STRUCT as [saved [STACK BASE]];
   pose proof (recycling_marker_frame g sector marker fuel recognize magic f s req round alignment pages start r count result
     L (proj1 (proj1 (proj1 (proj1 INV))))
     (proj1 (proj1 (proj1 (proj1 (proj2 (proj1 INV)))))) BASE S E W) as KEEP;
   unfold boundary_objects,boundary_journal,operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);exact KEEP end].
 all: try solve [destruct j as [ctrl pubs acks];destruct ctrl;intros kept address IN AT;reflexivity].
 all: try solve [destruct fatal;intros kept address IN AT;reflexivity].
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   apply (boundary_boot_objects_preserved g sector data_len valid view marker ranges decode topology pages
     G DIV _ _ _ INV H H0);lia.
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ H1))).
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|apply rt_step;exact H3].
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   destruct H0 as [before [PREFIX [BEFORE [STEP DEST]]]].
   eapply rt_trans;[exact (proj2 (proj2 (uncertain_trace_authorities _ _ _ _ _ _ _ _ PREFIX)))|apply rt_step;exact STEP].
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - intros kept address IN AT;unfold boundary_objects,object_flash.
   eapply logged_trace_frame_after_journal;[exact G|exact DIV|exact (proj1 (proj1 INV))| |lia].
   eapply rt_trans;[eapply successful_trace_is_logged;exact H2|].
   eapply rt_trans;[apply rt_step;exact H3|apply rt_step;apply record_step;apply reset_ready].
 - destruct (erased_admission_guards _ _ _ _ H3) as [FA BLANKA].
   destruct (idle_member_marker valid view f h a old d s e ia ea ra pa wa INV FA H6 H4)
     as [KEEP_A [DI BASE]].
   destruct (erased_admission_guards _ _ _ _ H7) as [FB BLANKB].
   pose proof (free_writer_marker_frame g sector marker
     (exact_member ranges (recovered_image d) ia ea ra (outer_local_begin s)) rb false
     (writer_flash wa) pb wb DI BASE FB
     (proj1 (writer_execution_locality _ _ _ _ _ _ _ (proj1 (proj1 (proj1 (proj1 INV)))) H4)) H8) as KEEP_B.
   intros kept address IN AT.
   change (object_flash sector (writer_flash wb) address=object_flash sector f address).
   rewrite (KEEP_B kept address IN AT);exact (KEEP_A kept address IN AT).
 - destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK].
   exact (proj1 (idle_member_marker valid view f h a old d s e index entry r plan result INV FREE H5 H3)).
Qed.

(* One initial physical fact; every intermediate safety/structure witness
   below is produced by the existing A11 induction, never requested anew. *)
Theorem episode_trace_marker_frame vi oi initial events vf of_ final :
 Safe vi oi initial -> external_structure initial ->
 episode_trace vi oi initial events vf of_ final ->
 unchanged [marker] (boundary_objects sector initial) (boundary_objects sector final).
Proof.
 intros INV STRUCT RUN;induction RUN;[intros kept address IN AT;reflexivity|].
 pose proof (episode_step_marker_frame _ _ _ _ _ _ _ INV STRUCT H) as KEEP.
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H)) as NEXT.
 pose proof (episode_external_structure _ _ _ _ _ _ _ INV STRUCT H) as SHAPE.
 specialize (IHRUN NEXT SHAPE).
 intros kept address IN AT;rewrite (IHRUN kept address IN AT);exact (KEEP kept address IN AT).
Qed.
Theorem episode_step_marker vi oi initial event vf of_ final :
 Safe vi oi initial -> external_structure initial -> marker_header_covered marker ->
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal initial))) ->
 episode_step vi oi initial event vf of_ final ->
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal final))).
Proof.
 intros INV STRUCT HEADER INITIAL RUN.
 eapply persistence_marker_transport;[exact HEADER| |exact INITIAL].
 exact (episode_step_marker_frame _ _ _ _ _ _ _ INV STRUCT RUN).
Qed.
Theorem episode_trace_marker vi oi initial events vf of_ final :
 Safe vi oi initial -> external_structure initial -> marker_header_covered marker ->
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal initial))) ->
 episode_trace vi oi initial events vf of_ final ->
 unchanged [marker] (boundary_objects sector initial) (boundary_objects sector final) /\
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal final))).
Proof.
 intros INV STRUCT HEADER INITIAL RUN.
 pose proof (episode_trace_marker_frame _ _ _ _ _ _ _ INV STRUCT RUN) as KEEP.
 split;[exact KEEP|]. eapply persistence_marker_transport;[exact HEADER|exact KEEP|exact INITIAL].
Qed.
Corollary episode_trace_marker_probe vi oi initial events vf of_ final area_len :
 Safe vi oi initial -> external_structure initial -> marker_header_covered marker ->
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal initial))) ->
 episode_trace vi oi initial events vf of_ final -> 8<=area_len ->
 persistence_marker_test sector area_len (control_image (journal_control (boundary_journal final)))=true.
Proof.
 intros INV STRUCT HEADER INITIAL RUN LEN;apply persistence_marker_test_spec;split;[exact LEN|].
 exact (proj2 (episode_trace_marker _ _ _ _ _ _ _ INV STRUCT HEADER INITIAL RUN)).
Qed.

Corollary initialized_episode_trace_marker vi oi j id decoded ram e events vf of_ final :
 Safe vi oi ((j,IdleBoundary id decoded ram),e) -> marker_header_covered marker ->
 persistence_marker_recognized sector (control_image (journal_control j)) ->
 episode_trace vi oi ((j,IdleBoundary id decoded ram),e) events vf of_ final ->
 unchanged [marker] (object_flash sector (control_image (journal_control j))) (boundary_objects sector final) /\
 persistence_marker_recognized sector (control_image (journal_control (boundary_journal final))).
Proof. intros INV HEADER INITIAL RUN;exact (episode_trace_marker _ _ _ _ _ _ _ INV I HEADER INITIAL RUN). Qed.

(* No duplicate saved image: this relation names the prestate already stored
   in the sole scope stack and the already protected physical authority. *)
Definition external_rollback_context (x:execution_boundary) :=
 match snd (fst x) with
 | OpenBoundary _ _ s | PublishingBoundary _ _ _ s => rollback_structure marker s
 | OperationBoundary _ _ s => operation_rollback_structure marker s
 | _ => True
 end.
Lemma episode_rollback_context vi oi x event vf of_ y :
 Safe vi oi x -> external_rollback_context x -> episode_step vi oi x event vf of_ y ->
 external_rollback_context y.
Proof.
 intros INV CTX RUN;destruct RUN.
 - destruct H1;try exact I.
   match goal with X:context[reserved_execution] |- _ => destruct X end.
   + unfold collected_failure,external_rollback_context;simpl;unfold failure_phase.
     destruct resolved;repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
   + exact I.
   + unfold collected_failure,external_rollback_context;simpl;unfold failure_phase.
     destruct resolved;repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
   + exact I.
   + match goal with X:context[publication_execution] |- _ => destruct X end;exact I.
 - destruct H4 as [[P BLANK] WRITE].
   unfold writer_exit_boundary;destruct (writer_end result);try exact I.
   + unfold external_rollback_context;simpl;unfold snapshot_written;rewrite P;exact CTX.
   + unfold external_rollback_context;simpl;unfold rollback_structure,snapshot_error,data_next in *.
     rewrite P;exact CTX.
   + exact CTX.
 - unfold writer_exit_boundary;rewrite H7.
   destruct H6 as [[P BLANK] WRITE]. unfold external_rollback_context;simpl.
   unfold snapshot_written;rewrite P;exact CTX.
 - unfold external_rollback_context;simpl;unfold exact_attach,data_next;rewrite H;exact CTX.
 - exact I.
 - exact I.
 - exact I.
 - pose proof (proj1 (proj1 (proj2 (proj1 INV)))) as [DI [F [STACK [P [CUR [BASE [PH ACK]]]]]]].
   unfold external_rollback_context,rollback_structure;simpl.
   rewrite STACK CUR BASE PH ACK;repeat split;reflexivity.
 - destruct boss;exact CTX.
 - unfold recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result);try exact I.
   destruct boss;exact CTX.
 - exact I.
 - unfold external_rollback_context;simpl;unfold install_candidate,data_next;rewrite H;exact CTX.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact CTX.
 - unfold external_rollback_context,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - unfold external_rollback_context,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact CTX.
 - unfold external_rollback_context,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact I.
 - exact I.
 - pose proof (proj1 (proj1 (proj2 (proj1 INV)))) as [DI [F [STACK [P [CUR [BASE [PH ACK]]]]]]].
   unfold external_rollback_context,rollback_structure,pair_accept,pair_body,exact_member,outer_local_begin;simpl.
   rewrite CUR BASE PH ACK;repeat split;reflexivity.
 - exact I.
 - exact (proj1 (proj2 (certified_operation_first g sector data_len valid view marker ranges decode pages
     f h a old d s e index entry r plan result validate G DIV INV H H0 H1
     ltac:(destruct (erased_admission_guards _ _ _ _ H2) as [FREE BLANK];split;[apply vacantb_spec|apply blankb_spec];assumption)
     H3 H4 H5))).
 - exact CTX.
 - destruct H4 as [[P BLANK] WRITE].
   unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);try exact I;
     unfold external_rollback_context,operation_rollback_structure,snapshot_written,snapshot_error,snapshot_retain_error,data_next in *;
     rewrite ?P;exact CTX.
 - exact (proj1 (proj2 (proj2 (certified_operation_cancel sector data_len valid view marker ranges decode pages
     f h a image root s e old d INV H H0 H1 H2)))).
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;
   destruct (neutral_end_ result);try exact I;exact CTX.
 - exact (proj2 (certified_operation_begin sector data_len valid view marker ranges decode pages j old d s e INV)).
 - unfold external_rollback_context,operation_rollback_structure,exact_attach,data_next in *;rewrite H;exact CTX.
 - destruct H as [STACK [BASE ACK]];unfold external_rollback_context,rollback_structure;simpl;auto.
 - exact (proj1 (proj2 (proj2 (certified_operation_cancel sector data_len valid view marker ranges decode pages
     f h a image root s e old d INV H H0 H1 H2)))).
 - exact CTX.
 - unfold external_rollback_context,failure_phase;destruct collection_enabled;[destruct resolved|];
     repeat match goal with |- context[if ?b then _ else _] => destruct b end;exact I.
 - exact CTX.
 - unfold external_rollback_context,operation_rollback_structure,data_next in *;exact CTX.
 - exact CTX.
 - exact I.
 - exact CTX.
 - exact CTX.
 - exact CTX.
 - exact CTX.
 - destruct fatal;exact I.
 - exact CTX.

 - unfold rehome_cached;rewrite H;unfold snapshot_rehome;rewrite H;exact CTX.

 - exact CTX.

 - unfold external_rollback_context;simpl;unfold install_candidate_observed,install_candidate,data_next;rewrite H2;exact CTX.

Qed.
Theorem episode_trace_rollback_context vi oi initial events vf of_ final :
 Safe vi oi initial -> external_rollback_context initial -> episode_trace vi oi initial events vf of_ final ->
 external_rollback_context final.
Proof.
 intros INV CTX TRACE;induction TRACE;[exact CTX|].
 apply IHTRACE;[exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INV H))|].
 eapply episode_rollback_context;eauto.
Qed.

Theorem operation_ensure_protection_from_trace vi oi initial events valid view j image root ram e :
 page_metadata_coherent initial ->
 episode_trace vi oi initial events valid view ((j,OperationBoundary image root ram),e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract ensure_protection_probe)
   ((j,OperationBoundary image root ram),e) true ((j,OperationBoundary image root ram),e) /\
 (forall final,~post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure ControllerAPI)
   controller_contract ensure_protection_probe) ((j,OperationBoundary image root ram),e) false final).
Proof.
 intros M TRACE;pose proof (episode_trace_pages _ _ _ _ _ _ _ M TRACE) as READY.
 split;[apply ensure_protection_probe_ready;exact READY|].
 intros final RUN;destruct (ensure_protection_probe_result _ _ _ RUN) as [E _].
 cbn in READY;cbn in E;rewrite READY in E;discriminate.
Qed.

(* Numeric reconstruction is consumed through the existing global induction.
   These contracts describe successful local decoder outputs, never table
   coverage or preservation of a transaction. *)
Theorem episode_trace_boot_numeric word_max vi oi initial events vf of_ j pc e :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ ((j,RebuildingBoundary pc),forget_volatile_evidence (e)) ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 phase_numeric word_max marker ranges (RebuildingBoundary pc).
Proof.
 intros INIT RUN MARK DEC.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT RUN)) as SAFE.
 exact (boot_numeric_from_local_decoding word_max sector data_len vf of_ marker ranges decode pages
   j pc MARK DEC (proj2 (proj1 SAFE))).
Qed.

Theorem episode_trace_idle_numeric word_max vi oi initial events vf of_ j id d ram e :
 Safe vi oi initial -> episode_trace vi oi initial events vf of_ ((j,IdleBoundary id d ram),e) ->
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 state_numeric word_max ram /\
 data_caller DataBegin ram /\ state_numeric word_max (data_next DataBegin ram).
Proof.
 intros INIT RUN MARK DEC.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT RUN)) as SAFE.
 pose proof (proj1 (Forall_forall _ _) (proj1 (proj1 (proj2 SAFE)))
   (Certificate id d) (proj2 (proj2 SAFE))) as [READ [BOSS OBJECTS]].
 cbn in READ,BOSS,OBJECTS.
 assert (RANGES:Forall (range_numeric word_max) (marker::root_extents (of_ id))).
 { constructor;[exact MARK|]. unfold root_extents;rewrite <- BOSS, <- OBJECTS.
   exact (DEC _ _ _ READ). }
 pose proof (proj1 (proj1 (proj2 (proj1 SAFE)))) as IDLE.
 pose proof (idle_numeric_from_ranges word_max of_ marker id ram IDLE RANGES) as NUM.
 pose proof (proj1 (episode_next_begin _ _ _ _ _ _ _ _ _ _ _ INIT RUN)) as CALL.
 split;[exact NUM|]. split;[exact CALL|].
 eapply data_numeric_preserves;[exact NUM|exact CALL|exact I].
Qed.

(* Complete numerical preservation for the SAME operational relation. *)
Theorem episode_step_numeric word_max vi oi x event vf of_ y :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi x -> phase_numeric word_max marker ranges (snd (fst x)) ->
 episode_step vi oi x event vf of_ y ->
 phase_numeric word_max marker ranges (snd (fst y)).
Proof.
 intros MARK DEC CAP GEO_BOUND INIT NUM RUN.
 pose proof (proj1 (episode_step_safe _ _ _ _ _ _ _ INIT RUN)) as FINAL.
 destruct RUN;cbn [fst snd phase_numeric] in NUM |- *.
 - exact (proj2 (boundary_step_numeric g sector data_len valid view marker ranges decode topology pages
     bytes dw bw dp bp G DIV H H0 word_max _ _ _ MARK DEC CAP INIT NUM H1)).
 - apply numeric_writer_exit;exact NUM.
 - apply numeric_writer_exit;exact NUM.
 - eapply numeric_attach_written;[exact NUM|exact H|exact H0| |exact H2].
   exact (proj1 (proj2 (proj2 (proj2 (proj1 INIT))))).
 - exact I.
 - eapply boot_numeric_from_local_decoding;[exact MARK|exact DEC|exact (proj2 (proj1 FINAL))].
 - exact (proj2 NUM).
 - apply numeric_begin_unconditionally;exact NUM.
 - apply numeric_reservation;[exact NUM|]. eapply range_numeric_monotone;[exact CAP|].
   exact (erased_admission_numeric _ _ _ _ H0).
 - apply numeric_acquisition;[exact NUM|]. eapply numeric_recycled_extent with (g:=g) (sector:=sector) (count:=count);[lia|exact GEO_BOUND|exact H7].
 - apply numeric_frozen_commands;[exact NUM| |exact H].
   exact (proj1 (proj2 (proj2 (proj1 INIT)))).
 - apply numeric_install;exact NUM.
 - eapply enriched_client_numeric;[exact MARK|exact DEC|exact FINAL].
 - apply numeric_frozen_commands;[|reflexivity|exact H3].
   unfold uncertain_return;eapply data_numeric_preserves;[|exact I|exact I].
   apply numeric_slot;[exact NUM|].
   exact (selected_numeric word_max sector view ranges decode error_j e DEC (proj1 (proj2 FINAL))).
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact NUM.
 - exact (numeric_snapshot_error word_max s false NUM).
 - apply numeric_failure_phase;apply numeric_close_ranges;[exact NUM|constructor|].
   unfold state_numeric in NUM;tauto.
 - apply numeric_failure_phase;apply numeric_close_ranges;[exact NUM|constructor|].
   unfold state_numeric in NUM;tauto.
 - exact NUM.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact I.
 - exact NUM.
 - apply numeric_failure_phase;apply numeric_close_ranges;[exact NUM|constructor|].
   unfold state_numeric in NUM;tauto.
 - exact I.
 - exact I.
 - assert (RA:range_numeric word_max ra) by
     (eapply range_numeric_monotone;[exact CAP|exact (erased_admission_numeric _ _ _ _ H3)]).
   assert (RB:range_numeric word_max rb) by
     (eapply range_numeric_monotone;[exact CAP|exact (erased_admission_numeric _ _ _ _ H7)]).
   unfold pair_accept;apply numeric_close_ranges.
   + unfold pair_body;eapply numeric_exact_member with (root:=[]);[|exact RB|reflexivity|unfold image_current_correspondence;cbn;rewrite app_nil_r;reflexivity|exact H10].
     eapply numeric_exact_member with (root:=[recovered_boss d]);[|exact RA|reflexivity| |exact H6].
     * apply numeric_begin_unconditionally,numeric_begin_unconditionally;exact NUM.
     * unfold image_current_correspondence;cbn;rewrite !app_nil_r.
       exact (proj2 (proj2 (proj2 (proj1 INIT)))).
   + constructor;[|constructor]. apply Forall_app;unfold state_numeric in NUM;tauto.
   + apply Forall_app;unfold state_numeric in NUM;tauto.
 - exact NUM.
 - eapply numeric_exact_member with (root:=[recovered_boss d]);[| |reflexivity| |exact H5].
   + apply numeric_begin_unconditionally,numeric_begin_unconditionally;exact NUM.
   + eapply range_numeric_monotone;[exact CAP|exact (erased_admission_numeric _ _ _ _ H2)].
   + unfold image_current_correspondence;cbn;rewrite !app_nil_r.
     exact (proj2 (proj2 (proj2 (proj1 INIT)))).
 - apply numeric_reservation;[exact NUM|].
   eapply range_numeric_monotone;[exact CAP|exact (erased_admission_numeric _ _ _ _ H0)].
 - apply numeric_operation_phase,numeric_writer_exit;exact NUM.
 - apply numeric_close_ranges;[exact NUM| |];unfold state_numeric in NUM;repeat constructor;tauto.
 - exact I.
 - eapply data_numeric_preserves;[exact NUM|exact H|exact I].
 - exact I.
 - exact I.
 - apply numeric_operation_phase,numeric_acquisition;[exact NUM|].
   eapply numeric_recycled_extent with (g:=g) (sector:=sector) (count:=count);[lia|exact GEO_BOUND|exact H7].
 - apply numeric_begin_unconditionally,numeric_begin_unconditionally;exact NUM.
 - eapply numeric_attach_written;[exact NUM|exact H|exact H0| |exact H2].
   exact (proj1 (proj2 (proj2 (proj2 (proj1 INIT))))).
 - apply numeric_close_ranges;[exact NUM| |];unfold state_numeric in NUM;repeat constructor;tauto.
 - apply numeric_close_ranges;[exact NUM| |];unfold state_numeric in NUM;repeat constructor;tauto.
 - exact NUM.
 - apply numeric_failure_phase;apply numeric_close_ranges;[exact NUM|constructor|].
   unfold state_numeric in NUM;tauto.
 - exact NUM.
 - eapply data_numeric_preserves;[exact NUM|exists p;exact H|exact I].
 - exact NUM.
 - eapply data_numeric_preserves;[exact NUM|exact H|exact I].
 - exact NUM.
 - exact NUM.
 - exact NUM.
 - exact NUM.
 - destruct fatal;exact I.
 - apply numeric_retain_error;exact NUM.

 - unfold rehome_cached;rewrite H;unfold remember_recovered_boss,update_validation,snapshot_rehome;rewrite H;unfold state_numeric,pending_ranges in NUM |- *;rewrite H in NUM;exact NUM.

 - exact NUM.

 - change (state_numeric word_max (install_candidate s));apply numeric_install;exact NUM.

Qed.

Theorem episode_trace_numeric word_max vi oi initial events vf of_ final :
 range_numeric word_max marker -> decoded_numeric_contract word_max ranges decode ->
 1024*256<=word_max -> area_start g+area_length g<=2*sector+1024*256 ->
 Safe vi oi initial -> phase_numeric word_max marker ranges (snd (fst initial)) ->
 episode_trace vi oi initial events vf of_ final ->
 Safe vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)).
Proof.
 intros MARK DEC CAP GEOM INIT NUM RUN;induction RUN;[auto|].
 apply IHRUN;[exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INIT H))|].
 eapply episode_step_numeric;eauto.
Qed.

(* Exact provenance of a materialized current image, separate from page coverage.
   Mutations invalidate the concrete current root even if their logical result
   happens to equal the prestate. *)
Definition current_root_origin (x:execution_boundary) :=
 let j:=boundary_journal x in let e:=snd x in
 match snd (fst x) with
 | OpenBoundary image root _ | OperationBoundary image root _ =>
   root=[] \/ exists id d,
     hd_error (publications j)=Some (N.of_nat id) /\
     In (Certificate id d) (live_certificates e) /\
     image=recovered_image d /\ root=[recovered_boss d]
 | _=>True end.
Lemma current_origin_selected valid view j image root s e old d :
 Safe valid view ((j,OpenBoundary image root s),e) ->
 current_root_origin ((j,OpenBoundary image root s),e) ->
 hd_error (publications j)=Some (N.of_nat old) -> In (Certificate old d) (live_certificates e) ->
 root=[] \/ image=recovered_image d /\ root=[recovered_boss d].
Proof.
 intros INV [EMPTY|[id [prior [HEAD [IN [IMAGE ROOT]]]]]] HEAD' IN';[auto|].
 assert (EQ:Certificate id prior=Certificate old d).
 { eapply selected_live_unique;[exact INV|split;assumption|split;assumption]. }
 inversion EQ;subst;auto.
Qed.

Lemma episode_step_current_origin vi oi x event vf of_ y :
 Safe vi oi x -> current_root_origin x -> episode_step vi oi x event vf of_ y ->
 current_root_origin y.
Proof.
 intros INV ORIGIN RUN;destruct RUN;cbn [current_root_origin boundary_journal fst snd] in ORIGIN |- *;
 try exact I;try exact ORIGIN;try (left;reflexivity).

 - { destruct H1;try exact I.
   match goal with R:context[reserved_execution] |- _=>destruct R end.
   all: try (match goal with R:context[publication_execution] |- _=>destruct R end);try exact I.
   all: unfold current_root_origin,collected_failure;cbn;unfold failure_phase;
     repeat match goal with |- context[if ?b then _ else _]=>destruct b end;
     try destruct resolved;exact I. }
 - pose proof (current_origin_selected valid view _ image root s e old previous INV ORIGIN H0 H1) as SHAPE.
   unfold writer_exit_boundary;destruct (writer_end result);cbn [current_root_origin boundary_journal fst snd];try exact I;
   (destruct SHAPE as [EMPTY|[IMAGE ROOT]];[left;exact EMPTY|right;exists old,previous;repeat split;auto;simpl;auto]).
 - pose proof (current_origin_selected valid view _ image root s e old previous INV ORIGIN H0 H1) as SHAPE.
   unfold writer_exit_boundary;destruct (writer_end result);cbn [current_root_origin boundary_journal fst snd];try exact I;
   (destruct SHAPE as [EMPTY|[IMAGE ROOT]];[left;exact EMPTY|right;exists old,previous;repeat split;auto;simpl;auto]).
 - right;exists id,d;split.
   + pose proof (proj1 (proj2 (proj1 INV))) as J;exact (proj1 (proj2 (proj2 (proj2 J)))).
   + split;[exact (proj2 (proj2 INV))|auto].
 - pose proof (current_origin_selected valid view _ image root s e old previous INV ORIGIN H0 H1) as SHAPE.
   unfold recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result);
   cbn [current_root_origin boundary_journal fst snd];try exact I;
   (destruct SHAPE as [EMPTY|[IMAGE ROOT]];[left;exact EMPTY|right;exists old,previous;repeat split;auto;simpl;auto]).
 - unfold current_root_origin;cbn;unfold failure_phase;destruct collection_enabled;[destruct resolved|];
   repeat match goal with |- context[if ?b then _ else _]=>destruct b end;exact I.
 - unfold current_root_origin;cbn;unfold failure_phase;destruct collection_enabled;[destruct resolved|];
   repeat match goal with |- context[if ?b then _ else _]=>destruct b end;exact I.
 - unfold current_root_origin;cbn;unfold failure_phase;destruct collection_enabled;[destruct resolved|];
   repeat match goal with |- context[if ?b then _ else _]=>destruct b end;exact I.
 - pose proof (current_origin_selected valid view _ image root s e old previous INV ORIGIN H0 H1) as SHAPE.
   unfold operation_writer_exit,writer_exit_boundary;destruct (writer_end result);
   cbn [operation_phase current_root_origin boundary_journal fst snd];try exact I;
   (destruct SHAPE as [EMPTY|[IMAGE ROOT]];[left;exact EMPTY|right;exists old,previous;repeat split;auto;simpl;auto]).
 - right;exists old,d;repeat split;auto.
 - pose proof (current_origin_selected valid view _ image root s e old previous INV ORIGIN H0 H1) as SHAPE.
   unfold operation_acquisition_boundary,recycling_acquisition_boundary,neutral_open_boundary;destruct (neutral_end_ result);
   cbn [operation_phase current_root_origin boundary_journal fst snd];try exact I;
   (destruct SHAPE as [EMPTY|[IMAGE ROOT]];[left;exact EMPTY|right;exists old,previous;repeat split;auto;simpl;auto]).
 - right;exists old,d;split.
   + pose proof (proj1 (proj2 (proj1 INV))) as J;exact (proj1 (proj2 (proj2 (proj2 J)))).
   + split;[exact (proj2 (proj2 INV))|auto].
 - right;exists old,d;repeat split;auto.
 - unfold current_root_origin;cbn;unfold failure_phase;destruct collection_enabled;[destruct resolved|];
   repeat match goal with |- context[if ?b then _ else _]=>destruct b end;exact I.
 - destruct fatal;exact I.
Qed.

Theorem episode_trace_current_origin vi oi initial events vf of_ final :
 Safe vi oi initial -> current_root_origin initial ->
 episode_trace vi oi initial events vf of_ final -> current_root_origin final.
Proof.
 intros INIT ROOT RUN;induction RUN;[exact ROOT|].
 apply IHRUN;[exact (proj1 (episode_step_safe _ _ _ _ _ _ _ INIT H))|].
 eapply episode_step_current_origin;eauto.
Qed.

Definition address_option_eqb (a b:option nat) := match a,b with
 | None,None=>true | Some x,Some y=>Nat.eqb x y | _,_=>false end.
Definition rust_dirty_observer active current outer :=
 andb active (negb (address_option_eqb current outer)).
Theorem phase_dirty_matches_roots valid view f h a image root s e old :
 Safe valid view ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 current_root_origin ((Logged (Ready f) h a,OpenBoundary image root s),e) ->
 hd_error h=Some (N.of_nat old) ->
 phase_dirty (OpenBoundary image root s)=
 rust_dirty_observer true (root_address root) (root_address (physical_authority s)).
Proof.
 intros INV ROOT HEAD.
 assert (PH:physical_authority s=root_extents (view old)).
 { pose proof (proj2 (proj2 (proj2 (proj2 (proj1 INV))))) as LINK.
   unfold protection_history_link in LINK;cbn in LINK;rewrite HEAD in LINK;cbn in LINK;
   rewrite Nat2N.id in LINK;exact LINK. }
 rewrite PH. destruct ROOT as [EMPTY|[id [d [H [IN [IMAGE ROOT]]]]]].
 - subst root;reflexivity.
 - assert (ID:id=old) by (apply Nat2N.inj;cbn [boundary_journal fst snd publications] in H;congruence);subst id root.
   pose proof (proj1 (Forall_forall _ _) (proj1 (proj1 (proj2 INV))) (Certificate old d) IN) as [READ [B O]].
   cbn in B. unfold phase_dirty,rust_dirty_observer,root_address,root_extents,address_option_eqb;cbn.
   rewrite B;rewrite Nat.eqb_refl;reflexivity.
Qed.
Lemma replacement_remains_dirty image s : phase_dirty (OpenBoundary image [] s)=true.
Proof. reflexivity. Qed.


Lemma ordinary_delivery_execution valid view j phase e route :
 controller_caller DeliverOwned phase (controller_read e) ->
 finish_selected (controller_read e)=Some route ->
 operation_execution valid view ((j,phase),e) [] valid view
   ((j,phase),controller_evidence DeliverOwned phase e) (ReturnedOrdinary route).
Proof.
 intros CALL ROUTE;eapply operation_end with (event:=None).
 - apply controller_episode;exact CALL.
 - destruct CALL as [ARM [CLOSED [PENDING PHASE]]].
   destruct phase;try contradiction;unfold edge_exit;cbn [fst snd];rewrite ROUTE;
   change ((if owner_armed (controller_read e) then None
     else if owner_armed (controller_read e) then None
     else if outer_live (controller_read e) then None else Some (ReturnedOrdinary route))=Some (ReturnedOrdinary route));
   rewrite ARM;rewrite CLOSED;reflexivity.
Qed.

Lemma body_delivery_execution valid view j phase e :
 controller_caller DeliverBodyError phase (controller_read e) ->
 operation_execution valid view ((j,phase),e) [] valid view
   ((j,phase),controller_evidence DeliverBodyError phase e) ReturnedBodyError.
Proof.
 intro CALL;eapply operation_end with (event:=None).
 - apply controller_episode;exact CALL.
 - destruct CALL as [BODY [NOFIN [ARM [CLOSED PHASE]]]].
   destruct phase;try contradiction;unfold edge_exit;cbn [fst snd];rewrite NOFIN;
   change ((if body_error_pending (controller_read e) then
     if owner_armed (controller_read e) then None else
     if owner_armed (controller_read e) then None else
     if outer_live (controller_read e) then None else Some ReturnedBodyError
     else None)=Some ReturnedBodyError);
   rewrite BODY;rewrite ARM;rewrite CLOSED;reflexivity.
Qed.
Lemma body_error_blocks_finish phase c : body_error_pending c=true ->
 ~ controller_caller SelectFinish phase c.
Proof. intros BODY CALL;destruct CALL as [_ [_ [_ [_ [_ PHASE]]]]];destruct phase;cbn in PHASE;congruence. Qed.
Lemma body_error_survives_abort_and_cleanup c :
 body_error_pending (control_drop_owner (control_close_local (control_take_local false (control_abort (control_body_error c)))))=true /\
 finish_selected (control_drop_owner (control_close_local (control_take_local false (control_abort (control_body_error c)))))=None.
Proof. split;reflexivity. Qed.

Lemma controller_ordinary_edge_is_delivery j phase e action route :
 controller_caller action phase (controller_read e) ->
 edge_exit ((j,phase),e) None ((j,phase),controller_evidence action phase e)=Some (ReturnedOrdinary route) ->
 action=DeliverOwned.
Proof.
 destruct e as [certs receipts [control|] metadata roots];
 [destruct control as [ab outer owns armed local taken selected body]|];
 intros CALL RETURN;destruct phase;destruct action;cbn in *;
 try reflexivity;try solve [intuition discriminate];
 try destruct current;try destruct selected;try destruct armed;try destruct body;try destruct outer;cbn in *;intuition discriminate.
Qed.
Lemma beginning_another_operation_is_not_delivery j id d ram e :
 edge_exit ((j,IdleBoundary id d ram),e) None
   ((j,IdleBoundary id d ram),controller_evidence ArmOwned (IdleBoundary id d ram) e)=None.
Proof.
 unfold edge_exit;cbn [fst snd controller_evidence evidence_with_control controller_update controller_read control_begin Control].
 destruct (finish_selected (controller_read e));destruct (owner_armed (controller_read e));destruct (body_error_pending (controller_read e));reflexivity.
Qed.
Lemma ordinary_delivery_no_second_return phase e :
 ~controller_caller DeliverOwned phase (controller_read (controller_evidence DeliverOwned phase e)).
Proof. intros [_ [_ [BAD _]]];apply BAD;reflexivity. Qed.
Lemma ordinary_delivery_no_storage j phase e :
 fst ((j,phase),controller_evidence DeliverOwned phase e)=(j,phase) /\
 boundary_receipts ((j,phase),controller_evidence DeliverOwned phase e)=client_receipts e.
Proof. split;reflexivity. Qed.
Lemma operation_execution_control vi oi x events vf of_ y exit :
 operation_execution vi oi x events vf of_ y exit -> terminal_control_absent y.
Proof.
 intro RUN;induction RUN.
 - eapply episode_step_control;exact H.
 - exact IHRUN.
 - exact H.
 - exact H.
 - exact I.
Qed.

Theorem delimited_publication_is_actual_delivery vi oi x events vf of_ y receipt :
 Safe vi oi x ->
 operation_execution vi oi x events vf of_ y (ReturnedPublished receipt) ->
 historical_delivery receipt.
Proof.
 intros INIT RUN.
 pose proof (operation_execution_trace _ _ _ _ _ _ _ _ RUN) as TRACE.
 destruct (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT TRACE) as [_ [_ [_ DELIVERED]]].
 rewrite (operation_execution_receipts _ _ _ _ _ _ _ _ RUN) in DELIVERED.
 exact (Forall_inv DELIVERED).
Qed.

(* These consumers use the existing step, including its writer/journal/service
   premises. They do not accept a safe destination or an expected result. *)
Lemma published_operation_execution vi oi x receipt vf of_ y :
 episode_step vi oi x (Some receipt) vf of_ y ->
 operation_execution vi oi x [receipt] vf of_ y (ReturnedPublished receipt).
Proof. intro RUN;eapply operation_end with (event:=Some receipt);[exact RUN|reflexivity]. Qed.
Lemma stopped_operation_execution vi oi x vf of_ j phase e :
 episode_step vi oi x None vf of_ ((j,phase),e) ->
 (phase=FatalBoundary \/ exists pc,phase=RebuildingBoundary pc) ->
 exists exit, operation_execution vi oi x [] vf of_ ((j,phase),e) exit /\
 exit_observation exit=None.
Proof.
 intros RUN [EQ|[pc EQ]];subst phase.
 - exists InterruptedFatal;split;[eapply operation_end with (event:=None);[exact RUN|reflexivity]|reflexivity].
 - exists InterruptedReset;split;[eapply operation_end with (event:=None);[exact RUN|reflexivity]|reflexivity].
Qed.
Theorem operation_then_continuation vi oi x events vm om returned exit later vf of_ final :
 operation_execution vi oi x events vm om returned exit ->
 episode_trace vm om returned later vf of_ final ->
 episode_trace vi oi x (later++events) vf of_ final /\
 events=match exit with ReturnedPublished r=>[r]|_=>[] end.
Proof.
 intros OP CONT;split.
 - eapply episodes_append;[eapply operation_execution_trace;exact OP|exact CONT].
 - eapply operation_execution_receipts;exact OP.
Qed.

(* A resume is outside the marked execution: the already delivered success
   survives even though the destination is Idle and no longer Client. *)
Corollary published_then_resume vi oi x events valid view j id d ram e receipt :
 operation_execution vi oi x events valid view ((j,ClientBoundary id d ram),e)
   (ReturnedPublished receipt) ->
 episode_trace vi oi x events valid view ((j,IdleBoundary id d ram),e) /\
 exit_observation (ReturnedPublished receipt)=Some RetainedResult /\ events=[receipt].
Proof.
 intro OP;pose proof (operation_execution_receipts _ _ _ _ _ _ _ _ OP) as RECEIPT.
 split.
 - eapply episodes_append with (more:=[]);[eapply operation_execution_trace;exact OP|].
   eapply episodes_cons with (events:=[]) (event:=None);[apply resume_client_episode|constructor].
 - split;[reflexivity|exact RECEIPT].
Qed.
Theorem two_delimited_operations vi oi x first vm om y first_exit second vf of_ z second_exit :
 operation_execution vi oi x first vm om y first_exit ->
 operation_execution vm om y second vf of_ z second_exit ->
 episode_trace vi oi x (second++first) vf of_ z /\
 forall observations,
 append_operation_observation (append_operation_observation observations first_exit) second_exit =
 observations ++
   (match exit_observation first_exit with Some r=>[r]|None=>[] end) ++
   (match exit_observation second_exit with Some r=>[r]|None=>[] end).
Proof.
 intros FIRST SECOND;split.
 - eapply episodes_append;[eapply operation_execution_trace;exact FIRST|eapply operation_execution_trace;exact SECOND].
 - intro observations;unfold append_operation_observation;
   destruct (exit_observation first_exit);destruct (exit_observation second_exit);
   cbn;repeat rewrite app_nil_r;try reflexivity;rewrite <- app_assoc;reflexivity.
Qed.


(* A marked endpoint of the existing cumulative trace. The prefix includes
   cleanup and owner consumption; the delimited tail ends at actual delivery.
   No destination invariant or expected result is a premise. *)
Definition completed_operation vi oi initial events vf of_ final exit :=
 exists vm om before previous returned,
 episode_trace vi oi initial previous vm om before /\
 operation_execution vm om before returned vf of_ final exit /\
 events=returned++previous.
Lemma completed_operation_trace vi oi initial events vf of_ final exit :
 completed_operation vi oi initial events vf of_ final exit ->
 episode_trace vi oi initial events vf of_ final.
Proof.
 intros [vm [om [before [previous [returned [PREFIX [TAIL EQ]]]]]]];subst events.
 eapply episodes_append;[exact PREFIX|eapply operation_execution_trace;exact TAIL].
Qed.
Lemma completed_operation_control vi oi initial events vf of_ final exit :
 completed_operation vi oi initial events vf of_ final exit -> terminal_control_absent final.
Proof.
 intros [vm [om [before [previous [returned [PREFIX [TAIL EQ]]]]]]].
 eapply operation_execution_control;exact TAIL.
Qed.
Lemma completed_operation_owner_closed vi oi initial events vf of_ final exit :
 completed_operation vi oi initial events vf of_ final exit ->
 exit_observation exit<>None -> delivered_owner_closed (snd final).
Proof.
 intros [vm [om [before [previous [returned [PREFIX [RUN EQ]]]]]]] OBS.
 eapply operation_execution_owner_closed;eassumption.
Qed.

Lemma completed_publication_from_trace vi oi initial events valid view source receipt vf of_ final :
 episode_trace vi oi initial events valid view source ->
 episode_step valid view source (Some receipt) vf of_ final ->
 completed_operation vi oi initial ([receipt]++events) vf of_ final (ReturnedPublished receipt).
Proof.
 intros PREFIX RETURN;exists valid,view,source,events,[receipt].
 split;[exact PREFIX|]. split;[apply published_operation_execution;exact RETURN|reflexivity].
Qed.
Theorem completed_error_then_success vi oi initial first vm om middle second vf of_ final receipt :
 completed_operation vi oi initial first vm om middle (ReturnedOrdinary FinishPublish) ->
 completed_operation vm om middle second vf of_ final (ReturnedPublished receipt) ->
 episode_trace vi oi initial (second++first) vf of_ final /\
 append_operation_observation
   (append_operation_observation [] (ReturnedOrdinary FinishPublish))
   (ReturnedPublished receipt)=[FinalizationError;RetainedResult].
Proof.
 intros FIRST SECOND;split;[|reflexivity].
 eapply episodes_append;[eapply completed_operation_trace;exact FIRST|eapply completed_operation_trace;exact SECOND].
Qed.
Lemma delivered_owned_observation {A E P} route (value:A) (failure:E) (payload:list P)
 sw1 sw2 error1 error2 :
 (observe_retained_or_aborted true value failure (ordinary_result route),
  observe_apdu (ordinary_result route) payload sw1 sw2 error1 error2)=
 match route with
 | FinishClean=>(OperationValue value,(payload,sw1,sw2))
 | FinishAbort=>(OperationInvalidState,observe_apdu AbortedResult payload sw1 sw2 error1 error2)
 | FinishPublish=>(OperationError failure,observe_apdu FinalizationError payload sw1 sw2 error1 error2)
 end.
Proof. destruct route;reflexivity. Qed.

Lemma completed_reset_from_trace vi oi initial events valid view source vf of_ j pc e :
 episode_trace vi oi initial events valid view source ->
 episode_step valid view source None vf of_ ((j,RebuildingBoundary pc),e) ->
 completed_operation vi oi initial events vf of_ ((j,RebuildingBoundary pc),e) InterruptedReset /\
 forall observations, append_operation_observation observations InterruptedReset=observations.
Proof.
 intros PREFIX CUT;split;[|reflexivity].
 exists valid,view,source,events,[];split;[exact PREFIX|]. split;[|reflexivity].
 eapply operation_end with (event:=None);[exact CUT|reflexivity].
Qed.
Lemma joined_operation_has_no_owned_delivery phase c :
 ~controller_caller DeliverOwned phase (control_join c).
Proof. intros [_ [_ [BAD _]]];apply BAD;reflexivity. Qed.

(* The usable boot transition derives the range and both arithmetic arguments
   from the SAME decoder output. No pre-reset allocation observation is read. *)
Lemma episode_trace_decoder_source vi oi initial events vf of_ final :
 episode_trace vi oi initial events vf of_ final ->
 counter_decoder (snd final)=counter_decoder (snd initial).
Proof.
 intro RUN;induction RUN;[reflexivity|].
 rewrite IHRUN;eapply episode_step_counter_source;exact H.
Qed.
Theorem resume_allocation_bounded_from_trace word_max vi oi initial events valid view j id d ram e :
 Safe vi oi initial ->
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_numeric_contract word_max ranges decode ->
 episode_trace vi oi initial events valid view
   ((j,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence e) ->
 let rebuilt:=recovered_page_evidence j id (forget_volatile_evidence e) in
 episode_trace vi oi initial events valid view ((j,IdleBoundary id d ram),rebuilt) /\
 Safe valid view ((j,IdleBoundary id d ram),rebuilt) /\
 volatile_allocation rebuilt=Some (allocation_from_decoded d) /\
 extent_end (recovered_boss d)<=word_max /\
 Nat.min word_max (extent_end (recovered_boss d))=extent_end (recovered_boss d).
Proof.
 intros INIT MATCH NUM PREFIX rebuilt.
 assert (ALL:episode_trace vi oi initial events valid view ((j,IdleBoundary id d ram),rebuilt)).
 { eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply resume_episode|constructor]. }
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT ALL)) as SAFE.
 pose proof (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ SAFE) as READ.
 pose proof (episode_trace_decoder_source _ _ _ _ _ _ _ PREFIX) as SOURCE.
 cbn in SOURCE.
 assert (LOCAL:generation_decoding_matches sector decode (counter_decoder e))
   by (rewrite SOURCE;exact MATCH).
 destruct (decoded_allocation_usize word_max sector ranges decode (counter_decoder e)
   (control_image (journal_control j)) id d NUM LOCAL READ) as [OBS BOUND].
 split;[exact ALL|]. split;[exact SAFE|]. split;[exact OBS|exact BOUND].
Qed.

(* Weak simulation of the RAM-only acquisition interval. No reserve/Drop is
   executed on the reset branch: all three concrete prefixes project to this
   same physical reset, so the existing reset step covers their observation. *)
Theorem erased_ram_cut_from_trace word_max vi oi initial events valid view f h a image root s e r boss point phase :
 Safe vi oi initial ->
 episode_trace vi oi initial events valid view ((Logged (Ready f) h a,phase),e) ->
 (phase=OpenBoundary image root s \/ phase=OperationBoundary image root s) ->
 pending_preparation s=None -> pages*256<=word_max ->
 runtime_erased_admission sector pages e s f r ->
 let dest:=acquisition_ram_reset point boss r s e (Logged (Ready f) h a) in
 episode_trace vi oi initial events valid view dest /\ Safe valid view dest /\
 boundary_receipts dest=events++boundary_receipts initial /\
 volatile_allocation (snd dest)=None /\ extent_end r<=word_max.
Proof.
 intros INIT PREFIX PHASE P CAP ADMIT dest.
 destruct (runtime_erased_advance_bounded sector pages e s f r word_max CAP ADMIT) as [BOUND SAT].
 assert (ALL:episode_trace vi oi initial events valid view dest).
 { unfold dest;rewrite acquisition_ram_reset_same.
   eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   apply reset_episode;apply record_step;apply reset_ready. }
 pose proof (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT ALL) as [SAFE [OBS REST]].
 split;[exact ALL|]. split;[exact SAFE|]. split;[exact OBS|].
 split;[unfold dest;rewrite acquisition_ram_reset_same;reflexivity|exact BOUND].
Qed.

Theorem recovered_found_erased_from_trace word_max vi oi initial events valid view f h a id d ram e
 bytes fuel recognize round alignment i n boss :
 Safe vi oi initial ->
 generation_decoding_matches sector decode (counter_decoder (snd initial)) ->
 decoded_numeric_contract word_max ranges decode -> decoded_allocation_geometry pages decode ->
 pages*256<=word_max -> pages<=1024 ->
 episode_trace vi oi initial events valid view
   ((Logged (Ready f) h a,RebuildingBoundary (Usable id d ram)),forget_volatile_evidence e) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector (pages*256) bytes (extent_end (recovered_boss d)) f)
   (probe_cursor_checked word_max)) (data_next DataBegin ram) ProbeMiss (data_next DataBegin ram) ->
 reusable_search sector fuel recognize f (protection_table (data_next DataBegin ram))
   (search_requirement word_max bytes) round alignment pages (extent_end (recovered_boss d)/256)=FoundErased i n ->
 let rebuilt:=recovered_page_evidence (Logged (Ready f) h a) id (forget_volatile_evidence e) in
 let dest:=((Logged (Ready f) h a,OpenBoundary (recovered_image d) [recovered_boss d]
   (reservation_state boss (block_pages i n) (data_next DataBegin ram))),
   advance_allocation_evidence (block_pages i n) rebuilt) in
 episode_trace vi oi initial events valid view dest /\ Safe valid view dest /\
 Nat.min word_max (extent_end (recovered_boss d))=extent_end (recovered_boss d) /\
 volatile_allocation (snd dest)=Some (AllocationRuntime (extent_end (block_pages i n)) (recovered_boss d)).
Proof.
 intros INIT MATCH NUM GEOM CAP LIMIT PREFIX PROBE SEARCH rebuilt dest.
 destruct (resume_allocation_bounded_from_trace word_max _ _ _ _ _ _ _ _ _ _ _ INIT MATCH NUM PREFIX)
   as [RESUME [READY [OBS [BOUND SAT]]]].
 pose proof (generation_ready_read _ _ _ _ _ _ _ _ _ _ _ _ _ READY) as READ.
 pose proof (episode_trace_decoder_source _ _ _ _ _ _ _ PREFIX) as SOURCE;cbn in SOURCE.
 assert (LOCAL:generation_decoding_matches sector decode (counter_decoder e)) by (rewrite SOURCE;exact MATCH).
 destruct (recovered_runtime_search_inputs sector pages word_max decode (Logged (Ready f) h a)
   id e d (data_next DataBegin ram) bytes LOCAL GEOM CAP READ PROBE) as [INPUTS SATURATE].
 assert (ADMIT:runtime_erased_admission sector pages rebuilt (data_next DataBegin ram) f (block_pages i n)).
 { eapply runtime_search;[exact INPUTS|exact SEARCH|reflexivity|exact LIMIT]. }
 pose proof (proj1 (episode_next_begin _ _ _ _ _ _ _ _ _ _ _ INIT RESUME)) as CALL.
 assert (ALL:episode_trace vi oi initial events valid view dest).
 { eapply episodes_append with (more:=[]);[exact RESUME|].
   eapply episodes_cons with (event:=None) (events:=[]);[apply begin_episode|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   apply acquire_erased;[reflexivity|eapply runtime_erased_admission_forget;exact ADMIT|].
   eapply runtime_erased_admission_mapped;exact ADMIT. }
 split;[exact ALL|]. split;[exact (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT ALL))|].
 split;[exact SAT|]. unfold dest;cbn [snd];exact (advance_allocation_observed _ _ _ OBS).
Qed.

(* The runtime assignments are RAM-only. A cut before, between, or after them
   has the same physical A10 entry, but never records a client receipt. *)
Theorem append_runtime_cut_from_trace vi oi initial events valid view ready id d s e saved
 out slot pubs acks point :
 Safe vi oi initial ->
 episode_trace vi oi initial events valid view ((ready,PublishingBoundary CandidatePrepared id d s),e) ->
 (forall c,In c (live_certificates e) -> incarnation_reader_local ranges decode c) ->
 protection_saved s=[saved] -> In marker (protection_base s) ->
 clos_refl_trans logged_state (successful_logged_step g sector 256 data_len valid (N.of_nat id))
   ready (Logged (AwaitAck out slot (N.of_nat id)) pubs acks) ->
 logged_step g sector 256 data_len valid (Logged (AwaitAck out slot (N.of_nat id)) pubs acks)
   (Logged (Ready out) pubs (N.of_nat id::acks)) ->
 let j:=Logged (Ready out) pubs (N.of_nat id::acks) in
 let reached:=runtime_sync_prefix point j (Certificate id d) e in
 let dest:=((Logged (Boot out) pubs (N.of_nat id::acks),RebuildingBoundary Selecting),forget_volatile_evidence reached) in
 episode_trace vi oi initial events valid view dest /\ Safe valid view dest /\
 hd_error pubs=Some (N.of_nat id) /\
 boundary_receipts dest=events++boundary_receipts initial /\
 volatile_allocation (snd dest)=None /\
 client_receipts reached=client_receipts e.
Proof.
 intros INIT PREFIX LOCAL STACK MARK APPEND ACK j reached dest.
 pose proof (proj1 (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT PREFIX)) as SOURCE.
 destruct (certified_append_evidence g sector data_len valid view marker ranges decode pages G DIV
   ready id d s e out slot pubs acks SOURCE LOCAL APPEND ACK) as [JI [EV HEAD]].
 assert (ALL:episode_trace vi oi initial events valid view dest).
 { unfold dest,reached;rewrite runtime_sync_prefix_reset.
   eapply episodes_append with (more:=[]);[exact PREFIX|].
   eapply episodes_cons with (event:=None) (events:=[]);[|constructor].
   eapply cut_exit_prepared with (phases:=[]) (suffix:=[SlotCompleted;DurableRamWritten;ExternalAccepted])
     (partial:=s);try eassumption;[reflexivity|].
   cbn [exit_program];split;reflexivity. }
 pose proof (a11_external_reserved_data_safety _ _ _ _ _ _ _ INIT ALL) as [SAFE [OBS REST]].
 split;[exact ALL|]. split;[exact SAFE|]. split;[exact HEAD|]. split;[exact OBS|].
 split;[reflexivity|apply runtime_sync_prefix_receipts].
Qed.

End ArbitraryEpisodes.

(* Fixed endpoint observations are a specialization of the single indexed
   relation, not another inductive trace or storage machine. *)
Definition stationary_episode_step g sector data_len valid view marker ranges decode topology pages x event y :=
 episode_step g sector data_len marker ranges decode topology pages valid view x event valid view y.
Definition stationary_episode_trace g sector data_len valid view marker ranges decode topology pages x events y :=
 episode_trace g sector data_len marker ranges decode topology pages valid view x events valid view y.
