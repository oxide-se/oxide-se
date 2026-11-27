From Stdlib Require Import List Arith NArith Lia.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import AllocationAdmission FlashSpec RetentionCoverage
  ScopeOwnership PreparedAuthority CompactImage CompactUpdates CollectionRoots
  PublicationPreparation PreparationOutcomes JournalHistory JournalRequests
  JournalReachableShape BootReconstruction BootTransaction TransactionBoundary
  PersistentBoundary DataEpisode FreerDataEpisode IncarnationBoundary.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export DecodedGeometryContract.
Import ListNotations.

(* Exact-cursor read-only service. A miss invokes fallback in Rust; it is NOT
   Capacity and does not prevent recycling. No physical effects in this branch.
   Numeric checks preceding RAM reserve remain explicit lower admission. *)
Inductive CursorAPI : interface :=
 | CursorProbe : CursorAPI (option extent)
 | CheckedCursor : nat -> CursorAPI cursor_reply
 | PayloadLength : nat -> nat -> CursorAPI (option nat)
 | PayloadArea : bool -> nat -> CursorAPI bool.
Definition cursor_caller (s : protection_state) (A : Type) (op : CursorAPI A) :=
  protection_frozen s = false.
Definition cursor_callee sector area_len req cursor f (s : protection_state)
    (A : Type) (op : CursorAPI A) (reply : A) : Prop :=
  match op in CursorAPI T return T -> Prop with
  | CursorProbe => fun answer => answer =
      cursor_probe sector area_len req cursor (protection_table s) f
  | CheckedCursor word_max => fun answer=>answer=checked_cursor sector word_max area_len req cursor (protection_table s) f
  | PayloadLength word_max bytes => fun answer=>answer=checked_data_total word_max bytes
  | PayloadArea available page => fun answer=>answer=andb available (Nat.eqb page 256)
  end reply.
Definition cursor_update (s : protection_state) (A : Type) (op : CursorAPI A) (reply : A) := s.
Definition cursor_contract sector area_len req cursor f :=
  make_contract cursor_update cursor_caller (cursor_callee sector area_len req cursor f).
Definition probe_cursor : impure CursorAPI (option extent) :=
  request_then CursorProbe (fun r => local r).

Lemma probe_cursor_execution sector area_len req cursor f s result final :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
    (cursor_contract sector area_len req cursor f) probe_cursor) s result final ->
  final=s /\ result=cursor_probe sector area_len req cursor (protection_table s) f.
Proof.
  intros P. simpl in P. unroll_post P.
  destruct P as [reply [middle [[CALL EQ] REST]]]. subst middle.
  unroll_post REST. destruct REST as [R S]. subst. split; reflexivity || exact CALL.
Qed.

Theorem probe_then_reserve sector area_len req cursor f s r final :
  data_invariant s -> protection_frozen s=false -> pending_preparation s=None ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
    (cursor_contract sector area_len req cursor f) probe_cursor) s (Some r) final ->
  data_caller (DataReserve r) final /\
  data_invariant (data_next (DataReserve r) final) /\ erased_object_extent sector f r.
Proof.
  intros I F P RUN. destruct (probe_cursor_execution _ _ _ _ _ _ _ _ RUN) as [-> HIT].
  symmetry in HIT.
  destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT) as [_ [_ [_ [_ [FREE ERASED]]]]].
  split; [simpl; auto|]. split; [apply data_command_preserves; auto; simpl; auto|exact ERASED].
Qed.

Section Consumer.
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
Hypothesis G : journal_geometry g sector 256.
Hypothesis DIV : sector mod 8=0.
Hypothesis CONTRACT : recovery_local_contracts view ranges decode.

(* A real consumer, not a new machine: the successful cursor execution supplies
   the two Data guards to the existing all-writer-outcomes consumer. Its
   DataReserve is the SAME reservation as probe_then_reserve, not a second
   allocation. BOSS allocation and circular fallback remain explicitly open. *)
Theorem cursor_to_enriched_data_episode data_bytes dw bw dp bp
    old id d index entry r s f h a e area_len req cursor final :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) h a,IdleBoundary old d s) e ->
  ranges entry=[r] ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
    (cursor_contract sector area_len req cursor f) probe_cursor)
    (data_next DataBegin s) (Some r) final ->
  outcome_writer_contracts g sector view data_bytes dw bw dp bp decode ->
  data_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    dw bw dp bp old id d index entry r s f h a e /\
  data_episode_delivery g sector data_len boss_ok view marker ranges decode topology pages
    dw bw old id d index entry r s f h a e.
Proof.
  intros INITIAL RANGE RUN WRITERS.
  destruct (probe_cursor_execution _ _ _ _ _ _ _ _ RUN) as [FINAL HIT].
  symmetry in HIT.
  destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT) as [_ [_ [_ [_ [FREE ERASED]]]]].
  eapply enriched_data_episode_freer; eauto.
Qed.
(* Fallback's erased-space result: recycling is not selected in this subcase.
   The Rust search also evaluates recycling predicates; their absence of
   arithmetic errors is a refinement/admission obligation, not Capacity. *)
Theorem erased_search_to_enriched_data_episode data_bytes dw bw dp bp
    old id d index entry r s f h a e area_len req start :
  enriched_invariant sector data_len boss_ok view marker ranges decode pages
    (Logged (Ready f) h a,IdleBoundary old d s) e ->
  ranges entry=[r] ->
  circular_erased sector area_len start req
    (protection_table (data_next DataBegin s)) f = Some r ->
  outcome_writer_contracts g sector view data_bytes dw bw dp bp decode ->
  data_episode_post g sector data_len boss_ok view marker ranges decode topology pages
    dw bw dp bp old id d index entry r s f h a e /\
  data_episode_delivery g sector data_len boss_ok view marker ranges decode topology pages
    dw bw old id d index entry r s f h a e.
Proof.
  intros INITIAL RANGE SEARCH WRITERS.
  destruct (circular_erased_sound _ _ _ _ _ _ _ SEARCH) as [FREE ERASED].
  eapply enriched_data_episode_freer; eauto.
Qed.
End Consumer.

(* Admission is an operational observation of the EXISTING RAM and flash.
   This relation stores neither. Fallback requires a cursor miss and normalizes
   the circular start exactly as format.rs. Numeric errors remain separate. *)
Inductive erased_admission sector s f r : Prop :=
| admission_cursor area_len req cursor final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) probe_cursor) s (Some r) final ->
    area_len <= 1024*256 -> erased_admission sector s f r
| admission_search area_len req cursor start final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) probe_cursor) s None final ->
    start <= area_len -> start mod 256=0 ->
    circular_erased sector area_len (if Nat.eqb start area_len then 0 else start) req
      (protection_table s) f = Some r ->
    area_len <= 1024*256 -> erased_admission sector s f r.
Lemma erased_admission_guards sector s f r : erased_admission sector s f r ->
  free_range 256 (protection_table s) r /\ erased_object_extent sector f r.
Proof.
  intros RUN; destruct RUN.
  - destruct (probe_cursor_execution _ _ _ _ _ _ _ _ H) as [_ HIT].
    symmetry in HIT. apply cursor_probe_sound in HIT; tauto.
  - eapply circular_erased_sound; eauto.
Qed.

(* reserve_persistent_span_sized advances append_offset to offset+total_len
   before reserve returns. Under the retained checked-arithmetic admission this
   does not saturate. BOSS must observe THAT cursor, not an independent one. *)
Inductive boss_admission sector previous s f r : Prop :=
| boss_at_cursor area_len req final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req (offset previous+span previous) f) probe_cursor)
      s (Some r) final -> area_len <= 1024*256 -> boss_admission sector previous s f r
| boss_after_search area_len req start final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req (offset previous+span previous) f) probe_cursor)
      s None final -> start <= area_len -> start mod 256=0 ->
    circular_erased sector area_len (if Nat.eqb start area_len then 0 else start) req
      (protection_table s) f = Some r -> area_len <= 1024*256 -> boss_admission sector previous s f r.
Lemma boss_admission_guards sector previous s f r : boss_admission sector previous s f r ->
  free_range 256 (protection_table s) r /\ erased_object_extent sector f r.
Proof.
  intro RUN. apply erased_admission_guards. destruct RUN.
  - eapply admission_cursor; eauto.
  - eapply admission_search; eauto.
Qed.

(* Successful service results are bounded by the initialized RAM table.
   This is a local geometry check, independent of free/blank and ownership. *)
Lemma erased_admission_numeric sector s f r : erased_admission sector s f r ->
 range_numeric (1024*256) r.
Proof.
 intro RUN;destruct RUN.
 - destruct (probe_cursor_execution _ _ _ _ _ _ _ _ H) as [_ HIT].
   symmetry in HIT;eapply cursor_probe_numeric;eauto.
 - unfold circular_erased in H2.
   destruct (first_erased sector area_len req
     (traversal (if start =? area_len then 0 else start) area_len) (protection_table s) f) eqn:F.
   + inversion H2;subst.
     destruct (first_erased_sound _ _ _ _ _ _ _ F) as [c [_ HIT]].
     eapply cursor_probe_numeric;eauto.
   + destruct (first_erased_sound _ _ _ _ _ _ _ H2) as [c [_ HIT]].
     eapply cursor_probe_numeric;[| |exact HIT];destruct (start =? area_len);lia.
Qed.
Lemma cursor_probe_alignment sector limit req cursor t f r :
 cursor_probe sector limit req cursor t f=Some r ->
 offset r mod 256=0 /\ span r mod 256=0.
Proof.
 intro HIT;destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT)
   as [OFF [ALIGN [BOUND [[n [REQ LEN]] REST]]]].
 split;[exact ALIGN|]. rewrite LEN;unfold rounded_required;apply Nat.mod_mul;lia.
Qed.
Lemma erased_admission_alignment sector s f r : erased_admission sector s f r ->
 offset r mod 256=0 /\ span r mod 256=0.
Proof.
 intro RUN;destruct RUN.
 - destruct (probe_cursor_execution _ _ _ _ _ _ _ _ H) as [_ HIT].
   symmetry in HIT;eapply cursor_probe_alignment;exact HIT.
 - unfold circular_erased in H2.
   destruct (first_erased sector area_len req
     (traversal (if start =? area_len then 0 else start) area_len) (protection_table s) f) eqn:F.
   + inversion H2;subst.
     destruct (first_erased_sound _ _ _ _ _ _ _ F) as [c [_ HIT]].
     eapply cursor_probe_alignment;exact HIT.
   + destruct (first_erased_sound _ _ _ _ _ _ _ H2) as [c [_ HIT]].
     eapply cursor_probe_alignment;exact HIT.
Qed.

(* The production caller passes read_area().len() to both probes. This
   indexed service retains that argument; forgetting it yields the historical
   admission interface, not another allocator or table. *)
Inductive mapped_erased_admission sector pages s f r : Prop :=
| mapped_cursor req cursor final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector (pages*256) req cursor f) probe_cursor) s (Some r) final ->
    pages<=1024 -> mapped_erased_admission sector pages s f r
| mapped_search req cursor start final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector (pages*256) req cursor f) probe_cursor) s None final ->
    start<=pages*256 -> start mod 256=0 ->
    circular_erased sector (pages*256) (if Nat.eqb start (pages*256) then 0 else start)
      req (protection_table s) f=Some r ->
    pages<=1024 -> mapped_erased_admission sector pages s f r.
Lemma mapped_erased_admission_forget sector pages s f r :
 mapped_erased_admission sector pages s f r -> erased_admission sector s f r.
Proof. intro RUN;destruct RUN;[eapply admission_cursor|eapply admission_search];eauto;lia. Qed.
Lemma mapped_erased_admission_bound sector pages s f r :
 mapped_erased_admission sector pages s f r -> offset r+span r<=pages*256.
Proof.
 intro RUN;destruct RUN.
 - destruct (probe_cursor_execution _ _ _ _ _ _ _ _ H) as [_ HIT].
   symmetry in HIT;apply cursor_probe_sound in HIT;tauto.
 - unfold circular_erased in H2.
   destruct (first_erased sector (pages*256) req
     (traversal (if start =? pages*256 then 0 else start) (pages*256)) (protection_table s) f) eqn:F.
   + inversion H2;subst;destruct (first_erased_sound _ _ _ _ _ _ _ F) as [c [_ HIT]].
     apply cursor_probe_sound in HIT;tauto.
   + destruct (first_erased_sound _ _ _ _ _ _ _ H2) as [c [_ HIT]].
     apply cursor_probe_sound in HIT.
     destruct (start =? pages*256);cbn in HIT;lia.
Qed.

Lemma boss_admission_numeric sector previous s f r : boss_admission sector previous s f r ->
 range_numeric (1024*256) r.
Proof.
 intro RUN;apply erased_admission_numeric with (sector:=sector) (s:=s) (f:=f).
 destruct RUN;[eapply admission_cursor|eapply admission_search];eauto.
Qed.

Definition probe_cursor_checked word_max : impure CursorAPI cursor_reply :=
 request_then (CheckedCursor word_max) (fun r=>local r).
Definition check_payload_area available page : impure CursorAPI bool :=
 request_then (PayloadArea available page) (fun r=>local r).
Definition check_payload_length word_max bytes : impure CursorAPI (option nat) :=
 request_then (PayloadLength word_max bytes) (fun r=>local r).
Lemma checked_probe_execution sector area_len req cursor f s word_max result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
  (cursor_contract sector area_len req cursor f) (probe_cursor_checked word_max)) s result final ->
 final=s /\ result=checked_cursor sector word_max area_len req cursor (protection_table s) f.
Proof.
 intro P;simpl in P;unroll_post P;destruct P as [reply [middle [[CALL EQ] REST]]];subst middle.
 unroll_post REST;destruct REST as [R S];subst;auto.
Qed.
Lemma payload_length_execution sector area_len req cursor f s word_max bytes result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
  (cursor_contract sector area_len req cursor f) (check_payload_length word_max bytes)) s result final ->
 final=s /\ result=checked_data_total word_max bytes.
Proof.
 intro P;simpl in P;unroll_post P;destruct P as [reply [middle [[CALL EQ] REST]]];subst middle.
 unroll_post REST;destruct REST as [R S];subst;auto.
Qed.

(* Returned local failures, observed at their actual service call. No command,
   allocation, table mutation or transaction postcondition is in this contract. *)
Inductive local_admission_rejection sector s f : Prop :=
| rejected_checked_probe area_len cursor word_max bytes total final :
    word_max mod 256=255 -> checked_data_total word_max bytes=Some total ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len (fun _=>Some total) cursor f) (probe_cursor_checked word_max))
      s ProbeRejected final -> local_admission_rejection sector s f
| rejected_payload_length area_len req cursor word_max bytes final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) (check_payload_length word_max bytes))
      s None final -> local_admission_rejection sector s f
| rejected_payload_area area_len req cursor available page final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) (check_payload_area available page))
      s false final -> local_admission_rejection sector s f.

Lemma payload_area_execution sector area_len req cursor f s available page result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
  (cursor_contract sector area_len req cursor f) (check_payload_area available page)) s result final ->
 final=s /\ result=andb available (Nat.eqb page 256).
Proof.
 intro P;simpl in P;unroll_post P;destruct P as [reply [middle [[CALL EQ] REST]]];subst middle.
 unroll_post REST;destruct REST as [R S];subst;auto.
Qed.

Theorem checked_data_probe_execution_not_rejected sector area_len cursor f s word_max bytes total result final :
 word_max mod 256=255 -> checked_data_total word_max bytes=Some total ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
  (cursor_contract sector area_len (fun _=>Some total) cursor f) (probe_cursor_checked word_max)) s result final ->
 result<>ProbeRejected.
Proof.
 intros MAX TOTAL RUN;destruct (checked_probe_execution _ _ _ _ _ _ _ _ _ RUN) as [FINAL OBS].
 rewrite OBS;eapply data_total_probe_no_numeric_error;eauto.
Qed.

(* The impossible probe-error constructor is eliminated at the consumer. *)
Inductive returned_payload_rejection sector s f : Prop :=
| returned_bad_length area_len req cursor word_max bytes final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) (check_payload_length word_max bytes))
      s None final -> returned_payload_rejection sector s f
| returned_bad_area area_len req cursor available page final :
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector area_len req cursor f) (check_payload_area available page))
      s false final -> returned_payload_rejection sector s f.
Lemma local_admission_error_classified sector s f :
 local_admission_rejection sector s f -> returned_payload_rejection sector s f.
Proof.
 intro RUN;destruct RUN.
 - exfalso;exact (checked_data_probe_execution_not_rejected _ _ _ _ _ _ _ _ _ _ H H0 H1 eq_refl).
 - eapply returned_bad_length;exact H.
 - eapply returned_bad_area;exact H.
Qed.

From OxideSE.Registry Require Import RecyclingSearch Neutralization.
Definition search_requirement word_max (req:nat->option nat) position :=
 match req position with
 | None=>RequiredSkip
 | Some n=>match checked_round word_max 256 n with
   | None=>RequiredError | Some rounded=>RequiredPages (rounded/256) end
 end.
(* The search is reached only after the checked fast probe returned Miss.
   `start` is in pages in reusable_search; the runtime stores byte offsets. *)
Definition runtime_search_inputs sector pages word_max e s f req start :=
 exists a bytes,
 volatile_allocation e=Some a /\
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector (pages*256) bytes (allocation_append a) f)
   (probe_cursor_checked word_max)) s ProbeMiss s /\
 req=search_requirement word_max bytes /\
 start=Nat.min word_max (extent_end (allocation_latest a))/256.
Lemma runtime_search_start_unique sector pages word_max e s f req start a :
 volatile_allocation e=Some a ->
 runtime_search_inputs sector pages word_max e s f req start ->
 start=Nat.min word_max (extent_end (allocation_latest a))/256.
Proof. intros OBS [actual [bytes [EQ [PROBE [REQ START]]]]].
 rewrite OBS in EQ;inversion EQ;subst;reflexivity. Qed.

(* Local format geometry, not authority preservation: the decoder checks the
   BOSS extent against the object mapping and page-rounded encoded length. *)
(* Persistent proof provenance, not another runtime field: the observed range
   comes from a decoded incarnation. The witness may be historical; it is not
   a promise that obsolete bytes remain readable in the current flash. *)
Definition allocation_range_origin sector pages (decode:flash->nat->option recovery_decoding) e :=
 forall a,volatile_allocation e=Some a ->
 exists f id d,decode (object_flash sector f) id=Some d /\
 volatile_latest_registry e=Some id /\ allocation_latest a=recovered_boss d /\
 extent_end (allocation_latest a)<=pages*256 /\
 extent_end (allocation_latest a) mod 256=0.
Lemma allocation_origin_same sector pages decode e e' :
 volatile_allocation e'=volatile_allocation e -> volatile_latest_registry e'=volatile_latest_registry e ->
 allocation_range_origin sector pages decode e -> allocation_range_origin sector pages decode e'.
Proof. intros EQ LATEST ORIGIN a OBS;unfold allocation_range_origin in ORIGIN;
 rewrite LATEST;apply ORIGIN;rewrite <- EQ;exact OBS. Qed.
Lemma allocation_origin_forget sector pages decode e :
 allocation_range_origin sector pages decode (forget_volatile_evidence e).
Proof. intros a BAD;discriminate. Qed.
Lemma allocation_origin_phase sector pages decode phase e :
 allocation_range_origin sector pages decode e ->
 allocation_range_origin sector pages decode (phase_evidence phase e).
Proof. intro O;destruct phase;exact O || apply allocation_origin_forget. Qed.
Lemma allocation_origin_advance sector pages decode r e :
 allocation_range_origin sector pages decode e ->
 allocation_range_origin sector pages decode (advance_allocation_evidence r e).
Proof.
 intros O a OBS;cbn in OBS;destruct (volatile_allocation e) as [before|] eqn:E;[|discriminate].
 inversion OBS;subst a;exact (O before E).
Qed.
Lemma allocation_origin_decoded sector pages decode read f id d :
 generation_decoding_matches sector decode read -> decoded_allocation_geometry pages decode ->
 decode (object_flash sector f) id=Some d ->
 forall a,read_allocation read f id=Some a ->
 exists ff chosen decoded,decode (object_flash sector ff) chosen=Some decoded /\
 Some id=Some chosen /\ allocation_latest a=recovered_boss decoded /\
 extent_end (allocation_latest a)<=pages*256 /\ extent_end (allocation_latest a) mod 256=0.
Proof.
 intros MATCH GEO READ a OBS;unfold read_allocation in OBS.
 specialize (MATCH f id);rewrite READ in MATCH.
 destruct (read f id) as [[actual n]|];cbn in OBS,MATCH;[|discriminate].
 inversion MATCH;subst actual;inversion OBS;subst a;exists f,id,d;split;[exact READ|].
 split;[reflexivity|]. split;[reflexivity|exact (GEO _ _ _ READ)].
Qed.
Lemma allocation_origin_observe sector pages decode j c e :
 decoded_allocation_geometry pages decode ->
 decode (object_flash sector (control_image (journal_control j))) (certificate_id c)=Some (certificate_decoded c) ->
 allocation_range_origin sector pages decode (observe_client j c e).
Proof.
 intros GEO READ a OBS;cbn in OBS;destruct (volatile_allocation e) as [before|] eqn:E;[|discriminate].
 inversion OBS;subst a;exists (control_image (journal_control j)),(certificate_id c),(certificate_decoded c).
 split;[exact READ|]. split;[reflexivity|]. split;[reflexivity|exact (GEO _ _ _ READ)].
Qed.
Lemma runtime_search_calculation sector pages word_max decode e s f req start :
 allocation_range_origin sector pages decode e -> pages*256<=word_max ->
 runtime_search_inputs sector pages word_max e s f req start ->
 exists a,volatile_allocation e=Some a /\
 Nat.min word_max (extent_end (allocation_latest a))=extent_end (allocation_latest a) /\
 256*start=extent_end (allocation_latest a) /\ start<=pages.
Proof.
 intros ORIGIN CAP [a [bytes [OBS [PROBE [REQ START]]]]].
 destruct (ORIGIN a OBS) as [ff [id [d [READ [LATEST [SAME [BOUND ALIGN]]]]]]].
 exists a;split;[exact OBS|].
 assert (SAT:Nat.min word_max (extent_end (allocation_latest a))=extent_end (allocation_latest a)) by (apply Nat.min_r;lia).
 split;[exact SAT|]. rewrite SAT in START;subst start.
 pose proof (Nat.div_mod (extent_end (allocation_latest a)) 256 ltac:(lia));split;lia.
Qed.
Lemma initialized_allocation_origin sector pages decode j id e d :
 generation_decoding_matches sector decode (counter_decoder e) ->
 decoded_allocation_geometry pages decode ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d ->
 volatile_latest_registry e=Some id ->
 allocation_range_origin sector pages decode (initialized_allocation_evidence j id e).
Proof. intros MATCH GEO READ LATEST a OBS.
 change (exists ff chosen decoded,decode (object_flash sector ff) chosen=Some decoded /\
 volatile_latest_registry e=Some chosen /\ allocation_latest a=recovered_boss decoded /\
 extent_end (allocation_latest a)<=pages*256 /\ extent_end (allocation_latest a) mod 256=0).
 rewrite LATEST;eapply allocation_origin_decoded;eassumption. Qed.
Definition allocation_append_bound pages e :=
 forall a,volatile_allocation e=Some a -> allocation_append a<=pages*256.
Lemma allocation_append_forget pages e : allocation_append_bound pages (forget_volatile_evidence e).
Proof. intros a BAD;discriminate. Qed.
Lemma allocation_append_phase pages phase e : allocation_append_bound pages e ->
 allocation_append_bound pages (phase_evidence phase e).
Proof. intro O;destruct phase;exact O || apply allocation_append_forget. Qed.
Lemma allocation_append_advance pages r e : extent_end r<=pages*256 ->
 allocation_append_bound pages (advance_allocation_evidence r e).
Proof.
 intros B a OBS;cbn in OBS;destruct (volatile_allocation e);inversion OBS;subst;exact B.
Qed.
Lemma allocation_append_observe pages j c e : allocation_append_bound pages e ->
 allocation_append_bound pages (observe_client j c e).
Proof.
 intros B a OBS;cbn in OBS;destruct (volatile_allocation e) as [prior|] eqn:E;[|discriminate].
 inversion OBS;subst;exact (B prior E).
Qed.
Lemma allocation_append_decoded sector pages decode read f id d :
 generation_decoding_matches sector decode read -> decoded_allocation_geometry pages decode ->
 decode (object_flash sector f) id=Some d ->
 forall a,read_allocation read f id=Some a -> allocation_append a<=pages*256.
Proof.
 intros MATCH GEO READ a OBS;unfold read_allocation in OBS.
 specialize (MATCH f id);rewrite READ in MATCH.
 destruct (read f id) as [[actual n]|];cbn in OBS,MATCH;[|discriminate].
 inversion MATCH;subst actual;inversion OBS;subst a;exact (proj1 (GEO _ _ _ READ)).
Qed.
Lemma initialized_allocation_append_bound sector pages decode j id e d :
 generation_decoding_matches sector decode (counter_decoder e) ->
 decoded_allocation_geometry pages decode ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d ->
 allocation_append_bound pages (initialized_allocation_evidence j id e).
Proof. intros MATCH GEO READ a OBS;eapply allocation_append_decoded;eassumption. Qed.
Lemma recovered_runtime_search_inputs sector pages word_max decode j id e d s bytes :
 generation_decoding_matches sector decode (counter_decoder e) ->
 decoded_allocation_geometry pages decode -> pages*256<=word_max ->
 decode (object_flash sector (control_image (journal_control j))) id=Some d ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
   (cursor_contract sector (pages*256) bytes (extent_end (recovered_boss d))
     (control_image (journal_control j))) (probe_cursor_checked word_max)) s ProbeMiss s ->
 runtime_search_inputs sector pages word_max
   (recovered_page_evidence j id (forget_volatile_evidence e)) s
   (control_image (journal_control j)) (search_requirement word_max bytes)
   (extent_end (recovered_boss d)/256) /\
 Nat.min word_max (extent_end (recovered_boss d))=extent_end (recovered_boss d).
Proof.
 intros MATCH GEOM CAP READ PROBE.
 destruct (GEOM _ _ _ READ) as [BOUND ALIGN].
 split.
 - exists (allocation_from_decoded d),bytes;split.
   + exact (allocation_recovered_after_reset sector decode j id e d MATCH READ).
   + split;[exact PROBE|]. split;[reflexivity|]. cbn [allocation_from_decoded allocation_latest].
     rewrite Nat.min_r;[reflexivity|lia].
 - apply Nat.min_r;lia.
Qed.

(* Runtime-bound version of the existing admission observation. Neither input
   is picked by the consumer: probe uses append, fallback uses durable end.
   Forgetting these arguments yields the historical safety-only interface. *)
Inductive runtime_erased_admission sector pages e s f r : Prop :=
| runtime_cursor req a final :
    volatile_allocation e=Some a ->
    post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure CursorAPI)
      (cursor_contract sector (pages*256) req (allocation_append a) f) probe_cursor)
      s (Some r) final ->
    pages<=1024 -> runtime_erased_admission sector pages e s f r
| runtime_search fuel recognize req round alignment start word_max i n :
    runtime_search_inputs sector pages word_max e s f req start ->
    reusable_search sector fuel recognize f (protection_table s) req round alignment pages start=FoundErased i n ->
    r=block_pages i n -> pages<=1024 -> runtime_erased_admission sector pages e s f r.

(* A pure safety witness for the old interface, NOT a second executed probe.
   The operational runtime_search constructor above retains the real walk. *)
Lemma selected_erased_mapped sector pages s f i n :
 i+n<=pages ->
 blankb sector f (block_pages i n)=true -> vacantb (protection_table s) (block_pages i n)=true ->
 pages<=1024 -> mapped_erased_admission sector pages s f (block_pages i n).
Proof.
 intros B BLANK FREE.
 assert (ROUND:rounded_required (256*n)=256*n).
 { unfold rounded_required;replace (256*n+255) with (255+n*256) by lia.
   rewrite Nat.div_add;[cbn;lia|lia]. }
 assert (HIT:cursor_probe sector (pages*256) (fun _=>Some (256*n)) (256*i) (protection_table s) f=Some (block_pages i n)).
 { unfold cursor_probe;rewrite ROUND;change ((if (((256*i) mod 256 =? 0) && (256*i+256*n<=?pages*256)) &&
    (vacantb (protection_table s) (block_pages i n) && blankb sector f (block_pages i n)) then Some (block_pages i n) else None) = Some (block_pages i n)).
   rewrite FREE BLANK.
   assert (ALIGN:(256*i) mod 256=0) by (rewrite Nat.mul_comm;apply Nat.mod_mul;lia).
   rewrite ALIGN;cbn [andb Nat.eqb].
   assert (BOUND:(256*i+256*n<=?pages*256)=true) by (apply Nat.leb_le;nia).
   rewrite BOUND;reflexivity. }
 intro CAP;eapply mapped_cursor with (req:=fun _=>Some (256*n)) (cursor:=256*i) (final:=s);[|exact CAP].
 cbn.
 exists (Some (block_pages i n)),s;split;[split;[exact (eq_sym HIT)|reflexivity]|].
 split;reflexivity.
Qed.
Lemma runtime_erased_admission_mapped sector pages e s f r :
 runtime_erased_admission sector pages e s f r ->
 mapped_erased_admission sector pages s f r.
Proof.
 intro RUN;destruct RUN.
 - eapply mapped_cursor;eauto.
 - subst r;destruct (reusable_search_erased _ _ _ _ _ _ _ _ _ _ _ _ H0) as [REQ [POS [BOUND [BLANK FREE]]]].
   destruct H as [a [bytes [OBS [PROBE REST]]]].
   eapply selected_erased_mapped;eassumption.
Qed.
Lemma runtime_erased_admission_forget sector pages e s f r :
 runtime_erased_admission sector pages e s f r -> erased_admission sector s f r.
Proof. intro RUN;apply mapped_erased_admission_forget with (pages:=pages).
 eapply runtime_erased_admission_mapped;exact RUN. Qed.
Lemma runtime_erased_admission_observed sector pages e s f r :
 runtime_erased_admission sector pages e s f r ->
 exists a,volatile_allocation e=Some a.
Proof. intro RUN;destruct RUN;eauto. destruct H as [a [bytes [OBS REST]]];eauto. Qed.

Lemma runtime_erased_advance_bounded sector pages e s f r word_max :
 pages*256<=word_max -> runtime_erased_admission sector pages e s f r ->
 extent_end r<=word_max /\ Nat.min word_max (extent_end r)=extent_end r.
Proof.
 intros SIZE RUN;pose proof (mapped_erased_admission_bound _ _ _ _ _
   (runtime_erased_admission_mapped _ _ _ _ _ _ RUN)) as END.
 unfold extent_end;split;[lia|apply Nat.min_r;lia].
Qed.
