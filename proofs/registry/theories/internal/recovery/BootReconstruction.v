From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority
  CompactUpdates CollectionRoots JournalHistory JournalReachableShape JournalRequests
  JournalRecoveryTrace JournalProtocolAuthority PreparationOutcomes.
Import ListNotations.

(* Control enrichment of the existing journal/protection witnesses. There is one
   logged_state (and therefore one flash/history), and at most one RAM table.
   The phases are program counters, NOT a new Rust readiness flag. *)
Inductive restore_stage := ImageRestored | CurrentInstalled | TopologyChecked | RuntimeInstalled.
Inductive boot_phase :=
| Selecting
| Decoding (id : nat)
| Installing (id : nat) (decoded : recovery_decoding) (stage : restore_stage)
| Retaining (id : nat) (decoded : recovery_decoding) (todo : list extent) (ram : protection_state)
| Caching (id : nat) (decoded : recovery_decoding) (ram : protection_state)
| Returning (id : nat) (decoded : recovery_decoding) (ram : protection_state)
| Usable (id : nat) (decoded : recovery_decoding) (ram : protection_state)
| Stopped.
Definition boot_state := (logged_state * boot_phase)%type.
Definition boot_journal (s : boot_state) := fst s.
Definition boot_pc (s : boot_state) := snd s.
Definition decoded_ranges marker ranges d := marker :: recovered_boss d :: image_dependencies ranges (recovered_image d).
Definition decoded_fresh marker ranges d := recovered_ram marker (recovered_boss d) (image_dependencies ranges (recovered_image d)).
Definition decoded_cached marker ranges pages d := remember_recovered_boss pages (recovered_boss d) (rebuild_decoded marker ranges d).
Definition ordinary_access s := match boot_pc s with Usable _ _ _ => True | _ => False end.

Lemma recovery_reset_projection g sector data_len boss_ok j :
  recovering_control (journal_control j) ->
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok) j (logged_after_reset j).
Proof.
  destruct j as [c h a]; destruct c as [f|f|f|f i d|f i d|slot old candidate [phase f]];
    simpl; intros R; try contradiction.
  - apply rt_step. split; [exact I|]. split; [exact I|].
    apply (record_step g sector 256 data_len boss_ok (Ready f) (Boot f)); apply reset_ready.
  - apply rt_refl.
  - destruct phase; simpl in R; try contradiction;
      apply rt_step; split; try exact I; split; try exact I;
      apply (record_step g sector 256 data_len boss_ok); apply reset_protocol.
Qed.

Section Boot.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Variable view : nat -> root_view.
Variable marker : extent.
Variable ranges : CompactImage.compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable area_pages : nat.

Inductive boot_step : boot_state -> boot_state -> Prop :=
| boot_journal_step j j' : recovery_logged_step g sector 256 data_len boss_ok j j' ->
    boot_step (j, Selecting) (j', Selecting)
| boot_select f h a id : observed sector 256 data_len boss_ok f = Some (N.of_nat id) ->
    boot_step (Logged (Ready f) h a, Selecting) (Logged (Ready f) h a, Decoding id)
| boot_decode j id d : decode (object_flash sector (control_image (journal_control j))) id = Some d ->
    boot_step (j, Decoding id) (j, Installing id d ImageRestored)
| boot_install_current j id d :
    boot_step (j, Installing id d ImageRestored) (j, Installing id d CurrentInstalled)
| boot_topology j id d : topology d = true ->
    boot_step (j, Installing id d CurrentInstalled) (j, Installing id d TopologyChecked)
| boot_runtime j id d :
    boot_step (j, Installing id d TopologyChecked) (j, Installing id d RuntimeInstalled)
| boot_pages_reset j id d :
    boot_step (j, Installing id d RuntimeInstalled)
      (j, Retaining id d (decoded_ranges marker ranges d) (decoded_fresh marker ranges d))
| boot_retain j id d r todo ram :
    boot_step (j, Retaining id d (r::todo) ram) (j, Retaining id d todo (recovery_retain r ram))
| boot_retains_done j id d ram : boot_step (j, Retaining id d [] ram) (j, Caching id d ram)
| boot_cache j id d ram : boot_step (j, Caching id d ram)
    (j, Returning id d (remember_recovered_boss area_pages (recovered_boss d) ram))
| boot_return j id d ram : boot_step (j, Returning id d ram) (j, Usable id d ram)
| boot_fail j phase : ordinary_access (j,phase) = False -> boot_step (j,phase) (j,Stopped)
| boot_partial j phase : ordinary_access (j,phase) = False -> boot_step (j,phase) (j,phase)
| boot_reset j phase : boot_step (j,phase) (logged_after_reset j, Selecting).

Definition decoded_link j id d :=
  (exists f, journal_control j = Ready f) /\
  hd_error (publications j) = Some (N.of_nat id) /\
  decode (object_flash sector (control_image (journal_control j))) id = Some d /\
  decoded_root_agrees view ranges id d.
Definition boot_invariant s :=
  logged_invariant sector 256 data_len boss_ok (boot_journal s) /\
  recovering_control (journal_control (boot_journal s)) /\
  match boot_pc s with
  | Selecting | Stopped => True
  | Decoding id => (exists f, journal_control (boot_journal s) = Ready f) /\
      hd_error (publications (boot_journal s)) = Some (N.of_nat id)
  | Installing id d _ => decoded_link (boot_journal s) id d
  | Retaining id d todo ram => decoded_link (boot_journal s) id d /\
      exists done, done ++ todo = decoded_ranges marker ranges d /\
        ram = recovery_retains done (decoded_fresh marker ranges d)
  | Caching id d ram => decoded_link (boot_journal s) id d /\ ram = rebuild_decoded marker ranges d
  | Returning id d ram | Usable id d ram => decoded_link (boot_journal s) id d /\
      ram = decoded_cached marker ranges area_pages d
  end.

Lemma boot_projection s s' : boot_invariant s -> boot_step s s' ->
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
    (boot_journal s) (boot_journal s').
Proof.
  intros [_ [REC _]] STEP. destruct STEP; simpl in *; try apply rt_refl.
  - apply rt_step; assumption.
  - apply recovery_reset_projection; assumption.
Qed.
Lemma recovery_retains_app xs ys s :
  recovery_retains (xs ++ ys) s = recovery_retains ys (recovery_retains xs s).
Proof. revert s; induction xs; intros; simpl; auto. Qed.

Theorem boot_step_preserves_certified_read :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  forall s s', boot_invariant s ->
  (forall id d,
    hd_error (publications (boot_journal s))=Some (N.of_nat id) ->
    decode (object_flash sector (control_image (journal_control (boot_journal s)))) id=Some d ->
    decoded_root_agrees view ranges id d) ->
  boot_step s s' -> boot_invariant s'.
Proof.
  intros G DIV s s' INV FORMAT STEP.
  pose proof (boot_projection s s' INV STEP) as TRACE.
  destruct INV as [JI [REC PHASE]].
  destruct (recovery_trace_history _ _ _ _ _ _ _ TRACE) as [HP [HA JT]].
  assert (JNEW : logged_invariant sector 256 data_len boss_ok (boot_journal s')).
  { eapply arbitrary_finite_history_preserves_invariant; eauto. }
  split; [exact JNEW|]. destruct STEP; simpl in *.
  - split; [exact (proj1 (proj2 H))|exact I].
  - split; [exact I|]. split; [eauto|]. rewrite <- (proj1 (proj2 JI)); exact H.
  - split; [exact REC|]. destruct PHASE as [READY HEAD].
    split; [exact READY|]. split; [exact HEAD|]. split; [exact H|exact (FORMAT _ _ HEAD H)].
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - split; [exact REC|]. split; [exact PHASE|]. exists []; split; reflexivity.
  - split; [exact REC|]. destruct PHASE as [LINK [done [ENUM RAM]]].
    split; [exact LINK|]. exists (done ++ [r]); split.
    + rewrite <- app_assoc; exact ENUM.
    + rewrite recovery_retains_app; simpl; rewrite <- RAM; reflexivity.
  - split; [exact REC|]. destruct PHASE as [LINK [done [ENUM RAM]]].
    rewrite app_nil_r in ENUM. subst done. split; [exact LINK|exact RAM].
  - split; [exact REC|]. destruct PHASE as [LINK RAM]; split; [exact LINK|].
    unfold decoded_cached; rewrite RAM; reflexivity.
  - split; assumption.
  - split; [exact REC|exact I].
  - split; assumption.
  - split; [|exact I]. destruct j as [c h a]; destruct c; simpl in *; try exact I; try contradiction.
Qed.

Theorem boot_step_preserves :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  forall s s', boot_invariant s -> boot_step s s' -> boot_invariant s'.
Proof.
 intros G DIV [FORMAT LOCAL] s s' INV STEP.
 eapply boot_step_preserves_certified_read; [exact G|exact DIV|exact INV| |exact STEP].
 intros id d HEAD READ; exact (FORMAT _ _ _ READ).
Qed.

Theorem boot_finite_trace :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  forall s s', boot_invariant s -> clos_refl_trans boot_state boot_step s s' ->
  boot_invariant s' /\
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
    (boot_journal s) (boot_journal s').
Proof.
  intros G DIV CONTRACT s s' INV TRACE. induction TRACE.
  - split; [eapply boot_step_preserves; eauto|eapply boot_projection; eauto].
  - split; [exact INV|apply rt_refl].
  - destruct (IHTRACE1 INV) as [MID FIRST]. destruct (IHTRACE2 MID) as [LAST SECOND].
    split; [exact LAST|eapply rt_trans; eauto].
Qed.

Theorem boot_usable_opens j id d ram :
  boot_invariant (j, Usable id d ram) ->
  journal_idle sector 256 data_len boss_ok view marker id ram j /\
  image_current_correspondence ranges (recovered_image d) [recovered_boss d] ram /\
  data_caller DataBegin ram /\ data_invariant (data_next DataBegin ram).
Proof.
  intros [JI [REC [[READY [HEAD [READ FORMAT]]] RAM]]]. subst ram.
  destruct (remembered_recovery_can_begin view marker ranges id d area_pages FORMAT)
    as [IDLE [CALL BEGIN]].
  split.
  - destruct j as [c h a]; destruct READY as [f E]; simpl in E; subst c.
    apply idle_root_links_ready; assumption.
  - split; [|split; assumption].
    change (image_current_correspondence ranges (recovered_image d) [recovered_boss d]
      (rebuild_decoded marker ranges d)).
    exact (proj1 (proj2 (decoded_reconstruction_opens_transaction view marker ranges id d FORMAT))).
Qed.

Theorem boot_prefix_safety initial final :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  logged_invariant sector 256 data_len boss_ok initial ->
  recovering_control (journal_control initial) ->
  clos_refl_trans boot_state boot_step (initial, Selecting) final ->
  boot_invariant final /\
  publications (boot_journal final) = publications initial /\
  acknowledgements (boot_journal final) = acknowledgements initial /\
  (forall x, 2*sector <= x -> control_image (journal_control (boot_journal final)) x =
    control_image (journal_control initial) x) /\
  (ordinary_access final -> exists id d ram,
    boot_pc final = Usable id d ram /\
    journal_idle sector 256 data_len boss_ok view marker id ram (boot_journal final) /\
    image_current_correspondence ranges (recovered_image d) [recovered_boss d] ram /\
    data_caller DataBegin ram /\ data_invariant (data_next DataBegin ram)).
Proof.
  intros G DIV CONTRACT J REC TRACE.
  assert (ENTRY : boot_invariant (initial,Selecting)) by (split; [exact J|split; assumption || exact I]).
  destruct (boot_finite_trace G DIV CONTRACT _ _ ENTRY TRACE) as [LAST PROJ].
  destruct (recovery_trace_history _ _ _ _ _ _ _ PROJ) as [H [A PHYSICAL]].
  split; [exact LAST|]. split; [exact H|]. split; [exact A|]. split.
  - intros x X. eapply logged_trace_frame_after_journal; eauto.
  - destruct final as [j phase]; destruct phase; simpl; try contradiction.
    intros _. exists id, decoded, ram; split; [reflexivity|]. apply boot_usable_opens; exact LAST.
Qed.

(* Reset never passes a partial table into the following attempt. This is a
   control-flow fact, not a physical assertion about zeroing every RAM byte. *)
Theorem reset_discards_partial j phase :
  boot_step (j,phase) (logged_after_reset j,Selecting) /\
  ~ ordinary_access (logged_after_reset j,Selecting).
Proof. split; [apply boot_reset|simpl; tauto]. Qed.

(* Same journal/control witness, no publication operation in RAM rebuilding. *)
Theorem boot_final_decode_stable initial final id d ram :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  logged_invariant sector 256 data_len boss_ok initial ->
  recovering_control (journal_control initial) ->
  clos_refl_trans boot_state boot_step (initial,Selecting) (final,Usable id d ram) ->
  hd_error (publications initial) = Some (N.of_nat id) /\
  decode (object_flash sector (control_image (journal_control initial))) id = Some d /\
  journal_idle sector 256 data_len boss_ok view marker id ram final /\
  data_caller DataBegin ram /\ data_invariant (data_next DataBegin ram).
Proof.
  intros G DIV CONTRACT J REC TRACE.
  destruct (boot_prefix_safety _ _ G DIV CONTRACT J REC TRACE) as [INV [H [A [FRAME USE]]]].
  pose proof INV as [_ [_ [[READY [HEAD [READ FORMAT]]] RAM]]].
  split; [rewrite <- H; exact HEAD|]. split.
  - destruct CONTRACT as [F LOCAL].
    assert (KEEP : unchanged (root_extents (view id))
      (object_flash sector (control_image (journal_control initial)))
      (object_flash sector (control_image (journal_control final)))).
    { intros r a IN AT; apply FRAME; lia. }
    rewrite (LOCAL _ _ id KEEP); exact READ.
  - destruct (boot_usable_opens _ _ _ _ INV) as [IDLE [IMAGE REST]]. split; assumption.
Qed.

Definition boot_restart_post (allowed : nat -> recovery_decoding -> Prop) initial :=
  forall final, clos_refl_trans boot_state boot_step (initial,Selecting) final ->
    boot_invariant final /\
    publications (boot_journal final) = publications initial /\
    acknowledgements (boot_journal final) = acknowledgements initial /\
    (forall x, 2*sector <= x -> control_image (journal_control (boot_journal final)) x =
      control_image (journal_control initial) x) /\
    (forall j id d ram, final = (j,Usable id d ram) ->
      allowed id d /\ journal_idle sector 256 data_len boss_ok view marker id ram j /\
      image_current_correspondence ranges (recovered_image d) [recovered_boss d] ram /\
      data_caller DataBegin ram /\ data_invariant (data_next DataBegin ram)).

Theorem persistent_authority_repeated_boot allowed initial :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  logged_invariant sector 256 data_len boss_ok initial ->
  recovering_control (journal_control initial) ->
  (forall id d, hd_error (publications initial) = Some (N.of_nat id) ->
    decode (object_flash sector (control_image (journal_control initial))) id = Some d -> allowed id d) ->
  boot_restart_post allowed initial.
Proof.
  intros G DIV CONTRACT J REC AUTH final TRACE.
  destruct (boot_prefix_safety _ _ G DIV CONTRACT J REC TRACE) as [INV [H [A [FRAME USE]]]].
  split; [exact INV|]. split; [exact H|]. split; [exact A|]. split; [exact FRAME|].
  intros j id d ram EQ; subst final.
  destruct (boot_final_decode_stable _ _ _ _ _ G DIV CONTRACT J REC TRACE) as [HEAD [READ REST]].
  split; [eapply AUTH; eauto|exact (boot_usable_opens _ _ _ _ INV)].
Qed.

Definition ordinary_caller c s := exists id d ram,
  boot_pc s = Usable id d ram /\ data_caller c ram.
Theorem ordinary_call_requires_completed_boot c s : ordinary_caller c s -> ordinary_access s.
Proof. intros [id [d [ram [PC CALL]]]]. unfold ordinary_access; rewrite PC; exact I. Qed.
Theorem stopped_attempt_no_ordinary j c : ~ ordinary_caller c (j,Stopped).
Proof. intros [id [d [ram [PC CALL]]]]; discriminate. Qed.
Theorem partial_table_no_ordinary j id d todo ram c :
  ~ ordinary_caller c (j,Retaining id d todo ram).
Proof. intros [i [x [s [PC CALL]]]]; discriminate. Qed.
Theorem stopped_attempt_next j s' : boot_step (j,Stopped) s' ->
  s' = (j,Stopped) \/ s' = (logged_after_reset j,Selecting).
Proof. intros STEP; inversion STEP; subst; auto. Qed.
(* Program-counter provenance of the existing runtime installation. Stopped
   deliberately carries no claim about the actual flag at the instant of stop. *)
Definition boot_runtime_known phase : Prop := match phase with
 | Installing _ _ RuntimeInstalled | Retaining _ _ _ _ | Caching _ _ _
 | Returning _ _ _ | Usable _ _ _=>True | _=>False end.
Lemma boot_step_runtime_origin x y : boot_step x y -> boot_runtime_known (boot_pc y) ->
 boot_runtime_known (boot_pc x) \/ exists j id d,
 x=(j,Installing id d TopologyChecked) /\ y=(j,Installing id d RuntimeInstalled).
Proof.
 intros STEP KNOWN;destruct STEP;cbn in *;try tauto.
 right;do 3 eexists;split;reflexivity.
Qed.
Theorem boot_trace_runtime_origin x y : clos_refl_trans boot_state boot_step x y ->
 boot_runtime_known (boot_pc y) -> boot_runtime_known (boot_pc x) \/
 exists j id d,
 clos_refl_trans boot_state boot_step x (j,Installing id d TopologyChecked) /\
 clos_refl_trans boot_state boot_step (j,Installing id d RuntimeInstalled) y.
Proof.
 intro RUN;induction RUN;intro KNOWN.
 - destruct (boot_step_runtime_origin _ _ H KNOWN) as [BEFORE|[j [id [d [X Y]]]]];[auto|].
   subst;right;do 3 eexists;split;apply rt_refl.
 - auto.
 - destruct (IHRUN2 KNOWN) as [MID|[j [id [d [PREFIX SUFFIX]]]]].
   + destruct (IHRUN1 MID) as [BEFORE|[j [id [d [PREFIX SUFFIX]]]]];[auto|].
     right;exists j,id,d;split;[exact PREFIX|eapply rt_trans;eassumption].
   + right;exists j,id,d;split;[eapply rt_trans;eassumption|exact SUFFIX].
Qed.
Corollary usable_boot_initialized initial j id d ram :
 clos_refl_trans boot_state boot_step (initial,Selecting) (j,Usable id d ram) ->
 exists jr ir dr,
 clos_refl_trans boot_state boot_step (initial,Selecting) (jr,Installing ir dr TopologyChecked) /\
 boot_step (jr,Installing ir dr TopologyChecked) (jr,Installing ir dr RuntimeInstalled) /\
 clos_refl_trans boot_state boot_step (jr,Installing ir dr RuntimeInstalled) (j,Usable id d ram).
Proof.
 intro RUN;destruct (boot_trace_runtime_origin _ _ RUN I) as [BAD|[jr [ir [dr [PRE POST]]]]];[contradiction|].
 exists jr,ir,dr;split;[exact PRE|]. split;[apply boot_runtime|exact POST].
Qed.
(* Exact source of the final RAM runtime: after its last installation the
   journal and decoded identity are unchanged. A reset must install anew. *)
Definition boot_counter_origin pc : option (nat * recovery_decoding) :=
 match pc with
 | Installing id d RuntimeInstalled | Retaining id d _ _ | Caching id d _
 | Returning id d _ | Usable id d _=>Some (id,d)
 | _=>None end.
Lemma boot_counter_step x y id d : boot_step x y ->
 boot_counter_origin (boot_pc y)=Some (id,d) ->
 (boot_journal x=boot_journal y /\ boot_counter_origin (boot_pc x)=Some (id,d)) \/
 x=(boot_journal y,Installing id d TopologyChecked).
Proof.
 intros STEP ORIGIN;destruct STEP;cbn in ORIGIN |- *;try discriminate;
 try (left;split;[reflexivity|exact ORIGIN]).
 inversion ORIGIN;subst;right;reflexivity.
Qed.
Lemma boot_counter_trace x y : clos_refl_trans boot_state boot_step x y ->
 forall id d, boot_counter_origin (boot_pc y)=Some (id,d) ->
 (boot_journal x=boot_journal y /\ boot_counter_origin (boot_pc x)=Some (id,d)) \/
 clos_refl_trans boot_state boot_step x (boot_journal y,Installing id d TopologyChecked).
Proof.
 intro RUN;induction RUN;intros id d ORIGIN.
 - destruct (boot_counter_step _ _ _ _ H ORIGIN) as [SAME|EQ];[auto|].
   right;rewrite EQ;apply rt_refl.
 - left;auto.
 - destruct (IHRUN2 id d ORIGIN) as [[J MID]|PREFIX].
   + destruct (IHRUN1 id d MID) as [[FIRST O]|PREFIX];[left;split;congruence|].
     right;rewrite <- J;exact PREFIX.
   + right;eapply rt_trans;eassumption.
Qed.
Theorem usable_boot_counter_origin initial j id d ram :
 clos_refl_trans boot_state boot_step (initial,Selecting) (j,Usable id d ram) ->
 clos_refl_trans boot_state boot_step (initial,Selecting) (j,Installing id d TopologyChecked) /\
 boot_step (j,Installing id d TopologyChecked) (j,Installing id d RuntimeInstalled).
Proof.
 intro RUN;destruct (boot_counter_trace _ _ RUN id d eq_refl) as [[_ BAD]|PREFIX];[discriminate|].
 split;[exact PREFIX|constructor].
Qed.
End Boot.
