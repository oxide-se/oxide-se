From Coq Require Import List Arith NArith Lia Relation_Operators.
From OxideSE.Registry Require Import FlashSpec JournalComplement JournalFlashBridge
  JournalWriteEntry JournalScan JournalIndex JournalAppendSelection JournalAppendAuthority
  JournalRecoveryTrace JournalRequests JournalPhaseShape JournalReachableShape
  JournalProtocolAuthority.
Import ListNotations.

Definition control_image s := match s with
  | Ready f | Boot f | Frozen f | Writing f _ _ | AwaitAck f _ _ => f
  | Running _ _ _ r => flash_of r
  end.

(* Only a candidate write emits a new publication. Copying/restoring A does
   not. Histories retain repeated offsets; no unique-address premise is used. *)
Definition record_candidate history f index d :=
  if candidate_completed f index d then d :: history else history.
Definition publication_history_after history s s' :=
  match s with
  | Writing _ i d => record_candidate history (control_image s') i d
  | Running _ _ d r => match phase_of r with
      | RotAppend => record_candidate history (control_image s') 1 d
      | _ => history end
  | _ => history
  end.

Lemma record_candidate_head history f index d :
  hd_error (record_candidate history f index d) =
  authority_after_candidate (hd_error history) f index d.
Proof. unfold record_candidate, authority_after_candidate.
  destruct (candidate_completed f index d); reflexivity. Qed.

Record logged_state := Logged {
  journal_control : control;
  publications : list N;
  acknowledgements : list N
}.
(* Append-level success observed after readback. The outer commit still has
   to synchronize durable RAM, close scopes and collect before client success. *)
Definition acknowledgement_history_after history s s' :=
  match s, s' with
  | AwaitAck _ _ d, Ready _ => d :: history
  | _, _ => history
  end.

Lemma publication_history_contains_previous history s s' d :
  In d history -> In d (publication_history_after history s s').
Proof.
  intro Hin. destruct s; cbn [publication_history_after]; try exact Hin.
  - unfold record_candidate. destruct candidate_completed; simpl; auto.
  - destruct s as [p f]. destruct p; cbn [phase_of]; try exact Hin.
    unfold record_candidate. destruct candidate_completed; simpl; auto.
Qed.

Section History.
Variable g : geometry.
Variable sector page : nat.
Variable data_len : N.
Variable boss_ok : N -> bool.
Hypothesis Hgeom : journal_geometry g sector page.
Hypothesis Hsector8 : sector mod 8 = 0.

Definition history_invariant history s := match s with
  | Ready f | Boot f | Frozen f | Writing f _ _ =>
      observed sector page data_len boss_ok f = hd_error history
  | AwaitAck f _ d =>
      observed sector page data_len boss_ok f = hd_error history /\
      hd_error history = Some d
  | Running _ a _ r =>
      phase_authority sector page a data_len boss_ok (hd_error history) r
  end.

Lemma writing_before_program_not_completed f i d :
  invariant sector page data_len boss_ok (Writing f i d) ->
  candidate_completed f i d = false.
Proof.
  intros [Hr [[Hu [Hrange [Halign Hb]]] Hfirst]].
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hi [Hff _]].
  eapply erased_candidate_not_completed; eauto.
  unfold sector_bytes in Hi. rewrite length_map, length_seq in Hi.
  rewrite physical_slot_of_flash in Hff.
  - exact Hff.
  - pose proof (Nat.div_mod sector 8 ltac:(lia)). lia.
Qed.

Lemma rotation_before_append_not_completed old_slot a d f :
  invariant sector page data_len boss_ok (Running old_slot a d (State RotAppend f)) ->
  candidate_completed f 1 d = false.
Proof.
  intros [Hfit [Ha [[Hu [Hr [Hal Hb]]] [Hi [Hs Hclean]]]]].
  change (JournalPhaseShape.single sector a f) in Hs.
  destruct Hs as [_ Htail].
  destruct Hgeom as [_ [_ [_ [_ [Hsize _]]]]].
  eapply erased_candidate_not_completed; eauto.
  apply Htail. assert (2 <= sector/8) by (apply Nat.div_le_lower_bound; lia). lia.
Qed.

Lemma stutter_has_no_publication history s :
  invariant sector page data_len boss_ok s ->
  publication_history_after history s s = history.
Proof.
  intro Hi. destruct s; cbn [publication_history_after control_image]; try reflexivity.
  - unfold record_candidate. rewrite (writing_before_program_not_completed _ _ _ Hi).
    reflexivity.
  - destruct s as [p f]. destruct p; cbn [phase_of]; try reflexivity.
    unfold record_candidate. cbn [control_image flash_of].
    rewrite (rotation_before_append_not_completed _ _ _ _ Hi). reflexivity.
Qed.

Theorem step_preserves_history history s s' :
  invariant sector page data_len boss_ok s -> history_invariant history s ->
  step g sector page data_len boss_ok s s' ->
  history_invariant (publication_history_after history s s') s'.
Proof.
  intros Hi Hhist Hstep.
  pose proof (step_preserves_invariant g sector page data_len boss_ok
    Hgeom Hsector8 s s' Hi Hstep) as Hi'.
  destruct Hgeom as [Hsector [Hpage [_ [_ [Hsize [Hpage8 Hmultiple]]]]]].
  destruct Hstep; cbn [history_invariant publication_history_after control_image] in *.
  - exact Hhist.
  - unfold phase_authority. cbn [phase_of flash_of].
    assert (Hobs : observed sector page data_len boss_ok f = Some a).
    { unfold observed. rewrite H1. reflexivity. }
    split; congruence.
  - destruct Hi as [Hr [[Hu [Hrange [Halign Hb]]] Hfirst]].
    pose proof (Nat.div_mod (8*i) page ltac:(lia)) as Haddr.
    assert (Hwithin : (8*i) mod page+8 <= page) by (apply slot_fits_page; lia).
    assert (Hobs : observed sector page data_len boss_ok f' =
        hd_error (record_candidate history f' i d)).
    { rewrite record_candidate_head. rewrite <- Hhist. unfold observed.
      eapply (any_candidate_outcome_updates_authority g f f' sector page i
        (8*i/page*page) (8*i mod page) d data_len boss_ok result);
        eauto; try nia. exact (proj1 (proj2 Hr)). }
    destruct result; cbn [history_invariant]; auto.
    split; [exact Hobs|]. unfold record_candidate. cbn [control_image].
    rewrite (successful_candidate_completed g f f' (8*i/page*page) page
      (8*i mod page) i d ltac:(nia) Hwithin H). reflexivity.
  - exact (proj1 Hhist).
  - exact (proj1 Hhist).
  - exact Hhist.
  - exact Hhist.
  - unfold record_candidate. rewrite (writing_before_program_not_completed _ _ _ Hi).
    exact Hhist.
  - exact (proj1 Hhist).
  - exact Hhist.
  - destruct Hi as [Hfit [[Hu [Hr [Hal Hb]]] [[Hdu [Hdr [Hdal Hdb]]]
      [Hinv [Hs Hclean]]]]].
    pose proof (protocol_step_preserves_authority g sector page old_slot a d
      data_len boss_ok Hsector Hpage Hsize Hsector8 Hfit Hu Hr Hal Hb
      Hdu Hdr Hdal Hdb (hd_error history) s s' Hinv Hs Hclean Hhist H1) as Hnext.
    destruct s as [p f]. destruct p; cbn [phase_of protocol_authority_after] in *;
      try exact Hnext.
    rewrite record_candidate_head. exact Hnext.
  - assert (Hcomplete : candidate_completed f' 1 d = true).
    { eapply (successful_candidate_completed g f f' 0 page 8 1 d); eauto; lia. }
    unfold record_candidate. rewrite Hcomplete. cbn [hd_error].
    destruct Hi' as [Hr Hselected]. split; [|reflexivity].
    unfold observed. rewrite Hselected. reflexivity.
  - exact Hhist.
  - assert (Hafter : phase_authority sector page a data_len boss_ok
        (hd_error history) (State Inspect (flash_of s))).
    { destruct Hi as [Hfit [[Hu [Hr [Hal Hb]]] [[Hdu [Hdr [Hdal Hdb]]]
        [Hinv [Hs Hclean]]]]].
      eapply (reset_preserves_authority g sector page old_slot a d data_len
        boss_ok Hsector Hpage Hsize Hsector8 Hfit Hu Hr Hal Hb Hdr Hdal);
        eauto. }
    destruct s as [p f]. destruct p; cbn [phase_of flash_of]; try exact Hafter.
    unfold record_candidate. cbn [control_image flash_of].
    rewrite (rotation_before_append_not_completed _ _ _ _ Hi). exact Hafter.
  - rewrite stutter_has_no_publication; assumption.
Qed.

Lemma initialized_history f : initialized sector f -> history_invariant [] (Boot f).
Proof.
  intros [Hv [Herased Hclean]].
  assert (Hcheck : forall i, i < sector/8 ->
    checked_slot boss_ok data_len (N.of_nat page) (sector_bytes f 0 sector) i = None).
  { intros i Hi. unfold checked_slot. rewrite physical_slot_of_flash.
    - rewrite Nat.add_0_l, (erased_primary_slot f sector i Herased).
      + rewrite erased_slot_invalid. reflexivity.
      + pose proof (Nat.div_mod sector 8 ltac:(lia)). lia.
    - pose proof (Nat.div_mod sector 8 ltac:(lia)). lia. }
  assert (Hscan : forall count, count <= sector/8 ->
    latest_scan boss_ok data_len (N.of_nat page) (sector_bytes f 0 sector) count = None).
  { induction count as [|n IH]; intros Hcount; [reflexivity|].
    simpl. rewrite Hcheck by lia. apply IH. lia. }
  unfold history_invariant, observed, latest_in_model.
  unfold sector_bytes at 2. rewrite length_map, length_seq.
  rewrite Hscan by lia. reflexivity.
Qed.

Inductive logged_step : logged_state -> logged_state -> Prop :=
| record_step s s' history acks :
    step g sector page data_len boss_ok s s' ->
    logged_step (Logged s history acks)
      (Logged s' (publication_history_after history s s')
        (acknowledgement_history_after acks s s')).

Definition logged_invariant s :=
  invariant sector page data_len boss_ok (journal_control s) /\
  history_invariant (publications s) (journal_control s) /\
  Forall (fun d => In d (publications s)) (acknowledgements s).

Theorem logged_step_preserves_invariant s s' :
  logged_invariant s -> logged_step s s' -> logged_invariant s'.
Proof.
  intros [Hi [Hhist Hacks]] Hstep. destruct Hstep. cbn in Hi, Hhist, Hacks.
  split.
  - eapply step_preserves_invariant; eauto.
  - split.
    + eapply step_preserves_history; eauto.
    + cbn [publications acknowledgements].
      assert (Hold : Forall (fun d => In d (publication_history_after history s s')) acks).
      { eapply Forall_impl; [|exact Hacks]. intros d Hin.
        apply publication_history_contains_previous. exact Hin. }
      destruct s; cbn [acknowledgement_history_after]; try exact Hold.
      destruct s'; cbn [acknowledgement_history_after]; try exact Hold.
      constructor; [|exact Hold].
      destruct Hhist as [_ Hhead]. cbn [publication_history_after].
      destruct history as [|x xs]; cbn in Hhead; [discriminate|].
      inversion Hhead; subst. left. reflexivity.
Qed.

Theorem arbitrary_finite_history_preserves_invariant s s' :
  logged_invariant s -> clos_refl_trans logged_state logged_step s s' ->
  logged_invariant s'.
Proof.
  intros Hi Htrace. induction Htrace.
  - eapply logged_step_preserves_invariant; eauto.
  - exact Hi.
  - apply IHHtrace2. apply IHHtrace1. exact Hi.
Qed.

Definition logged_reachable s := exists f, initialized sector f /\
  clos_refl_trans logged_state logged_step (Logged (Boot f) [] []) s.

Theorem logged_reachable_invariant s : logged_reachable s -> logged_invariant s.
Proof.
  intros [f [Hinit Htrace]]. eapply arbitrary_finite_history_preserves_invariant;
    [|exact Htrace].
  split.
  - apply (initialized_invariant sector page data_len boss_ok Hsector8 f). exact Hinit.
  - split; [apply initialized_history; exact Hinit|constructor].
Qed.

Theorem ready_selection_is_latest_physical_publication f history acks :
  logged_reachable (Logged (Ready f) history acks) ->
  observed sector page data_len boss_ok f = hd_error history.
Proof. intro H. exact (proj1 (proj2 (logged_reachable_invariant _ H))). Qed.

Theorem acknowledged_no_later_publication_cannot_roll_back
    f i d history acks final final_history final_acks :
  logged_reachable (Logged (AwaitAck f i d) history acks) ->
  clos_refl_trans logged_state logged_step
    (Logged (Ready f) history (d::acks))
    (Logged (Ready final) final_history final_acks) ->
  final_history = history ->
  observed sector page data_len boss_ok final = Some d.
Proof.
  intros Hreachable Htrace Hsame.
  pose proof (logged_reachable_invariant _ Hreachable) as Hinv.
  assert (Hacked : logged_invariant (Logged (Ready f) history (d::acks))).
  { eapply logged_step_preserves_invariant; [exact Hinv|].
    apply (record_step (AwaitAck f i d) (Ready f) history acks).
    apply acknowledge. }
  pose proof (arbitrary_finite_history_preserves_invariant _ _ Hacked Htrace)
    as [_ [Hfinal _]].
  destruct Hinv as [_ [[_ Hhead] _]].
  cbn [history_invariant journal_control publications] in Hfinal, Hhead.
  rewrite Hsame in Hfinal. rewrite Hfinal. exact Hhead.
Qed.

End History.

(* Relational observer of the existing protection state. No second page table,
   no assertion that offsets are immutable identities. [view] is meaningful only
   for a fixed incarnation interpretation; maintaining that interpretation is a
   storage obligation, not a decoder or cryptographic guarantee. *)
From OxideSE.Registry Require Import PreparedAuthority CollectionRoots RetentionCoverage PageOwnership CompactUpdates.
Definition protection_history_link view s j :=
  physical_authority s = optional_root view
    (option_map N.to_nat (hd_error (publications j))).

Theorem collection_keeps_history_link page initialized durable current resolved view s j :
  protection_history_link view s j ->
  protection_history_link view
    (collection_return page initialized durable current resolved s) j.
Proof.
  unfold protection_history_link, collection_return.
  destruct (collection_enabled initialized durable current s);
    [destruct resolved|]; exact (fun H => H).
Qed.

Theorem ready_selected_dependencies_protected sector page data_len boss_ok view s f history acks d :
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history acks) ->
  protection_history_link view s (Logged (Ready f) history acks) ->
  protection_invariant page s ->
  observed sector page data_len boss_ok f = Some d ->
  protected (needed page (root_extents (view (N.to_nat d)))) (protection_table s).
Proof.
  intros [_ [H _]] LINK [[C _] _] SELECT.
  change (observed sector page data_len boss_ok f = hd_error history) in H.
  unfold protection_history_link in LINK; simpl in LINK.
  rewrite <- H, SELECT in LINK. simpl in LINK.
  eapply protected_subset; [|exact C]. intros r R.
  unfold required_ranges. repeat rewrite in_app_iff. right; right; left.
  rewrite LINK; exact R.
Qed.

Theorem collected_ready_authority_protected sector page data_len boss_ok view marker
    durable current entries load initialized resolved s f history acks d :
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history acks) ->
  protection_history_link view s (Logged (Ready f) history acks) ->
  protection_invariant page s ->
  collection_boundary view marker durable current entries load s ->
  (forall ranges, resolved = Some ranges -> ranges = collect_ranges view marker current entries load) ->
  observed sector page data_len boss_ok f = Some d ->
  protected (needed page (root_extents (view (N.to_nat d))))
    (protection_table (collection_return page initialized durable current resolved s)).
Proof.
  intros J L I B R S. eapply ready_selected_dependencies_protected; eauto.
  - eapply collection_keeps_history_link; eauto.
  - eapply collection_return_preserves; eauto.
Qed.

(* Local Data services (including freeze and RAM close) do not alter the
   physical journal or its authority envelope. This does not cover publication. *)
Lemma local_data_keeps_history_link view command s j :
  protection_history_link view s j ->
  protection_history_link view (data_next command s) j.
Proof.
  unfold protection_history_link. destruct command; cbn [data_next];
    try exact (fun H => H);
    destruct (pending_preparation s); exact (fun H => H).
Qed.
Theorem finite_local_data_keeps_history_link view commands s j :
  protection_history_link view s j ->
  protection_history_link view (execute_data commands s) j.
Proof.
  revert s; induction commands as [|c tail IH]; intros s L; simpl; auto.
  apply IH. apply local_data_keeps_history_link; exact L.
Qed.

(* Success of the candidate command, with or without rotation, leads to
   AwaitAck. Its history invariant identifies the actual completed candidate.
   Journal acknowledgement below is append success, NOT the client response. *)
Definition candidate_write_source j d :=
  match journal_control j with
  | Writing _ _ candidate => candidate = d
  | Running _ _ candidate r => candidate = d /\ phase_of r = RotAppend
  | _ => False end.

Theorem publication_exit_to_collection g sector page data_len boss_ok view marker
    s saved j f index d history acks initialized resolved :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  logged_step g sector page data_len boss_ok j (Logged (AwaitAck f index d) history acks) ->
  data_invariant s -> protection_frozen s = false ->
  protection_saved s = [saved] -> pending_preparation s = None ->
  In marker (protection_base s) ->
  protection_current s ++ attached_ranges s = root_extents (view (N.to_nat d)) ->
  (forall ranges, resolved = Some ranges -> ranges =
    collect_ranges view marker (Some (N.to_nat d)) (object_extents (view (N.to_nat d))) []) ->
  let candidate := root_extents (view (N.to_nat d)) in
  let physical := slot_publication candidate s in
  let closed := successful_external_close marker candidate saved s in
  let final := collection_return 256 initialized (Some (N.to_nat d)) (Some (N.to_nat d)) resolved closed in
  hd_error history = Some d /\
  protection_history_link view physical (Logged (AwaitAck f index d) history acks) /\
  protection_invariant 256 physical /\
  protection_invariant 256 final /\
  collection_boundary view marker (Some (N.to_nat d)) (Some (N.to_nat d))
    (object_extents (view (N.to_nat d))) [] closed /\
  protection_history_link view final (Logged (Ready f) history (d :: acks)).
Proof.
  intros GEOM DIV J STEP INV F STACK P M CUR RES; cbn zeta.
  pose proof (logged_step_preserves_invariant g sector page data_len boss_ok GEOM DIV
    _ _ J STEP) as J'.
  destruct J' as [_ [[OBS HEAD] _]].
  change (hd_error history = Some d) in HEAD.
  destruct (successful_exit_collection view marker (N.to_nat d) saved s initialized resolved
    INV F STACK P M CUR RES) as [SAFE BOUNDARY].
  split; [exact HEAD|]. split.
  - unfold protection_history_link; simpl. rewrite HEAD; reflexivity.
  - split; [apply slot_publication_preserves; [exact (proj1 INV)|exact P|exact CUR]|].
    split; [exact SAFE|]. split; [exact BOUNDARY|].
    apply collection_keeps_history_link. unfold protection_history_link; simpl.
    rewrite HEAD; reflexivity.
Qed.

Lemma await_ack_slot_completed sector page data_len boss_ok f index d history acks :
  sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (AwaitAck f index d) history acks) ->
  candidate_completed f index d = true.
Proof.
  intros DIV [[_ SELECT] _].
  destruct (selected_has_code sector page data_len boss_ok DIV f index d SELECT)
    as [_ [_ CODE]]. unfold candidate_completed. rewrite CODE.
  destruct (list_eq_dec N.eq_dec (code_bytes d) (code_bytes d)); congruence.
Qed.
Theorem ordinary_completion_emits_candidate sector page data_len boss_ok before after index d history acks :
  sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (AwaitAck after index d) history acks) ->
  publication_history_after history (Writing before index d) (AwaitAck after index d) = d :: history.
Proof.
  intros DIV INV. cbn [publication_history_after control_image]. unfold record_candidate.
  rewrite (await_ack_slot_completed sector page data_len boss_ok after index d history acks DIV INV).
  reflexivity.
Qed.
Theorem rotation_completion_emits_candidate sector page data_len boss_ok before after old_slot old d history acks :
  sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (AwaitAck after 1 d) history acks) ->
  publication_history_after history (Running old_slot old d (State RotAppend before))
    (AwaitAck after 1 d) = d :: history.
Proof.
  intros DIV INV. cbn [publication_history_after phase_of control_image]. unfold record_candidate.
  rewrite (await_ack_slot_completed sector page data_len boss_ok after 1 d history acks DIV INV).
  reflexivity.
Qed.
Theorem append_return_preserves_logged_invariant g sector page data_len boss_ok f index d history acks :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (AwaitAck f index d) history acks) ->
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history (d :: acks)).
Proof.
  intros G D I. eapply (logged_step_preserves_invariant g sector page data_len boss_ok G D); [exact I|].
  apply (record_step g sector page data_len boss_ok (AwaitAck f index d) (Ready f) history acks).
  apply acknowledge.
Qed.

Definition journal_idle sector page data_len boss_ok view marker id s j :=
  idle_root view marker id s /\ logged_invariant sector page data_len boss_ok j /\
  (exists f, journal_control j = Ready f) /\
  hd_error (publications j) = Some (N.of_nat id) /\ protection_history_link view s j.

Theorem completed_trace_returns_ready g sector page data_len boss_ok j f index id history acks :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok)
    j (Logged (AwaitAck f index (N.of_nat id)) history acks) ->
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history (N.of_nat id :: acks)) /\
  hd_error history = Some (N.of_nat id) /\
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok)
    j (Logged (Ready f) history (N.of_nat id :: acks)).
Proof.
  intros G D I T.
  pose proof (arbitrary_finite_history_preserves_invariant g sector page data_len boss_ok G D _ _ I T) as A.
  split; [eapply append_return_preserves_logged_invariant; eauto|]. split.
  - exact (proj2 (proj1 (proj2 A))).
  - eapply rt_trans; [exact T|]. apply rt_step.
    apply (record_step g sector page data_len boss_ok (AwaitAck f index (N.of_nat id))
      (Ready f) history acks). apply acknowledge.
Qed.

Lemma idle_root_links_ready sector page data_len boss_ok view marker id s f history acks :
  idle_root view marker id s ->
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history acks) ->
  hd_error history = Some (N.of_nat id) ->
  journal_idle sector page data_len boss_ok view marker id s (Logged (Ready f) history acks).
Proof.
  intros R J H. split; [exact R|]. split; [exact J|]. split; [exists f; reflexivity|].
  split; [exact H|]. unfold protection_history_link; simpl. rewrite H; simpl.
  rewrite Nat2N.id. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 R))))))).
Qed.

(* Successful append continuations only: resetting a running protocol enters
   Inspect, while returned physical errors enter Frozen/ReturnedError. Those
   states are deliberately excluded from this pre-reset transaction join. *)
Definition successful_append_control d c : Prop := match c with
  | Ready _ => True
  | Writing _ _ candidate | AwaitAck _ _ candidate => candidate = d
  | Running _ _ candidate r => candidate = d /\
      match phase_of r with
      | RotCopy | RotErasePrimary | RotRestorePrimary | RotEraseSecondary | RotAppend => True
      | _ => False end
  | _ => False end.
Definition successful_logged_step g sector page data_len boss_ok d j j' :=
  successful_append_control d (journal_control j) /\
  successful_append_control d (journal_control j') /\
  logged_step g sector page data_len boss_ok j j'.
Lemma successful_trace_is_logged g sector page data_len boss_ok d j j' :
  clos_refl_trans logged_state (successful_logged_step g sector page data_len boss_ok d) j j' ->
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok) j j'.
Proof.
  intros T; induction T.
  - apply rt_step; exact (proj2 (proj2 H)).
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Theorem two_transactions_with_journal g sector page data_len boss_ok view marker root0 root1 root2
    kind ranges image i a b ra rb s j0 f1 k1 h1 ack1 f2 k2 h2 ack2 :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  journal_idle sector page data_len boss_ok view marker root0 s j0 ->
  object_extents (view root0) = image_dependencies ranges image ->
  image_unique kind image -> data_slot_for kind image (entry_key kind a) = Some i ->
  entry_key kind a = entry_key kind b ->
  ranges a = [ra] -> ranges b = [rb] ->
  free_range 256 (protection_table (data_next DataBegin s)) ra ->
  free_range 256 (protection_table (modified_transaction ranges image i a ra s)) (boss_extent (view root1)) ->
  object_extents (view root1) = image_dependencies ranges (image_replace image i (Some a)) ->
  clos_refl_trans logged_state (successful_logged_step g sector page data_len boss_ok (N.of_nat root1))
    j0 (Logged (AwaitAck f1 k1 (N.of_nat root1)) h1 ack1) ->
  let first := data_transaction view marker root1 ranges image i a ra s in
  free_range 256 (protection_table (data_next DataBegin first)) rb ->
  free_range 256 (protection_table (modified_transaction ranges (image_replace image i (Some a)) i b rb first))
    (boss_extent (view root2)) ->
  object_extents (view root2) = image_dependencies ranges (image_replace image i (Some b)) ->
  clos_refl_trans logged_state (successful_logged_step g sector page data_len boss_ok (N.of_nat root2))
    (Logged (Ready f1) h1 (N.of_nat root1 :: ack1)) (Logged (AwaitAck f2 k2 (N.of_nat root2)) h2 ack2) ->
  data_slot_for kind (image_replace image i (Some a)) (entry_key kind b) = Some i /\
  journal_idle sector page data_len boss_ok view marker root2
    (data_transaction view marker root2 ranges (image_replace image i (Some a)) i b rb first)
    (Logged (Ready f2) h2 (N.of_nat root2 :: ack2)) /\
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok)
    j0 (Logged (Ready f2) h2 (N.of_nat root2 :: ack2)).
Proof.
  intros G D [R0 [J0 _]] E0 UNIQUE SLOT KEY A B FA BA E1 T1 first FB BB E2 T2.
  apply successful_trace_is_logged in T1. apply successful_trace_is_logged in T2.
  destruct (completed_trace_returns_ready g sector page data_len boss_ok j0 f1 k1 root1 h1 ack1
    G D J0 T1) as [J1 [H1 REACH1]].
  assert (MID : journal_idle sector page data_len boss_ok view marker root1 first
      (Logged (Ready f1) h1 (N.of_nat root1 :: ack1))).
  { apply idle_root_links_ready; [|exact J1|exact H1].
    eapply data_transaction_idle; eauto. }
  destruct MID as [RMID [JMID REST]].
  destruct (completed_trace_returns_ready g sector page data_len boss_ok _ f2 k2 root2 h2 ack2
    G D JMID T2) as [J2 [H2 REACH2]].
  split.
  - rewrite <- KEY. apply repeated_identity_uses_same_slot. eapply data_slot_for_admissible; eauto.
  - split.
    + apply idle_root_links_ready; [|exact J2|exact H2].
      eapply data_transaction_idle with (old_id:=root1); try eassumption.
      rewrite image_replace_shadow; exact E2.
    + eapply rt_trans; [exact REACH1|exact REACH2].
Qed.

(* The fallible append interval, with no reset and no successful append
   acknowledgement. This is a restriction of the existing logged transitions,
   not a second journal or ownership state. *)
Definition uncertain_append_control d c : Prop := match c with
  | Ready _ | Frozen _ => True
  | Writing _ _ x | AwaitAck _ _ x => x = d
  | Running _ _ x r => x = d /\
      match phase_of r with
      | RotCopy | RotErasePrimary | RotRestorePrimary | RotEraseSecondary |
        RotAppend | ReturnedError => True
      | _ => False end
  | Boot _ => False
  end.
Definition no_append_return before after : Prop :=
  match before, after with AwaitAck _ _ _, Ready _ => False | _, _ => True end.
Definition uncertain_logged_step g sector page data_len boss_ok d j j' :=
  uncertain_append_control d (journal_control j) /\
  uncertain_append_control d (journal_control j') /\
  no_append_return (journal_control j) (journal_control j') /\
  logged_step g sector page data_len boss_ok j j'.

Lemma uncertain_step_heads g sector page data_len boss_ok d j j' :
  uncertain_logged_step g sector page data_len boss_ok d j j' ->
  (hd_error (publications j') = hd_error (publications j) \/
   hd_error (publications j') = Some d) /\
  acknowledgements j' = acknowledgements j.
Proof.
  intros [BEFORE [AFTER [NO STEP]]]. destruct STEP as [c c' hist acks STEP].
  cbn in BEFORE, AFTER, NO |- *.
  split.
  - destruct c; cbn [publication_history_after]; try (left; reflexivity).
    + cbn in BEFORE. subst. unfold record_candidate.
      destruct candidate_completed; [right|left]; reflexivity.
    + cbn in BEFORE. destruct BEFORE as [E PH]. subst.
      destruct s as [phase f]; destruct phase; cbn [phase_of];
        try (left; reflexivity).
      unfold record_candidate. destruct candidate_completed; [right|left]; reflexivity.
  - unfold acknowledgement_history_after.
    destruct c; try reflexivity. destruct c'; try reflexivity. contradiction.
Qed.

Theorem uncertain_trace_authorities g sector page data_len boss_ok d j j' :
  clos_refl_trans logged_state (uncertain_logged_step g sector page data_len boss_ok d) j j' ->
  (hd_error (publications j') = hd_error (publications j) \/
   hd_error (publications j') = Some d) /\
  acknowledgements j' = acknowledgements j /\
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok) j j'.
Proof.
  intro T. induction T.
  - destruct (uncertain_step_heads _ _ _ _ _ _ _ _ H) as [HEAD ACK].
    split; [exact HEAD|]. split; [exact ACK|]. apply rt_step; exact (proj2 (proj2 (proj2 H))).
  - split; [left; reflexivity|]. split; [reflexivity|apply rt_refl].
  - destruct IHT1 as [A [B C]], IHT2 as [D [E F]].
    split; [destruct A, D; [left|right|right|right]; congruence|].
    split; [congruence|eapply rt_trans; eauto].
Qed.

(* The physical history determines the selected envelope. Candidate protection
   comes from the current image; previous protection comes from the initial
   authority. No union-coverage premise is supplied at the error exit. *)
Theorem uncertain_publication_then_cleanup g sector page data_len boss_ok view
    old d s j j' commands :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  protection_invariant 256 s -> pending_preparation s = None ->
  hd_error (publications j) = Some old ->
  protection_history_link view s j ->
  protection_current s ++ attached_ranges s = root_extents (view (N.to_nat d)) ->
  clos_refl_trans logged_state (uncertain_logged_step g sector page data_len boss_ok d) j j' ->
  let selected := optional_root view (option_map N.to_nat (hd_error (publications j'))) in
  data_calls commands (uncertain_return selected s) ->
  let final := execute_data commands (uncertain_return selected s) in
  logged_invariant sector page data_len boss_ok j' /\
  (hd_error (publications j') = Some old \/ hd_error (publications j') = Some d) /\
  acknowledgements j' = acknowledgements j /\
  data_invariant final /\ protection_frozen final = true /\
  protection_table final = protection_table s /\
  protection_history_link view final j' /\
  acknowledged_authority final = acknowledged_authority s /\
  protected (needed 256 (root_extents (view (N.to_nat old)) ++
    root_extents (view (N.to_nat d)))) (protection_table final).
Proof.
  intros G DIV J INV P OLD LINK CUR TRACE selected CALL final.
  destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ TRACE) as [HEAD [ACK LOG]].
  assert (OLDROOT : physical_authority s = root_extents (view (N.to_nat old))).
  { unfold protection_history_link in LINK. rewrite OLD in LINK. exact LINK. }
  assert (SEL : forall r, In r selected ->
      In r (physical_authority s ++ root_extents (view (N.to_nat d)))).
  { unfold selected. destruct HEAD as [H|H]; rewrite H; [rewrite OLD|]; simpl;
      intros r R; apply in_app_iff; [left; rewrite OLDROOT|right]; exact R. }
  destruct (frozen_data_cleanup _ selected s commands INV P CUR SEL CALL)
    as [I [F [T [PH [A COVER]]]]].
  split; [eapply arbitrary_finite_history_preserves_invariant; eauto|].
  split; [rewrite OLD in HEAD; exact HEAD|]. split; [exact ACK|].
  split; [exact I|]. split; [exact F|]. split; [exact T|].
  split; [exact PH|]. split; [exact A|]. rewrite OLDROOT in COVER. exact COVER.
Qed.

Theorem readback_error_uncertain_edge g sector page data_len boss_ok f i d history acks :
  uncertain_logged_step g sector page data_len boss_ok d
    (Logged (AwaitAck f i d) history acks) (Logged (Frozen f) history acks).
Proof.
  split; [reflexivity|]. split; [exact I|]. split; [exact I|].
  apply (record_step g sector page data_len boss_ok (AwaitAck f i d) (Frozen f)).
  apply postwrite_readback_error.
Qed.

Theorem rotation_error_uncertain_edge g sector page data_len boss_ok old_slot old d phase f after history acks :
  uncertain_append_control d (Running old_slot old d (State phase f)) ->
  phase <> ReturnedError ->
  protocol_step g sector page old data_len boss_ok d (State phase f) (State ReturnedError after) ->
  uncertain_logged_step g sector page data_len boss_ok d
    (Logged (Running old_slot old d (State phase f)) history acks)
    (Logged (Running old_slot old d (State ReturnedError after))
      (publication_history_after history (Running old_slot old d (State phase f))
        (Running old_slot old d (State ReturnedError after))) acks).
Proof.
  intros PH NOTERR STEP. split; [exact PH|]. split; [split; reflexivity|]. split; [exact I|].
  apply (record_step g sector page data_len boss_ok
    (Running old_slot old d (State phase f)) (Running old_slot old d (State ReturnedError after))).
  apply advance_protocol; [exact NOTERR|right; discriminate|exact STEP].
Qed.

(* Relative journal addresses occupy [0,2*sector). Translating this frame to
   the Rust persistence area remains a numeric/layout refinement obligation. *)
Lemma protocol_frame_after_journal g sector page old d data_len boss_ok before after x :
  sector_size g = sector -> page <= sector -> 2*sector <= x ->
  protocol_step g sector page old data_len boss_ok d before after ->
  flash_of after x = flash_of before x.
Proof.
  intros SECTOR PAGE X STEP. destruct STEP as [b a R|b a R]; destruct R;
    try destruct result; cbn [flash_of]; try reflexivity;
    match goal with
    | H : program_step _ _ _ _ _ _ |- _ =>
        apply (program_locality _ _ _ _ _ _ H); right;
        unfold copied_buffer, restored_buffer, appended_buffer;
        rewrite write_entry_page_length; lia
    | H : erase_step _ _ _ _ _ |- _ =>
        apply (erase_locality _ _ _ _ _ H); right; rewrite SECTOR; lia
    end.
Qed.

Theorem journal_step_frame_after_journal g sector page data_len boss_ok before after x :
  journal_geometry g sector page ->
  invariant sector page data_len boss_ok before ->
  step g sector page data_len boss_ok before after -> 2*sector <= x ->
  control_image after x = control_image before x.
Proof.
  intros G INV STEP X.
  destruct G as [SECTOR [PAGE [_ [_ [SIZE [DIV MULT]]]]]].
  destruct STEP; cbn [control_image]; try reflexivity.
  - destruct INV as [_ [_ FIRST]].
    destruct (first_empty_slot_sound _ _ FIRST) as [BOUND _].
    unfold sector_bytes in BOUND; rewrite length_map, length_seq in BOUND.
    assert (FIT : 8*i/page*page + page <= sector).
    { apply aligned_page_stays_in_primary with (addr := 8*i); try reflexivity; try lia.
      pose proof (Nat.div_mod sector 8 ltac:(lia)); lia. }
    destruct result; cbn [control_image]; apply (program_locality _ _ _ _ _ _ H);
      right; unfold candidate_buffer; rewrite write_entry_page_length; lia.
  - eapply (protocol_frame_after_journal g sector page a d data_len boss_ok s s' x); eauto; lia.
  - apply (program_locality _ _ _ _ _ _ H); right.
    unfold appended_buffer; rewrite write_entry_page_length; lia.
Qed.

Theorem logged_trace_frame_after_journal g sector page data_len boss_ok j j' x :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok) j j' ->
  2*sector <= x -> control_image (journal_control j') x = control_image (journal_control j) x.
Proof.
  intros G DIV INV TRACE X. induction TRACE.
  - destruct H. eapply journal_step_frame_after_journal; eauto. exact (proj1 INV).
  - reflexivity.
  - rewrite IHTRACE2.
    + apply IHTRACE1; exact INV.
    + eapply arbitrary_finite_history_preserves_invariant; eauto.
Qed.

Definition returned_error_control c : Prop := match c with
  | Frozen _ => True
  | Running _ _ _ r => phase_of r = ReturnedError
  | _ => False end.
Lemma returned_error_control_stutters g sector page data_len boss_ok d before after :
  returned_error_control before -> uncertain_append_control d after ->
  step g sector page data_len boss_ok before after -> after = before.
Proof.
  intros ERROR NEXT STEP. destruct STEP; cbn in ERROR, NEXT; try contradiction;
    try discriminate; try reflexivity.
  tauto.
Qed.

Theorem frozen_journal_continuation_stutters g sector page data_len boss_ok d j j' :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  returned_error_control (journal_control j) ->
  uncertain_logged_step g sector page data_len boss_ok d j j' -> j' = j.
Proof.
  intros G DIV INV ERROR [BEFORE [AFTER [NO STEP]]].
  destruct STEP as [c c' history acks STEP]. cbn in ERROR, BEFORE, AFTER, NO, INV |- *.
  assert (E : c' = c) by (eapply returned_error_control_stutters; eauto).
  subst c'. rewrite (stutter_has_no_publication g sector page data_len boss_ok G DIV history c (proj1 INV)).
  destruct c; cbn in ERROR; try contradiction; reflexivity.
Qed.

Theorem frozen_journal_finite_continuation_stutters g sector page data_len boss_ok d j j' :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  returned_error_control (journal_control j) ->
  clos_refl_trans logged_state (uncertain_logged_step g sector page data_len boss_ok d) j j' ->
  j' = j.
Proof.
  intros G DIV INV ERROR TRACE. induction TRACE.
  - eapply frozen_journal_continuation_stutters; eauto.
  - reflexivity.
  - assert (E : y = x) by (apply IHTRACE1; assumption). subst y.
    apply IHTRACE2; assumption.
Qed.

Theorem uncertain_trace_reset_boundary g sector page data_len boss_ok d j j' :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  clos_refl_trans logged_state (uncertain_logged_step g sector page data_len boss_ok d) j j' ->
  logged_invariant sector page data_len boss_ok j' /\
  (hd_error (publications j') = hd_error (publications j) \/
    hd_error (publications j') = Some d) /\
  acknowledgements j' = acknowledgements j /\
  (forall x, 2*sector <= x ->
    control_image (journal_control j') x = control_image (journal_control j) x).
Proof.
  intros G DIV INV TRACE.
  destruct (uncertain_trace_authorities _ _ _ _ _ _ _ _ TRACE) as [HEAD [ACK LOG]].
  split; [eapply arbitrary_finite_history_preserves_invariant; eauto|].
  split; [exact HEAD|]. split; [exact ACK|]. intros x X.
  eapply logged_trace_frame_after_journal; eauto.
Qed.

(* Only flash is operational across reset. Logged history is a proof observer;
   no protection_state is an argument of this reset/recovery interface. *)
Definition journal_after_reset c := match c with
  | Running slot old candidate r => Running slot old candidate (State Inspect (flash_of r))
  | _ => Boot (control_image c) end.
Definition logged_after_reset j := Logged (journal_after_reset (journal_control j))
  (publications j) (acknowledgements j).
Theorem returned_error_reset_step g sector page data_len boss_ok j :
  returned_error_control (journal_control j) ->
  logged_step g sector page data_len boss_ok j (logged_after_reset j).
Proof.
  destruct j as [c history acks]; intros E; destruct c as [f|f|f|f i d|f i d|slot old candidate r]; cbn in E; try contradiction.
  - apply (record_step g sector page data_len boss_ok (Frozen f) (Boot f)); apply reset_frozen.
  - destruct r as [phase f]; cbn in E; subst phase.
    apply (record_step g sector page data_len boss_ok
      (Running slot old candidate (State ReturnedError f)) (Running slot old candidate (State Inspect f))).
    apply reset_protocol.
Qed.
Definition recovering_control c : Prop := match c with
  | Boot _ | Ready _ => True
  | Running _ _ _ r => match phase_of r with
      | Inspect | ErasePrimary | RestorePrimary | EraseSecondary | Done | ReturnedError => True
      | _ => False end
  | _ => False end.
Definition recovery_logged_step g sector page data_len boss_ok j j' :=
  recovering_control (journal_control j) /\ recovering_control (journal_control j') /\
  logged_step g sector page data_len boss_ok j j'.
Lemma recovery_edge_history g sector page data_len boss_ok j j' :
  recovery_logged_step g sector page data_len boss_ok j j' ->
  publications j' = publications j /\ acknowledgements j' = acknowledgements j.
Proof.
  intros [B [A STEP]]. destruct STEP as [c c' h a STEP]; cbn in B, A |- *.
  destruct c; cbn in B; try contradiction; try (split; reflexivity).
  destruct s as [phase f]; destruct phase; cbn in B; try contradiction; split; reflexivity.
Qed.
Theorem recovery_trace_history g sector page data_len boss_ok j j' :
  clos_refl_trans logged_state (recovery_logged_step g sector page data_len boss_ok) j j' ->
  publications j' = publications j /\ acknowledgements j' = acknowledgements j /\
  clos_refl_trans logged_state (logged_step g sector page data_len boss_ok) j j'.
Proof.
  intro T; induction T.
  - destruct (recovery_edge_history _ _ _ _ _ _ _ H) as [P A].
    split; [exact P|]. split; [exact A|]. apply rt_step; exact (proj2 (proj2 H)).
  - split; [reflexivity|]. split; [reflexivity|apply rt_refl].
  - destruct IHT1 as [P1 [A1 TRACE1]], IHT2 as [P2 [A2 TRACE2]].
    split; [congruence|]. split; [congruence|eapply rt_trans; eauto].
Qed.

Theorem reset_recovery_selects_history g sector page data_len boss_ok j f history acks :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  returned_error_control (journal_control j) ->
  clos_refl_trans logged_state (recovery_logged_step g sector page data_len boss_ok)
    (logged_after_reset j) (Logged (Ready f) history acks) ->
  logged_invariant sector page data_len boss_ok (Logged (Ready f) history acks) /\
  history = publications j /\ acks = acknowledgements j /\
  observed sector page data_len boss_ok f = hd_error (publications j) /\
  (forall x, 2*sector <= x -> f x = control_image (journal_control j) x).
Proof.
  intros G DIV INV ERROR TRACE.
  pose proof (returned_error_reset_step g sector page data_len boss_ok j ERROR) as RESET.
  destruct (recovery_trace_history _ _ _ _ _ _ _ TRACE) as [P [A T]].
  assert (ALL : clos_refl_trans logged_state (logged_step g sector page data_len boss_ok)
    j (Logged (Ready f) history acks)).
  { eapply rt_trans; [apply rt_step; exact RESET|exact T]. }
  pose proof (arbitrary_finite_history_preserves_invariant _ _ _ _ _ G DIV _ _ INV ALL) as FINAL.
  split; [exact FINAL|]. split; [exact P|]. split; [exact A|]. split.
  - change (history = publications j) in P. rewrite <- P. exact (proj1 (proj2 FINAL)).
  - intros x X. exact (logged_trace_frame_after_journal _ _ _ _ _ _ _ x G DIV INV ALL X).
Qed.

Definition object_flash sector (f : flash) : flash := fun a => f (2*sector+a).
Theorem reset_recovery_preserves_object_extents g sector page data_len boss_ok j f history acks ranges :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok j ->
  returned_error_control (journal_control j) ->
  clos_refl_trans logged_state (recovery_logged_step g sector page data_len boss_ok)
    (logged_after_reset j) (Logged (Ready f) history acks) ->
  unchanged ranges (object_flash sector (control_image (journal_control j))) (object_flash sector f).
Proof.
  intros G DIV INV ERR TRACE.
  destruct (reset_recovery_selects_history _ _ _ _ _ _ _ _ _ G DIV INV ERR TRACE)
    as [_ [_ [_ [_ FRAME]]]].
  intros r a IN RANGE. apply FRAME; lia.
Qed.

(* Decode is a local lower component: success specifies BOSS range and exact
   image dependencies. It does not guarantee ownership or storage lifetime. *)
Theorem recovered_registry_can_start_transaction g sector data_len boss_ok view marker ranges
    (decode : flash -> nat -> option recovery_decoding)
    j f history acks selected decoded :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok j ->
  returned_error_control (journal_control j) ->
  hd_error (publications j) = Some (N.of_nat selected) ->
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
    (logged_after_reset j) (Logged (Ready f) history acks) ->
  (forall bytes id reply, decode bytes id = Some reply -> decoded_root_agrees view ranges id reply) ->
  decode (object_flash sector f) selected = Some decoded ->
  journal_idle sector 256 data_len boss_ok view marker selected
    (rebuild_decoded marker ranges decoded) (Logged (Ready f) history acks) /\
  image_current_correspondence ranges (recovered_image decoded) [recovered_boss decoded]
    (rebuild_decoded marker ranges decoded) /\
  data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
  data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)).
Proof.
  intros G DIV INV ERR HEAD TRACE FORMAT READ.
  destruct (reset_recovery_selects_history _ _ _ _ _ _ _ _ _ G DIV INV ERR TRACE)
    as [J [H [A [SELECT FRAME]]]].
  destruct (decoded_reconstruction_opens_transaction view marker ranges selected decoded
    (FORMAT _ _ _ READ)) as [IDLE [IMAGE BEGIN]].
  split; [|split; assumption].
  apply idle_root_links_ready; [exact IDLE|exact J|]. rewrite H; exact HEAD.
Qed.

Theorem uncertain_reset_recovery_restart g sector data_len boss_ok view marker ranges
    (decode : flash -> nat -> option recovery_decoding)
    j error_j f history acks old candidate :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok j ->
  hd_error (publications j) = Some old ->
  clos_refl_trans logged_state (uncertain_logged_step g sector 256 data_len boss_ok candidate) j error_j ->
  returned_error_control (journal_control error_j) ->
  clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
    (logged_after_reset error_j) (Logged (Ready f) history acks) ->
  (forall bytes id reply, decode bytes id = Some reply -> decoded_root_agrees view ranges id reply) ->
  (forall bytes bytes' id, unchanged (root_extents (view id)) bytes bytes' ->
    decode bytes id = decode bytes' id) ->
  (forall id, id = N.to_nat old \/ id = N.to_nat candidate ->
    exists reply, decode (object_flash sector (control_image (journal_control j))) id = Some reply) ->
  exists selected decoded,
    (selected = N.to_nat old \/ selected = N.to_nat candidate) /\
    decode (object_flash sector f) selected = Some decoded /\
    journal_idle sector 256 data_len boss_ok view marker selected
      (rebuild_decoded marker ranges decoded) (Logged (Ready f) history acks) /\
    image_current_correspondence ranges (recovered_image decoded) [recovered_boss decoded]
      (rebuild_decoded marker ranges decoded) /\
    data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
    data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded)).
Proof.
  intros G DIV INV OLD UNC ERROR REC FORMAT LOCAL READABLE.
  destruct (uncertain_trace_reset_boundary _ _ _ _ _ _ _ _ G DIV INV UNC)
    as [ERRINV [HEAD [ACK FRAME]]].
  assert (EX : exists id, (id = N.to_nat old \/ id = N.to_nat candidate) /\
    hd_error (publications error_j) = Some (N.of_nat id)).
  { destruct HEAD as [H|H].
    - exists (N.to_nat old); split; [auto|]. rewrite N2Nat.id; congruence.
    - exists (N.to_nat candidate); split; [auto|]. rewrite N2Nat.id; exact H. }
  destruct EX as [id [CHOICE HEADID]]. destruct (READABLE id CHOICE) as [decoded READ].
  assert (STABLE : unchanged (root_extents (view id))
      (object_flash sector (control_image (journal_control j))) (object_flash sector f)).
  { intros r a IN BOUND. unfold object_flash.
    destruct (reset_recovery_selects_history _ _ _ _ _ _ _ _ _ G DIV ERRINV ERROR REC)
      as [_ [_ [_ [_ AFTER]]]]. rewrite AFTER by lia. apply FRAME; lia. }
  rewrite (LOCAL _ _ id STABLE) in READ.
  exists id, decoded. split; [exact CHOICE|]. split; [exact READ|].
  eapply recovered_registry_can_start_transaction; eauto.
Qed.

Theorem recovered_journal_remember_can_begin sector data_len boss_ok view marker id s j area_pages :
  journal_idle sector 256 data_len boss_ok view marker id s j ->
  let final := remember_recovered_boss area_pages (boss_extent (view id)) s in
  journal_idle sector 256 data_len boss_ok view marker id final j /\
  data_caller DataBegin final /\ data_invariant (data_next DataBegin final).
Proof.
  intros [IDLE REST] final.
  assert (NEW : idle_root view marker id final).
  { apply validation_update_preserves_idle; exact IDLE. }
  assert (CALL : data_caller DataBegin final).
  { destruct NEW as [I [F [S [P R]]]]. unfold data_caller; rewrite F, S, P; simpl; repeat split; auto; lia. }
  split; [split; [exact NEW|exact REST]|]. split; [exact CALL|].
  apply data_command_preserves; [exact (proj1 NEW)|exact CALL].
Qed.

(* Local providers, deliberately separate from the transactional invariant.
   Neither field asserts recovery choice, page coverage, or byte preservation. *)
Record recovery_local_contracts view ranges
    (decode : flash -> nat -> option recovery_decoding) : Prop := {
  recovery_format_contract : forall bytes id reply,
    decode bytes id = Some reply -> decoded_root_agrees view ranges id reply;
  recovery_locality_contract : forall bytes bytes' id,
    unchanged (root_extents (view id)) bytes bytes' ->
    decode bytes id = decode bytes' id
}.

(* Consumer of freeze/cleanup AND fresh reconstruction.  The exact decoded
   record is preserved, not merely its dependency list.  This is one fallible
   publication episode, not yet the arbitrary-transaction arc.  In particular
   the incoming prepared image still has to be joined to physical preparation.
   Recovery is quantified in the conclusion: no successful recovery is needed
   to obtain safety of the frozen state or of a non-Ready recovery prefix. *)
Theorem uncertain_data_transaction_safety g sector data_len boss_ok view marker ranges
    (decode : flash -> nat -> option recovery_decoding)
    s j error_j commands old candidate old_decoded candidate_decoded :
  journal_geometry g sector 256 -> sector mod 8 = 0 ->
  logged_invariant sector 256 data_len boss_ok j ->
  protection_invariant 256 s -> pending_preparation s = None ->
  hd_error (publications j) = Some old ->
  protection_history_link view s j ->
  protection_current s ++ attached_ranges s = root_extents (view (N.to_nat candidate)) ->
  clos_refl_trans logged_state
    (uncertain_logged_step g sector 256 data_len boss_ok candidate) j error_j ->
  returned_error_control (journal_control error_j) ->
  recovery_local_contracts view ranges decode ->
  decode (object_flash sector (control_image (journal_control j))) (N.to_nat old)
    = Some old_decoded ->
  decode (object_flash sector (control_image (journal_control j))) (N.to_nat candidate)
    = Some candidate_decoded ->
  let selected := optional_root view (option_map N.to_nat (hd_error (publications error_j))) in
  data_calls commands (uncertain_return selected s) ->
  let frozen := execute_data commands (uncertain_return selected s) in
  (* FROZEN: arbitrary permitted RAM cleanup, including scope rollback. *)
  (data_invariant frozen /\ protection_frozen frozen = true /\
   protection_table frozen = protection_table s /\
   protection_history_link view frozen error_j /\
   protected (needed 256 (root_extents (view (N.to_nat old)) ++
     root_extents (view (N.to_nat candidate)))) (protection_table frozen)) /\
  (* NO_APPEND_ACK: this is intentionally not called a client acknowledgement. *)
  acknowledgements error_j = acknowledgements j /\
  (* PREFIX: includes interrupted/error prefixes, without a Ready premise. *)
  (forall prefix,
    clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
      (logged_after_reset error_j) prefix ->
    logged_invariant sector 256 data_len boss_ok prefix /\
    publications prefix = publications error_j /\
    acknowledgements prefix = acknowledgements error_j) /\
  (* RESTART: old or exact complete candidate, fresh table and legal begin. *)
  (forall f history acks,
    clos_refl_trans logged_state (recovery_logged_step g sector 256 data_len boss_ok)
      (logged_after_reset error_j) (Logged (Ready f) history acks) ->
    exists id decoded,
      ((id = N.to_nat old /\ decoded = old_decoded) \/
       (id = N.to_nat candidate /\ decoded = candidate_decoded)) /\
      decode (object_flash sector f) id = Some decoded /\
      unchanged (root_extents (view id))
        (object_flash sector (control_image (journal_control j))) (object_flash sector f) /\
      journal_idle sector 256 data_len boss_ok view marker id
        (rebuild_decoded marker ranges decoded) (Logged (Ready f) history acks) /\
      image_current_correspondence ranges (recovered_image decoded) [recovered_boss decoded]
        (rebuild_decoded marker ranges decoded) /\
      data_caller DataBegin (rebuild_decoded marker ranges decoded) /\
      data_invariant (data_next DataBegin (rebuild_decoded marker ranges decoded))).
Proof.
  intros G DIV J PENDING_INV P OLD LINK CUR UNC ERROR [FORMAT LOCAL]
    READ_OLD READ_NEW selected CALL frozen.
  destruct (uncertain_publication_then_cleanup g sector 256 data_len boss_ok view
    old candidate s j error_j commands G DIV J PENDING_INV P OLD LINK CUR UNC CALL)
    as [ERRINV [CHOICE [ACK [FI [FF [FT [FL [FA COVER]]]]]]]].
  split.
  { split; [exact FI|]. split; [exact FF|]. split; [exact FT|].
    split; [exact FL|exact COVER]. }
  split; [exact ACK|]. split.
  - intros prefix TRACE.
    destruct (recovery_trace_history _ _ _ _ _ _ _ TRACE) as [H [A T]].
    split; [|split; assumption].
    eapply arbitrary_finite_history_preserves_invariant; [exact G|exact DIV|exact ERRINV|].
    eapply rt_trans; [apply rt_step; apply returned_error_reset_step; exact ERROR|exact T].
  - intros f history acks REC.
    assert (READABLE : forall id, id = N.to_nat old \/ id = N.to_nat candidate ->
      exists reply, decode (object_flash sector (control_image (journal_control j))) id = Some reply).
    { intros id [E|E]; subst id; eauto. }
    destruct (uncertain_reset_recovery_restart g sector data_len boss_ok view marker ranges
      decode j error_j f history acks old candidate G DIV J OLD UNC ERROR REC
      FORMAT LOCAL READABLE) as [id [decoded [WHICH [READ REST]]]].
    assert (FRAME : unchanged (root_extents (view id))
      (object_flash sector (control_image (journal_control j))) (object_flash sector f)).
    { destruct (uncertain_trace_reset_boundary _ _ _ _ _ _ _ _ G DIV J UNC)
        as [_ [_ [_ BEFORE]]].
      destruct (reset_recovery_selects_history _ _ _ _ _ _ _ _ _ G DIV ERRINV ERROR REC)
        as [_ [_ [_ [_ AFTER]]]].
      intros r a IN RANGE. unfold object_flash. rewrite AFTER by lia. apply BEFORE; lia. }
    assert (EXACT : (id = N.to_nat old /\ decoded = old_decoded) \/
      (id = N.to_nat candidate /\ decoded = candidate_decoded)).
    { pose proof (LOCAL _ _ id FRAME) as E.
      destruct WHICH as [WHICH|WHICH]; subst id; [left|right]; split; [reflexivity| |reflexivity|];
        congruence. }
    exists id, decoded. split; [exact EXACT|]. split; [exact READ|].
    split; [exact FRAME|exact REST].
Qed.
