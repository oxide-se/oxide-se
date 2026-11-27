From Coq Require Import List Arith Bool NArith Lia.
From OxideSE.Registry Require Import PageOwnership RetentionCoverage FlashSpec
  ScopeOwnership PreparedAuthority PublicationPreparation JournalHistory.
Import ListNotations.

(* Observers of the EXISTING table and flash, not another allocator state.
   Coordinates are object-area relative; object_flash supplies the journal
   displacement. usize overflow/conversion remains an explicit refinement task. *)
Definition rounded_required n := ((n + 255) / 256) * 256.
Definition page_limit r := (offset r + span r + 255) / 256.
Definition vacantb (t : page_table) r :=
  forallb (fun p => negb (touches 256 r p) || Nat.eqb (owner (t p)) 0)
    (seq 0 (page_limit r)).
Definition blankb sector f r :=
  forallb (fun a => N.eqb (object_flash sector f a) 255%N)
    (seq (offset r) (span r)).
Definition cursor_probe sector area_len (required_at : nat -> option nat)
    cursor t f : option extent :=
  match required_at cursor with
  | None => None
  | Some n =>
    let r := {| offset := cursor; span := rounded_required n |} in
    if (Nat.eqb (cursor mod 256) 0 && (cursor + span r <=? area_len)) &&
       (vacantb t r && blankb sector f r)
    then Some r else None
  end.

Lemma vacantb_spec t r : vacantb t r = true <-> free_range 256 t r.
Proof.
  unfold vacantb, free_range. rewrite forallb_forall. split.
  - intros H p T. assert (I : In p (seq 0 (page_limit r))).
    { apply in_seq. unfold touches in T. apply andb_true_iff in T.
      destruct T as [_ T]. apply Nat.ltb_lt in T. unfold page_limit. replace (offset r + span r + 256 - 1) with (offset r + span r + 255) in T by lia. lia. }
    specialize (H p I). rewrite T in H. simpl in H. now apply Nat.eqb_eq.
  - intros H p I. destruct (touches 256 r p) eqn:T; simpl; auto.
    apply Nat.eqb_eq. now apply H.
Qed.
Lemma blankb_spec sector f r : blankb sector f r = true <-> erased_object_extent sector f r.
Proof.
  unfold blankb, erased_object_extent. rewrite forallb_forall. split;
  intros H a A; specialize (H a); [apply N.eqb_eq|apply N.eqb_eq];
  apply H; [apply in_seq|apply in_seq in A]; unfold contains in *; lia.
Qed.

Theorem cursor_probe_sound sector area_len req cursor t f r :
  cursor_probe sector area_len req cursor t f = Some r ->
  offset r = cursor /\ offset r mod 256 = 0 /\
  offset r + span r <= area_len /\
  (exists n, req cursor = Some n /\ span r = rounded_required n) /\
  free_range 256 t r /\ erased_object_extent sector f r.
Proof.
  unfold cursor_probe. destruct (req cursor) as [n|] eqn:R; try discriminate.
  destruct (_ && _) eqn:B; try discriminate. intros H; inversion H; subst.
  repeat rewrite andb_true_iff in B. destruct B as [[ALIGN BOUND] [FREE BLANK]].
  apply Nat.eqb_eq in ALIGN. apply Nat.leb_le in BOUND.
  apply vacantb_spec in FREE. apply blankb_spec in BLANK.
  simpl in *. repeat split; auto. exists n; auto.
Qed.

(* Availability only at this exact cursor, not from a free-page count.
   None means fallback is required, NEVER global capacity exhaustion. *)
Theorem cursor_probe_available sector area_len req cursor t f n :
  req cursor = Some n -> cursor mod 256 = 0 ->
  cursor + rounded_required n <= area_len ->
  free_range 256 t {| offset := cursor; span := rounded_required n |} ->
  erased_object_extent sector f {| offset := cursor; span := rounded_required n |} ->
  cursor_probe sector area_len req cursor t f =
    Some {| offset := cursor; span := rounded_required n |}.
Proof.
  intros R A B F E. unfold cursor_probe; rewrite R.
  apply vacantb_spec in F. apply blankb_spec in E.
  rewrite F, E. cbn [offset span]. rewrite A, Nat.eqb_refl.
  assert ((cursor + rounded_required n <=? area_len) = true) by (apply Nat.leb_le; exact B).
  now rewrite H.
Qed.

(* The successful RAM reservation is the existing DataReserve transition.
   It clears the validation bit, sets the owner from active depth and updates
   summaries through data_next. The cursor update precedes it in Rust but has
   no flash/table effect; failures of numeric admission are not included here. *)
Theorem cursor_reserve_preserves sector area_len req cursor f s r :
  data_invariant s -> protection_frozen s = false -> pending_preparation s = None ->
  cursor_probe sector area_len req cursor (protection_table s) f = Some r ->
  data_invariant (data_next (DataReserve r) s) /\
  pending_preparation (data_next (DataReserve r) s) =
    Some (Build_preparation ObjectPreparation r Reserved) /\
  erased_object_extent sector f r.
Proof.
  intros INV F P HIT.
  destruct (cursor_probe_sound _ _ _ _ _ _ _ HIT) as [_ [_ [_ [_ [FREE ERASED]]]]].
  split. apply data_command_preserves; auto. simpl; auto.
  split; [reflexivity|exact ERASED].
Qed.

Example cursor_erased_witness :
  cursor_probe 4096 8192 (fun _ => Some 17) 256 (fun _ => free_cell)
    (fun _ => 255%N) = Some {| offset := 256; span := 256 |}.
Proof. vm_compute. reflexivity. Qed.
Example cursor_occupied_witness :
  cursor_probe 4096 8192 (fun _ => Some 17) 256 (fun _ => free_cell)
    (fun _ => 0%N) = None.
Proof. vm_compute. reflexivity. Qed.
Example cursor_address_dependent_witness :
  cursor_probe 4096 8192 (fun a => if Nat.eqb a 256 then Some 257 else None)
    256 (fun _ => free_cell) (fun _ => 255%N) =
    Some {| offset := 256; span := 512 |}.
Proof. vm_compute. reflexivity. Qed.

(* The erased-space projection of find_span_in. Recycling candidates are
   remembered in Rust but do not preempt any later erased placement. Arithmetic
   failures are excluded by the separate usize-admission obligation. *)
Fixpoint first_erased sector limit req candidates t f : option extent :=
  match candidates with
  | [] => None
  | cursor::tail => match cursor_probe sector limit req cursor t f with
    | Some r => Some r
    | None => first_erased sector limit req tail t f
    end
  end.
Theorem first_erased_sound sector limit req candidates t f r :
  first_erased sector limit req candidates t f = Some r ->
  exists cursor, In cursor candidates /\
    cursor_probe sector limit req cursor t f = Some r.
Proof.
  induction candidates as [|c cs IH]; simpl; [discriminate|].
  destruct (cursor_probe sector limit req c t f) eqn:P.
  - intros H; inversion H; subst. exists c; auto.
  - intros H. destruct (IH H) as [x [IN HIT]]. exists x; auto.
Qed.
Theorem first_erased_absent sector limit req candidates t f :
  first_erased sector limit req candidates t f = None <->
  forall cursor, In cursor candidates -> cursor_probe sector limit req cursor t f = None.
Proof.
  induction candidates as [|c cs IH]; simpl.
  - split; auto. intros _ x H; contradiction.
  - destruct (cursor_probe sector limit req c t f) eqn:P.
    + split; [discriminate|]. intros H; specialize (H c (or_introl eq_refl)); congruence.
    + rewrite IH. split.
      * intros H x [<-|IN]; auto.
      * intros H x IN. apply H; auto.
Qed.
Theorem first_erased_available sector limit req candidates t f cursor r :
  In cursor candidates -> cursor_probe sector limit req cursor t f = Some r ->
  exists selected, first_erased sector limit req candidates t f = Some selected.
Proof.
  intros IN HIT. destruct (first_erased sector limit req candidates t f) eqn:F; eauto.
  pose proof (proj1 (first_erased_absent sector limit req candidates t f) F cursor IN) as BAD; congruence.
Qed.
Definition traversal start stop :=
  map (fun i => start + i*256) (seq 0 ((stop-start)/256)).
Definition circular_erased sector area_len start req t f :=
  match first_erased sector area_len req (traversal start area_len) t f with
  | Some r => Some r
  | None => first_erased sector start req (traversal 0 start) t f
  end.
Theorem circular_erased_sound sector area_len start req t f r :
  circular_erased sector area_len start req t f = Some r ->
  free_range 256 t r /\ erased_object_extent sector f r.
Proof.
  unfold circular_erased.
  destruct (first_erased sector area_len req (traversal start area_len) t f) eqn:F.
  - intros H; inversion H; subst.
    destruct (first_erased_sound _ _ _ _ _ _ _ F) as [c [_ HIT]].
    apply cursor_probe_sound in HIT; tauto.
  - intros H. destruct (first_erased_sound _ _ _ _ _ _ _ H) as [c [_ HIT]].
    apply cursor_probe_sound in HIT; tauto.
Qed.
Theorem circular_erased_absent sector area_len start req t f :
  circular_erased sector area_len start req t f = None <->
  (forall c, In c (traversal start area_len) -> cursor_probe sector area_len req c t f=None) /\
  (forall c, In c (traversal 0 start) -> cursor_probe sector start req c t f=None).
Proof.
  unfold circular_erased.
  destruct (first_erased sector area_len req (traversal start area_len) t f) eqn:F.
  - split; [discriminate|]. intros [H _].
    pose proof (proj2 (first_erased_absent sector area_len req (traversal start area_len) t f) H) as BAD; congruence.
  - rewrite first_erased_absent. pose proof (proj1 (first_erased_absent sector area_len req (traversal start area_len) t f) F); tauto.
Qed.

(* Fresh observations matter independently: a free table does not certify FF,
   and old FF bytes do not certify that a page remains unreserved. *)
Example post_data_occupied_probe :
  cursor_probe 4096 8192 (fun _ => Some 17) 256
    (reserve_extent 256 {| offset:=256; span:=256 |} 1 (fun _ => free_cell))
    (fun _ => 255%N) = None.
Proof. vm_compute. reflexivity. Qed.
Example post_data_nonblank_probe :
  cursor_probe 4096 8192 (fun _ => Some 17) 256 (fun _ => free_cell)
    (fun a => if Nat.eqb a (2*4096+256) then 0%N else 255%N) = None.
Proof. vm_compute. reflexivity. Qed.

(* Checked arithmetic services. Natural numbers are only the mathematical
   carrier; word_max bounds the Rust checked_add before rounding. *)
Definition checked_round word_max alignment value :=
 if (0<?alignment) && (value+alignment-1<=?word_max)
 then Some (((value+alignment-1)/alignment)*alignment) else None.
Definition checked_data_total word_max payload :=
 match checked_round word_max 16 payload with
 | None=>None
 | Some encrypted=>if encrypted+32<=?word_max
     then checked_round word_max 256 (encrypted+32) else None
 end.
Inductive cursor_reply := ProbeRejected | ProbeMiss | ProbeFound (r:extent).
Definition checked_cursor sector word_max area_len req cursor t f :=
 match req cursor with
 | None=>ProbeMiss
 | Some n=>match checked_round word_max 256 n with
   | None=>ProbeRejected
   | Some _=>match cursor_probe sector area_len req cursor t f with
     | None=>ProbeMiss | Some r=>ProbeFound r end
   end
 end.
Lemma checked_cursor_rejection sector word_max area_len req cursor t f :
 checked_cursor sector word_max area_len req cursor t f=ProbeRejected ->
 exists n,req cursor=Some n /\ checked_round word_max 256 n=None.
Proof.
 unfold checked_cursor;destruct (req cursor) as [n|] eqn:R;try discriminate.
 destruct (checked_round word_max 256 n) eqn:C;[destruct cursor_probe;discriminate|].
 intro;exists n;auto.
Qed.
Lemma checked_cursor_found sector word_max area_len req cursor t f r :
 checked_cursor sector word_max area_len req cursor t f=ProbeFound r ->
 cursor_probe sector area_len req cursor t f=Some r.
Proof.
 unfold checked_cursor;destruct (req cursor);try discriminate;destruct checked_round;try discriminate.
 destruct cursor_probe eqn:P;intro E;inversion E;subst;reflexivity.
Qed.
Example large_payload_rejected : checked_data_total 65535 65535=None.
Proof. vm_compute;reflexivity. Qed.
Example cursor_overflow_is_not_miss :
 checked_cursor 4096 65535 4096 (fun _=>Some 65535) 0 (fun _=>free_cell) (fun _=>255%N)=ProbeRejected.
Proof. vm_compute;reflexivity. Qed.

Lemma checked_round_numeric word_max alignment value total :
 checked_round word_max alignment value=Some total ->
 total<=word_max /\ total mod alignment=0.
Proof.
 unfold checked_round;destruct ((0<?alignment) && (value+alignment-1<=?word_max)) eqn:G;try discriminate.
 intro E;inversion E;subst total. apply andb_true_iff in G;destruct G as [POS BOUND].
 apply Nat.ltb_lt in POS;apply Nat.leb_le in BOUND.
 split;[pose proof (Nat.div_mod (value+alignment-1) alignment ltac:(lia));nia|apply Nat.mod_mul;lia].
Qed.
Lemma checked_data_total_numeric word_max bytes total :
 checked_data_total word_max bytes=Some total -> total<=word_max /\ total mod 256=0.
Proof.
 unfold checked_data_total;destruct checked_round;try discriminate.
 destruct (_<=?_);try discriminate;apply checked_round_numeric.
Qed.
Theorem data_total_probe_no_numeric_error sector word_max bytes total area cursor t f :
 word_max mod 256=255 -> checked_data_total word_max bytes=Some total ->
 checked_cursor sector word_max area (fun _=>Some total) cursor t f<>ProbeRejected.
Proof.
 intros MAX TOTAL. destruct (checked_data_total_numeric _ _ _ TOTAL) as [BOUND ALIGNED].
 assert (FIT:total+256-1<=word_max).
 { pose proof (Nat.div_mod word_max 256 ltac:(lia));pose proof (Nat.div_mod total 256 ltac:(lia));nia. }
 assert (ROUND:checked_round word_max 256 total<>None).
 { unfold checked_round;apply Nat.leb_le in FIT;rewrite FIT;discriminate. }
 unfold checked_cursor;destruct (checked_round word_max 256 total) eqn:R;[|contradiction].
 destruct (cursor_probe sector area (fun _=>Some total) cursor t f);discriminate.
Qed.
