From Coq Require Import List Arith Bool Lia.
From OxideSE.Registry Require Import PageOwnership FlashSpec.
Import ListNotations.

(* Range observer used by pages.rs::range/update_mask. Unbounded arithmetic;
   checked usize addition, the 1024 limit and page > 0 are caller obligations. *)
Record extent := { offset : nat; span : nat }.
Definition contains (r : extent) a := offset r <= a < offset r + span r.
Definition touches page (r : extent) p :=
  (offset r / page <=? p) && (p <? (offset r + span r + page - 1) / page).
Definition marked page (ranges : list extent) p :=
  existsb (fun r => touches page r p) ranges.
Definition needed page ranges p := exists r, In r ranges /\ touches page r p = true.
Definition collect_table page ranges (t : page_table) : page_table :=
  fun p => if marked page ranges p
           then {| owner := 1; validated := validated (t p) |} else free_cell.
Definition free_range page (t : page_table) r :=
  forall p, touches page r p = true -> owner (t p) = 0.
Definition unchanged ranges (f f' : flash) :=
  forall r a, In r ranges -> contains r a -> f' a = f a.

Lemma byte_page_touched page r a :
  page > 0 -> contains r a -> touches page r (a / page) = true.
Proof.
  intros P [L U]. unfold touches. apply andb_true_iff; split.
  - apply Nat.leb_le. apply Nat.Div0.div_le_mono; lia.
  - apply Nat.ltb_lt.
    pose proof (Nat.div_mod a page ltac:(lia)) as A.
    pose proof (Nat.mod_upper_bound a page ltac:(lia)) as B.
    pose proof (Nat.div_mod (offset r + span r + page - 1) page ltac:(lia)) as C.
    pose proof (Nat.mod_upper_bound (offset r + span r + page - 1) page ltac:(lia)) as D.
    nia.
Qed.

Lemma marked_spec page ranges p : marked page ranges p = true <-> needed page ranges p.
Proof. unfold marked, needed. rewrite existsb_exists. reflexivity. Qed.

Theorem collection_establishes_coverage page ranges t :
  protected (needed page ranges) (collect_table page ranges t).
Proof.
  intros p H. apply marked_spec in H. unfold collect_table. rewrite H. simpl; lia.
Qed.

(* A release by collection is justified by the constructed mask, not by a
   caller-supplied assertion that the released page is unneeded. *)
Theorem collection_free_implies_no_listed_reference page ranges t p :
  owner (collect_table page ranges t p) = 0 -> ~ needed page ranges p.
Proof. intros F N. exact (collection_establishes_coverage page ranges t p N F). Qed.

Lemma covered_free_range_disjoint page ranges t r a :
  page > 0 -> protected (needed page ranges) t -> free_range page t r ->
  contains r a -> forall live, In live ranges -> ~ contains live a.
Proof.
  intros P C F R live I L.
  apply (C (a / page)).
  - exists live. split; [exact I|eapply byte_page_touched; eauto].
  - apply F. eapply byte_page_touched; eauto.
Qed.

Theorem erase_preserves_covered_ranges g page ranges t f f' a result :
  page > 0 -> protected (needed page ranges) t ->
  free_range page t {| offset := a; span := sector_size g |} ->
  erase_step g f a result f' -> unchanged ranges f f'.
Proof.
  intros P C F E live b I B. apply (erase_locality _ _ _ _ _ E).
  destruct (Nat.lt_ge_cases b a); [auto|].
  right. destruct (Nat.le_gt_cases (a + sector_size g) b); [assumption|].
  exfalso. eapply covered_free_range_disjoint; eauto.
  unfold contains; simpl; lia.
Qed.

Theorem program_preserves_covered_ranges g page ranges t f f' a data result :
  page > 0 -> protected (needed page ranges) t ->
  free_range page t {| offset := a; span := length data |} ->
  program_step g f a data result f' -> unchanged ranges f f'.
Proof.
  intros P C F E live b I B. apply (program_locality _ _ _ _ _ _ E).
  destruct (Nat.lt_ge_cases b a); [auto|].
  right. destruct (Nat.le_gt_cases (a + length data) b); [assumption|].
  exfalso. eapply covered_free_range_disjoint; eauto.
  unfold contains; simpl; lia.
Qed.

(* The admission check is independent of the physical result. Reset and
   VerifyFailed are both admitted; this is not a freeze/control-flow model. *)
Inductive guarded_command g page (ranges : list extent) t : flash -> flash -> Prop :=
| guarded_erase f f' a result :
    free_range page t {| offset := a; span := sector_size g |} ->
    erase_step g f a result f' -> guarded_command g page ranges t f f'
| guarded_program f f' a data result :
    free_range page t {| offset := a; span := length data |} ->
    program_step g f a data result f' -> guarded_command g page ranges t f f'.
Inductive guarded_trace g page ranges t : flash -> flash -> Prop :=
| trace_refl f : guarded_trace g page ranges t f f
| trace_cons f middle last : guarded_command g page ranges t f middle ->
    guarded_trace g page ranges t middle last -> guarded_trace g page ranges t f last.

Theorem finite_guarded_trace_preserves_ranges g page ranges t f f' :
  page > 0 -> protected (needed page ranges) t ->
  guarded_trace g page ranges t f f' -> unchanged ranges f f'.
Proof.
  intros P C T. induction T.
  - intros r a I B; reflexivity.
  - assert (U : unchanged ranges f middle).
    { destruct H; [eapply erase_preserves_covered_ranges|eapply program_preserves_covered_ranges]; eauto. }
    intros r a I B. rewrite (IHT r a I B). exact (U r a I B).
Qed.

(* collect/visit_live enumerate direct physical extents: a BOSS and all its
   compact-image entries. Shared references may occur more than once. This
   observer does not claim that Rust decoding has produced the correct list. *)
Record root_view := { boss_extent : extent; object_extents : list extent }.
Definition root_extents r := boss_extent r :: object_extents r.
Definition enumerate_roots (marker : extent) (roots : list root_view)
    (reservations : list extent) := marker :: flat_map root_extents roots ++ reservations.
Theorem enumerated_root_covered page marker roots reservations t root r p :
  In root roots -> In r (root_extents root) -> touches page r p = true ->
  owner (collect_table page (enumerate_roots marker roots reservations) t p) <> 0.
Proof.
  intros R I T. apply collection_establishes_coverage.
  exists r. split; [|exact T]. unfold enumerate_roots. right.
  apply in_or_app; left. apply in_flat_map. exists root; auto.
Qed.
Theorem enumerated_reservation_covered page marker roots reservations t r p :
  In r reservations -> touches page r p = true ->
  owner (collect_table page (enumerate_roots marker roots reservations) t p) <> 0.
Proof.
  intros I T. apply collection_establishes_coverage. exists r. split; [|exact T].
  unfold enumerate_roots. right. apply in_or_app; auto.
Qed.

(* Ghost identity is an allocation-event label, not the persisted u32 mutation
   counter. No freshness/no-overflow assertion about that counter is made. *)
Record incarnation := { allocation_event : nat; block_extent : extent }.
Theorem live_incarnation_cannot_be_recycled page ranges t old candidate a :
  page > 0 -> In (block_extent old) ranges -> protected (needed page ranges) t ->
  free_range page t candidate -> contains candidate a -> ~ contains (block_extent old) a.
Proof. intros; eapply covered_free_range_disjoint; eauto. Qed.

(* Rust object-area prefix and journal suffix. Natural-number arithmetic here
   requires the usual checked usize/u32 conversions at the implementation edge. *)
Theorem object_area_length count page sector :
  0 < page -> sector mod page = 0 ->
  (count - (2*sector)/page)*page = count*page - 2*sector.
Proof.
  intros PAGE MULT. pose proof (Nat.div_mod sector page ltac:(lia)) as D.
  assert (E : 2*sector = (2*(sector/page))*page) by nia.
  rewrite E, Nat.div_mul by lia. rewrite Nat.mul_sub_distr_r. reflexivity.
Qed.
Theorem object_extent_before_journal base count page sector r a :
  0 < page -> sector mod page = 0 -> 2*sector <= count*page ->
  offset r + span r <= (count - (2*sector)/page)*page -> contains r a ->
  base+a < base+count*page-2*sector.
Proof.
  intros PAGE MULT SIZE BOUND IN.
  rewrite object_area_length in BOUND by assumption. unfold contains in IN. lia.
Qed.

(* Reindex the single physical image: journal first, objects afterwards.
   This is an observer, not another flash store. Slot values remain object offsets. *)
Definition journal_object_view base data_bytes sector (physical : flash) : flash :=
  fun x => if x <? 2*sector then physical (base+data_bytes+x)
           else physical (base+(x-2*sector)).
Lemma journal_object_view_object base data_bytes sector physical a :
  journal_object_view base data_bytes sector physical (2*sector+a) = physical (base+a).
Proof.
  unfold journal_object_view. assert (E : (2*sector+a <? 2*sector) = false) by (apply Nat.ltb_ge; lia). rewrite E.
  replace (2*sector+a-2*sector) with a by lia. reflexivity.
Qed.
Theorem journal_frame_implies_object_frame base data_bytes sector physical physical' ranges :
  (forall x, 2*sector <= x ->
    journal_object_view base data_bytes sector physical' x =
    journal_object_view base data_bytes sector physical x) ->
  unchanged ranges (fun a => physical (base+a)) (fun a => physical' (base+a)).
Proof.
  intros FRAME r a IN BOUND.
  specialize (FRAME (2*sector+a) ltac:(lia)).
  rewrite !journal_object_view_object in FRAME. exact FRAME.
Qed.

Lemma aligned_journal_page_after_objects base data_bytes page address :
  0 < page -> (base+data_bytes) mod page = 0 -> base+data_bytes <= address ->
  base+data_bytes <= address/page*page.
Proof.
  intros PAGE ALIGN AFTER.
  pose proof (Nat.div_mod (base+data_bytes) page ltac:(lia)) as D.
  pose proof (Nat.div_le_mono (base+data_bytes) address page ltac:(lia) AFTER) as Q.
  nia.
Qed.
Theorem physical_journal_program_preserves_objects g base data_bytes address data result f f' ranges :
  base+data_bytes <= address ->
  (forall r, In r ranges -> offset r+span r <= data_bytes) ->
  program_step g f address data result f' ->
  unchanged ranges (fun a => f (base+a)) (fun a => f' (base+a)).
Proof.
  intros AFTER BOUNDS STEP r a IN RANGE. apply (program_locality _ _ _ _ _ _ STEP).
  left. specialize (BOUNDS r IN). unfold contains in RANGE. lia.
Qed.
Theorem physical_journal_erase_preserves_objects g base data_bytes address result f f' ranges :
  base+data_bytes <= address ->
  (forall r, In r ranges -> offset r+span r <= data_bytes) ->
  erase_step g f address result f' ->
  unchanged ranges (fun a => f (base+a)) (fun a => f' (base+a)).
Proof.
  intros AFTER BOUNDS STEP r a IN RANGE. apply (erase_locality _ _ _ _ _ STEP).
  left. specialize (BOUNDS r IN). unfold contains in RANGE. lia.
Qed.
