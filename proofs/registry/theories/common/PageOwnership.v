From Coq Require Import Arith Bool Lia.

(* Logical view of one nibble in pages.rs. The concrete encoding is owner in
   bits 0..2 and complete-validation bit 3. The table is ghost proof state. *)
Record page_cell := { owner : nat; validated : bool }.
Definition free_cell : page_cell := {| owner := 0; validated := false |}.
Definition nibble (c : page_cell) : nat :=
  owner c + if validated c then 8 else 0.
Definition cell_well_formed (c : page_cell) := owner c <= 7.
Definition page_table := nat -> page_cell.
Definition change_page (t : page_table) (p : nat) (c : page_cell) : page_table :=
  fun q => if Nat.eq_dec q p then c else t q.

Definition reserve_page (t : page_table) (p depth : nat) : option page_table :=
  if Nat.eqb (owner (t p)) 0
  then Some (change_page t p {| owner := S depth; validated := false |})
  else None.
Definition rehome_page (t : page_table) (p depth : nat) : page_table :=
  change_page t p {| owner := S depth; validated := validated (t p) |}.
Definition release_page (t : page_table) (p : nat) : page_table :=
  change_page t p free_cell.

(* Registry closure is a separate invariant. The lower table operations do not
   define which pages are needed by durable/current/snapshot/LOAD roots. *)
Definition protected (needed : nat -> Prop) (t : page_table) : Prop :=
  forall p, needed p -> owner (t p) <> 0.

Lemma nibble_bound c : cell_well_formed c -> nibble c < 16.
Proof. unfold cell_well_formed, nibble; destruct (validated c); lia. Qed.
Lemma change_other t p q c : q <> p -> change_page t p c q = t q.
Proof. intros H; unfold change_page; destruct (Nat.eq_dec q p); congruence. Qed.
Lemma reserve_rejects_occupied t p depth :
  owner (t p) <> 0 -> reserve_page t p depth = None.
Proof.
  intros H. unfold reserve_page. apply Nat.eqb_neq in H. rewrite H. reflexivity.
Qed.
Lemma reserve_result_well_formed t p depth t' :
  depth <= 6 -> reserve_page t p depth = Some t' ->
  cell_well_formed (t' p).
Proof.
  intros D H. unfold reserve_page in H.
  destruct (Nat.eqb (owner (t p)) 0); [|discriminate].
  inversion H; subst. unfold change_page, cell_well_formed.
  destruct (Nat.eq_dec p p); simpl; lia.
Qed.
Lemma reserve_clears_validation t p depth t' :
  reserve_page t p depth = Some t' -> validated (t' p) = false.
Proof.
  unfold reserve_page. destruct (Nat.eqb (owner (t p)) 0); [|discriminate].
  intros H; inversion H; subst. unfold change_page.
  destruct (Nat.eq_dec p p); simpl; congruence.
Qed.
Lemma reserve_preserves_protection needed t p depth t' :
  protected needed t -> reserve_page t p depth = Some t' ->
  protected needed t'.
Proof.
  intros P H q N. unfold reserve_page in H.
  destruct (Nat.eqb (owner (t p)) 0) eqn:E; [|discriminate].
  inversion H; subst. unfold change_page.
  destruct (Nat.eq_dec q p); subst; simpl; [lia|apply P; exact N].
Qed.
Lemma rehome_keeps_validation t p depth :
  validated (rehome_page t p depth p) = validated (t p).
Proof.
  unfold rehome_page, change_page. destruct (Nat.eq_dec p p); simpl; congruence.
Qed.
Lemma rehome_result_well_formed t p depth :
  depth <= 6 -> cell_well_formed (rehome_page t p depth p).
Proof.
  intros D. unfold rehome_page, change_page, cell_well_formed.
  destruct (Nat.eq_dec p p); simpl; lia.
Qed.
Lemma rehome_preserves_protection needed t p depth :
  protected needed t -> protected needed (rehome_page t p depth).
Proof.
  intros P q N. unfold rehome_page, change_page.
  destruct (Nat.eq_dec q p); subst; simpl; [lia|apply P; exact N].
Qed.
Lemma release_preserves_protection_if_unneeded needed t p :
  protected needed t -> ~ needed p ->
  protected needed (release_page t p).
Proof.
  intros P U q N. unfold release_page, change_page.
  destruct (Nat.eq_dec q p); subst; [contradiction|apply P; exact N].
Qed.
Lemma release_clears_validation t p :
  validated (release_page t p p) = false.
Proof.
  unfold release_page, change_page.
  destruct (Nat.eq_dec p p); simpl; congruence.
Qed.
