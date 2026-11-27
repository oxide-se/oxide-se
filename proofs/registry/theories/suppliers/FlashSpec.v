From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Types.
Import ListNotations.

Definition flash := nat -> byte.
Definition valid_flash (f : flash) := forall p, valid_byte (f p).
Record geometry := {
  area_start : nat;
  area_length : nat;
  page_size : nat;
  sector_size : nat
}.
Definition geometry_valid (g : geometry) :=
  page_size g > 0 /\ sector_size g > 0 /\
  sector_size g mod page_size g = 0 /\
  area_start g mod sector_size g = 0 /\
  area_length g mod sector_size g = 0.
Definition within (g : geometry) (a n : nat) :=
  area_start g <= a /\ a + n <= area_start g + area_length g.
Definition frame (a n : nat) (before after : flash) :=
  forall p, p < a \/ a + n <= p -> after p = before p.
Definition program_bits (old new : byte) := N.land old new = new.
Definition erase_bits (old new : byte) := N.land old new = old.
Definition program_request (g : geometry) (f : flash) a data :=
  length data = page_size g /\ a mod page_size g = 0 /\
  within g a (length data) /\ valid_payload data /\
  forall i b, nth_error data i = Some b -> program_bits (f (a+i)) b.
Definition erase_request (g : geometry) a :=
  a mod sector_size g = 0 /\ within g a (sector_size g).
Definition programmed (f : flash) a data :=
  forall i b, nth_error data i = Some b -> f (a+i) = b.
Definition erased (f : flash) a n := forall i, i < n -> f (a+i) = 255%N.
(* An argument rejection before the physical command has no flash effect.
   It is outside [program_step], whose constructors require a valid request.
   A returned error on a valid request may still be physically unchanged. *)
Definition rejected_program_request (g : geometry) (f : flash) a data after :=
  ~ program_request g f a data /\ after = f.
(* Oxi-core hardware contract, not a claim established by a datasheet:
   physical programming may complete any subset of the requested 1->0 bit
   transitions, independently across bits and bytes. Commands are serialized.
   Success is complete and durable; Reset may also observe a complete image
   before the return is delivered. *)
Definition requested_only (after : flash) a data :=
  forall i b, nth_error data i = Some b -> program_bits (after (a+i)) b.

Definition program_progress (before after : flash) a data :=
  frame a (length data) before after /\
  forall i b, nth_error data i = Some b ->
    valid_byte (after (a+i)) /\
    program_bits (before (a+i)) (after (a+i)) /\
    program_bits (after (a+i)) b.
Definition erase_progress (before after : flash) a n :=
  frame a n before after /\
  forall i, i < n -> valid_byte (after (a+i)) /\
    erase_bits (before (a+i)) (after (a+i)).

Inductive outcome := Success | VerifyFailed | Reset.
(* This relation specifies trusted possible hardware outcomes, not an
   implementation nor an axiom that interrupted images are rejected by a CRC. *)
Inductive program_step (g : geometry) (before : flash) a data : outcome -> flash -> Prop :=
| program_success after : program_request g before a data ->
    frame a (length data) before after -> programmed after a data ->
    program_step g before a data Success after
| program_interrupted after : program_request g before a data ->
    program_progress before after a data -> program_step g before a data Reset after
| program_verify_failed after : program_request g before a data ->
    program_progress before after a data ->
    program_step g before a data VerifyFailed after.

Inductive erase_step (g : geometry) (before : flash) a : outcome -> flash -> Prop :=
| erase_success after : erase_request g a ->
    frame a (sector_size g) before after -> erased after a (sector_size g) ->
    erase_step g before a Success after
| erase_interrupted after : erase_request g a ->
    erase_progress before after a (sector_size g) -> erase_step g before a Reset after
| erase_verify_failed after : erase_request g a ->
    erase_progress before after a (sector_size g) -> erase_step g before a VerifyFailed after.

Theorem rejected_request_has_no_program_step g f a data after result :
  rejected_program_request g f a data after ->
  ~ program_step g f a data result after.
Proof.
  intros [Hinvalid _] Hstep. inversion Hstep; contradiction.
Qed.

Lemma program_success_contents g f a data f' :
  program_step g f a data Success f' -> programmed f' a data.
Proof. intros H; inversion H; assumption. Qed.

Lemma erase_success_contents g f a f' :
  erase_step g f a Success f' -> erased f' a (sector_size g).
Proof. intros H; inversion H; assumption. Qed.

Theorem program_completed_before_reset g f a data f' :
  program_step g f a data Success f' ->
  program_step g f a data Reset f'.
Proof.
  intro H. inversion H; subst; clear H.
  apply program_interrupted; [exact H0|].
  split; [exact H1|].
  intros i b Hnth. pose proof (H2 i b Hnth) as Heq.
  destruct H0 as [_ [_ [_ [Hvalid Hrequest]]]].
  assert (V : valid_byte b).
  { unfold valid_payload in Hvalid.
    apply (proj1 (Forall_forall valid_byte data) Hvalid b).
    eapply nth_error_In; eauto. }
  rewrite Heq. split; [exact V|]. split.
  - exact (Hrequest i b Hnth).
  - unfold program_bits. rewrite N.land_diag. reflexivity.
Qed.

(* Explicit overapproximation of a returned verification failure: even an
   exact, durable page image can accompany the error. The registry must then
   freeze rather than infer absence of publication from the return value. *)
Theorem program_completed_can_return_verify_failed g f a data f' :
  program_step g f a data Success f' ->
  program_step g f a data VerifyFailed f'.
Proof.
  intro Hsuccess.
  pose proof (program_completed_before_reset _ _ _ _ _ Hsuccess) as Hreset.
  inversion Hreset; subst. eapply program_verify_failed; eauto.
Qed.

Theorem erase_completed_before_reset g f a f' :
  erase_step g f a Success f' ->
  (forall i, i < sector_size g -> valid_byte (f (a+i))) ->
  erase_step g f a Reset f'.
Proof.
  intros H Hvalid. inversion H; subst; clear H.
  apply erase_interrupted; [exact H0|].
  split; [exact H1|]. intros i Hi. rewrite (H2 i Hi).
  split; [unfold valid_byte; lia|].
  unfold erase_bits. change 255%N with (N.ones 8).
  rewrite N.land_ones.
  rewrite N.mod_small; [reflexivity|].
  exact (Hvalid i Hi).
Qed.

(* Equality of possible physical images does not identify the control flow:
   VerifyFailed returns to its caller; Reset abandons that continuation. *)
Lemma failed_program_image_can_be_reset g f a data f' :
  program_step g f a data VerifyFailed f' ->
  program_step g f a data Reset f'.
Proof.
  intro H. inversion H; subst. apply program_interrupted; assumption.
Qed.

Lemma failed_erase_image_can_be_reset g f a f' :
  erase_step g f a VerifyFailed f' ->
  erase_step g f a Reset f'.
Proof.
  intro H. inversion H; subst. apply erase_interrupted; assumption.
Qed.

Theorem erase_no_effect_error_allowed g f a :
  valid_flash f -> erase_request g a ->
  erase_step g f a VerifyFailed f.
Proof.
  intros Hvalid Hrequest.
  apply erase_verify_failed; [exact Hrequest|].
  split.
  - intros p _. reflexivity.
  - intros i _. split; [apply Hvalid|].
    unfold erase_bits. rewrite N.land_diag. reflexivity.
Qed.
Lemma program_locality g f a data result f' :
  program_step g f a data result f' -> frame a (length data) f f'.
Proof. intros H; inversion H; subst; auto; destruct H1; assumption. Qed.

Lemma erase_locality g f a result f' :
  erase_step g f a result f' -> frame a (sector_size g) f f'.
Proof. intros H; inversion H; subst; auto; destruct H1; assumption. Qed.

Theorem program_step_preserves_valid_flash g f a data result f' :
  valid_flash f -> program_step g f a data result f' -> valid_flash f'.
Proof.
  intros Hvalid Hstep p.
  destruct (Nat.lt_ge_cases p a) as [Hbefore|Hfrom].
  - rewrite (program_locality _ _ _ _ _ _ Hstep p (or_introl Hbefore)).
    apply Hvalid.
  - destruct (Nat.lt_ge_cases p (a + length data)) as [Hinside|Hafter].
    + assert (Hi : p-a < length data) by lia.
      destruct (nth_error data (p-a)) eqn:E.
      * replace p with (a+(p-a)) by lia.
        destruct Hstep as [after Hreq _ Hprogram |
                           after _ Hprogress | after _ Hprogress].
        -- rewrite (Hprogram _ _ E).
           destruct Hreq as [_ [_ [_ [Hpayload _]]]].
           unfold valid_payload in Hpayload.
           apply (proj1 (Forall_forall valid_byte data) Hpayload b).
           eapply nth_error_In; eauto.
        -- exact (proj1 (proj2 Hprogress _ _ E)).
        -- exact (proj1 (proj2 Hprogress _ _ E)).
      * apply nth_error_None in E. lia.
    + rewrite (program_locality _ _ _ _ _ _ Hstep p (or_intror Hafter)).
      apply Hvalid.
Qed.

Theorem erase_step_preserves_valid_flash g f a result f' :
  valid_flash f -> erase_step g f a result f' -> valid_flash f'.
Proof.
  intros Hvalid Hstep p.
  destruct (Nat.lt_ge_cases p a) as [Hbefore|Hfrom].
  - rewrite (erase_locality _ _ _ _ _ Hstep p (or_introl Hbefore)).
    apply Hvalid.
  - destruct (Nat.lt_ge_cases p (a + sector_size g)) as [Hinside|Hafter].
    + replace p with (a+(p-a)) by lia.
      destruct Hstep as [after _ _ Herased |
                           after _ Hprogress | after _ Hprogress].
      * rewrite (Herased (p-a) ltac:(lia)). unfold valid_byte. lia.
      * exact (proj1 (proj2 Hprogress (p-a) ltac:(lia))).
      * exact (proj1 (proj2 Hprogress (p-a) ltac:(lia))).
    + rewrite (erase_locality _ _ _ _ _ Hstep p (or_intror Hafter)).
      apply Hvalid.
Qed.

Lemma interrupted_program_requested_only g f a data f' :
  program_step g f a data Reset f' -> requested_only f' a data.
Proof.
  intro Hstep. inversion Hstep; subst; clear Hstep.
  intros i b Hnth. exact (proj2 (proj2 (proj2 H0 i b Hnth))).
Qed.

Lemma failed_program_requested_only g f a data f' :
  program_step g f a data VerifyFailed f' -> requested_only f' a data.
Proof.
  intro Hstep. inversion Hstep; subst; clear Hstep.
  intros i b Hnth. exact (proj2 (proj2 (proj2 H0 i b Hnth))).
Qed.

Lemma program_bits_antisym x y :
  program_bits x y -> program_bits y x -> x = y.
Proof.
  unfold program_bits. intros Hxy Hyx.
  rewrite N.land_comm in Hyx. congruence.
Qed.

Lemma identical_progress_unchanged f f' a data :
  program_progress f f' a data ->
  (forall i b, nth_error data i = Some b -> f (a+i) = b) ->
  forall p, f' p = f p.
Proof.
  intros [Hframe Hprogress] Hsame p.
  destruct (Nat.lt_ge_cases p a) as [Hbefore|Hfrom].
  - apply Hframe. left. exact Hbefore.
  - destruct (Nat.lt_ge_cases p (a + length data)) as [Hinside|Hafter].
    + assert (Hi : p-a < length data) by lia.
      destruct (nth_error data (p-a)) eqn:E.
      * assert (Hp : p = a+(p-a)) by lia. rewrite Hp.
        pose proof (Hsame _ _ E) as Hrequest.
        destruct (Hprogress _ _ E) as [_ [Hmono Htarget]].
        rewrite <- Hrequest in Htarget.
        apply program_bits_antisym; assumption.
      * apply nth_error_None in E. lia.
    + apply Hframe. right. exact Hafter.
Qed.

Theorem identical_page_rewrite_unchanged g f a data result f' :
  program_step g f a data result f' ->
  (forall i b, nth_error data i = Some b -> f (a+i) = b) ->
  forall p, f' p = f p.
Proof.
  intros Hstep Hsame p. destruct Hstep as
    [after _ Hframe Hprogram | after _ Hprogress | after _ Hprogress].
  - destruct (Nat.lt_ge_cases p a) as [Hbefore|Hfrom].
    + apply Hframe. left. exact Hbefore.
    + destruct (Nat.lt_ge_cases p (a + length data)) as [Hinside|Hafter].
      * assert (Hi : p-a < length data) by lia.
        destruct (nth_error data (p-a)) eqn:E.
        -- assert (Hp : p = a+(p-a)) by lia. rewrite Hp.
           rewrite (Hprogram _ _ E). symmetry. apply Hsame. exact E.
        -- apply nth_error_None in E. lia.
      * apply Hframe. right. exact Hafter.
  - eapply identical_progress_unchanged; eauto.
  - eapply identical_progress_unchanged; eauto.
Qed.

Theorem identical_byte_preserved g f a data result f' i b :
  program_step g f a data result f' ->
  nth_error data i = Some b -> f (a+i) = b -> f' (a+i) = b.
Proof.
  intros Hstep Hnth Hbefore.
  destruct Hstep as [after _ _ Hprogram | after _ Hprogress |
                     after _ Hprogress].
  - exact (Hprogram _ _ Hnth).
  - destruct Hprogress as [_ Hprogress].
    destruct (Hprogress _ _ Hnth) as [_ [Hmono Htarget]].
    rewrite Hbefore in Hmono.
    pose proof (program_bits_antisym _ _ Htarget Hmono) as Heq.
    exact Heq.
  - destruct Hprogress as [_ Hprogress].
    destruct (Hprogress _ _ Hnth) as [_ [Hmono Htarget]].
    rewrite Hbefore in Hmono.
    pose proof (program_bits_antisym _ _ Htarget Hmono) as Heq.
    exact Heq.
Qed.
