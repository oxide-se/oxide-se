From Stdlib Require Import List.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Types FlashSpec.

(* A lower-level effect: nondeterministic physical state is returned explicitly.
   Reset is excluded from normal replies and belongs to an interrupt trace. *)
Inductive FlashAPI : interface :=
| FlashRead : nat -> FlashAPI byte
| FlashProgram : nat -> payload -> FlashAPI (outcome * flash)%type
| FlashErase : nat -> FlashAPI (outcome * flash)%type.

Section FlashContract.
Variable g : geometry.

Definition flash_caller (f : flash) (A : Type) (e : FlashAPI A) : Prop :=
  match e with
  | FlashRead a => within g a 1
  | FlashProgram a data => program_request g f a data
  | FlashErase a => erase_request g a
  end.

Definition flash_callee (f : flash) (A : Type) (e : FlashAPI A) (x : A) : Prop :=
  match e in FlashAPI T return T -> Prop with
  | FlashRead a => fun b => b = f a
  | FlashProgram a data => fun reply =>
      program_step g f a data (fst reply) (snd reply) /\ fst reply <> Reset
  | FlashErase a => fun reply =>
      erase_step g f a (fst reply) (snd reply) /\ fst reply <> Reset
  end x.

Definition flash_update (f : flash) (A : Type) (e : FlashAPI A) (x : A) : flash :=
  match e in FlashAPI T return T -> flash with
  | FlashRead _ => fun _ => f
  | FlashProgram _ _ => fun reply => snd reply
  | FlashErase _ => fun reply => snd reply
  end x.

Definition flash_contract : contract FlashAPI flash :=
  make_contract flash_update flash_caller flash_callee.

Lemma read_reply f a b :
  flash_callee f _ (FlashRead a) b -> b = f a.
Proof. exact (fun H => H). Qed.

Lemma program_reply_local f a data reply :
  flash_callee f _ (FlashProgram a data) reply ->
  frame a (length data) f (flash_update f _ (FlashProgram a data) reply).
Proof.
  intros [H _]. exact (program_locality _ _ _ _ _ _ H).
Qed.

Lemma program_success_reply_exact f a data reply :
  flash_callee f _ (FlashProgram a data) reply ->
  fst reply = Success ->
  programmed (flash_update f _ (FlashProgram a data) reply) a data.
Proof.
  intros [H _] Hr. destruct reply as [r f']; simpl in *; subst.
  exact (program_success_contents _ _ _ _ _ H).
Qed.

Lemma program_error_reply_requested_only f a data reply :
  flash_callee f _ (FlashProgram a data) reply ->
  fst reply = VerifyFailed ->
  requested_only (flash_update f _ (FlashProgram a data) reply) a data.
Proof.
  intros [H _] Hr. destruct reply as [r f']; simpl in *; subst.
  exact (failed_program_requested_only _ _ _ _ _ H).
Qed.

Lemma program_reply_identical_page f a data reply :
  flash_callee f _ (FlashProgram a data) reply ->
  (forall i b, nth_error data i = Some b -> f (a+i) = b) ->
  forall p, flash_update f _ (FlashProgram a data) reply p = f p.
Proof.
  intros [H _] Hsame p. destruct reply as [r f']; simpl in *.
  exact (identical_page_rewrite_unchanged _ _ _ _ _ _ H Hsame p).
Qed.

End FlashContract.

(* A reset is an abandoned call with a reached physical flash state. It is
   deliberately outside the ordinary reply/update path of the Hoare contract;
   a registry-level trace must start recovery from [after]. *)
Inductive interrupted_flash_call (g : geometry) (before : flash) :
    forall A : Type, FlashAPI A -> flash -> Prop :=
| interrupted_program a data after :
    program_step g before a data Reset after ->
    interrupted_flash_call g before _ (FlashProgram a data) after
| interrupted_erase a after :
    erase_step g before a Reset after ->
    interrupted_flash_call g before _ (FlashErase a) after.

Lemma program_reset_has_no_normal_reply g f a data after :
  ~ flash_callee g f _ (FlashProgram a data) (Reset, after).
Proof. intros [_ H]; apply H; reflexivity. Qed.

Lemma erase_reset_has_no_normal_reply g f a after :
  ~ flash_callee g f _ (FlashErase a) (Reset, after).
Proof. intros [_ H]; apply H; reflexivity. Qed.

(* No registry invariant is inserted into flash_callee. A failed page rewrite
   does preserve the bytes requested unchanged, by the physical contract. *)
