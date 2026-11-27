From Stdlib Require Import List.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Types FlashSpec PreparationOutcomes FreerFlash.
Import ListNotations.

(* Each edge of writer_execution consumes the same lower FlashAPI contract.
   Prefix composition remains relational, including abandoned continuations. *)
Definition preparation_command (c : writer_command) : impure FlashAPI (outcome * flash) :=
  request_then (FlashProgram (command_address c) (command_bytes c)) (fun reply => local reply).

Theorem preparation_command_post g c before reply after :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (preparation_command c)) before reply after ->
  program_step g before (command_address c) (command_bytes c) (fst reply) after /\
  after = snd reply /\ fst reply <> Reset.
Proof.
  intros H. unfold preparation_command in H. unroll_post H.
  destruct H0 as [middle [[[STEP NORESET] UPDATE] REST]].
  unroll_post REST. destruct REST as [REPLY FINAL]. subst reply after middle.
  split; [exact STEP|]. split; [reflexivity|exact NORESET].
Qed.

Theorem failed_preparation_command_refines g sector r boss c tail before reply after :
  command_in_reservation sector r c -> fst reply = VerifyFailed ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (preparation_command c)) before reply after ->
  writer_execution g sector r boss before (c::tail)
    (WriterObservation after [(c,VerifyFailed)] WriterPhysicalError).
Proof.
  intros IN ERROR POST. apply preparation_command_post in POST.
  destruct POST as [STEP REST]. rewrite ERROR in STEP.
  apply writer_failed_command; assumption.
Qed.

Theorem successful_preparation_command_composes g sector r boss c tail before reply after result :
  command_in_reservation sector r c -> fst reply = Success ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (preparation_command c)) before reply after ->
  writer_execution g sector r boss after tail result ->
  writer_execution g sector r boss before (c::tail)
    (WriterObservation (writer_flash result) ((c,Success)::writer_prefix result) (writer_end result)).
Proof.
  intros IN OK POST REST. apply preparation_command_post in POST.
  destruct POST as [STEP OTHER]. rewrite OK in STEP.
  eapply writer_successful_command; eauto.
Qed.

Theorem interrupted_preparation_command_refines g sector r boss c tail before after :
  command_in_reservation sector r c ->
  interrupted_flash_call g before _ (FlashProgram (command_address c) (command_bytes c)) after ->
  writer_execution g sector r boss before (c::tail)
    (WriterObservation after [(c,Reset)] WriterInterrupted).
Proof.
  intros IN INTERRUPT. inversion INTERRUPT; subst.
  apply writer_reset_command; assumption.
Qed.
