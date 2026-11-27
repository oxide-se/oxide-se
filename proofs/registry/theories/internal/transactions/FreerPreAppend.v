From Stdlib Require Import List NArith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec TransactionBoundary PreAppendValidation.

(* One typed request to the existing software format component, not a new
   physical flash command. The diagnostic event list documents its inner path.
   Its observation provider is always applied to the reached flash. *)
Inductive BossCheckAPI : interface :=
 | DecodeBossBeforeAppend : nat -> bool -> BossCheckAPI boss_check_result.
Definition boss_check_caller (f:flash) A (op:BossCheckAPI A) : Prop := True.
Definition boss_check_callee observe (f:flash) A (op:BossCheckAPI A) : A->Prop :=
 match op with DecodeBossBeforeAppend id cached =>
   fun reply=>reply=snd (check_boss_before_append cached (observe f id)) end.
Definition boss_check_update (f:flash) A (op:BossCheckAPI A) (reply:A) := f.
Definition boss_check_contract observe :=
 make_contract boss_check_update boss_check_caller (boss_check_callee observe).
Definition boss_check_program id cached : impure BossCheckAPI boss_check_result :=
 request_then (DecodeBossBeforeAppend id cached) (fun reply=>local reply).
Lemma boss_check_program_post observe f id cached result after :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (boss_check_program id cached)) f result after ->
 after=f /\ result=snd (check_boss_before_append cached (observe f id)).
Proof.
 intro H;unfold boss_check_program in H;unroll_post H.
 destruct H0 as [middle [CALL LOCAL]].
 destruct CALL as [VALUE FRAME].
 change (middle=f) in FRAME;subst middle.
 change (post (to_hoare
   (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (local x)) f result after) in LOCAL.
 unroll_post LOCAL;subst;split;reflexivity.
Qed.
Theorem composed_boss_check read observe f id d n cached result after :
 boss_check_provider read observe -> read f id=Some (d,n) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BossCheckAPI)
   (boss_check_contract observe) (boss_check_program id cached)) f result after ->
 after=f /\ (result=BossCheckReady (counter_value n) \/
 result=BossCheckFailed GenerationError \/
 (cached=false /\ result=BossCheckFailed AuthenticationError)).
Proof.
 intros CONTRACT READ RUN.
 destruct (boss_check_program_post _ _ _ _ _ _ RUN) as [FRAME VALUE].
 split;[exact FRAME|]. rewrite VALUE.
 exact (checked_boss_from_decoding _ _ _ _ _ _ cached CONTRACT READ).
Qed.
