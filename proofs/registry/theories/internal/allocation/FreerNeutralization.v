From Stdlib Require Import List Arith NArith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Neutralization NeutralizationBoundary DataEpisode
 TransactionBoundary PersistentBoundary FlashSpec JournalHistory JournalRequests
 JournalReachableShape BootReconstruction PreparedAuthority RetentionCoverage.

(* Internal service witness is the existing boundary. No second flash/table.
   A normal response contains the executed physical prefix; Reset is excluded
   from this interface and consumed directly by selected_neutralization_boundary. *)
Inductive NeutralAPI : interface := Neutralize : NeutralAPI neutral_observation.
Definition neutral_update old d s h a (_ : transaction_boundary) A
 (op : NeutralAPI A) (reply : A) : transaction_boundary :=
 match op in NeutralAPI T return T -> transaction_boundary with
 | Neutralize => neutral_boundary old d s h a
 end reply.
Definition neutral_caller fuel recognize lo hi (state : transaction_boundary) A (op : NeutralAPI A) :=
 match snd state with
 | IdleBoundary _ _ s => protection_frozen s=false /\
    recycling_selection_check fuel recognize (control_image (journal_control (fst state)))
      lo hi (protection_table s)=true
 | _ => False
 end.
Definition neutral_callee g sector recognize magic lo hi (state : transaction_boundary) A
 (op : NeutralAPI A) (reply : A) :=
 match op in NeutralAPI T return T -> Prop with
 | Neutralize => fun r =>
   neutral_run g sector recognize magic hi lo (control_image (journal_control (fst state))) r /\
   (neutral_end_ r<>NeutralReset /\ neutral_end_ r<>NeutralFatal)
 end reply.
Definition neutral_contract g sector recognize magic fuel lo hi old d s h a :=
 make_contract (neutral_update old d s h a) (neutral_caller fuel recognize lo hi)
   (neutral_callee g sector recognize magic lo hi).
Definition run_neutralization : impure NeutralAPI neutral_observation :=
 request_then Neutralize (fun r=>local r).

Lemma neutral_normal_execution g sector recognize magic fuel lo hi old d s f h a result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure NeutralAPI)
  (neutral_contract g sector recognize magic fuel lo hi old d s h a) run_neutralization)
  (Logged (Ready f) h a,IdleBoundary old d s) result final ->
 neutral_run g sector recognize magic hi lo f result /\ neutral_end_ result<>NeutralReset /\
 final=neutral_boundary old d s h a result.
Proof.
 intros P. simpl in P. unroll_post P.
 destruct P as [reply [middle [[CALL EQ] REST]]]; subst middle.
 unroll_post REST. destruct REST as [R S]; subst.
 destruct CALL as [RUN [END FATAL]]. split; [exact RUN|]. split; [exact END|reflexivity].
Qed.

Theorem neutralization_normal_consumer g sector data_len boss_ok view marker ranges decode pages
 recognize magic fuel lo hi old d s f h a e result final :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
  (Logged (Ready f) h a,IdleBoundary old d s) e ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure NeutralAPI)
  (neutral_contract g sector recognize magic fuel lo hi old d s h a) run_neutralization)
  (Logged (Ready f) h a,IdleBoundary old d s) result final ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages final (selected_evidence old d e) /\
 neutral_end_ result<>NeutralReset.
Proof.
 intros G DIV C L INV SEL RUN.
 destruct (neutral_normal_execution g sector recognize magic fuel lo hi old d s f h a result final RUN) as [EXEC [END ->]].
 pose proof (selected_neutralization_boundary g sector data_len boss_ok view marker ranges decode
   (fun _=>true) pages recognize magic fuel lo hi f h a old d s e result G DIV C L INV SEL EXEC)
   as [_ [_ [SAFE BOOT]]]. auto.
Qed.

Definition neutral_open_update old image root s h a (_ : transaction_boundary) A
 (op : NeutralAPI A) (reply : A) : transaction_boundary :=
 match op in NeutralAPI T return T -> transaction_boundary with
 | Neutralize => neutral_open_boundary old image root s h a
 end reply.
Definition neutral_open_caller fuel recognize lo hi (state : transaction_boundary) A (op : NeutralAPI A) :=
 match snd state with
 | OpenBoundary _ _ s => protection_frozen s=false /\
    recycling_selection_check fuel recognize (control_image (journal_control (fst state)))
      lo hi (protection_table s)=true
 | _ => False
 end.
Definition neutral_open_contract g sector recognize magic fuel lo hi old image root s h a :=
 make_contract (neutral_open_update old image root s h a) (neutral_open_caller fuel recognize lo hi)
   (neutral_callee g sector recognize magic lo hi).

Theorem neutralization_open_normal_consumer g sector data_len boss_ok view marker ranges decode pages
 recognize magic fuel lo hi old image root s f h a e result final :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
  (Logged (Ready f) h a,OpenBoundary image root s) e ->
 hd_error h=Some (N.of_nat old) ->
 recycling_selection_check fuel recognize f lo hi (protection_table s)=true ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure NeutralAPI)
  (neutral_open_contract g sector recognize magic fuel lo hi old image root s h a) run_neutralization)
  (Logged (Ready f) h a,OpenBoundary image root s) result final ->
 exists d, enriched_invariant sector data_len boss_ok view marker ranges decode pages final
  (selected_evidence old d e) /\ neutral_end_ result<>NeutralReset.
Proof.
 intros G DIV C L INV HEAD SEL P. simpl in P. unroll_post P.
 destruct P as [reply [middle [[CALL EQ] REST]]]; subst middle.
 unroll_post REST; destruct REST as [R S]; subst. destruct CALL as [EXEC [END FATAL]].
 destruct (selected_neutralization_open_boundary g sector data_len boss_ok view marker ranges decode
  (fun _=>true) pages recognize magic fuel lo hi f h a old image root s e result
  G DIV C L INV HEAD SEL EXEC) as [_ [_ [d [SAFE BOOT]]]]. exists d; auto.
Qed.
