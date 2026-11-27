From Stdlib Require Import Bool.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import JournalFreeze.

(* Typed registry-side gate layered above FreerFlash. Its witness has concrete
   volatile freeze/readiness fields and ghost acknowledgement/protection data.
   Rust satisfaction is a separate correspondence obligation. *)
Inductive JournalGateAPI : interface :=
| RecordJournalError : JournalGateAPI unit
| CheckAppend : JournalGateAPI bool
| CheckPhysical : JournalGateAPI bool
| CheckAllocation : JournalGateAPI bool
| CheckRelease : JournalGateAPI bool.

Definition gate_caller (s : witness) (A : Type) (e : JournalGateAPI A) : Prop :=
  True.

Definition gate_callee (s : witness) (A : Type)
    (e : JournalGateAPI A) (x : A) : Prop :=
  match e in JournalGateAPI T return T -> Prop with
  | RecordJournalError => fun _ => True
  | CheckAppend => fun allowed =>
      allowed = negb (frozen s) && boot_ready s
  | CheckPhysical => fun allowed => allowed = negb (frozen s)
  | CheckAllocation => fun allowed => allowed = negb (frozen s)
  | CheckRelease => fun allowed => allowed = negb (frozen s)
  end x.

Definition gate_update (s : witness) (A : Type)
    (e : JournalGateAPI A) (x : A) : witness :=
  match e in JournalGateAPI T return T -> witness with
  | RecordJournalError => fun _ => freeze_with s (image s)
  | CheckAppend => fun _ => s
  | CheckPhysical => fun _ => s
  | CheckAllocation => fun _ => s
  | CheckRelease => fun _ => s
  end x.

Definition gate_contract : contract JournalGateAPI witness :=
  make_contract gate_update gate_caller gate_callee.

Lemma fault_then_append_gate_closed s :
  gate_callee (gate_update s _ RecordJournalError tt) _ CheckAppend false.
Proof. unfold gate_callee, gate_update, freeze_with. simpl. reflexivity. Qed.

Definition fault_then_check_append : impure JournalGateAPI bool :=
  request_then RecordJournalError (fun _ =>
  request_then CheckAppend (fun allowed => local allowed)).

Theorem composed_fault_refuses_append s s' allowed :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure JournalGateAPI)
    gate_contract fault_then_check_append) s allowed s' ->
  allowed = false /\ frozen s' = true /\ image s' = image s.
Proof.
  intro H. unfold fault_then_check_append in H.
  unroll_post H.
  destruct H0 as [middle [Hrecord Hrest]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure JournalGateAPI)
    gate_contract (request_then CheckAppend (fun x => local x)))
    middle allowed s') in Hrest.
  unroll_post Hrest.
  destruct H as [last [Hcheck Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure JournalGateAPI)
    gate_contract (local x0)) last allowed s') in Hlocal.
  unroll_post Hlocal.
  subst. unfold gate_update in *. simpl in *.
  unfold gate_callee in *. simpl in *.
  unfold freeze_with in *. simpl in *.
  repeat split; congruence.
Qed.
