(* Public signature of the initialized owned Data component. The interpretation
   supplies types, observations and operational relations, never their proofs. *)
From Coq Require Import List.
Import ListNotations.

Record SupplierLaws := {
  journal_layout : Prop;
  slot_alignment : Prop;
  validator_acceptance : Prop;
  reader_locality : Prop;
  marker_coverage : Prop;
  journal_mapping : Prop;
  page_mapping : Prop;
  address_decoding : Prop;
  marker_bounds : Prop;
  decoded_bounds : Prop;
  word_capacity : Prop;
  area_bounds : Prop;
  allocation_geometry : Prop;
  registry_base : Prop
}.

Definition required (laws : SupplierLaws) :=
  journal_layout laws /\
  slot_alignment laws /\
  validator_acceptance laws /\
  reader_locality laws /\
  marker_coverage laws /\
  journal_mapping laws /\
  page_mapping laws /\
  address_decoding laws /\
  marker_bounds laws /\
  decoded_bounds laws /\
  word_capacity laws /\
  area_bounds laws /\
  allocation_geometry laws /\
  registry_base laws.

Record Vocabulary := {
  Validator : Type;
  View : Type;
  State : Type;
  Receipt : Type;
  Exit : Type;
  Observation : Type;
  Response : Type;
  invariant : Validator -> View -> State -> Prop;
  numeric : State -> Prop;
  entry_closed : State -> Prop;
  ordinary_closed : State -> Prop;
  safe : Validator -> View -> State -> Prop;
  trace : Validator -> View -> State -> list Receipt -> Validator -> View -> State -> Prop;
  receipts : State -> list Receipt;
  valid_receipt : View -> State -> Receipt -> Prop;
  historical : Receipt -> Prop;
  receipts_of_exits : list Exit -> list Receipt;
  receipts_of_responses : list Response -> list Receipt;
  receipts_of_exit : Exit -> list Receipt;
  observations : list Exit -> list Observation;
  observe : list Observation -> Exit -> list Observation;
  matches : Response -> Exit -> Prop;
  ready : Response -> State -> Prop;
  first_call : (Response -> Prop) -> Prop;
  completed : list Receipt -> Validator -> View -> State -> Exit -> Prop;
  return_post : list Receipt -> Validator -> View -> State -> Prop;
  prepass_matches : Validator -> View -> State -> Exit -> Prop;
  schedule : nat -> list (Response -> Prop) -> Validator -> View -> State -> Prop
}.

Section Contract.
Variable m : Vocabulary.
Variable v : Validator m.
Variable o : View m.
Variable initial : State m.
Variable fuel : nat.
Variable requests : list (Response m -> Prop).
Variable first : Response m -> Prop.

Definition entry := invariant m v o initial /\ numeric m initial /\ entry_closed m initial.

(* Services for the first call and the remaining schedule. Callers need
   supply continuations only for an actual completed operation and response. *)
Definition executions :=
  first_call m first /\
  forall log vo oo reached exit response,
    completed m log vo oo reached exit -> return_post m log vo oo reached ->
    invariant m vo oo reached -> log = receipts_of_exit m exit ->
    matches m response exit -> first response -> ready m response reached ->
    prepass_matches m vo oo reached exit -> schedule m fuel requests vo oo reached.

Definition offered :=
  exists vf of_ final exits responses,
    trace m v o initial (receipts_of_exits m exits) vf of_ final /\
    invariant m vf of_ final /\ numeric m final /\ ordinary_closed m final /\
    receipts m final = receipts_of_exits m exits ++ receipts m initial /\
    Forall (valid_receipt m of_ final) (receipts m final) /\
    Forall (historical m) (receipts_of_exits m exits) /\
    (forall history, history ++ observations m exits = fold_left (observe m) exits history) /\
    (forall events vp op prefix, trace m v o initial events vp op prefix ->
       safe m vp op prefix /\ numeric m prefix) /\
    Forall2 (matches m) responses exits /\
    Forall2 (fun predicate response => predicate response) (first :: requests) responses /\
    receipts_of_exits m exits = receipts_of_responses m responses.

Definition signature laws := required laws -> entry -> executions -> offered.
End Contract.
