From OxideSE.Registry Require Import Types FlashSpec.

(* Specifications only: no recovery algorithm, commit protocol or theorem is
   asserted here. The executable model will later supply these parameters. *)
Definition recovers_as (recover : flash -> option view) (f : flash) (v : view) : Prop :=
  exists recovered, recover f = Some recovered /\ same_view recovered v.
Definition recovers_old_or_new (recover : flash -> option view)
    (f : flash) (old new : view) : Prop :=
  recovers_as recover f old \/ recovers_as recover f new.
Definition interrupted_commit_safe (recover : flash -> option view)
    (reachable_cut : flash -> Prop) (old new : view) : Prop :=
  forall f, reachable_cut f -> recovers_old_or_new recover f old new.
Definition acknowledged_commit_durable (recover : flash -> option view)
    (returned_success : flash -> Prop) (new : view) : Prop :=
  forall f, returned_success f -> recovers_as recover f new.
