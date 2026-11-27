From Coq Require Import List Arith NArith Bool.
Import ListNotations.

(* Bytes are numbers with a separate well-formedness predicate. *)
Definition byte := N.
Definition valid_byte (b : byte) : Prop := (b < 256)%N.
Definition payload := list byte.
Definition valid_payload (p : payload) : Prop := Forall valid_byte p.

(* Abstract owner and object AIDs; Data is the only object kind in this lot. *)
Definition identity := (nat * nat)%type.
Definition identity_eq_dec : forall x y : identity, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition view := identity -> option payload.
Definition same_view (a b : view) := forall k, a k = b k.
Definition empty_view : view := fun _ => None.
Definition put (v : view) (k : identity) (x : option payload) : view :=
  fun q => if identity_eq_dec q k then x else v q.
Lemma put_same v k x : put v k x k = x.
Proof. unfold put; destruct (identity_eq_dec k k); congruence. Qed.
Lemma put_other v k q x : q <> k -> put v k x q = v q.
Proof. intros H; unfold put; destruct (identity_eq_dec q k); congruence. Qed.
