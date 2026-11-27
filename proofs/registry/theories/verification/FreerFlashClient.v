From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Types FlashSpec FreerFlash.

(* A genuinely impure program interpreted by FreerDPS's Hoare semantics. *)
Definition read_twice (a : nat) : impure FlashAPI (byte * byte) :=
  request_then (FlashRead a) (fun first =>
  request_then (FlashRead a) (fun second =>
  local (first, second))).

Theorem read_twice_same (g : geometry) (f f' : flash)
    (a : nat) (x y : byte) :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (read_twice a)) f (x, y) f' ->
  x = y /\ f' = f.
Proof.
  intro H. unfold read_twice in H.
  unroll_post H.
  destruct H0 as [middle [[first_reply middle_eq]
    [second [last [[second_reply last_eq] [pair_eq final_eq]]]]]].
  cbn in *. inversion pair_eq; subst. split; congruence.
Qed.

(* A normal continuation after one physical page command observes the reached
   flash image. A reset takes the separate interrupted-call path and never
   enters this continuation. *)
Definition program_then_read (page : nat) (data : payload) (probe : nat) :
    impure FlashAPI (outcome * byte) :=
  request_then (FlashProgram page data) (fun reply =>
  request_then (FlashRead probe) (fun observed =>
  local (fst reply, observed))).

Theorem program_then_read_observes_reached (g : geometry) (f f' : flash)
    (page : nat) (data : payload) (probe : nat) (r : outcome) (observed : byte) :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (program_then_read page data probe))
    f (r, observed) f' ->
  r <> Reset /\ observed = f' probe.
Proof.
  intro H. unfold program_then_read in H.
  unroll_post H.
  destruct H0 as [middle [Hprogram Hrest]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g)
    (request_then (FlashRead probe) (fun v => local (fst x, v))))
    middle (r, observed) f') in Hrest.
  unroll_post Hrest.
  destruct H2 as [last [Hread Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (local (fst x, x0)))
    last (r, observed) f') in Hlocal.
  unroll_post Hlocal.
  inversion H3; subst. split; assumption || reflexivity.
Qed.
