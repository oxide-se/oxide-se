From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Types FlashSpec PageOwnership RetentionCoverage FreerFlash.

(* The allocator's normal erase call. The lower callee contract remains exactly
   FlashSpec; coverage is proved separately and composed at the client boundary. *)
Definition erase_reserved_sector a : impure FlashAPI outcome :=
  request_then (FlashErase a) (fun reply => local (fst reply)).

Lemma erase_reserved_sector_caller g f a :
  erase_request g a -> flash_caller g f _ (FlashErase a).
Proof. exact (fun H => H). Qed.

Theorem erase_reserved_sector_post g f f' a result :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (erase_reserved_sector a)) f result f' ->
  erase_step g f a result f' /\ result <> Reset.
Proof.
  intro H. unfold erase_reserved_sector in H. unroll_post H.
  destruct H0 as [middle [He Hlocal]].
  change (post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (local (fst x))) middle result f') in Hlocal.
  unroll_post Hlocal. subst. split; assumption.
Qed.

Theorem composed_collected_erase_preserves g page ranges t f f' a result :
  page > 0 ->
  free_range page (collect_table page ranges t)
    {| offset := a; span := sector_size g |} ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (erase_reserved_sector a)) f result f' ->
  unchanged ranges f f'.
Proof.
  intros P F H. apply erase_reserved_sector_post in H.
  eapply erase_preserves_covered_ranges; eauto using collection_establishes_coverage.
  exact (proj1 H).
Qed.

Theorem interrupted_collected_erase_preserves g page ranges t f f' a :
  page > 0 ->
  free_range page (collect_table page ranges t)
    {| offset := a; span := sector_size g |} ->
  erase_step g f a Reset f' -> unchanged ranges f f'.
Proof.
  intros. eapply erase_preserves_covered_ranges;
    eauto using collection_establishes_coverage.
Qed.
