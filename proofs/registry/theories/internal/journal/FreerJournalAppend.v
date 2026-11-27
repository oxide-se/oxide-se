From Stdlib Require Import List Arith NArith Lia.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import Types FlashSpec FreerFlash
  JournalComplement JournalFlashBridge JournalWriteEntry JournalIndex JournalRequests
  JournalReachableShape JournalHistory.
Import ListNotations.

Fixpoint read_bytes_then {A} (address count : nat)
    (k : list byte -> impure FlashAPI A) : impure FlashAPI A :=
  match count with
  | O => k []
  | S n => request_then (FlashRead address) (fun b =>
      read_bytes_then (S address) n (fun bytes => k (b :: bytes)))
  end.

Lemma read_bytes_then_post g A count address k f (x : A) f' :
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (read_bytes_then address count k)) f x f' ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (k (map f (seq address count)))) f x f'.
Proof.
  revert address k f. induction count as [|n IH]; intros address k f H.
  - exact H.
  - cbn [read_bytes_then] in H. unroll_post H.
    destruct H0 as [middle [Hread Hrest]].
    destruct Hread as [Hvalue Hmiddle].
    change (x0 = f address) in Hvalue.
    change (middle = f) in Hmiddle. subst middle x0.
    apply (IH (S address) (fun bytes => k (f address :: bytes)) f Hrest).
Qed.

(* Physical command, error return, then the eight-byte readback only on
   success. AwaitAck is still before the outer commit acknowledgement. *)
Definition write_candidate (page : nat) (f : flash) (index : nat) (d : N) :
    impure FlashAPI control :=
  request_then
    (FlashProgram (8*index/page*page) (candidate_buffer page f index d))
    (fun reply => match fst reply with
     | Success => read_bytes_then (8*index) 8 (fun bytes =>
         local (match list_eq_dec N.eq_dec bytes (code_bytes d) with
                | left _ => AwaitAck (snd reply) index d
                | right _ => Frozen (snd reply) end))
     | VerifyFailed => local (Frozen (snd reply))
     | Reset => local (Boot (snd reply))
     end).

Theorem reachable_write_flash_caller g sector page data_len boss_ok f i d :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  reachable g sector page data_len boss_ok (Writing f i d) ->
  flash_caller g f _
    (FlashProgram (8*i/page*page) (candidate_buffer page f i d)).
Proof.
  intros Hgeom Hsector8 Hreach.
  eapply reachable_candidate_request; eauto.
Qed.

Theorem reachable_readback_flash_callers g sector page data_len boss_ok f i d
    reached j :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  reachable g sector page data_len boss_ok (Writing f i d) -> j < 8 ->
  flash_caller g reached _ (FlashRead (8*i+j)).
Proof.
  intros Hgeom Hsector8 Hreach Hj.
  pose proof (reachable_invariant g sector page data_len boss_ok Hgeom Hsector8
    _ Hreach) as [_ [_ Hfirst]].
  destruct (first_empty_slot_sound _ _ Hfirst) as [Hi _].
  unfold sector_bytes in Hi. rewrite length_map in Hi. rewrite length_seq in Hi.
  destruct Hgeom as [Hs [Hp [Hstart [Harea Hrest]]]].
  change (within g (8*i+j) 1). unfold within. rewrite Hstart.
  pose proof (Nat.div_mod sector 8 ltac:(lia)). split; lia.
Qed.

Theorem write_candidate_normal_refines_step g sector page data_len boss_ok
    f i d next after :
  journal_geometry g sector page ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (write_candidate page f i d)) f next after ->
  step g sector page data_len boss_ok (Writing f i d) next.
Proof.
  intros Hgeom Hpost.
  unfold write_candidate in Hpost. unroll_post Hpost.
  match goal with H : exists middle, _ |- _ =>
    destruct H as [command_state [Hcommand Hrest]] end.
  destruct Hcommand as [[Hphysical Hnormal] Hmiddle].
  destruct x as [result reached].
  change (command_state = reached) in Hmiddle. subst command_state.
  cbn [fst snd] in Hphysical, Hnormal, Hrest.
  destruct Hgeom as [Hs [Hp [_ [_ [Hsize [Hpage8 Hmultiple]]]]]].
  clear Hs Hp.
  destruct result; [| |contradiction].
  - pose proof (read_bytes_then_post g control 8 (8*i)
      (fun bytes => local
        (match list_eq_dec N.eq_dec bytes (code_bytes d) with
         | left _ => AwaitAck reached i d | right _ => Frozen reached end))
      reached next after Hrest) as Hread.
    assert (Hcode : map reached (seq (8*i) 8) = code_bytes d).
    { change (flash_slot reached (8*i) = code_bytes d).
      pose proof (Nat.div_mod (8*i) page ltac:(lia)) as Haddr.
      replace (8*i) with (8*i/page*page + 8*i mod page) by nia.
      rewrite (success_program_slot_exact _ _ _ _ _ (8*i mod page) Hphysical).
      - apply write_entry_page_target_slot; [apply code_bytes_length|].
        apply slot_fits_page; lia.
      - unfold candidate_buffer. rewrite write_entry_page_length.
        apply slot_fits_page; lia. }
    rewrite Hcode in Hread.
    destruct (list_eq_dec N.eq_dec (code_bytes d) (code_bytes d));
      [|contradiction].
    unroll_post Hread. subst.
    apply (candidate_program g sector page data_len boss_ok f after i d Success).
    exact Hphysical.
  - change (post (to_hoare
      (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
      (flash_contract g) (local (Frozen reached))) reached next after) in Hrest.
    unroll_post Hrest. subst.
    apply (candidate_program g sector page data_len boss_ok f after i d VerifyFailed).
    exact Hphysical.
Qed.

Theorem composed_write_preserves_journal_history g sector page data_len boss_ok
    f i d history acks next after :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (Writing f i d) history acks) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (write_candidate page f i d)) f next after ->
  logged_invariant sector page data_len boss_ok
    (Logged next (publication_history_after history (Writing f i d) next)
      (acknowledgement_history_after acks (Writing f i d) next)).
Proof.
  intros Hgeom Hsector8 Hinv Hpost.
  eapply (logged_step_preserves_invariant g sector page data_len boss_ok
    Hgeom Hsector8); [exact Hinv|].
  apply record_step. eapply write_candidate_normal_refines_step; eauto.
Qed.

Theorem interrupted_candidate_refines_reset g sector page data_len boss_ok
    f i d after :
  interrupted_flash_call g f _
    (FlashProgram (8*i/page*page) (candidate_buffer page f i d)) after ->
  step g sector page data_len boss_ok (Writing f i d) (Boot after).
Proof.
  intro H. inversion H; subst.
  apply (candidate_program g sector page data_len boss_ok f after i d Reset).
  assumption.
Qed.

(* The actual ordinary write/readback program justifies the internal
   SlotCompleted update. No authority correspondence at arrival is a premise. *)
From OxideSE.Registry Require Import PreparedAuthority RetentionCoverage CollectionRoots.
Theorem write_readback_justifies_slot_completed g sector page data_len boss_ok
    view s before after index d history acks :
  journal_geometry g sector page -> sector mod 8 = 0 ->
  logged_invariant sector page data_len boss_ok (Logged (Writing before index d) history acks) ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (write_candidate page before index d)) before (AwaitAck after index d) after ->
  let next_history := publication_history_after history (Writing before index d) (AwaitAck after index d) in
  logged_invariant sector page data_len boss_ok (Logged (Ready after) next_history (d :: acks)) /\
  protection_history_link view (slot_publication (root_extents (view (N.to_nat d))) s)
    (Logged (Ready after) next_history (d :: acks)).
Proof.
  intros G D I POST; cbn zeta.
  pose proof (composed_write_preserves_journal_history g sector page data_len boss_ok
    before index d history acks (AwaitAck after index d) after G D I POST) as NEXT.
  cbn [acknowledgement_history_after] in NEXT.
  split; [eapply append_return_preserves_logged_invariant; eauto|].
  destruct NEXT as [_ [[_ HEAD] _]].
  unfold protection_history_link; simpl.
  change (hd_error (publication_history_after history (Writing before index d)
    (AwaitAck after index d)) = Some d) in HEAD.
  rewrite HEAD; reflexivity.
Qed.

Theorem write_error_justifies_uncertain_edge g sector page data_len boss_ok
    before after index d history acks :
  journal_geometry g sector page ->
  post (to_hoare
    (im:=ImpureModule_acto__canonical__Impure_MonadImpure FlashAPI)
    (flash_contract g) (write_candidate page before index d)) before (Frozen after) after ->
  uncertain_logged_step g sector page data_len boss_ok d
    (Logged (Writing before index d) history acks)
    (Logged (Frozen after)
      (publication_history_after history (Writing before index d) (Frozen after)) acks).
Proof.
  intros G POST. split; [reflexivity|]. split; [exact I|]. split; [exact I|].
  apply (record_step g sector page data_len boss_ok (Writing before index d) (Frozen after)).
  eapply write_candidate_normal_refines_step; eauto.
Qed.
