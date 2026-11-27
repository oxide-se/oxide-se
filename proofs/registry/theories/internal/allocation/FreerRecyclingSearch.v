From Stdlib Require Import List Arith NArith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import RecyclingSearch RecyclingSearchBoundary Neutralization
 NeutralizationBoundary FreerNeutralization RetentionCoverage FlashSpec PreparedAuthority JournalHistory
 JournalRequests JournalReachableShape TransactionBoundary BootReconstruction.

Inductive RecyclingAPI : interface :=
 | SearchReusable : RecyclingAPI search_reply
 | RetireCandidate : recycle_candidate -> RecyclingAPI neutral_observation.
Section Service.
Variable g:geometry.
Variable sector fuel:nat.
Variable recognize:flash->nat->option nat.
Variable magic:flash->nat->bool.
Variable req:nat->required_reply.
Variable round:nat->option nat.
Variable alignment pages start old:nat.
Variable image:list CompactImage.compact_slot.
Variable root:list extent.
Variable ram:protection_state.
Variable h a:list N.
Definition search_at (s:transaction_boundary) :=
 reusable_search sector fuel recognize (control_image (journal_control (fst s)))
   (protection_table ram) req round alignment pages start.
Definition recycling_caller (s:transaction_boundary) A (op:RecyclingAPI A) :=
 match op with
 | SearchReusable=>protection_frozen ram=false
 | RetireCandidate r=>search_at s=FoundRecyclable r
 end.
Definition recycling_callee (s:transaction_boundary) A (op:RecyclingAPI A) (reply:A) :=
 match op in RecyclingAPI T return T->Prop with
 | SearchReusable=>fun answer=>answer=search_at s
 | RetireCandidate r=>fun result=>
   neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r)
     (control_image (journal_control (fst s))) result /\
   neutral_end_ result<>NeutralReset /\ neutral_end_ result<>NeutralFatal
 end reply.
Definition recycling_update (s:transaction_boundary) A (op:RecyclingAPI A) (reply:A) :=
 match op in RecyclingAPI T return T->transaction_boundary with
 | SearchReusable=>fun _=>s
 | RetireCandidate _=>neutral_open_boundary old image root ram h a
 end reply.
Definition recycling_contract := make_contract recycling_update recycling_caller recycling_callee.
Definition search_then_retire : impure RecyclingAPI (search_reply+neutral_observation) :=
 request_then SearchReusable (fun answer=>match answer with
 | FoundRecyclable r=>request_then (RetireCandidate r) (fun result=>local (inr result))
 | other=>local (inl other)
 end).

Lemma search_then_retire_execution f result final :
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecyclingAPI)
   recycling_contract search_then_retire)
   (Logged (Ready f) h a,OpenBoundary image root ram) (inr result) final ->
 exists r,
 reusable_search sector fuel recognize f (protection_table ram) req round alignment pages start=FoundRecyclable r /\
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result /\
 final=neutral_open_boundary old image root ram h a result.
Proof.
 intro P. simpl in P; unroll_post P.
 destruct P as [reply [middle [[ANSWER EQ] REST]]]; subst middle.
 destruct reply; simpl in REST; unroll_post REST; try (destruct REST as [BAD _]; discriminate BAD).
 destruct REST as [observed [next [[RUN EQ] DONE]]]; subst next.
 unroll_post DONE. destruct DONE as [R S]. inversion R; subst observed. subst final.
 exists r. split; [symmetry; exact ANSWER|]. split; [exact (proj1 RUN)|reflexivity].
Qed.
End Service.

(* Normal impure execution consumes the search and the actual neutralization.
   The logical invariant is supplied only at entry, outside the callee. *)
Theorem search_then_retire_safe g sector fuel recognize magic req round alignment pages start old image root ram h a
 data_len boss_ok view marker ranges decode (topology:recovery_decoding->bool) f e result final :
 journal_geometry g sector 256 -> sector mod 8=0 ->
 recovery_local_contracts view ranges decode -> recognizer_local sector recognize ->
 enriched_invariant sector data_len boss_ok view marker ranges decode pages
   (Logged (Ready f) h a,OpenBoundary image root ram) e ->
 hd_error h=Some (N.of_nat old) ->
 post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure RecyclingAPI)
   (recycling_contract g sector fuel recognize magic req round alignment pages start old image root ram h a)
   search_then_retire)
   (Logged (Ready f) h a,OpenBoundary image root ram) (inr result) final ->
 exists d, enriched_invariant sector data_len boss_ok view marker ranges decode pages final (selected_evidence old d e).
Proof.
 intros G DIV C L INITIAL HEAD RUN.
 destruct (search_then_retire_execution g sector fuel recognize magic req round alignment pages start old image root ram h a
  f result final RUN) as [r [SEARCH [EXEC ->]]].
 destruct (searched_neutralization_open_boundary g sector data_len boss_ok view marker ranges decode topology pages
  recognize magic fuel f h a old image root ram e req round alignment start r result
  G DIV C L INITIAL HEAD SEARCH EXEC) as [d [FINAL REST]]. exists d; exact FINAL.
Qed.
