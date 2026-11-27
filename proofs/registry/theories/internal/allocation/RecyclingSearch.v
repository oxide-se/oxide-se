From Coq Require Import List Arith NArith Bool Lia.
From OxideSE.Registry Require Import AllocationAdmission Neutralization FlashSpec RetentionCoverage PageOwnership JournalHistory.
Import ListNotations.

(* Control of find_span_in/find_reusable_span_sized_from. No storage state.
   Page coordinates; checked size conversion/rounding is a local service.
   RequiredError is arithmetic failure, RequiredSkip is required_at=None. *)
Inductive required_reply := RequiredError | RequiredSkip | RequiredPages (n:nat).
Record recycle_candidate := RecycleCandidate { recycle_lo:nat; useful_pages:nat; erase_pages:nat }.
Inductive search_reply := SearchError | SearchMiss
 | FoundErased (i n:nat) | FoundRecyclable (r:recycle_candidate).
Definition candidate_guard fuel recognize f t r :=
 recycling_selection_check fuel recognize f (recycle_lo r)
   (recycle_lo r + erase_pages r) t.

Fixpoint search_candidates sector fuel recognize f t
 (required_at:nat->required_reply) (erase_round:nat->option nat) (erase_alignment:nat)
 (positions:list (nat*nat)) (first:option recycle_candidate) : search_reply :=
 match positions with
 | [] => match first with None=>SearchMiss | Some r=>FoundRecyclable r end
 | (i,last)::tail =>
   match required_at (256*i) with
   | RequiredError => SearchError
   | RequiredSkip => search_candidates sector fuel recognize f t required_at erase_round erase_alignment tail first
   | RequiredPages n =>
     if ((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n)
     then FoundErased i n
     else match first with
     | Some _ => search_candidates sector fuel recognize f t required_at erase_round erase_alignment tail first
     | None => if Nat.eqb (i mod erase_alignment) 0 then
       match erase_round n with
       | None=>SearchError
       | Some k=>let r:=RecycleCandidate i n k in
         let next:=if (i+k<=?last) && candidate_guard fuel recognize f t r then Some r else None in
         search_candidates sector fuel recognize f t required_at erase_round erase_alignment tail next
       end
       else search_candidates sector fuel recognize f t required_at erase_round erase_alignment tail None
     end
   end
 end.
Definition search_positions pages start :=
 map (fun i=>(i,pages)) (seq start (pages-start)) ++
 map (fun i=>(i,start)) (seq 0 start).
Definition reusable_search sector fuel recognize f t req round alignment pages start :=
 if (0<?alignment) && (start<=?pages) then
 search_candidates sector fuel recognize f t req round alignment
   (search_positions pages (if Nat.eqb start pages then 0 else start)) None
 else SearchError.
Definition memo_checked fuel recognize f t first :=
 match first with None=>True | Some r=>candidate_guard fuel recognize f t r=true end.

Lemma search_candidates_guard sector fuel recognize f t req round alignment positions first r :
 memo_checked fuel recognize f t first ->
 search_candidates sector fuel recognize f t req round alignment positions first=FoundRecyclable r ->
 candidate_guard fuel recognize f t r=true.
Proof.
 revert first; induction positions as [|[i last] tail IH]; intros first M RUN; cbn [search_candidates] in RUN.
 - destruct first; inversion RUN; subst; exact M.
 - destruct (req (256*i)); try discriminate.
   + exact (IH first M RUN).
   + destruct (((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n)) eqn:ER; try discriminate.
     destruct first as [saved|].
     * eapply IH; eauto.
     * destruct (Nat.eqb (i mod alignment) 0); [|eapply IH; eauto; exact I].
       destruct (round n) as [k|]; try discriminate.
       destruct ((i+k<=?last) && candidate_guard fuel recognize f t (RecycleCandidate i n k)) eqn:G.
       -- eapply IH; [|exact RUN]. unfold memo_checked.
          apply andb_true_iff in G; exact (proj2 G).
       -- exact (IH None I RUN).
Qed.
Theorem reusable_search_derives_guard sector fuel recognize f t req round alignment pages start r :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 selected_recycling recognize f (recycle_lo r) (recycle_lo r+erase_pages r) t.
Proof.
 unfold reusable_search. destruct (_ && _); [|discriminate]. intro RUN.
 apply selected_check_sound with (fuel:=fuel).
 exact (search_candidates_guard sector fuel recognize f t req round alignment _ None r I RUN).
Qed.

Theorem search_to_neutralization g sector fuel recognize magic f t req round alignment pages start r result live :
 recognizer_local sector recognize -> valid_flash f -> protected (needed 256 live) t ->
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 free_range 256 t (block_pages (recycle_lo r) (erase_pages r)) /\
 valid_flash (neutral_flash result) /\
 unchanged live (object_flash sector f) (object_flash sector (neutral_flash result)) /\
 (forall a, a<2*sector -> neutral_flash result a=f a).
Proof.
 intros LOCAL VALID COVER SEARCH RUN.
 pose proof (reusable_search_derives_guard _ _ _ _ _ _ _ _ _ _ _ SEARCH) as SELECT.
 pose proof (neutralization_consumer g sector recognize magic (recycle_lo r)
   (recycle_lo r+erase_pages r) t f result live LOCAL VALID COVER SELECT RUN) as POST.
 replace (recycle_lo r+erase_pages r-recycle_lo r) with (erase_pages r) in POST by lia.
 exact POST.
Qed.

Example search_skip_is_not_capacity :
 reusable_search 4096 8 example_recognize (fun _=>255%N) (fun _=>free_cell)
   (fun _=>RequiredSkip) (fun n=>Some n) 1 8 0=SearchMiss.
Proof. reflexivity. Qed.
Example search_arithmetic_error :
 reusable_search 4096 8 example_recognize (fun _=>255%N) (fun _=>free_cell)
   (fun _=>RequiredError) (fun n=>Some n) 1 8 0=SearchError.
Proof. reflexivity. Qed.

Theorem reusable_search_check sector fuel recognize f t req round alignment pages start r :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 candidate_guard fuel recognize f t r=true.
Proof.
 unfold reusable_search; destruct (_ && _); [|discriminate]; intro RUN.
 exact (search_candidates_guard sector fuel recognize f t req round alignment _ None r I RUN).
Qed.

Example recycled_search_witness :
 reusable_search 4096 8 example_recognize (fun _=>0%N) (fun _=>free_cell)
   (fun address=>if Nat.eqb address 512 then RequiredPages 1 else RequiredSkip)
   (fun _=>Some 2) 2 8 2=FoundRecyclable (RecycleCandidate 2 1 2).
Proof. vm_compute; reflexivity. Qed.
Example later_erased_precedes_memoized_recycle :
 reusable_search 4096 8 example_recognize
   (fun address=>if (9216<=?address) && (address<?9472) then 255%N else 0%N)
   (fun _=>free_cell)
   (fun address=>if Nat.eqb address 512 || Nat.eqb address 1024 then RequiredPages 1 else RequiredSkip)
   (fun _=>Some 2) 2 8 2=FoundErased 4 1.
Proof. vm_compute; reflexivity. Qed.

Fixpoint check_returned fuel (returned:flash->nat->Prop) recognize f lo hi t i : Prop :=
 if hi<=?i then True else match fuel with
 | 0=>True
 | S fuel' => returned f i /\ match recognize f i with
   | None=>check_returned fuel' returned recognize f lo hi t (S i)
   | Some n=>if (0<?n) && ((i+n<=?lo) || ((lo<=?i) && vacantb t (block_pages i n)))
      then check_returned fuel' returned recognize f lo hi t (i+n) else True
   end end.
Definition selection_returned fuel returned recognize f lo hi t :=
 if (lo<?hi) && vacantb t (block_pages lo (hi-lo))
 then check_returned fuel returned recognize f lo hi t 0 else True.

(* A12.g.29: prefixes reaching a recognition call, not a second search/store.
   Successful preceding observations use the existing recognizer. The last
   call has no returned value when crypto stops or a reset cuts the read. *)
Inductive recognition_call_prefix (returned:flash->nat->Prop) (recognize:flash->nat->option nat) (f:flash) lo hi t : nat -> nat -> nat -> Prop :=
| recognition_here fuel i : i<hi ->
    recognition_call_prefix returned recognize f lo hi t (S fuel) i i
| recognition_next fuel i target : i<hi -> returned f i -> recognize f i=None ->
    recognition_call_prefix returned recognize f lo hi t fuel (S i) target ->
    recognition_call_prefix returned recognize f lo hi t (S fuel) i target
| recognition_jump fuel i n target : i<hi -> returned f i -> recognize f i=Some n ->
    (0<?n) && ((i+n<=?lo) || ((lo<=?i) && vacantb t (block_pages i n)))=true ->
    recognition_call_prefix returned recognize f lo hi t fuel (i+n) target ->
    recognition_call_prefix returned recognize f lo hi t (S fuel) i target.

Inductive search_call_prefix sector fuel returned recognize f t req round alignment :
 list (nat*nat) -> option recycle_candidate -> nat -> Prop :=
| search_skip_required i last tail first target : req (256*i)=RequiredSkip ->
    search_call_prefix sector fuel returned recognize f t req round alignment tail first target ->
    search_call_prefix sector fuel returned recognize f t req round alignment ((i,last)::tail) first target
| search_call_here i last tail n k target :
    req (256*i)=RequiredPages n ->
    ((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n)=false ->
    Nat.eqb (i mod alignment) 0=true -> round n=Some k -> i+k<=last ->
    (i<?i+k) && vacantb t (block_pages i k)=true ->
    recognition_call_prefix returned recognize f i (i+k) t fuel 0 target ->
    search_call_prefix sector fuel returned recognize f t req round alignment ((i,last)::tail) None target
| search_skip_candidate i last tail first n target :
    req (256*i)=RequiredPages n ->
    ((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n)=false ->
    (first<>None \/ Nat.eqb (i mod alignment) 0=false) ->
    search_call_prefix sector fuel returned recognize f t req round alignment tail first target ->
    search_call_prefix sector fuel returned recognize f t req round alignment ((i,last)::tail) first target
| search_checked_candidate i last tail n k target :
    req (256*i)=RequiredPages n ->
    ((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n)=false ->
    Nat.eqb (i mod alignment) 0=true -> round n=Some k ->
    (if i+k<=?last then selection_returned fuel returned recognize f i (i+k) t else True) ->
    search_call_prefix sector fuel returned recognize f t req round alignment tail
      (if (i+k<=?last) && candidate_guard fuel recognize f t (RecycleCandidate i n k)
       then Some (RecycleCandidate i n k) else None) target ->
    search_call_prefix sector fuel returned recognize f t req round alignment ((i,last)::tail) None target.

Definition reusable_call_prefix sector fuel returned recognize f t req round alignment pages start target :=
  (0<?alignment) && (start<=?pages)=true /\
  search_call_prefix sector fuel returned recognize f t req round alignment
    (search_positions pages (if Nat.eqb start pages then 0 else start)) None target.

Lemma recognition_call_before_end returned recognize f lo hi t fuel i target :
 recognition_call_prefix returned recognize f lo hi t fuel i target -> target<hi.
Proof. intro P;induction P;assumption. Qed.
Lemma search_call_empty_impossible sector fuel returned recognize f t req round alignment first target :
 ~search_call_prefix sector fuel returned recognize f t req round alignment [] first target.
Proof. intro P;inversion P. Qed.
Lemma search_call_requires_candidate sector fuel returned recognize f t req round alignment positions first target :
 search_call_prefix sector fuel returned recognize f t req round alignment positions first target ->
 exists lo hi,target<hi /\ recognition_call_prefix returned recognize f lo hi t fuel 0 target.
Proof. intro P;induction P;auto. exists i,(i+k);split;[eapply recognition_call_before_end;eauto|assumption]. Qed.

(* Local recognition contract: malformed bounds/magic => no crypto; a crypto
   provider error after an admissible header => panic, not an invalid header.
   shape/verify are format/backend observations, never root-safety promises. *)
Definition header_returned (shape:flash->nat->option nat) (verify:flash->nat->option bool) f i :=
 match shape f i with None=>True | Some _=>verify f i<>None end.
Definition header_reply (shape:flash->nat->option nat) (verify:flash->nat->option bool) f i :=
 match shape f i with
 | None=>None | Some n=>match verify f i with Some true=>Some n | _=>None end end.
Inductive recognition_interruption (shape:flash->nat->option nat) (verify:flash->nat->option bool) (f:flash) (target:nat) : bool -> Prop :=
| header_crypto_fatal n : shape f target=Some n -> verify f target=None ->
    recognition_interruption shape verify f target true
| header_read_reset : recognition_interruption shape verify f target false.
Lemma fatal_header_has_not_returned shape verify f target :
 recognition_interruption shape verify f target true -> ~header_returned shape verify f target.
Proof. intro STOP;inversion STOP;subst;unfold header_returned;rewrite H;congruence. Qed.


Definition memo_extent_bound pages first :=
 match first with None=>True |Some r=>recycle_lo r+erase_pages r<=pages end.
Lemma search_candidates_extent_bound sector fuel recognize f t req round alignment positions first r pages :
 Forall (fun position=>snd position<=pages) positions -> memo_extent_bound pages first ->
 search_candidates sector fuel recognize f t req round alignment positions first=FoundRecyclable r ->
 recycle_lo r+erase_pages r<=pages.
Proof.
 revert first;induction positions as [|[i last] tail IH];intros first POS MEM RUN.
 - cbn in RUN;destruct first;inversion RUN;subst;exact MEM.
 - inversion POS as [|pos rest LIMIT REST];subst;cbn in LIMIT.
   cbn [search_candidates] in RUN.
   destruct (req (256*i));try discriminate;[eapply IH;eauto|].
   destruct (((i+n<=?last) && blankb sector f (block_pages i n)) && vacantb t (block_pages i n));try discriminate.
   destruct first as [saved|];[eapply IH;eauto|].
   destruct (Nat.eqb (i mod alignment) 0);[|eapply IH;eauto;exact I].
   destruct (round n) as [k|];try discriminate.
   destruct ((i+k<=?last) && candidate_guard fuel recognize f t (RecycleCandidate i n k)) eqn:CHECK.
   + eapply IH;[exact REST| |exact RUN].
     apply andb_true_iff in CHECK;destruct CHECK as [BOUND _];apply Nat.leb_le in BOUND.
     cbn;lia.
   + eapply IH;eauto;exact I.
Qed.
Theorem reusable_search_extent_bound sector fuel recognize f t req round alignment pages start r :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 recycle_lo r+erase_pages r<=pages.
Proof.
 unfold reusable_search;destruct ((0<?alignment) && (start<=?pages)) eqn:CHECK;[|discriminate].
 apply andb_true_iff in CHECK;destruct CHECK as [_ START];apply Nat.leb_le in START.
 intro RUN;eapply search_candidates_extent_bound with (first:=None);[|exact I|exact RUN].
 unfold search_positions;apply Forall_app;split;apply Forall_forall;intros pos IN;
 apply in_map_iff in IN;destruct IN as [i [<- IN]];cbn;destruct (start=?pages);lia.
Qed.

(* An erased result is selected by the traversal itself, including after a
   recyclable candidate was memoized. Its length remains address dependent. *)
Lemma search_candidates_erased sector fuel recognize f t req round alignment positions first i n :
 search_candidates sector fuel recognize f t req round alignment positions first=FoundErased i n ->
 exists last, In (i,last) positions /\ req (256*i)=RequiredPages n /\
 i+n<=last /\ blankb sector f (block_pages i n)=true /\ vacantb t (block_pages i n)=true.
Proof.
 revert first;induction positions as [|[p limit] tail IH];intros first RUN;cbn [search_candidates] in RUN.
 - destruct first;discriminate.
 - destruct (req (256*p)) eqn:REQ;try discriminate.
   + destruct (IH first RUN) as [last [IN REST]];exists last;split;[right;exact IN|exact REST].
   + destruct (((p+n0<=?limit) && blankb sector f (block_pages p n0)) && vacantb t (block_pages p n0)) eqn:CHECK.
     * inversion RUN;subst. repeat rewrite andb_true_iff in CHECK.
       destruct CHECK as [[BOUND BLANK] FREE];apply Nat.leb_le in BOUND.
       exists limit;split;[left;reflexivity|]. split;[exact REQ|]. auto.
     * assert (TAIL:exists memo,search_candidates sector fuel recognize f t req round alignment tail memo=FoundErased i n).
       { destruct first as [saved|];[eexists;exact RUN|].
         destruct (Nat.eqb (p mod alignment) 0);[|eexists;exact RUN].
         destruct (round n0);try discriminate;eexists;exact RUN. }
       destruct TAIL as [memo RUN'];destruct (IH memo RUN') as [last [IN REST]].
       exists last;split;[right;exact IN|exact REST].
Qed.
Lemma search_positions_bound pages start i last : start<=pages ->
 In (i,last) (search_positions pages start) -> i<pages /\ last<=pages.
Proof.
 intros START IN;unfold search_positions in IN;apply in_app_iff in IN;
 destruct IN as [IN|IN];apply in_map_iff in IN;destruct IN as [p [EQ IN]];
 inversion EQ;subst;apply in_seq in IN;lia.
Qed.
Theorem reusable_search_erased sector fuel recognize f t req round alignment pages start i n :
 reusable_search sector fuel recognize f t req round alignment pages start=FoundErased i n ->
 req (256*i)=RequiredPages n /\ i<pages /\ i+n<=pages /\
 blankb sector f (block_pages i n)=true /\ vacantb t (block_pages i n)=true.
Proof.
 unfold reusable_search;destruct ((0<?alignment) && (start<=?pages)) eqn:GUARD;[|discriminate].
 intro RUN;apply andb_true_iff in GUARD;destruct GUARD as [_ B];apply Nat.leb_le in B.
 destruct (search_candidates_erased _ _ _ _ _ _ _ _ _ _ _ _ RUN) as [last [IN [REQ [END [BLANK FREE]]]]].
 assert (START:(if start =? pages then 0 else start)<=pages) by (destruct (start =? pages);lia).
 destruct (search_positions_bound _ _ _ _ START IN);repeat split;auto;lia.
Qed.
