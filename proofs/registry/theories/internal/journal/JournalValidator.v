From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import JournalScan JournalComplement.
Import ListNotations.

(* Per-flash validators may differ on dead BOSS blocks. No second history. *)
Definition raw_slot sector data_len page i := decode_slot (physical_slot sector i) data_len page.
Definition raw_latest_witness sector data_len page count index authority :=
 index<count /\ raw_slot sector data_len page index=Some authority /\
 forall higher, index<higher<count -> raw_slot sector data_len page higher=None.

Theorem raw_latest_validated_selects sector data_len page count index authority validate :
 raw_latest_witness sector data_len page count index authority -> validate authority=true ->
 latest_scan validate data_len page sector count=Some(index,authority).
Proof.
 intros [BOUND [SLOT HIGH]] VALID. apply latest_scan_selects_given; [exact BOUND| |].
 - unfold checked_slot; unfold raw_slot in SLOT; rewrite SLOT, VALID; reflexivity.
 - intros h H. unfold checked_slot; unfold raw_slot in HIGH. rewrite (HIGH h H); reflexivity.
Qed.
Theorem changed_validator_preserves_raw_latest sector data_len page count index authority before after :
 raw_latest_witness sector data_len page count index authority ->
 before authority=true -> after authority=true ->
 latest_scan before data_len page sector count=Some(index,authority) /\
 latest_scan after data_len page sector count=Some(index,authority).
Proof. intros RAW B A; split; apply raw_latest_validated_selects; assumption. Qed.

(* General exact criterion: newly valid lower-priority candidates do not matter.
   Only the winner and failed higher-priority checks have to be transported. *)
Theorem changing_validator_selection sector data_len page count index authority before after :
 latest_scan before data_len page sector count=Some(index,authority) ->
 after authority=true ->
 (forall i id, index<i<count -> raw_slot sector data_len page i=Some id ->
    after id=true -> before id=true) ->
 latest_scan after data_len page sector count=Some(index,authority).
Proof.
 intros OLD VALID HIGH. destruct (latest_scan_sound _ _ _ _ _ _ _ OLD) as [BOUND [SLOT ABOVE]].
 apply latest_scan_selects_given; [exact BOUND| |].
 - unfold checked_slot in *. destruct (decode_slot (physical_slot sector index) data_len page)
     as [id|] eqn:R; try discriminate. destruct (before id); inversion SLOT; subst.
   rewrite VALID; reflexivity.
 - intros i I. specialize (ABOVE i I). unfold checked_slot in *.
   destruct (decode_slot (physical_slot sector i) data_len page) as [id|] eqn:R; [|reflexivity].
   destruct (after id) eqn:A; [|reflexivity].
   specialize (HIGH i id I R A). rewrite HIGH in ABOVE; discriminate.
Qed.

(* This witnesses the missing information, NOT an established Rust execution.
   Slot bytes and the old winner's validity are unchanged, but an unchecked
   higher slot can win when its BOSS becomes valid. *)
Definition validator_gap_slots := code_bytes 256 ++ code_bytes 512.
Example validator_gap_before :
 latest_scan (fun x=>N.eqb x 256) 8192 256 validator_gap_slots 2=Some(0,256%N).
Proof. vm_compute; reflexivity. Qed.
Example validator_gap_after :
 latest_scan (fun _=>true) 8192 256 validator_gap_slots 2=Some(1,512%N).
Proof. vm_compute; reflexivity. Qed.
Example validator_gap_old_preserved : (N.eqb 256 256)=true.
Proof. reflexivity. Qed.

From OxideSE.Registry Require Import FlashSpec JournalIndex JournalWriteEntry JournalAppendSelection.
Lemma all_true_scan_raw sector data_len page count index authority :
 latest_scan (fun _=>true) data_len page sector count=Some(index,authority) ->
 raw_latest_witness sector data_len page count index authority.
Proof.
 intro S. destruct (latest_scan_sound _ _ _ _ _ _ _ S) as [BOUND [SLOT HIGH]].
 split; [exact BOUND|]. split.
 - unfold raw_slot, checked_slot in *.
   destruct (decode_slot (physical_slot sector index) data_len page); inversion SLOT; reflexivity.
 - intros i I. specialize (HIGH i I). unfold raw_slot, checked_slot in *.
   destruct (decode_slot (physical_slot sector i) data_len page); [discriminate|reflexivity].
Qed.

(* A producer, not a new caller assumption: ordinary append establishes the
   missing raw ordering fact independently of every old BOSS validator. *)
Theorem successful_append_produces_raw_winner
 g f f' sector page index aligned within d data_len :
 sector mod 8=0 -> 8<=page -> aligned+within=8*index -> within+8<=page ->
 first_empty_slot (sector_bytes f 0 sector)=Some index ->
 erased_suffix (sector_bytes f 0 sector) ->
 program_step g f aligned (write_entry_page f aligned page within (code_bytes d)) Success f' ->
 u32 d -> (N.of_nat page<=d<data_len)%N -> (d mod N.of_nat page=0)%N ->
 raw_latest_witness (sector_bytes f' 0 sector) data_len (N.of_nat page)
   (length (sector_bytes f' 0 sector)/8) index d.
Proof.
 intros DIV SIZE ADDRESS WITHIN FIRST SHAPE STEP U RANGE ALIGN.
 apply all_true_scan_raw.
 exact (successful_nonrotation_append_selects g f f' sector page index aligned within d data_len
   (fun _=>true) DIV SIZE ADDRESS WITHIN FIRST SHAPE STEP U RANGE ALIGN eq_refl).
Qed.

From OxideSE.Registry Require Import RecyclingSearch Neutralization PreparedAuthority
 CollectionRoots RetentionCoverage PageOwnership JournalHistory PublicationPreparation.
Definition validator_root_local sector view (validate:flash->N->bool) :=
 forall before after id,
 unchanged (root_extents (view (N.to_nat id))) (object_flash sector before) (object_flash sector after) ->
 validate before id=validate after id.

(* Conditional bridge: RAW is a local slot-layout fact. It is NOT added to a
   decoder contract or silently inferred from the old enriched invariant. *)
Theorem searched_neutralization_dynamic_selection g sector fuel recognize magic req round alignment pages start
 f result t live view validate r index old data_len :
 recognizer_local sector recognize -> validator_root_local sector view validate ->
 valid_flash f -> protected (needed 256 live) t ->
 (forall x, In x (root_extents (view (N.to_nat old))) -> In x live) ->
 raw_latest_witness (sector_bytes f 0 sector) data_len 256 (sector/8) index old ->
 validate f old=true ->
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 latest_scan (validate (neutral_flash result)) data_len 256
   (sector_bytes (neutral_flash result) 0 sector) (sector/8)=Some(index,old).
Proof.
 intros LOCAL VLOCAL VALID COVER INCLUDED RAW BOSS SEARCH RUN.
 destruct (search_to_neutralization g sector fuel recognize magic f t req round alignment pages start r result live
  LOCAL VALID COVER SEARCH RUN) as [FREE [V [KEEP FRAME]]].
 assert (ROOT : unchanged (root_extents (view (N.to_nat old)))
  (object_flash sector f) (object_flash sector (neutral_flash result))).
 { intros x pos IN AT; exact (KEEP x pos (INCLUDED x IN) AT). }
 assert (BYTES : sector_bytes (neutral_flash result) 0 sector=sector_bytes f 0 sector).
 { unfold sector_bytes; apply map_ext_in; intros x IN; apply in_seq in IN; apply FRAME; lia. }
 rewrite BYTES. apply raw_latest_validated_selects; [exact RAW|].
 rewrite <- (VLOCAL _ _ _ ROOT); exact BOSS.
Qed.

(* Consumer with a concrete RAW producer: no intermediate raw-layout or
   candidate guard is supplied. The remaining initialization/boot/global
   transport gap is explicitly separate from this append suffix. *)
Theorem successful_append_then_search_neutralization g sector fuel recognize magic req round alignment pages start
 before f result t live view validate r index aligned within old data_len :
 sector mod 8=0 -> aligned+within=8*index -> within+8<=256 ->
 first_empty_slot (sector_bytes before 0 sector)=Some index ->
 erased_suffix (sector_bytes before 0 sector) ->
 program_step g before aligned (write_entry_page before aligned 256 within (code_bytes old)) Success f ->
 u32 old -> (256<=old<data_len)%N -> (old mod 256=0)%N ->
 recognizer_local sector recognize -> validator_root_local sector view validate ->
 valid_flash f -> protected (needed 256 live) t ->
 (forall x, In x (root_extents (view (N.to_nat old))) -> In x live) ->
 validate f old=true ->
 reusable_search sector fuel recognize f t req round alignment pages start=FoundRecyclable r ->
 neutral_run g sector recognize magic (recycle_lo r+erase_pages r) (recycle_lo r) f result ->
 latest_scan (validate (neutral_flash result)) data_len 256
   (sector_bytes (neutral_flash result) 0 sector) (sector/8)=Some(index,old).
Proof.
 intros DIV ADDRESS WITHIN FIRST SHAPE STEP U RANGE ALIGN LOCAL VLOCAL V COVER INC VALID SEARCH RUN.
 pose proof (successful_append_produces_raw_winner g before f sector 256 index aligned within old data_len
  DIV ltac:(lia) ADDRESS WITHIN FIRST SHAPE STEP U RANGE ALIGN) as RAW.
 unfold sector_bytes in RAW at 2; rewrite map_length, seq_length in RAW.
 eapply searched_neutralization_dynamic_selection; eauto.
Qed.
