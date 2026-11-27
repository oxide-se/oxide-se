From Coq Require Import List Bool Arith NArith Lia.
From OxideSE.Registry Require Import FlashSpec RecycledWriter JournalReachableShape JournalHistory JournalProtocolAuthority JournalIndex JournalScan JournalRecoveryTrace JournalComplement JournalFlashBridge TransactionBoundary IncarnationBoundary PreparedAuthority ScopeOwnership RetentionCoverage PageOwnership.
(* Compatibility re-export: the contracts have one definition, in these modules. *)
From OxideSE.Registry Require Export BossValidationContract.
Import ListNotations.

(* Local software component for format::decode_registry_block_at, AFTER
   read_area/offset_in and the latest_registry equality test.  These preceding
   controls are deliberately not hidden in this provider contract.  None from
   either crypto service is a returned error, not a power cut. *)

Definition check_generation o : list boss_check_event * boss_check_result :=
 if internal_format_ok o then
   match generation_reply o with
   | None => ([CheckInternalFormat;DecryptGeneration],BossCheckFailed GenerationError)
   | Some n => ([CheckInternalFormat;DecryptGeneration;ConvertGeneration],
       if (n <=? 4294967295)%N then BossCheckReady n
       else BossCheckFailed GenerationOverflow)
   end
 else ([CheckInternalFormat],BossCheckFailed InternalFormatRejected).
Definition check_boss_before_append (cached:bool) o :=
 if envelope_ok o then
   if cached then
     let '(events,result):=check_generation o in
     (CheckEnvelope::AuthenticationCacheHit::events,result)
   else match authentication_reply o with
     | None => ([CheckEnvelope;ComputeAuthentication],BossCheckFailed AuthenticationError)
     | Some false => ([CheckEnvelope;ComputeAuthentication],BossCheckFailed AuthenticationRejected)
     | Some true => let '(events,result):=check_generation o in
         (CheckEnvelope::ComputeAuthentication::events,result)
     end
 else ([CheckEnvelope],BossCheckFailed EnvelopeRejected).

(* This is a LOCAL realization obligation for the format/crypto services.
   A logical full decode proves structure and the value on successful crypto
   return.  It does not force a crypto call to succeed.  In particular the
   cached path still decrypts the generation. No journal/history appears here. *)

Theorem checked_boss_from_decoding read observe f id d n cached :
 boss_check_provider read observe -> read f id=Some (d,n) ->
 let result:=snd (check_boss_before_append cached (observe f id)) in
 result=BossCheckReady (counter_value n) \/
 result=BossCheckFailed GenerationError \/
 (cached=false /\ result=BossCheckFailed AuthenticationError).
Proof.
 intros CONTRACT READ;cbn zeta.
 destruct (CONTRACT f id d n READ) as [OUTER [INNER [AUTH VALUE]]].
 assert (GEN:snd (check_generation (observe f id))=BossCheckReady (counter_value n) \/
   snd (check_generation (observe f id))=BossCheckFailed GenerationError).
 { unfold check_generation;rewrite INNER.
   destruct (generation_reply (observe f id)) as [value|] eqn:R;[|auto].
   rewrite (VALUE value eq_refl).
   assert (BOUND:(counter_value n <=? 4294967295)%N=true)
     by (apply N.leb_le;apply counter_u32).
   rewrite BOUND;auto. }
 unfold check_boss_before_append;rewrite OUTER.
 destruct cached.
 - destruct (check_generation (observe f id));cbn in *;tauto.
 - destruct (authentication_reply (observe f id)) as [[|]|] eqn:A;
     try contradiction;try (cbn;tauto).
   destruct (check_generation (observe f id));cbn in *;tauto.
Qed.

Lemma cached_boss_does_not_compute_authentication o :
 ~In ComputeAuthentication (fst (check_boss_before_append true o)).
Proof.
 unfold check_boss_before_append,check_generation.
 destruct (envelope_ok o), (internal_format_ok o), (generation_reply o);
   cbn;intuition discriminate.
Qed.

Lemma cached_generation_error_is_possible :
 snd (check_boss_before_append true (BossCheckObservations true None true None))=
 BossCheckFailed GenerationError.
Proof. reflexivity. Qed.

(* A reset can cut any prefix of this read-only component. No normal return
   is fabricated from that prefix; the caller uses A11's reset transition. *)
Definition boss_check_cut cached o prefix :=
 exists suffix,prefix++suffix=fst (check_boss_before_append cached o).


(* Production Cortex-M mapping: checked usize multiplication, then the exact
   Address::offset_in(...,32) controls. Inputs are configuration, not a claim
   that a particular candidate passed them. *)
Definition read_area_32 (pages:nat) : option N :=
 let len:=(N.of_nat pages*256)%N in
 if (len=?0)%N || (4294967295 <? len)%N then None else Some len.
Definition offset_in_32 (base raw len:N) : option N :=
 if (raw <? base)%N then None else
 let off:=(raw-base)%N in
 if (4294967295 <? off+32)%N || (len <? off+32)%N ||
    (4294967296 <? base+len)%N then None else Some off.
Inductive preappend_gate_result :=
 | AreaUnavailable | AddressOutside | AlreadyLatest | EnterBossCheck (offset:N).
Definition preappend_gate base pages raw (latest:option nat) :=
 match read_area_32 pages with
 | None=>AreaUnavailable
 | Some len=>match offset_in_32 base raw len with
   | None=>AddressOutside
   | Some off=>if match latest with None=>false |Some old=>(off=?N.of_nat old)%N end
     then AlreadyLatest else EnterBossCheck off end end.
Definition mapped_pages pages := 0<pages /\ pages<=1024.
Lemma mapped_area_available pages : mapped_pages pages ->
 read_area_32 pages=Some (N.of_nat pages*256)%N.
Proof.
 intros [POS TOP];unfold read_area_32.
 assert (P:(0<N.of_nat pages<=1024)%N) by lia.
 assert (NZ:(N.of_nat pages*256=?0)%N=false) by (apply N.eqb_neq;lia).
 assert (MAX:(4294967295 <? N.of_nat pages*256)%N=false) by (apply N.ltb_ge;lia).
 rewrite NZ,MAX;reflexivity.
Qed.
Lemma admitted_offset_in_32 base pages id :
 mapped_registry_base base -> mapped_pages pages -> id+32<=pages*256 ->
 offset_in_32 base (base+N.of_nat id) (N.of_nat pages*256)=Some (N.of_nat id).
Proof.
 intros [BASE LIMIT] [POS TOP] BOUND.
 assert (P:(N.of_nat pages<=1024)%N) by lia.
 assert (B:(N.of_nat id+32<=N.of_nat pages*256)%N).
 { change (N.of_nat id+N.of_nat 32<=N.of_nat pages*N.of_nat 256)%N.
   rewrite <-Nat2N.inj_mul,<-Nat2N.inj_add;lia. }
 unfold offset_in_32.
 assert (LOW:(base+N.of_nat id <? base)%N=false) by (apply N.ltb_ge;lia).
 rewrite LOW;replace (base+N.of_nat id-base)%N with (N.of_nat id) by lia.
 assert (W:(4294967295 <? N.of_nat id+32)%N=false) by (apply N.ltb_ge;lia).
 assert (END:(N.of_nat pages*256 <? N.of_nat id+32)%N=false) by (apply N.ltb_ge;lia).
 assert (ABS:(4294967296 <? base+N.of_nat pages*256)%N=false) by (apply N.ltb_ge;lia).
 rewrite W,END,ABS;reflexivity.
Qed.
Theorem prepared_preappend_gate base pages id old :
 mapped_registry_base base -> mapped_pages pages -> id+32<=pages*256 -> id<>old ->
 preappend_gate base pages (base+N.of_nat id) (Some old)=EnterBossCheck (N.of_nat id).
Proof.
 intros BASE PAGES BOUND DISTINCT;unfold preappend_gate.
 rewrite (mapped_area_available pages PAGES),(admitted_offset_in_32 base pages id BASE PAGES BOUND).
 assert (NE:(N.of_nat id=?N.of_nat old)%N=false) by (apply N.eqb_neq;intro EQ;apply DISTINCT;lia).
 rewrite NE;reflexivity.
Qed.

Definition xip_authenticated base pages id (header_pointer:N) (t:page_table) :=
 (id mod 256 =? 0) && (id/256 <? pages) &&
 ((base+N.of_nat id <? 4294967296)%N) &&
 ((base+N.of_nat id=?header_pointer)%N) && validated (t (id/256)).
Lemma remembered_installed_cache_hit pages r s p lifetime next base :
 mapped_registry_base base -> mapped_pages pages ->
 pending_preparation s=Some p -> prep_range p=r ->
 offset r mod 256=0 -> 0<span r -> offset r/256<pages ->
 xip_authenticated base pages (offset r) (base+N.of_nat (offset r))
   (protection_table (install_candidate_observed (image_generation_set next
     (remember_recovered_boss pages r (snapshot_rehome lifetime s)))))=true.
Proof.
 intros CONFIG [PAGE_POS PAGE_TOP] P RANGE ALIGN NONEMPTY INSIDE.
 assert (INDEX:offset r<pages*256).
 { pose proof (Nat.div_mod (offset r) 256 ltac:(lia)) as EQ.
   pose proof (Nat.mod_upper_bound (offset r) 256 ltac:(lia)) as MOD;nia. }
 assert (ABS:(base+N.of_nat (offset r) <? 4294967296)%N=true).
 { destruct CONFIG as [BASE TOP];apply N.ltb_lt.
   assert (BOUND:(N.of_nat (offset r)<262144)%N).
   { assert (SMALL:offset r<1024*256) by nia.
     change (N.of_nat (offset r)<N.of_nat (1024*256))%N;lia. }
   lia. }
 assert (TOUCH:touches 256 r (offset r/256)=true).
 { apply byte_page_touched;[lia|unfold contains;lia]. }
 assert (LT:(offset r/256 <? pages)=true) by (apply Nat.ltb_lt;exact INSIDE).
 unfold xip_authenticated;rewrite ALIGN,LT,ABS,N.eqb_refl;cbn [andb].
 unfold install_candidate_observed,install_candidate,image_generation_set,image_generation_observe,
   remember_recovered_boss,update_validation,snapshot_rehome.
 rewrite P.
 cbv beta iota zeta delta [Build_protection_state ProtectionState change_preparation pending_preparation protection_table
   protection_image_generation protection_bits protection_dirty protection_frozen
   image_generation_observe data_next replace_current_dependencies set_phase
   ScopeOwnership.rehome_extent].
 rewrite RANGE.
 rewrite TOUCH;cbn [validated owner].
 rewrite ALIGN,LT;repeat rewrite Nat.eqb_refl;rewrite !Bool.andb_true_l;apply Bool.orb_true_r.
Qed.

(* The append call receives the same object slice as publication. This equality
   is a configuration/argument correspondence, not a journal safety contract. *)
Definition journal_object_mapping (data_len:N) pages := data_len=N.of_nat (pages*256).

Lemma reserved_boss_after_marker marker s p :
 data_invariant s -> In marker (protection_base s) -> marker_header_covered marker ->
 pending_preparation s=Some p -> 0<span (prep_range p) -> offset (prep_range p) mod 256=0 ->
 256<=offset (prep_range p).
Proof.
 intros INV BASE HEADER TOKEN POS ALIGN.
 assert (NZ:offset (prep_range p)<>0).
 { intro ZERO.
   eapply (reserved_address_not_live s p marker 0 INV TOKEN).
   - apply base_marker_protected_roots;exact BASE.
   - unfold contains;rewrite ZERO;lia.
   - apply HEADER;lia. }
 destruct (Nat.lt_ge_cases (offset (prep_range p)) 256);[|assumption].
 rewrite Nat.mod_small in ALIGN by assumption;contradiction.
Qed.

Lemma acquired_validated_candidate data_len pages r valid :
 mapped_pages pages -> journal_object_mapping data_len pages ->
 256<=offset r -> 0<span r -> offset r+span r<=pages*256 -> offset r mod 256=0 ->
 valid (N.of_nat (offset r))=true ->
 candidate_valid 256 data_len valid (N.of_nat (offset r)).
Proof.
 intros [POS TOP] MAPPING LOW LEN BOUND ALIGN VALID.
 assert (SMALL:offset r<1024*256) by nia.
 unfold candidate_valid,u32;rewrite MAPPING.
 split.
 - change (N.of_nat (offset r)<4294967296)%N.
   assert (B:(N.of_nat (offset r)<N.of_nat (1024*256))%N) by lia;lia.
 - split.
   + change (N.of_nat 256<=N.of_nat (offset r)<N.of_nat (pages*256))%N;lia.
   + split;[|exact VALID].
     change (N.of_nat (offset r) mod N.of_nat 256=N.of_nat 0)%N.
     rewrite <-Nat2N.inj_mod,ALIGN;reflexivity.
Qed.

(* Deterministic scan dispatch of the existing journal. No slot or rotation is
   picked by a caller and no command success is asserted here. *)
Definition validated_append_entry sector data_len valid f id :=
 match first_empty_slot (sector_bytes f 0 sector) with
 | Some slot=>Some (Writing f slot id)
 | None=>match latest_in_model valid data_len 256 (sector_bytes f 0 sector) with
   | Some (slot,old)=>Some (Running (8*slot) old id (State RotCopy f))
   | None=>None end end.
Lemma validated_append_entry_step g sector data_len valid f h a id old :
 logged_invariant sector 256 data_len valid (Logged (Ready f) h a) ->
 hd_error h=Some old -> candidate_valid 256 data_len valid id ->
 exists next,validated_append_entry sector data_len valid f id=Some next /\
 logged_step g sector 256 data_len valid (Logged (Ready f) h a) (Logged next h a).
Proof.
 intros [INV [HIST ACK]] HEAD VALID;unfold validated_append_entry.
 destruct (first_empty_slot (sector_bytes f 0 sector)) as [slot|] eqn:SLOT.
 - exists (Writing f slot id);split;[reflexivity|].
   apply record_step;apply begin_append;assumption.
 - change (observed sector 256 data_len valid f=hd_error h) in HIST.
   unfold observed in HIST;rewrite HEAD in HIST.
   change (option_map snd (latest_in_model valid data_len 256 (sector_bytes f 0 sector))=Some old) in HIST.
   destruct (latest_in_model valid data_len 256 (sector_bytes f 0 sector)) as [[slot previous]|] eqn:LATEST;
     cbn in HIST;try discriminate.
   exists (Running (8*slot) previous id (State RotCopy f));split;[reflexivity|].
   apply record_step;apply begin_rotation;[exact VALID|exact SLOT|exact LATEST].
Qed.
