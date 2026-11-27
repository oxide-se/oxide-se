From Coq Require Import NArith Bool Lia List.
Import ListNotations.
Local Open Scope N_scope.

(* The two words of one physical eight-byte slot. [N.lnot a 32] is
   exactly the 32-bit complement used by Rust's !u32. *)
Definition u32 (a : N) : Prop := (a < 2 ^ 32)%N.
Definition code_words (a : N) : N * N := (a, N.lnot a 32).
Definition word_subset (a b : N) : Prop := N.land a b = a.

Definition code_subset (a b : N) : Prop :=
  word_subset a b /\ word_subset (N.lnot a 32) (N.lnot b 32).

Lemma u32_high_bits_zero a n :
  u32 a -> (32 <= n)%N -> N.testbit a n = false.
Proof.
  intros Ha Hn. unfold u32 in Ha.
  rewrite <- (N.mod_small a (2 ^ 32)) by exact Ha.
  apply N.mod_pow2_bits_high. exact Hn.
Qed.

Theorem distinct_codes_incomparable a b :
  u32 a -> u32 b -> code_subset a b -> a = b.
Proof.
  intros Ha Hb [Hfirst Hsecond].
  apply N.bits_inj. intros n.
  destruct (N.lt_ge_cases n 32) as [Hlow|Hhigh].
  - pose proof (f_equal (fun w => N.testbit w n) Hfirst) as P.
    pose proof (f_equal (fun w => N.testbit w n) Hsecond) as Q.
    cbn beta in P, Q.
    rewrite N.land_spec in P, Q.
    rewrite !N.lnot_spec_low in Q by exact Hlow.
    destruct (N.testbit a n), (N.testbit b n); simpl in *;
      congruence.
  - rewrite (u32_high_bits_zero _ _ Ha Hhigh).
    rewrite (u32_high_bits_zero _ _ Hb Hhigh). reflexivity.
Qed.

Corollary distinct_codes_neither_direction a b :
  u32 a -> u32 b -> a <> b ->
  ~ code_subset a b /\ ~ code_subset b a.
Proof.
  intros Ha Hb Hneq. split; intro H.
  - apply Hneq. exact (distinct_codes_incomparable _ _ Ha Hb H).
  - apply Hneq. symmetry. exact (distinct_codes_incomparable _ _ Hb Ha H).
Qed.

(* Program from an already valid code: new bits are a subset of old bits.
   Erase: old bits are a subset of new bits. Both preserve the decoded
   address whenever the reached pair is itself a valid code. *)
Theorem program_cannot_retarget a b :
  u32 a -> u32 b -> code_subset b a -> a = b.
Proof. intros Ha Hb H. symmetry.
  exact (distinct_codes_incomparable _ _ Hb Ha H).
Qed.
Theorem erase_cannot_retarget a b :
  u32 a -> u32 b -> code_subset a b -> a = b.
Proof. exact (distinct_codes_incomparable a b). Qed.

Definition erased_words : N * N := (N.ones 32, N.ones 32).
Definition valid_words (p : N * N) : Prop :=
  u32 (fst p) /\ snd p = N.lnot (fst p) 32.

Lemma erased_words_invalid : ~ valid_words erased_words.
Proof.
  intros [_ H]. unfold erased_words in H. simpl in H.
  discriminate H.
Qed.

(* A torn program of an erased slot remains a superset of its target code.
   A subsequent partial erase also only adds bits. *)
Theorem torn_program_then_erase_cannot_retarget a p q b :
  u32 a -> u32 b ->
  word_subset a (fst p) ->
  word_subset (N.lnot a 32) (snd p) ->
  word_subset (fst p) (fst q) ->
  word_subset (snd p) (snd q) ->
  q = code_words b -> a = b.
Proof.
  intros Ha Hb Hpa Hpc Hqp Hqc Hq. subst q.
  unfold word_subset in *; cbn in *.
  apply (distinct_codes_incomparable _ _ Ha Hb). split.
  - transitivity (N.land a (fst p)).
    + rewrite <- Hqp. rewrite N.land_assoc. rewrite Hpa. reflexivity.
    + exact Hpa.
  - transitivity (N.land (N.lnot a 32) (snd p)).
    + rewrite <- Hqc. rewrite N.land_assoc. rewrite Hpc. reflexivity.
    + exact Hpc.
Qed.

(* The concrete byte order, without yet interpreting a byte slice as an
   authenticated or published address. *)
Definition le32 (a : N) : list N :=
  [a mod 256; (a / 256) mod 256;
   (a / 256 / 256) mod 256;
   (a / 256 / 256 / 256) mod 256].
Definition code_bytes (a : N) : list N := le32 a ++ le32 (N.lnot a 32).
Definition from_le32 (bytes : list N) : option N :=
  match bytes with
  | [b0;b1;b2;b3] =>
      if (b0 <? 256) && (b1 <? 256) && (b2 <? 256) && (b3 <? 256)
      then Some (b0 + 256*b1 + 65536*b2 + 16777216*b3)%N else None
  | _ => None
  end.

Lemma le32_roundtrip a : u32 a -> from_le32 (le32 a) = Some a.
Proof.
  intro Ha. unfold from_le32, le32.
  set (q1 := a / 256).
  set (q2 := q1 / 256).
  set (q3 := q2 / 256).
  set (q4 := q3 / 256).
  assert (B0 : (a mod 256 <? 256) = true)
    by (apply N.ltb_lt, N.mod_lt; lia).
  assert (B1 : (q1 mod 256 <? 256) = true)
    by (apply N.ltb_lt, N.mod_lt; lia).
  assert (B2 : (q2 mod 256 <? 256) = true)
    by (apply N.ltb_lt, N.mod_lt; lia).
  assert (B3 : (q3 mod 256 <? 256) = true)
    by (apply N.ltb_lt, N.mod_lt; lia).
  rewrite B0, B1, B2, B3.
  pose proof (N.div_mod a 256 ltac:(lia)) as D0.
  pose proof (N.div_mod q1 256 ltac:(lia)) as D1.
  pose proof (N.div_mod q2 256 ltac:(lia)) as D2.
  pose proof (N.div_mod q3 256 ltac:(lia)) as D3.
  cbn [andb].
  fold q1 in D0. fold q2 in D1. fold q3 in D2.
  unfold u32 in Ha. change (a < 4294967296) in Ha.
  assert (Hq1 : q1 < 16777216).
  { unfold q1. apply N.Div0.div_lt_upper_bound; lia. }
  assert (Hq2 : q2 < 65536).
  { unfold q2. apply N.Div0.div_lt_upper_bound; lia. }
  assert (Hq3 : q3 < 256).
  { unfold q3. apply N.Div0.div_lt_upper_bound; lia. }
  rewrite (N.mod_small q3 256 Hq3).
  f_equal. nia.
Qed.

Lemma le32_pack b0 b1 b2 b3 :
  (b0 < 256)%N -> (b1 < 256)%N ->
  (b2 < 256)%N -> (b3 < 256)%N ->
  le32 (b0 + 256*b1 + 65536*b2 + 16777216*b3) =
    [b0;b1;b2;b3].
Proof.
  intros H0 H1 H2 H3.
  set (q1 := b1 + 256 * (b2 + 256 * b3)).
  set (q2 := b2 + 256 * b3).
  set (a := b0 + 256*b1 + 65536*b2 + 16777216*b3).
  assert (D0 : a = 256*q1 + b0) by (unfold a, q1; nia).
  assert (D1 : q1 = 256*q2 + b1) by (unfold q1, q2; nia).
  assert (D2 : q2 = 256*b3 + b2) by (unfold q2; nia).
  assert (R0 : a mod 256 = b0).
  { symmetry. apply N.mod_unique with (q:=q1); assumption. }
  assert (Q0 : a / 256 = q1).
  { symmetry. apply N.div_unique with (r:=b0); assumption. }
  assert (R1 : q1 mod 256 = b1).
  { symmetry. apply N.mod_unique with (q:=q2); assumption. }
  assert (Q1 : q1 / 256 = q2).
  { symmetry. apply N.div_unique with (r:=b1); assumption. }
  assert (R2 : q2 mod 256 = b2).
  { symmetry. apply N.mod_unique with (q:=b3); assumption. }
  assert (Q2 : q2 / 256 = b3).
  { symmetry. apply N.div_unique with (r:=b2); assumption. }
  unfold le32. fold a. rewrite R0, Q0, R1, Q1, R2, Q2.
  rewrite (N.mod_small b3 256 H3). reflexivity.
Qed.

Lemma from_le32_sound bytes a :
  from_le32 bytes = Some a -> u32 a /\ le32 a = bytes.
Proof.
  destruct bytes as [|b0 [|b1 [|b2 [|b3 [|extra rest]]]]];
    unfold from_le32; try discriminate.
  destruct ((b0 <? 256) && (b1 <? 256) &&
            (b2 <? 256) && (b3 <? 256)) eqn:Hvalid;
    try discriminate.
  intro H. inversion H; subst a.
  repeat rewrite Bool.andb_true_iff in Hvalid.
  destruct Hvalid as [[[H0 H1] H2] H3].
  apply N.ltb_lt in H0. apply N.ltb_lt in H1.
  apply N.ltb_lt in H2. apply N.ltb_lt in H3.
  split.
  - unfold u32. change
      (b0 + 256*b1 + 65536*b2 + 16777216*b3 < 4294967296)%N.
    nia.
  - change (le32 (b0 + 256*b1 + 65536*b2 + 16777216*b3) =
            [b0;b1;b2;b3]).
    apply le32_pack; assumption.
Qed.

Lemma le32_byte_testbit a i j :
  (i < 4)%N -> (j < 8)%N ->
  N.testbit (nth (N.to_nat i) (le32 a) 0) j =
  N.testbit a (8*i+j).
Proof.
  intros Hi Hj.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%N as Cases by lia.
  destruct Cases as [E|[E|[E|E]]]; subst i;
    unfold le32; cbn [N.to_nat Pos.to_nat nth];
    change (256)%N with (2 ^ 8)%N.
  - rewrite N.mod_pow2_bits_low by exact Hj. reflexivity.
  - replace (Pos.to_nat 1) with 1%nat by reflexivity.
    cbn [nth].
    rewrite N.mod_pow2_bits_low by exact Hj.
    rewrite N.div_pow2_bits. f_equal; lia.
  - replace (Pos.to_nat 2) with 2%nat by reflexivity.
    cbn [nth]. rewrite N.mod_pow2_bits_low by exact Hj.
    repeat rewrite N.div_pow2_bits. f_equal; lia.
  - replace (Pos.to_nat 3) with 3%nat by reflexivity.
    cbn [nth]. rewrite N.mod_pow2_bits_low by exact Hj.
    repeat rewrite N.div_pow2_bits. f_equal; lia.
Qed.

Definition le32_byte_subset (a b : N) : Prop :=
  forall i, (i < 4)%N ->
    word_subset (nth (N.to_nat i) (le32 a) 0)
                (nth (N.to_nat i) (le32 b) 0).

Lemma le32_byte_subset_implies_word_subset a b :
  u32 a -> u32 b ->
  le32_byte_subset a b -> word_subset a b.
Proof.
  intros Ha Hb Hbytes. unfold word_subset.
  apply N.bits_inj. intros n. rewrite N.land_spec.
  destruct (N.lt_ge_cases n 32) as [Hlow|Hhigh].
  - set (i := n / 8). set (j := n mod 8).
    assert (Hi : (i < 4)%N).
    { unfold i. apply N.Div0.div_lt_upper_bound. lia. }
    assert (Hj : (j < 8)%N).
    { unfold j. apply N.mod_lt. lia. }
    assert (Hn : n = 8*i+j).
    { unfold i, j. pose proof (N.div_mod n 8 ltac:(lia)). lia. }
    pose proof (Hbytes i Hi) as Hbyte.
    unfold word_subset in Hbyte.
    pose proof (f_equal (fun w => N.testbit w j) Hbyte) as Hbit.
    cbn beta in Hbit. rewrite N.land_spec in Hbit.
    rewrite (le32_byte_testbit a i j Hi Hj) in Hbit.
    rewrite (le32_byte_testbit b i j Hi Hj) in Hbit.
    rewrite Hn. exact Hbit.
  - rewrite (u32_high_bits_zero _ _ Ha Hhigh).
    rewrite (u32_high_bits_zero _ _ Hb Hhigh). reflexivity.
Qed.

Lemma u32_complement a : u32 a -> u32 (N.lnot a 32).
Proof.
  intro Ha.
  assert (Hlog : (N.log2 a < 32)%N).
  { destruct (N.eq_dec a 0) as [Hz|Hz].
    - subst. reflexivity.
    - apply N.log2_lt_pow2; [lia|exact Ha]. }
  rewrite N.lnot_sub_low by exact Hlog.
  unfold u32 in *. rewrite N.ones_equiv. lia.
Qed.

Definition slot_byte_subset (old new : list N) : Prop :=
  forall i, (i < 8)%N ->
    word_subset (nth (N.to_nat i) old 0)
                (nth (N.to_nat i) new 0).

Lemma code_bytes_valid a : Forall (fun b => (b < 256)%N) (code_bytes a).
Proof.
  unfold code_bytes, le32. repeat constructor; apply N.mod_lt; lia.
Qed.

Lemma erased_slot_above_code a :
  slot_byte_subset (code_bytes a) (repeat 255%N 8).
Proof.
  intros i Hi. unfold word_subset.
  rewrite (nth_indep (repeat 255%N 8) 0%N 255%N)
    by (rewrite repeat_length; lia).
  rewrite nth_repeat.
  change 255%N with (N.ones 8).
  rewrite N.land_ones.
  apply N.mod_small.
  apply (proj1 (Forall_nth (fun b => (b < 256)%N) (code_bytes a))
    (code_bytes_valid a) (N.to_nat i) 0%N).
  unfold code_bytes, le32. simpl. lia.
Qed.

Lemma byte_subset_of_codes_implies_word_subset a b :
  u32 a -> u32 b ->
  slot_byte_subset (code_bytes a) (code_bytes b) ->
  code_subset a b.
Proof.
  intros Ha Hb Hbytes. split.
  - apply le32_byte_subset_implies_word_subset; try assumption.
    intros i Hi. specialize (Hbytes i ltac:(lia)).
    unfold code_bytes in Hbytes.
    rewrite !app_nth1 in Hbytes.
    + exact Hbytes.
    + unfold le32. simpl. lia.
    + unfold le32. simpl. lia.
  - apply le32_byte_subset_implies_word_subset.
    + apply u32_complement; exact Ha.
    + apply u32_complement; exact Hb.
    + intros i Hi. specialize (Hbytes (i+4) ltac:(lia)).
      unfold code_bytes in Hbytes.
      rewrite !app_nth2 in Hbytes.
      * replace (N.to_nat (i+4) - length (le32 a))%nat
          with (N.to_nat i) in Hbytes
          by (rewrite N2Nat.inj_add; unfold le32; simpl; lia).
        replace (N.to_nat (i+4) - length (le32 b))%nat
          with (N.to_nat i) in Hbytes
          by (rewrite N2Nat.inj_add; unfold le32; simpl; lia).
        exact Hbytes.
      * rewrite N2Nat.inj_add. unfold le32; simpl. lia.
      * rewrite N2Nat.inj_add. unfold le32; simpl. lia.
Qed.

Theorem distinct_byte_codes_incomparable a b :
  u32 a -> u32 b ->
  slot_byte_subset (code_bytes a) (code_bytes b) -> a = b.
Proof.
  intros Ha Hb H.
  apply (distinct_codes_incomparable a b Ha Hb).
  exact (byte_subset_of_codes_implies_word_subset a b Ha Hb H).
Qed.

Lemma word_subset_trans x y z :
  word_subset x y -> word_subset y z -> word_subset x z.
Proof.
  unfold word_subset. intros Hxy Hyz.
  transitivity (N.land x y).
  - rewrite <- Hyz. rewrite N.land_assoc. rewrite Hxy. reflexivity.
  - exact Hxy.
Qed.

Lemma slot_byte_subset_trans x y z :
  slot_byte_subset x y -> slot_byte_subset y z -> slot_byte_subset x z.
Proof.
  intros Hxy Hyz i Hi.
  eapply word_subset_trans; [apply Hxy|apply Hyz]; exact Hi.
Qed.

Theorem complete_byte_program_cannot_retarget a b :
  u32 a -> u32 b ->
  slot_byte_subset (code_bytes b) (code_bytes a) -> a = b.
Proof.
  intros Ha Hb H. symmetry.
  exact (distinct_byte_codes_incomparable b a Hb Ha H).
Qed.

Theorem complete_byte_erase_cannot_retarget a b :
  u32 a -> u32 b ->
  slot_byte_subset (code_bytes a) (code_bytes b) -> a = b.
Proof. exact (distinct_byte_codes_incomparable a b). Qed.

Definition decode_slot (bytes : list N) (data_len page : N) : option N :=
  if Nat.eqb (length bytes) 8 then
      match from_le32 (firstn 4 bytes), from_le32 (skipn 4 bytes) with
      | Some offset, Some complement =>
          if N.leb page offset && N.ltb offset data_len &&
             N.eqb (offset mod page) 0 &&
             N.eqb complement (N.lnot offset 32)
          then Some offset else None
      | _, _ => None
      end
  else None.

Theorem decode_code_bytes a data_len page :
  u32 a -> (page <= a < data_len)%N ->
  (a mod page = 0)%N ->
  decode_slot (code_bytes a) data_len page = Some a.
Proof.
  intros Ha [Hmin Hmax] Halign.
  unfold decode_slot, code_bytes.
  rewrite length_app. cbn [length le32 Nat.eqb].
  rewrite firstn_app, skipn_app.
  cbn [length le32 Nat.sub firstn skipn List.app].
  cbn [Nat.eqb]. fold (le32 a).
  rewrite (le32_roundtrip a Ha).
  rewrite (le32_roundtrip (N.lnot a 32) (u32_complement a Ha)).
  apply N.leb_le in Hmin. apply N.ltb_lt in Hmax.
  rewrite Hmin, Hmax, Halign.
  replace (Nat.eqb (4 + 4) 8) with true by reflexivity.
  repeat rewrite N.eqb_refl. reflexivity.
Qed.

Theorem decode_slot_sound bytes data_len page a :
  decode_slot bytes data_len page = Some a ->
  u32 a /\ (page <= a < data_len)%N /\
  (a mod page = 0)%N /\ code_bytes a = bytes.
Proof.
  intro H. unfold decode_slot in H.
  destruct (Nat.eqb (length bytes) 8) eqn:Hlen; try discriminate.
  destruct (from_le32 (firstn 4 bytes)) as [offset|] eqn:Hoff;
    try discriminate.
  destruct (from_le32 (skipn 4 bytes)) as [complement|] eqn:Hcom;
    try discriminate.
  destruct ((page <=? offset) &&
            (offset <? data_len) && (offset mod page =? 0) &&
            (complement =? N.lnot offset 32)) eqn:Hchecks;
    try discriminate.
  inversion H; subst.
  pose proof (from_le32_sound _ _ Hoff) as [Hu Hprefix].
  pose proof (from_le32_sound _ _ Hcom) as [_ Hsuffix].
  repeat rewrite Bool.andb_true_iff in Hchecks.
  destruct Hchecks as [[[Hmin Hmax] Halign] Hsame].
  apply N.leb_le in Hmin. apply N.ltb_lt in Hmax.
  apply N.eqb_eq in Halign. apply N.eqb_eq in Hsame.
  repeat split; try assumption.
  unfold code_bytes. rewrite <- Hsame.
  rewrite Hprefix, Hsuffix. apply firstn_skipn.
Qed.

(* [journal_area] rejects zero sector and fewer than three sectors;
   [layout] rejects pages shorter than one entry and nonintegral sectors.
   Arithmetic-overflow checks on Rust usize remain a correspondence duty. *)
Definition journal_layout_accepts (total page sector : N) : bool :=
  (0 <? sector) && (8 <=? page) && (sector mod page =? 0) &&
  (3*sector <=? total).

Definition decode_journal_entry (bytes : list N) (total page sector : N)
    : option N :=
  if journal_layout_accepts total page sector
  then decode_slot bytes (total - 2*sector) page
  else None.

Theorem decode_journal_entry_sound bytes total page sector a :
  decode_journal_entry bytes total page sector = Some a ->
  journal_layout_accepts total page sector = true /\
  u32 a /\ (page <= a < total - 2*sector)%N /\
  (a mod page = 0)%N /\ code_bytes a = bytes.
Proof.
  unfold decode_journal_entry.
  destruct (journal_layout_accepts total page sector) eqn:Hlayout;
    try discriminate.
  intro H. split; [reflexivity|].
  exact (decode_slot_sound _ _ _ _ H).
Qed.

Theorem decode_journal_entry_code a total page sector :
  journal_layout_accepts total page sector = true ->
  u32 a -> (page <= a < total - 2*sector)%N ->
  (a mod page = 0)%N ->
  decode_journal_entry (code_bytes a) total page sector = Some a.
Proof.
  intros Hlayout Ha Hbounds Halign.
  unfold decode_journal_entry. rewrite Hlayout.
  apply decode_code_bytes; assumption.
Qed.

Theorem torn_byte_program_then_erase_cannot_retarget a torn reached
    data_len page b :
  u32 a ->
  slot_byte_subset (code_bytes a) torn ->
  slot_byte_subset torn reached ->
  decode_slot reached data_len page = Some b -> b = a.
Proof.
  intros Ha Hprogram Herase Hdecode.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  subst reached. symmetry.
  apply (distinct_byte_codes_incomparable a b Ha Hb).
  eapply slot_byte_subset_trans; eassumption.
Qed.

Definition validated_slot (boss_ok : N -> bool) (bytes : list N)
    (data_len page : N) : option N :=
  match decode_slot bytes data_len page with
  | Some a => if boss_ok a then Some a else None
  | None => None
  end.

Definition pick_valid_backup_or_primary (boss_ok : N -> bool)
    (backup primary : list N) (data_len page : N) : option N :=
  match validated_slot boss_ok backup data_len page with
  | Some a => Some a
  | None => validated_slot boss_ok primary data_len page
  end.

Theorem validated_backup_only_requested_address
    (boss_ok : N -> bool) a reached data_len page b :
  u32 a -> slot_byte_subset (code_bytes a) reached ->
  validated_slot boss_ok reached data_len page = Some b -> b = a.
Proof.
  intros Ha Hsuperset Hvalid.
  unfold validated_slot in Hvalid.
  destruct (decode_slot reached data_len page) as [found|] eqn:Hdecode;
    try discriminate.
  destruct (boss_ok found) eqn:Hboss; inversion Hvalid; subst b.
  pose proof (decode_slot_sound _ _ _ _ Hdecode)
    as [Hb [_ [_ Hbytes]]].
  subst reached. symmetry.
  apply (distinct_byte_codes_incomparable a found Ha Hb Hsuperset).
Qed.

Theorem rejected_backup_requires_primary_authority
    (boss_ok : N -> bool) a backup primary data_len page :
  u32 a -> (page <= a < data_len)%N -> (a mod page = 0)%N ->
  boss_ok a = true ->
  (backup = code_bytes a \/ primary = code_bytes a) ->
  validated_slot boss_ok backup data_len page = None ->
  primary = code_bytes a.
Proof.
  intros Ha Hrange Halign Hboss [Hbackup|Hprimary] Hnone;
    [|exact Hprimary].
  subst backup. unfold validated_slot in Hnone.
  rewrite (decode_code_bytes a data_len page Ha Hrange Halign),
    Hboss in Hnone. discriminate.
Qed.

Theorem restored_primary_survives_secondary_byte_erase
    (boss_ok : N -> bool) a reached data_len page :
  u32 a -> (page <= a < data_len)%N -> (a mod page = 0)%N ->
  boss_ok a = true ->
  slot_byte_subset (code_bytes a) reached ->
  pick_valid_backup_or_primary boss_ok reached (code_bytes a)
    data_len page = Some a.
Proof.
  intros Ha Hbounds Halign Hboss Herase.
  unfold pick_valid_backup_or_primary, validated_slot.
  destruct (decode_slot reached data_len page) as [b|] eqn:Hbackup.
  - pose proof (decode_slot_sound _ _ _ _ Hbackup)
      as [Hb [_ [_ Hbytes]]].
    subst reached.
    pose proof (complete_byte_erase_cannot_retarget a b Ha Hb Herase)
      as E. subst b. rewrite Hboss. reflexivity.
  - rewrite (decode_code_bytes a data_len page Ha Hbounds Halign).
    rewrite Hboss. reflexivity.
Qed.

Lemma code_bytes_length a : length (code_bytes a) = 8%nat.
Proof. reflexivity. Qed.
Lemma erased_slot_invalid data_len page :
  decode_slot (repeat 255 8%nat) data_len page = None.
Proof.
  unfold decode_slot, from_le32. cbn.
  rewrite andb_false_r. reflexivity.
Qed.

(* A word-level view of the same decoder. Its u32 guard corresponds to the
   four source bytes; the byte-to-word converse is tracked separately. *)
Definition decode_words (p : N * N) (data_len page : N) : option N :=
  let a := fst p in
  if (a <? 2 ^ 32) && (page <=? a) && (a <? data_len) &&
     (a mod page =? 0) && (snd p =? N.lnot a 32)
  then Some a else None.

Lemma decode_words_sound p data_len page b :
  decode_words p data_len page = Some b ->
  b = fst p /\ u32 b /\ snd p = N.lnot b 32 /\
  (page <= b < data_len)%N /\ (b mod page = 0)%N.
Proof.
  intro H. unfold decode_words in H. destruct p as [a c]. cbn in H.
  destruct (a <? 4294967296) eqn:Ha;
  destruct (page <=? a) eqn:Hp;
  destruct (a <? data_len) eqn:Hl;
  destruct (a mod page =? 0) eqn:Hr;
  destruct (c =? N.lnot a 32) eqn:Hc;
  cbn in H; try discriminate.
  inversion H; subst. repeat split; try reflexivity.
  - apply N.ltb_lt; exact Ha.
  - apply N.eqb_eq; exact Hc.
  - apply N.leb_le; exact Hp.
  - apply N.ltb_lt; exact Hl.
  - apply N.eqb_eq; exact Hr.
Qed.

Theorem secondary_erase_cannot_redirect a reached data_len page b :
  u32 a ->
  word_subset a (fst reached) ->
  word_subset (N.lnot a 32) (snd reached) ->
  decode_words reached data_len page = Some b -> b = a.
Proof.
  intros Ha Hfirst Hsecond Hdecode.
  pose proof (decode_words_sound _ _ _ _ Hdecode)
    as [Hb [Hbu [Hcomp [_ _]]]].
  subst b. destruct reached as [r c]. cbn in *.
  subst c.
  symmetry. apply (distinct_codes_incomparable a r Ha Hbu).
  split; assumption.
Qed.

(* With a restored primary A, a partially erased secondary either still
   decodes A or is ignored. This is a local rotation phase, not the complete
   latest/recovery algorithm. *)
Definition pick_backup_or_primary (backup primary : N * N)
    (data_len page : N) : option N :=
  match decode_words backup data_len page with
  | Some a => Some a
  | None => decode_words primary data_len page
  end.

Theorem restored_primary_survives_secondary_erase a reached data_len page :
  u32 a -> (page <= a < data_len)%N -> (a mod page = 0)%N ->
  word_subset a (fst reached) ->
  word_subset (N.lnot a 32) (snd reached) ->
  pick_backup_or_primary reached (code_words a) data_len page = Some a.
Proof.
  intros Ha Hbounds Halign Hfirst Hsecond.
  unfold pick_backup_or_primary.
  destruct (decode_words reached data_len page) as [b|] eqn:Hbackup.
  - rewrite (secondary_erase_cannot_redirect _ _ _ _ _ Ha Hfirst Hsecond Hbackup).
    reflexivity.
  - unfold decode_words, code_words. cbn.
    destruct Hbounds as [Hmin Hmax].
    apply N.ltb_lt in Ha. apply N.leb_le in Hmin.
    apply N.ltb_lt in Hmax.
    change ((a <? 4294967296) = true) in Ha.
    rewrite Ha, Hmin, Hmax, Halign.
    repeat rewrite N.eqb_refl. reflexivity.
Qed.

(* The wider returned-error clause can still destroy availability: clearing
   an unrequested offset bit invalidates A=256 without creating another code. *)
Example extra_zero_can_invalidate_complete_code :
  valid_words (code_words 256) /\
  word_subset 0 256 /\
  ~ valid_words (0, N.lnot 256 32).
Proof. vm_compute. repeat split; try reflexivity.
  intros [_ H]. discriminate H.
Qed.
