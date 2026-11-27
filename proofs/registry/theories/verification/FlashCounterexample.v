From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Types FlashSpec.
Import ListNotations.

(* Historical illustration of the retired, wider returned-error contract.
   This predicate is deliberately separate from active FlashSpec.program_step. *)
Definition old_broad_program_error (g : geometry) (before : flash) a data after :=
  program_request g before a data /\
  frame a (length data) before after /\
  forall i, i < length data -> valid_byte (after (a+i)) /\
    program_bits (before (a+i)) (after (a+i)).

(* A two-byte instance of the page-rewrite pattern used by journal::write_entry. *)
Definition counter_geometry : geometry :=
  {| area_start := 0; area_length := 2; page_size := 2; sector_size := 2 |}.
Definition counter_before : flash :=
  fun p => if Nat.eqb p 0 then 254%N else 255%N.
Definition counter_after : flash :=
  fun p => if Nat.eqb p 0 then 252%N
           else if Nat.eqb p 1 then 254%N else 255%N.
Definition counter_data : payload := [254%N; 254%N].

Lemma counter_request :
  program_request counter_geometry counter_before 0 counter_data.
Proof.
  repeat split; try reflexivity; try lia.
  - constructor; [unfold valid_byte; lia|constructor; [unfold valid_byte; lia|constructor]].
  - intros i b H. destruct i as [|[|i]]; simpl in H.
    + inversion H; subst. unfold program_bits, counter_before; reflexivity.
    + inversion H; subst. unfold program_bits, counter_before; reflexivity.
    + destruct i; discriminate H.
Qed.

Lemma counter_failed_step :
  old_broad_program_error counter_geometry counter_before 0 counter_data
    counter_after.
Proof.
  unfold old_broad_program_error. split; [exact counter_request|]. split.
  - unfold frame. intros p Hp. unfold counter_after, counter_before, counter_data in *.
    simpl in Hp. assert (p <> 0) by lia. assert (p <> 1) by lia.
    apply Nat.eqb_neq in H. apply Nat.eqb_neq in H0.
    rewrite H, H0. reflexivity.
  - intros i Hi. destruct i as [|[|i]]; try lia;
      unfold counter_after, counter_before, valid_byte, program_bits;
      simpl; split; try lia; reflexivity.
Qed.

Theorem verify_failed_can_corrupt_previous_page_contents :
  old_broad_program_error counter_geometry counter_before 0 counter_data
    counter_after /\
  counter_before 0 <> counter_after 0.
Proof.
  split; [exact counter_failed_step|discriminate].
Qed.

Theorem returned_program_error_exceeds_requested_bits :
  old_broad_program_error counter_geometry counter_before 0 counter_data
    counter_after /\
  ~ requested_only counter_after 0 counter_data.
Proof.
  split; [exact counter_failed_step|].
  intro H. specialize (H 0 254%N eq_refl).
  unfold program_bits, counter_after in H. discriminate H.
Qed.

Theorem active_contract_excludes_counterexample :
  ~ program_step counter_geometry counter_before 0 counter_data
      VerifyFailed counter_after.
Proof.
  intro H. pose proof (failed_program_requested_only _ _ _ _ _ H) as Hr.
  exact ((proj2 returned_program_error_exceeds_requested_bits) Hr).
Qed.
