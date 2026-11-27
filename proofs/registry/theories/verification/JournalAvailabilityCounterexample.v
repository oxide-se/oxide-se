From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Types FlashSpec FlashCounterexample JournalComplement JournalFlashBridge.
Import ListNotations.

(* Historical illustration of the retired broad returned-error relation.
   Neither trace below is allowed by the active oxi-core contract. *)
Definition availability_geometry : geometry :=
  {| area_start := 0; area_length := 4096;
     page_size := 256; sector_size := 4096 |}.
Definition availability_data : payload :=
  code_bytes 256 ++ repeat 255%N 248.
Definition availability_before : flash :=
  fun p => nth p availability_data 255%N.
Definition availability_after : flash :=
  fun p => if Nat.eqb p 1 then 0%N else availability_before p.
Definition availability_append_data : payload :=
  code_bytes 256 ++ code_bytes 512 ++ repeat 255%N 240.

Lemma availability_data_length : length availability_data = 256.
Proof.
  unfold availability_data. rewrite length_app, code_bytes_length,
    repeat_length. reflexivity.
Qed.

Lemma forall2_nth_error_right {A B : Type} (R : A -> B -> Prop)
    (xs : list A) (ys : list B) i y :
  Forall2 R xs ys -> nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  intros H. revert i y.
  induction H; intros [|i] item Hy; simpl in Hy; try discriminate.
  - inversion Hy; subst. exists x. simpl. auto.
  - apply IHForall2 in Hy. exact Hy.
Qed.

Lemma availability_append_length : length availability_append_data = 256.
Proof.
  unfold availability_append_data.
  repeat rewrite length_app. repeat rewrite code_bytes_length.
  rewrite repeat_length. reflexivity.
Qed.
Lemma availability_append_valid : valid_payload availability_append_data.
Proof.
  unfold availability_append_data, valid_payload.
  apply Forall_app. split.
  - vm_compute. repeat constructor; lia.
  - apply Forall_app. split.
    + vm_compute. repeat constructor; lia.
    + apply Forall_forall. intros x Hin.
      apply repeat_spec in Hin. subst. unfold valid_byte; lia.
Qed.
Lemma availability_append_bits :
  Forall2 program_bits availability_data availability_append_data.
Proof.
  unfold availability_data, availability_append_data.
  replace 248%nat with (8+240)%nat by lia.
  rewrite repeat_app. repeat rewrite <- app_assoc.
  apply Forall2_app.
  - vm_compute. repeat constructor; reflexivity.
  - apply Forall2_app.
    + vm_compute. repeat constructor; reflexivity.
    + assert (Hrepeat : forall n,
        Forall2 program_bits (repeat 255%N n) (repeat 255%N n)).
      { intro n. induction n; simpl; constructor;
          [unfold program_bits; reflexivity|exact IHn]. }
      apply Hrepeat.
Qed.

Lemma availability_append_request :
  program_request availability_geometry availability_before 0
    availability_append_data.
Proof.
  unfold program_request. repeat split.
  - unfold availability_geometry; simpl. lia.
  - unfold availability_geometry; simpl. lia.
  - exact availability_append_valid.
  - intros i b Hnth.
    destruct (forall2_nth_error_right _ _ _ _ _
      availability_append_bits Hnth) as [old [Hold Hbits]].
    unfold availability_before.
    replace (0+i)%nat with i by lia.
    rewrite (nth_error_nth availability_data i 255%N Hold).
    exact Hbits.
Qed.
Lemma availability_data_valid : valid_payload availability_data.
Proof.
  unfold availability_data, valid_payload.
  apply Forall_app. split.
  - vm_compute. repeat constructor; lia.
  - apply Forall_forall. intros x Hin.
    apply repeat_spec in Hin. subst. unfold valid_byte; lia.
Qed.

Lemma availability_request :
  program_request availability_geometry availability_before 0
    availability_data.
Proof.
  unfold program_request. repeat split.
  - unfold availability_geometry; simpl. lia.
  - unfold availability_geometry; simpl. lia.
  - exact availability_data_valid.
  - intros i b Hnth. unfold availability_before.
    replace (0+i)%nat with i by lia.
    rewrite (nth_error_nth availability_data i 255%N Hnth).
    unfold program_bits. rewrite N.land_diag. reflexivity.
Qed.

Lemma availability_failed_step :
  old_broad_program_error availability_geometry availability_before 0
    availability_data availability_after.
Proof.
  unfold old_broad_program_error. split; [exact availability_request|]. split.
  - unfold frame. intros p Hp. unfold availability_after.
    rewrite availability_data_length in Hp.
    assert (p <> 1) by lia. apply Nat.eqb_neq in H.
    rewrite H. reflexivity.
  - intros i Hi. replace (0+i)%nat with i by lia.
    unfold availability_after.
    destruct (Nat.eqb i 1) eqn:E.
    + apply Nat.eqb_eq in E. subst i. vm_compute. split; reflexivity.
    + assert (V : valid_byte (availability_before i)).
      { unfold availability_before.
        apply Forall_nth with (l:=availability_data);
          [exact availability_data_valid|].
        rewrite availability_data_length; exact Hi. }
      split; [exact V|]. unfold program_bits.
      rewrite N.land_diag. reflexivity.
Qed.

Theorem returned_error_can_destroy_recoverable_A :
  old_broad_program_error availability_geometry availability_before 0
    availability_data availability_after /\
  decode_slot (flash_slot availability_before 0) (992*256)%N 256%N = Some 256%N /\
  decode_slot (flash_slot availability_after 0) (992*256)%N 256%N = None.
Proof.
  split; [exact availability_failed_step|].
  vm_compute. split; reflexivity.
Qed.

Lemma availability_append_failed_step :
  old_broad_program_error availability_geometry availability_before 0
    availability_append_data availability_after.
Proof.
  unfold old_broad_program_error. split; [exact availability_append_request|]. split.
  - unfold frame. intros p Hp. unfold availability_after.
    rewrite availability_append_length in Hp.
    assert (p <> 1) by lia. apply Nat.eqb_neq in H.
    rewrite H. reflexivity.
  - intros i Hi. replace (0+i)%nat with i by lia.
    unfold availability_after.
    destruct (Nat.eqb i 1) eqn:E.
    + apply Nat.eqb_eq in E. subst i. vm_compute. split; reflexivity.
    + assert (V : valid_byte (availability_before i)).
      { unfold availability_before.
        apply Forall_nth with (l:=availability_data);
          [exact availability_data_valid|].
        rewrite availability_data_length.
        rewrite availability_append_length in Hi.
        exact Hi. }
      split; [exact V|]. unfold program_bits.
      rewrite N.land_diag. reflexivity.
Qed.

Theorem failed_append_can_lose_A_without_writing_C :
  old_broad_program_error availability_geometry availability_before 0
    availability_append_data availability_after /\
  decode_slot (flash_slot availability_after 0) (992*256)%N 256%N = None /\
  decode_slot (flash_slot availability_after 8) (992*256)%N 256%N = None.
Proof.
  split; [exact availability_append_failed_step|].
  vm_compute. split; reflexivity.
Qed.

Theorem active_contract_excludes_failed_append :
  ~ program_step availability_geometry availability_before 0
      availability_append_data VerifyFailed availability_after.
Proof.
  intro H. pose proof (failed_program_requested_only _ _ _ _ _ H) as Hr.
  specialize (Hr 1 1%N eq_refl).
  vm_compute in Hr. discriminate Hr.
Qed.
