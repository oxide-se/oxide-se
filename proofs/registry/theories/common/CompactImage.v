From Coq Require Import List Arith NArith Lia.
From OxideSE.Registry Require Import Types.
Import ListNotations.

(* The in-memory slots are represented here by their logical fields. This is
   a pure serialization fragment, not a proof that flash decodes them safely. *)
Definition image_capacity := 63.
Definition entry_length := 40.
Definition header_length := 32.

Record compact_entry := {
  object_aid : list byte;
  parent_aid : list byte;
  kind_word : list byte;
  absolute_address : list byte
}.
Definition entry_well_formed (e : compact_entry) :=
  length (object_aid e) = 17 /\ length (parent_aid e) = 17 /\
  length (kind_word e) = 2 /\ length (absolute_address e) = 4 /\
  valid_payload (object_aid e ++ parent_aid e ++
                 kind_word e ++ absolute_address e).
Definition encode_entry (e : compact_entry) : list byte :=
  object_aid e ++ parent_aid e ++ kind_word e ++ absolute_address e.
Definition compact_slot := option compact_entry.
Definition encode_slot (s : compact_slot) : list byte :=
  match s with None => repeat 0%N entry_length | Some e => encode_entry e end.
Definition image_well_formed (generation : list byte) (slots : list compact_slot) :=
  length generation = 8 /\ valid_payload generation /\
  length slots <= image_capacity /\
  Forall (fun s => match s with None => True | Some e => entry_well_formed e end) slots.
Definition encode_image (generation : list byte) (slots : list compact_slot) : list byte :=
  generation ++ concat (map encode_slot slots).

Lemma encode_entry_length e : entry_well_formed e -> length (encode_entry e) = entry_length.
Proof.
  intros (A & B & C & D & _). unfold encode_entry, entry_length.
  repeat rewrite length_app. lia.
Qed.
Lemma encode_slot_length s :
  (match s with None => True | Some e => entry_well_formed e end) ->
  length (encode_slot s) = entry_length.
Proof.
  intros H. destruct s as [e|]; simpl in *;
    [apply encode_entry_length; exact H|reflexivity].
Qed.
Lemma encoded_slots_length slots :
  Forall (fun s => match s with None => True | Some e => entry_well_formed e end) slots ->
  length (concat (map encode_slot slots)) = entry_length * length slots.
Proof.
  induction 1 as [|x xs Hx Hxs IH]; simpl; [reflexivity|].
  rewrite length_app, encode_slot_length by exact Hx.
  rewrite IH. unfold entry_length. lia.
Qed.
Theorem compact_image_length generation slots :
  image_well_formed generation slots ->
  length (encode_image generation slots) = 8 + 40 * length slots /\
  length (encode_image generation slots) <= 2528.
Proof.
  intros (G & _ & B & W). unfold encode_image.
  repeat rewrite length_app. repeat rewrite G.
  repeat rewrite encoded_slots_length by exact W.
  unfold entry_length, image_capacity in *. split; [reflexivity|].
  change (8 + 40 * length slots <= 8 + 40 * 63).
  apply Nat.add_le_mono; [lia|].
  apply Nat.mul_le_mono_l. exact B.
Qed.
Lemma empty_slot_retains_its_index slots i :
  nth_error slots i = Some None ->
  nth_error (map encode_slot slots) i = Some (repeat 0%N entry_length).
Proof.
  revert i. induction slots as [|s tail IH]; intros [|i] H; simpl in *;
    try discriminate.
  - inversion H; subst. reflexivity.
  - apply IH. exact H.
Qed.
Lemma full_image_fits_ten_256_byte_pages generation slots :
  image_well_formed generation slots ->
  header_length + length (encode_image generation slots) <= 10 * 256.
Proof.
  intros H. pose proof (compact_image_length _ _ H) as [_ B].
  unfold header_length; lia.
Qed.
