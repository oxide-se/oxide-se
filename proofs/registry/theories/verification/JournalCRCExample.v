From Coq Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

(* Direct transcription of format.rs::crc32_body: non-reflected polynomial,
   zero initial state and no final xor. This is a finite counterexample check,
   not a general CRC integrity theorem. *)
Definition crc_round (c : N) : N :=
  let shifted := N.modulo (N.shiftl c 1) (2 ^ 32) in
  if N.testbit c 31 then N.lxor shifted 79764919 else shifted.
Definition crc_byte (c b : N) : N :=
  Nat.iter 8%nat crc_round (N.lxor c (N.shiftl b 24)).
Definition crc32 (bytes : list N) : N := fold_left crc_byte bytes 0.

Definition previous_offset : list N := [0; 253; 2; 0].
Definition previous_crc : list N := [124; 222; 111; 20].
Definition changed_offset : list N := [0; 28; 0; 0].
Definition changed_crc : list N := [84; 30; 45; 20].
Definition le32 (bytes : list N) : N :=
  match bytes with
  | [a; b; c; d] => a + 256 * b + 65536 * c + 16777216 * d
  | _ => 0
  end.
Definition decodable_pico_slot (offset_bytes crc_bytes : list N) : Prop :=
  256 <= le32 offset_bytes < 992 * 256 /\
  N.modulo (le32 offset_bytes) 256 = 0 /\
  crc32 offset_bytes = le32 crc_bytes.

Example previous_crc_valid : crc32 previous_offset = 342875772.
Proof. vm_compute. reflexivity. Qed.
Example changed_crc_valid : crc32 changed_offset = 338501204.
Proof. vm_compute. reflexivity. Qed.
Example both_slots_decode_in_pico_data_area :
  decodable_pico_slot previous_offset previous_crc /\
  decodable_pico_slot changed_offset changed_crc /\
  le32 previous_offset <> le32 changed_offset.
Proof. vm_compute. repeat split; discriminate. Qed.
Example previous_slot_can_be_programmed_to_another_valid_slot :
  Forall2 (fun old new => N.land old new = new)
    (previous_offset ++ previous_crc) (changed_offset ++ changed_crc) /\
  previous_offset <> changed_offset.
Proof. vm_compute. repeat constructor; congruence. Qed.

(* The reverse direction is a legal bitwise partial erase. In the retired
   format, a secondary backup of the smaller-bit slot could become the other
   CRC-valid slot while recovery preferred the secondary over primary. *)
Example secondary_erase_can_redirect_old_crc_slot :
  Forall2 (fun old new => N.land old new = old)
    (changed_offset ++ changed_crc) (previous_offset ++ previous_crc) /\
  decodable_pico_slot changed_offset changed_crc /\
  decodable_pico_slot previous_offset previous_crc /\
  le32 changed_offset <> le32 previous_offset.
Proof. vm_compute. repeat split; try discriminate;
  repeat constructor; congruence.
Qed.
