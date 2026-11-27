From Coq Require Import List NArith.
From OxideSE.Registry Require Import JournalCRCExample.
Import ListNotations.
Open Scope N_scope.

(* Same CRC32 calculation as format.rs::crc32_body. LOAD authenticates the
   header containing this CRC, but not the XIP body itself. *)
Definition load_body_a : list N := [0; 0; 0; 0; 0].
Definition load_body_b : list N := [169; 211; 230; 166; 1].

Theorem distinct_load_bodies_have_equal_crc :
  load_body_a <> load_body_b /\
  length load_body_a = length load_body_b /\
  crc32 load_body_a = crc32 load_body_b.
Proof. vm_compute. repeat split; discriminate. Qed.
