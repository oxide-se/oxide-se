From Stdlib Require Import List.
From OxideSE.Registry Require Import CompactImage.

(* Shared control observations; no additional RAM or execution semantics. *)
Inductive owned_body_pc :=
 | BodyWaiting | BodyAcquiring | BodyWriting | BodyPrepared
 | BodyFailed | BodyInterrupted | BodyFinished.
Record owned_attachment := OwnedAttachment {
 attachment_argument : nat;
 attachment_slot : nat;
 attachment_entry : compact_entry
}.
