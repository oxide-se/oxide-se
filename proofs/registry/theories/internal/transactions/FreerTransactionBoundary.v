From Stdlib Require Import List Arith.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import PreparedAuthority JournalHistory BootReconstruction
  TransactionBoundary FreerPrepared FreerBoot.
Import ListNotations.

(* Reuse the existing typed services and their caller/callee/update. The common
   invariant is not a callee guarantee and there is no new atomic service. *)
Theorem common_data_begin_program sector data_len boss_ok view marker ranges decode pages
    j id d ram final :
  common_invariant sector data_len boss_ok view marker ranges decode pages
    (j,IdleBoundary id d ram) ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure DataAPI)
    data_contract (data_program [DataBegin])) ram tt final ->
  data_calls [DataBegin] ram /\
  common_invariant sector data_len boss_ok view marker ranges decode pages
    (j,OpenBoundary (recovered_image d) [recovered_boss d] final).
Proof.
  intros INV POST.
  destruct (common_begin sector data_len boss_ok view marker ranges decode pages j id d ram INV)
    as [CALL NEXT].
  apply data_program_post in POST. simpl in POST; subst final.
  split; [split; [exact CALL|exact I]|exact NEXT].
Qed.

Theorem common_boot_ram_program g sector data_len boss_ok view marker ranges decode topology pages
    actions initial j id d ram :
  JournalRequests.journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  boot_invariant sector data_len boss_ok view marker ranges decode pages initial ->
  boot_ram_calls marker ranges topology pages actions initial ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BootRamAPI)
    (boot_ram_contract marker ranges topology pages) (boot_ram_program actions)) initial tt (j,Usable id d ram) ->
  common_invariant sector data_len boss_ok view marker ranges decode pages (j,IdleBoundary id d ram) /\
  data_caller DataBegin ram /\
  common_invariant sector data_len boss_ok view marker ranges decode pages
    (j,OpenBoundary (recovered_image d) [recovered_boss d] (data_next DataBegin ram)).
Proof.
  intros G DIV CONTRACT INV CALL POST.
  pose proof (composed_boot_ram_preserves marker ranges topology pages g sector data_len boss_ok view decode
    actions initial (j,Usable id d ram) G DIV CONTRACT INV CALL POST) as BOOT.
  pose proof (completed_boot_common sector data_len boss_ok view marker ranges decode pages j id d ram BOOT) as COMMON.
  split; [exact COMMON|]. exact (common_begin sector data_len boss_ok view marker ranges decode pages j id d ram COMMON).
Qed.
