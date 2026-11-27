From Stdlib Require Import List Arith Relation_Operators.
From FreerDPS Require Import Core.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage PreparedAuthority
  JournalHistory BootReconstruction.
Import ListNotations.

Inductive BootRamAction := InstallCurrent | ValidateTopology | InstallRuntime |
  ResetPages | RetainNext | FinishRetains | RememberCache | ReturnInitialized.
Inductive BootRamAPI : interface := BootRam : BootRamAction -> BootRamAPI unit.
Section Ram.
Variable marker : extent.
Variable ranges : CompactImage.compact_entry -> list extent.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Definition boot_ram_caller s A (e : BootRamAPI A) := match e with BootRam action =>
  match action, boot_pc s with
  | InstallCurrent, Installing _ _ ImageRestored => True
  | ValidateTopology, Installing _ d CurrentInstalled => topology d = true
  | InstallRuntime, Installing _ _ TopologyChecked => True
  | ResetPages, Installing _ _ RuntimeInstalled => True
  | RetainNext, Retaining _ _ (_::_) _ => True
  | FinishRetains, Retaining _ _ [] _ => True
  | RememberCache, Caching _ _ _ => True
  | ReturnInitialized, Returning _ _ _ => True
  | _, _ => False end end.
Definition boot_ram_next action phase := match action, phase with
  | InstallCurrent, Installing id d ImageRestored => Installing id d CurrentInstalled
  | ValidateTopology, Installing id d CurrentInstalled => Installing id d TopologyChecked
  | InstallRuntime, Installing id d TopologyChecked => Installing id d RuntimeInstalled
  | ResetPages, Installing id d RuntimeInstalled => Retaining id d (decoded_ranges marker ranges d) (decoded_fresh marker ranges d)
  | RetainNext, Retaining id d (r::todo) ram => Retaining id d todo (recovery_retain r ram)
  | FinishRetains, Retaining id d [] ram => Caching id d ram
  | RememberCache, Caching id d ram => Returning id d (remember_recovered_boss pages (recovered_boss d) ram)
  | ReturnInitialized, Returning id d ram => Usable id d ram
  | _, _ => phase end.
Definition boot_ram_callee (s : boot_state) A (e : BootRamAPI A) (reply : A) : Prop := True.
Definition boot_ram_update s A (e : BootRamAPI A) (reply : A) := match e with
  | BootRam action => (boot_journal s, boot_ram_next action (boot_pc s)) end.
Definition boot_ram_contract := make_contract boot_ram_update boot_ram_caller boot_ram_callee.
Fixpoint boot_ram_program actions : impure BootRamAPI unit := match actions with
  | [] => local tt | a::tail => request_then (BootRam a) (fun _ => boot_ram_program tail) end.
Fixpoint boot_ram_execute actions s := match actions with
  | [] => s | a::tail => boot_ram_execute tail (boot_ram_update s _ (BootRam a) tt) end.
Fixpoint boot_ram_calls actions s := match actions with
  | [] => True | a::tail => boot_ram_caller s _ (BootRam a) /\
      boot_ram_calls tail (boot_ram_update s _ (BootRam a) tt) end.

Lemma boot_ram_refines g sector data_len boss_ok decode s action :
  boot_ram_caller s _ (BootRam action) ->
  boot_step g sector data_len boss_ok marker ranges decode topology pages s
    (boot_ram_update s _ (BootRam action) tt).
Proof.
  destruct s as [j phase]; destruct action; destruct phase; simpl; try contradiction;
    try (destruct stage; simpl; try contradiction);
    try (destruct todo; simpl; try contradiction);
    intros; constructor; assumption || exact I.
Qed.

Lemma boot_ram_program_post actions s final :
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BootRamAPI)
    boot_ram_contract (boot_ram_program actions)) s tt final -> final = boot_ram_execute actions s.
Proof.
  revert s final; induction actions as [|a tail IH]; intros s final H; simpl in H.
  - unroll_post H; simpl; congruence.
  - unroll_post H. destruct H as [reply [middle [[CALL UPDATE] REST]]]. destruct reply; subst middle.
    apply IH in REST; exact REST.
Qed.

Theorem boot_ram_program_refines g sector data_len boss_ok decode actions s final :
  boot_ram_calls actions s ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BootRamAPI)
    boot_ram_contract (boot_ram_program actions)) s tt final ->
  clos_refl_trans boot_state (boot_step g sector data_len boss_ok marker ranges decode topology pages) s final.
Proof.
  intros CALL POST; apply boot_ram_program_post in POST; subst final.
  revert s CALL; induction actions as [|a tail IH]; intros s CALL; simpl.
  - apply rt_refl.
  - destruct CALL as [FIRST REST]. eapply rt_trans; [apply rt_step; apply boot_ram_refines; exact FIRST|].
    apply IH; exact REST.
Qed.

Definition finish_boot_actions (todo : list extent) := repeat RetainNext (length todo) ++
  [FinishRetains; RememberCache; ReturnInitialized].
Theorem finish_boot_callers j id d todo ram :
  boot_ram_calls (finish_boot_actions todo) (j,Retaining id d todo ram).
Proof.
  revert ram; induction todo as [|r todo IH]; intro ram; simpl.
  - repeat split; exact I.
  - split; [exact I|apply IH].
Qed.
Theorem restored_image_callers j id d : topology d = true ->
  boot_ram_calls ([InstallCurrent; ValidateTopology; InstallRuntime; ResetPages] ++
    finish_boot_actions (decoded_ranges marker ranges d)) (j,Installing id d ImageRestored).
Proof.
  intro T. cbn [boot_ram_calls boot_ram_update boot_ram_next boot_pc boot_journal app].
  split; [exact I|]. split; [exact T|]. split; [exact I|]. split; [exact I|].
  apply finish_boot_callers.
Qed.

Theorem composed_boot_ram_preserves g sector data_len boss_ok view decode actions s final :
  JournalRequests.journal_geometry g sector 256 -> sector mod 8 = 0 ->
  recovery_local_contracts view ranges decode ->
  boot_invariant sector data_len boss_ok view marker ranges decode pages s ->
  boot_ram_calls actions s ->
  post (to_hoare (im:=ImpureModule_acto__canonical__Impure_MonadImpure BootRamAPI)
    boot_ram_contract (boot_ram_program actions)) s tt final ->
  boot_invariant sector data_len boss_ok view marker ranges decode pages final.
Proof.
  intros G DIV CONTRACT INV CALL POST.
  pose proof (boot_ram_program_refines g sector data_len boss_ok decode actions s final CALL POST) as TRACE.
  exact (proj1 (boot_finite_trace g sector data_len boss_ok view marker ranges decode topology pages
    G DIV CONTRACT s final INV TRACE)).
Qed.
End Ram.
