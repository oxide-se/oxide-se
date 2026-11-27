From Stdlib Require Import List Arith NArith.
From OxideSE.Registry Require Import
  BossDecodingContract CompactImage CompactUpdates FlashSpec FreerGlobalDataTrace
  FreerRecycledWriter IncarnationReaderContract JournalRequests OwnedDataBinding
  OwnedDataInvariant OwnedDataOffered OwnedDataRequirements OwnedDataResponses
  OwnedDataServices PreparationOutcomes PreparedAuthority RetentionCoverage
  TransactionBoundary.
(* Composition of the concrete supplier contracts with the owner induction. *)
Section OwnerDataComponent.
Variable g:geometry.
Variable sector:nat.
Variable data_len:N.
Variable marker:extent.
Variable ranges:compact_entry->list extent.
Variable decode:flash->nat->option recovery_decoding.
Variable topology:recovery_decoding->bool.
Variable pages:nat.
Variable validate:flash->N->bool.
Variable runtime_kind:list N->nat.
Variable argument_key:nat->object_key.
Variable argument_plan:nat->extent->list writer_command.
Variable word_max:nat.
Variable base:N.
Variable n:nat.
Variable requests:list (owner_service_response->Prop).
Variable Q:owner_service_response->Prop.
Variable valid:N->bool.
Variable view:nat->root_view.
Variable f:flash.
Variable h a:list N.
Variable old:nat.
Variable d:recovery_decoding.
Variable s:protection_state.
Variable e:boundary_evidence.
Variable result:pair_prepass_result.

Local Notation RequiredLaws :=
 (owned_data_suppliers g sector data_len marker ranges decode pages validate word_max base).
Local Notation Entry :=
 (owned_data_entry sector data_len marker ranges decode pages word_max valid view f h a old d s e).
Local Notation Executions :=
 (owned_data_executions g sector data_len marker ranges decode topology pages validate
   runtime_kind argument_key argument_plan word_max n requests Q valid view f h a old d s e result).
Local Notation Offered :=
 (owned_data_offered g sector data_len marker ranges decode topology pages word_max requests Q
   valid view f h a old d s e).

(* The actual type of the historical theorem, not a hand-maintained copy of
   its conclusions. This checking definition belongs to this PROOF facade. *)
Definition owned_data_historical_statement (checked:bool) : Prop :=
 forall (G:journal_geometry g sector 256) (DIV:sector mod 8=0)
   (ACCEPT:validator_accepts_decoded sector decode validate)
   (READERS:forall c,incarnation_reader_local ranges decode c),
 ltac:(let T := type of (@owned_calls_from_idle g sector data_len marker ranges decode topology pages
   validate G DIV ACCEPT READERS runtime_kind argument_key argument_plan word_max base checked
   n requests Q valid view f h a old d s e result) in exact T).

(* Both directions expose the grouping/ungrouping; no new precondition. *)
Theorem owned_data_signature_equivalent (checked:bool) :
 (RequiredLaws -> Entry -> Executions -> Offered) <-> owned_data_historical_statement checked.
Proof.
 split.
 - intros COMPONENT;unfold owned_data_historical_statement.
   intros G DIV ACCEPT READERS HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
     INV NUM CLOSED SERVICES NEXT.
   apply COMPONENT.
   + unfold owned_data_suppliers;repeat first [assumption | split].
   + unfold owned_data_entry;repeat first [assumption | split].
   + unfold owned_data_executions;split;assumption.
 - intros HIST LAWS ENTRY RUN.
   destruct LAWS as [G [DIV [ACCEPT [READERS [HEADER [MAP [PAGES [ADDRESS [MARK [DEC [WORD [GEO [DECODE BASE]]]]]]]]]]]]].
   destruct ENTRY as [INV [NUM CLOSED]];destruct RUN as [SERVICES NEXT].
   exact (HIST G DIV ACCEPT READERS HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE
     INV NUM CLOSED SERVICES NEXT).
Qed.

(* Real component proof: consume J3, not a supplied safe trace/result. *)
Theorem owned_data_component (checked:bool) : RequiredLaws -> Entry -> Executions -> Offered.
Proof.
 intros LAWS ENTRY RUN.
 destruct LAWS as [G [DIV [ACCEPT [READERS [HEADER [MAP [PAGES [ADDRESS [MARK [DEC [WORD [GEO [DECODE BASE]]]]]]]]]]]]].
 destruct ENTRY as [INV [NUM CLOSED]];destruct RUN as [SERVICES NEXT].
 exact (@owned_calls_from_idle g sector data_len marker ranges decode topology pages
   validate G DIV ACCEPT READERS runtime_kind argument_key argument_plan word_max base checked
   n requests Q valid view f h a old d s e result
   HEADER MAP PAGES ADDRESS MARK DEC WORD GEO DECODE BASE INV NUM CLOSED SERVICES NEXT).
Qed.

Theorem registry_satisfies_signature :
 registry_signature g sector data_len marker ranges decode topology pages validate
   runtime_kind argument_key argument_plan word_max base n requests Q valid view f h a old d s e result.
Proof. exact (owned_data_component true). Qed.

(* Make the historical embedding of reader laws in the entry record visible.
   This projection does not ask for a fresh law at each subsequent call. *)
Lemma owned_data_entry_reader_laws : Entry ->
 generation_decoding_matches sector decode (counter_decoder e) /\
 generation_decoding_local sector (counter_decoder e).
Proof.
 intros [INV _];destruct INV;simpl in *;split;assumption.
Qed.
End OwnerDataComponent.

(* Same existing recovery/reentry corollaries, including their exact guards.
   These are theorem aliases, not new promises or a second recovery relation. *)
Definition owned_data_reentry := @owner_delivered_reentry.
Definition owned_data_uncertain_recovery := @episode_uncertain_no_hybrid.
Definition owned_data_boot_reentry := @owner_completed_reset_reentry.
