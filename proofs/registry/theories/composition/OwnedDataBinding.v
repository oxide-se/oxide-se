From Stdlib Require Import List Arith NArith.
From OxideSE.Registry Require Import
  BossDecodingContract CompactImage CompactUpdates DecodedGeometryContract FlashSpec
  FreerGlobalDataTrace FreerPublicationReturn IncarnationBoundary
  IncarnationReaderContract JournalHistory JournalReachableShape JournalRequests
  OwnedDataInvariant OwnedDataOffered OwnedDataRequirements OwnedDataResponses
  OwnedDataServices PreAppendValidation PreparationOutcomes PreparedAuthority
  RecycledWriter RetentionCoverage TransactionBoundary.
Require OxideSE.Registry.OwnedDataContract.
Module API := OwnedDataContract.

(* Interpretation of the public contract in the initialized owner machine. *)
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

Definition registry_supplier_laws : API.SupplierLaws := {|
  API.journal_layout := journal_geometry g sector 256;
  API.slot_alignment := sector mod 8=0;
  API.validator_acceptance := validator_accepts_decoded sector decode validate;
  API.reader_locality := forall c,incarnation_reader_local ranges decode c;
  API.marker_coverage := marker_header_covered marker;
  API.journal_mapping := journal_object_mapping data_len pages;
  API.page_mapping := mapped_pages pages;
  API.address_decoding := decoding_address_contract decode;
  API.marker_bounds := range_numeric word_max marker;
  API.decoded_bounds := decoded_numeric_contract word_max ranges decode;
  API.word_capacity := 1024*256<=word_max;
  API.area_bounds := area_start g+area_length g<=2*sector+1024*256;
  API.allocation_geometry := decoded_allocation_geometry pages decode;
  API.registry_base := mapped_registry_base base
|}.

Definition registry_vocabulary : API.Vocabulary := {|
  API.Validator := N -> bool;
  API.View := nat -> root_view;
  API.State := execution_boundary;
  API.Receipt := client_receipt;
  API.Exit := operation_exit;
  API.Observation := finalization_result;
  API.Response := owner_service_response;
  API.invariant := owner_invariants sector data_len marker ranges decode pages;
  API.numeric := fun st => phase_numeric word_max marker ranges (snd (fst st));
  API.entry_closed := fun st => delivered_owner_closed (snd st);
  API.ordinary_closed := ordinary_owner_closed;
  API.safe := fun v o => boundary_safe sector data_len v o marker ranges decode pages;
  API.trace := episode_trace g sector data_len marker ranges decode topology pages;
  API.receipts := boundary_receipts;
  API.valid_receipt := fun v st => receipt_valid v ranges (publications (boundary_journal st));
  API.historical := historical_delivery marker;
  API.receipts_of_exits := delivered_receipt_log;
  API.receipts_of_responses := owner_response_receipt_log;
  API.receipts_of_exit := delivered_receipts;
  API.observations := delivered_observations;
  API.observe := append_operation_observation;
  API.matches := owner_response_matches;
  API.ready := owner_reply_ready;
  API.first_call := fun predicate => owned_call_services_for g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan predicate word_max valid view f h a old d s e result;
  API.completed := completed_operation g sector data_len marker ranges decode topology pages valid view ((Logged (Ready f) h a,IdleBoundary old d s),e);
  API.return_post := controller_result_post g sector data_len marker ranges decode topology pages word_max valid view ((Logged (Ready f) h a,IdleBoundary old d s),e);
  API.prepass_matches := fun vo oo => prepass_completion_matches result valid vo view oo ((Logged (Ready f) h a,IdleBoundary old d s),e);
  API.schedule := owned_service_schedule g sector data_len marker ranges decode topology pages validate runtime_kind argument_key argument_plan word_max
|}.

Definition registry_signature := API.signature registry_vocabulary valid view
  ((Logged (Ready f) h a,IdleBoundary old d s),e) n requests Q registry_supplier_laws.

Example registry_signature_exact : registry_signature = (RequiredLaws -> Entry -> Executions -> Offered).
Proof. reflexivity. Qed.
End OwnerDataComponent.
