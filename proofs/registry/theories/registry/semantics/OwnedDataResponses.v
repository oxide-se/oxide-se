From Stdlib Require Import List.
From OxideSE.Registry Require Import OwnedDataTypes FreerGlobalDataTrace FreerPrepared TransactionBoundary Neutralization PreparationOutcomes BossValidationContract PreparedAuthority RetentionCoverage.

(* Observations of existing calls; these are not new persistent state. *)
Inductive append_service_reply :=
| AppendFinishReply (delivered:bool) (stamp:nat)
| AppendRestoreReply (observed:RestoreObservation)
| AppendSyncCutReply (point:runtime_sync_point)
| AppendExitCutReply (phases:list PublicationExitPhase)
| AppendCollectionCutReply (resolved:option (list extent))
| AppendPhysicalCutReply
| AppendRestoreCutReply (point:RestoreCut).

Inductive cleanup_service_response :=
| CleanupReturned (observed:RestoreObservation) (mask_input:option (list extent))
| CleanupInterrupted (point:RestoreCut).

Inductive preparation_ram_cut :=
| PreparationAfterRehomeCache | PreparationAfterSetter | PreparationAfterInstallation.

Inductive owner_service_response :=
| EntryResponse (entry:pair_prepass_result)
| BeforeBossResponse (body:owned_body_pc) (cleanup:cleanup_service_response)
| PreflightResponse (stage:nat) (cleanup:cleanup_service_response)
| AcquisitionResponse (stage:nat) (cleanup:cleanup_service_response)
| SearchInterruptedResponse (fatal:bool)
| AcquisitionCutResponse (point:acquisition_ram_point)
| RecyclingInterruptedResponse (ending:neutral_end)
| WriterFailureResponse (ending:writer_termination) (cleanup:cleanup_service_response)
| WriterInterruptedResponse
| PreparationCutResponse (point:preparation_ram_cut)
| ValidationFailureResponse (reason:boss_check_error) (cleanup:cleanup_service_response)
| ValidationCutResponse (prefix:list boss_check_event)
| AppendResponse (id:nat) (decoded:recovery_decoding) (reply:append_service_reply)
| LocalBodyCleanupResponse (mask:list extent).
