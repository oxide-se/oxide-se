From Stdlib Require Import List Arith NArith.
From OxideSE.Registry Require Import FlashSpec RetentionCoverage CompactImage PreparedAuthority JournalHistory JournalReachableShape JournalRawOrder TransactionBoundary FreerGlobalDataTrace FreerPrepared FreerDataEpisode FreerPublicationReturn IncarnationBoundary OwnedDataInvariant OwnedDataTypes OwnedDataResponses.
Import ListNotations.

Definition restoration_delivery_exit outcome :=
 match outcome with RestoreValidated=>ReturnedOrdinary FinishPublish | _=>InterruptedFatal end.

Definition delivered_receipts exit :=
 match exit with ReturnedPublished receipt=>[receipt] | _=>[] end.

Inductive append_service_kind := AppendClient (delivered:bool) | AppendError | AppendReset.

Definition append_reply_kind reply :=
 match reply with
 | AppendFinishReply delivered _=>AppendClient delivered
 | AppendRestoreReply _=>AppendError | _=>AppendReset end.

Definition append_reply_exit id d reply :=
 match reply with
 | AppendFinishReply true stamp=>ReturnedPublished (Receipt stamp (Certificate id d))
 | AppendFinishReply false _=>InterruptedFatal
 | AppendRestoreReply observed=>restoration_delivery_exit observed
 | _=>InterruptedReset end.

Definition owner_reply_ready response (reached:execution_boundary) : Prop :=
 match response with
 | LocalBodyCleanupResponse _=>exists f h a id d ram ev,
      reached=((Logged (Ready f) h a,IdleBoundary id d ram),ev)
 | _=>True end.

Definition owner_response_matches response exit :=
 match response with
 | LocalBodyCleanupResponse _=>exit=ReturnedBodyError
 | EntryResponse entry=>match pair_prepass_return entry with Some success=>exit=ReturnedEntry success | None=>False end
 | AppendResponse id decoded reply=>exit=append_reply_exit id decoded reply
 | PreparationCutResponse _ | AcquisitionCutResponse _ | ValidationCutResponse _ |
   WriterInterruptedResponse=>exit=InterruptedReset
 | _=>delivered_receipts exit=[] end.

Definition erase_local_response response :=
 match response with
 | LocalBodyCleanupResponse mask=>BeforeBossResponse BodyFailed (CleanupReturned RestoreValidated (Some mask))
 | _=>response end.

Definition ordinary_owner_closed (state:execution_boundary) :=
 match snd (fst state) with IdleBoundary _ _ _ | ClientBoundary _ _ _ =>
   delivered_owner_closed (snd state) | _=>True end.

Fixpoint delivered_receipt_log (exits:list operation_exit) : list client_receipt :=
 match exits with []=>[] | exit::rest=>delivered_receipt_log rest++delivered_receipts exit end.

Fixpoint delivered_observations (exits:list operation_exit) : list finalization_result :=
 match exits with []=>[] | exit::rest=>
   match exit_observation exit with None=>delivered_observations rest
    | Some result=>result::delivered_observations rest end end.

Definition owner_response_receipts response :=
 match response with
 | AppendResponse id d reply=>delivered_receipts (append_reply_exit id d reply)
 | _=>[] end.

Fixpoint owner_response_receipt_log responses :=
 match responses with []=>[] | response::rest=>
   owner_response_receipt_log rest++owner_response_receipts response end.

Definition prepass_completion_matches result (vi vo:N->bool) (oi oo:nat->root_view)
 (source reached:execution_boundary) exit :=
 match pair_prepass_return result with
 | Some success=>vo=vi /\ oo=oi /\ reached=source /\ exit=ReturnedEntry success
 | None=>True end.

Section Offered.
Variable g : geometry.
Variable sector : nat.
Variable data_len : N.
Variable marker : extent.
Variable ranges : compact_entry -> list extent.
Variable decode : flash -> nat -> option recovery_decoding.
Variable topology : recovery_decoding -> bool.
Variable pages : nat.
Local Notation Safe v o := (boundary_safe sector data_len v o marker ranges decode pages).
Local Notation Trace := (episode_trace g sector data_len marker ranges decode topology pages).
Local Notation owner_invariants := (owner_invariants sector data_len marker ranges decode pages).

Definition controller_result_post word_max vi oi initial events valid view final :=
 Trace vi oi initial events valid view final /\ Safe valid view final /\
 phase_numeric word_max marker ranges (snd (fst final)) /\
 boundary_receipts final=events++boundary_receipts initial /\
 terminal_control_absent final /\
 (forall id d ram,snd (fst final)=IdleBoundary id d ram -> data_caller DataBegin ram).

Definition owned_data_offered word_max requests (Q:owner_service_response->Prop)
 valid view f h a old d s e : Prop :=
 exists vf of_ final exits responses,
 Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) (delivered_receipt_log exits) vf of_ final /\
 owner_invariants vf of_ final /\ phase_numeric word_max marker ranges (snd (fst final)) /\
 ordinary_owner_closed final /\
 boundary_receipts final=delivered_receipt_log exits++boundary_receipts ((Logged (Ready f) h a,IdleBoundary old d s),e) /\
 Forall (receipt_valid of_ ranges (publications (boundary_journal final))) (boundary_receipts final) /\
 Forall (historical_delivery marker) (delivered_receipt_log exits) /\
 (forall history,history++delivered_observations exits=
   fold_left append_operation_observation exits history) /\
 (forall events vp op prefix,
   Trace valid view ((Logged (Ready f) h a,IdleBoundary old d s),e) events vp op prefix ->
   Safe vp op prefix /\ phase_numeric word_max marker ranges (snd (fst prefix))) /\
 Forall2 owner_response_matches responses exits /\
 Forall2 (fun predicate response=>predicate response) (Q::requests) responses /\
 delivered_receipt_log exits=owner_response_receipt_log responses.

End Offered.
