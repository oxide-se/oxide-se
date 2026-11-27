From OxideSE.Registry Require Import FreerFlash FreerFlashClient FreerJournalGate FreerJournalAppend.

Print Assumptions read_reply.
Print Assumptions program_reply_local.
Print Assumptions program_success_reply_exact.
Print Assumptions program_error_reply_requested_only.
Print Assumptions program_reply_identical_page.
Print Assumptions program_reset_has_no_normal_reply.
Print Assumptions erase_reset_has_no_normal_reply.
Print Assumptions read_twice_same.
Print Assumptions program_then_read_observes_reached.
Print Assumptions fault_then_append_gate_closed.
Print Assumptions composed_fault_refuses_append.

Print Assumptions read_bytes_then_post.
Print Assumptions reachable_write_flash_caller.
Print Assumptions reachable_readback_flash_callers.
Print Assumptions write_candidate_normal_refines_step.
Print Assumptions composed_write_preserves_journal_history.
Print Assumptions interrupted_candidate_refines_reset.

From OxideSE.Registry Require Import FreerRetention.
Print Assumptions erase_reserved_sector_caller.
Print Assumptions erase_reserved_sector_post.
Print Assumptions composed_collected_erase_preserves.
Print Assumptions interrupted_collected_erase_preserves.

From OxideSE.Registry Require Import FreerScopeRetention.
Print Assumptions close_pages_post.
Print Assumptions close_pages_caller_from_invariant.
Print Assumptions composed_rollback_preserves_prestate.
Print Assumptions composed_reachable_scope_erase.

From OxideSE.Registry Require Import FreerPrepared.
Print Assumptions withdrawal_refines_step.
Print Assumptions composed_withdrawal_preserves.
Print Assumptions composed_preparation_erase.
Print Assumptions composed_withdrawal_preserves_common.
Print Assumptions composed_protection_erase.
Print Assumptions data_program_post.
Print Assumptions composed_data_program_preserves.
Print Assumptions snapshot_service_preserves.
Print Assumptions snapshot_program_post.
Print Assumptions composed_snapshot_data_preserves.
Print Assumptions snapshot_success_services_callers.
Print Assumptions composed_snapshot_then_data.
Print Assumptions exact_service_preserves.
Print Assumptions exact_service_program_post.
Print Assumptions compiled_exact_execute.
Print Assumptions compiled_exact_callers.
Print Assumptions composed_exact_edits.
Print Assumptions collection_service_preserves.
Print Assumptions composed_collection_preserves.
Print Assumptions successful_exit_callers.
Print Assumptions composed_successful_close.
Print Assumptions composed_successful_exit_collection.
Print Assumptions composed_successful_close_restores_data.
Print Assumptions write_readback_justifies_slot_completed.
Print Assumptions candidate_service_preserves.
Print Assumptions composed_final_boss_preparation.
Print Assumptions final_boss_prepare_callers.
Print Assumptions composed_uncertain_cleanup.
Print Assumptions write_error_justifies_uncertain_edge.
Print Assumptions recovery_pages_callers.
Print Assumptions recovery_pages_program_post.
Print Assumptions composed_reconstruction_opens_transaction.

From OxideSE.Registry Require Import FreerPublicationReturn.
Print Assumptions client_success_only_after_close_collection.
Print Assumptions client_collection_failure_stops.
Print Assumptions prepared_client_return_matches.
Print Assumptions prepared_client_callers.

From OxideSE.Registry Require Import FreerPreparationOutcomes.
Print Assumptions preparation_command_post.
Print Assumptions failed_preparation_command_refines.
Print Assumptions successful_preparation_command_composes.
Print Assumptions interrupted_preparation_command_refines.

From OxideSE.Registry Require Import FreerBoot.
Print Assumptions boot_ram_refines.
Print Assumptions boot_ram_program_refines.
Print Assumptions finish_boot_callers.
Print Assumptions restored_image_callers.
Print Assumptions composed_boot_ram_preserves.

From OxideSE.Registry Require Import FreerTransactionBoundary.
Print Assumptions common_data_begin_program.
Print Assumptions common_boot_ram_program.

From OxideSE.Registry Require Import FreerPersistentBoundary.
Print Assumptions stopped_no_receipt.
Print Assumptions return_adds_one_receipt.
Print Assumptions prepared_freer_client_boot.
Print Assumptions stopped_client_keeps_evidence.

From OxideSE.Registry Require Import FreerDataEpisode.
Print Assumptions collection_service_prefix_post.
Print Assumptions episode_client_finish.
Print Assumptions episode_exit_prefix_reset.
Print Assumptions episode_collection_prefix_reset.
Print Assumptions enriched_data_episode_freer.

From OxideSE.Registry Require Import FreerGlobalDataTrace.
Print Assumptions boundary_step_preserves.
Print Assumptions frozen_boundary_cleanup.
Print Assumptions a11_external_reserved_data_safety.
Print Assumptions episode_no_publication_transport.
Print Assumptions episode_success_durable.
Print Assumptions episode_before_publication.
Print Assumptions episode_uncertain_no_hybrid.
Print Assumptions episode_next_begin.
Print Assumptions episode_prefixes.
Print Assumptions failed_preparation_has_no_publication.
Print Assumptions boundary_emission_is_delivery.
Print Assumptions two_reserved_successes_witness.
Print Assumptions reset_then_reserved_witness.
Print Assumptions completed_unacknowledged_episode_witness.
Print Assumptions published_cut_recovers_exact.
Print Assumptions lift_boundary_trace.
Print Assumptions two_episode_returns_witness.
Print Assumptions episodes_append.

From OxideSE.Registry Require Import FreerAllocationAdmission.
Print Assumptions probe_cursor_execution.
Print Assumptions probe_then_reserve.
Print Assumptions cursor_to_enriched_data_episode.
Print Assumptions erased_search_to_enriched_data_episode.

From OxideSE.Registry Require Import FreerAdmittedTrace.
Print Assumptions erased_admission_guards.
Print Assumptions boss_admission_guards.
Print Assumptions admitted_execution_refines.
Print Assumptions reject_completed_execution.
Print Assumptions rejected_data_contracts.
Print Assumptions rejected_boss_rollback_same.
Print Assumptions erased_step_refines.
Print Assumptions erased_trace_refines.
Print Assumptions a11_erased_allocations_safety.
Print Assumptions admitted_episode_success_durable.
Print Assumptions admitted_episode_before_publication.
Print Assumptions admitted_episode_next_begin.
Print Assumptions admitted_episode_uncertain_no_hybrid.
Print Assumptions admitted_next_episode_prefixes.
Print Assumptions boss_admission_rejection_safe.
Print Assumptions erased_traces_append.

From OxideSE.Registry Require Import FreerNeutralization.
Print Assumptions neutral_normal_execution.
Print Assumptions neutralization_normal_consumer.
Print Assumptions neutralization_open_normal_consumer.

From OxideSE.Registry Require Import FreerRecyclingSearch.
Print Assumptions search_then_retire_execution.
Print Assumptions search_then_retire_safe.

From OxideSE.Registry Require Import FreerRawBoundary FreerReachableNeutralization.
Print Assumptions episode_raw_preserves.
Print Assumptions a11_trace_raw.
Print Assumptions initialized_a11_trace_raw.
Print Assumptions admitted_a11_trace_raw.
Print Assumptions a11_reachable_neutralization_dynamic.
Print Assumptions admitted_reachable_neutralization_dynamic.

Print Assumptions boot_raw_transport.

From OxideSE.Registry Require Import FreerRecyclingErase.
Print Assumptions a11_reachable_recycling_reservation.
Print Assumptions admitted_reachable_recycling_reservation.
Print Assumptions recycling_normal_execution.
Print Assumptions late_reserve_execution.
Print Assumptions recycling_normal_then_reserve.

From OxideSE.Registry Require Import FreerRecycledWriter OwnedDataWitnesses.
Print Assumptions a12f_reservation_to_writer.
Print Assumptions admitted_a12f_reservation_to_writer.

(* A12.g.3: consumers used inside the existing A11 induction. *)
Print Assumptions boundary_boot_prefix_safe.
Print Assumptions boundary_reset_prefix_safe.
Print Assumptions boundary_live_readers.
Print Assumptions boundary_boot_objects_preserved.

(* A12.g.4: indexed observations in the single global episode relation. *)
Print Assumptions episode_step_safe.
Print Assumptions episode_step_history.
Print Assumptions episode_step_selected.
Print Assumptions FreerGlobalDataTrace.episode_raw_preserves.
Print Assumptions episode_trace_raw.
Print Assumptions recycling_acquisition_from_trace.
Print Assumptions recycled_writer_episode.
Print Assumptions recycled_decoded_episode.
Print Assumptions erased_writer_episode.
Print Assumptions recycled_data_attach_episode.

(* A12.g.5: evolving publication suffix and consumers. *)
Print Assumptions certified_append_evidence.
Print Assumptions certified_client_return.
Print Assumptions certified_append_fatal.
Print Assumptions certified_append_cut.
Print Assumptions episode_external_structure.
Print Assumptions episode_trace_external_structure.
Print Assumptions recycled_installed_episode.
Print Assumptions installed_client_from_trace.
Print Assumptions recycled_publication_client_episode.
Print Assumptions installed_suffix_from_trace.
Print Assumptions recycled_publication_suffixes.
Print Assumptions client_trace_opens.
Print Assumptions two_client_episodes_reusing_offset.
Print Assumptions recycled_data_boss_client.
Print Assumptions installed_exit_callers_from_trace.
Print Assumptions installed_publication_prefix_from_trace.

(* A12.g.6: callers derived from the single operational trace. *)
Print Assumptions collection_service_prefix_mask.
Print Assumptions episode_rollback_context.
Print Assumptions episode_trace_rollback_context.
Print Assumptions normal_rollback_from_trace.
Print Assumptions drop_then_rollback_from_trace.
Print Assumptions recycled_writer_local_rollback.
Print Assumptions prepared_rejection_from_trace.
Print Assumptions freer_normal_rollback_from_trace.
Print Assumptions rollback_then_next_success.
Print Assumptions rollback_reset_boot_from_trace.
Print Assumptions recycled_error_then_reused_success.

(* A12.g.7: checked reservation, terminal restoration and direct reset. *)
Print Assumptions restore_probe_outcome.
Print Assumptions checked_recycling_from_trace.
Print Assumptions failed_restore_from_trace.
Print Assumptions failed_restore_boot_from_trace.
Print Assumptions interrupted_restore_boot_from_trace.
Print Assumptions recycling_cut_boot_from_trace.
Print Assumptions reconstructed_trace_opens.
Print Assumptions prepared_restore_failure_from_trace.
Print Assumptions prepared_restore_cut_from_trace.
Print Assumptions fatal_trace_boot.

(* A12.g.8: checked cleanup and local rejections. *)
Print Assumptions check_program_result.
Print Assumptions checked_drop_from_trace.
Print Assumptions rejected_admission_from_trace.
Print Assumptions recycled_rehome_failure_rollback.
Print Assumptions writer_drop_failure_from_trace.
Print Assumptions admitted_drop_from_trace.

(* A12.g.9: pair consumed by the existing global relation. *)
Print Assumptions outer_pair_then_suffix.
Print Assumptions outer_pair_publication_callers.

(* A12.g.10: OperationScope control and B failure after A attachment. *)
Print Assumptions operation_writer_from_trace.
Print Assumptions operation_cancel_from_trace.
Print Assumptions outer_a_b_local_error_restart.
Print Assumptions outer_a_b_writer_outcomes.
Print Assumptions operation_frozen_cleanup_from_trace.
Print Assumptions episode_trace_external_structure.
Print Assumptions episode_trace_rollback_context.
Print Assumptions operation_restore_stop_from_trace.
Print Assumptions operation_drop_failure_from_trace.

(* A12.g.11: recycling acquisition inside OperationScope. *)
Print Assumptions operation_recycling_acquisition_from_trace.
Print Assumptions operation_recycled_writer_episode.
Print Assumptions checked_operation_recycling_from_trace.
Print Assumptions operation_recycled_member.
Print Assumptions operation_accept_from_trace.
Print Assumptions operation_recycled_pair.
Print Assumptions operation_recycled_writer_numeric.
Print Assumptions operation_recycled_local_error_restart.

(* A12.g.13: numerical conclusions consumed through A11 and by pair/rollback. *)
Print Assumptions episode_trace_boot_numeric.
Print Assumptions episode_trace_idle_numeric.
Print Assumptions recycled_extent_numeric.

(* A12.g.14: numeric producer facts now consumed by historical admissions. *)
Print Assumptions erased_admission_numeric.
Print Assumptions boss_admission_numeric.
Print Assumptions admitted_execution_refines.
Print Assumptions erased_step_refines.

(* A12.g.15: all 5 reserved, 7 publication and 47 episode cases. *)
Print Assumptions publication_execution_numeric.
Print Assumptions reserved_execution_numeric.
Print Assumptions boundary_step_numeric.
Print Assumptions episode_step_numeric.
Print Assumptions episode_trace_numeric.

(* A12.g.16: checked cleanup and late reservation consumed by A11. *)
Print Assumptions boss_local_cleanup_from_trace.
Print Assumptions certified_late_reservation_from_trace.

(* A12.g.17: first selected member, including second-only original index. *)
Print Assumptions prepass_dispatch_cases.
Print Assumptions prepass_first_writer_from_idle.
Print Assumptions prepass_first_recycling_from_idle.
Print Assumptions prepass_first_local_rollback.
Print Assumptions prepass_unchanged_from_idle.

(* 87537f2 / A12.g.18: returned finalization observations, not receipts. *)
Print Assumptions owned_aborted_is_invalid.
Print Assumptions joined_success_is_provisional.
Print Assumptions aborted_apdu_no_payload_or_success.
Print Assumptions retained_apdu_unchanged.
Print Assumptions failed_finalization_apdu.
Print Assumptions aborted_external_observation_from_trace.
Print Assumptions aborted_external_apdu_failure.
Print Assumptions local_accept_aborted_observation_from_trace.

(* A12.g.19: operational abort prefix consumed by the same A11 induction. *)
Print Assumptions controller_program_post.
Print Assumptions controller_program_episode.
Print Assumptions episode_step_safe.
Print Assumptions episode_step_numeric.
Print Assumptions episode_trace_numeric.
Print Assumptions owned_local_control_from_idle.
Print Assumptions requested_abort_then_local_success.
Print Assumptions owned_requested_abort_from_idle.
Print Assumptions owned_abort_client_from_idle.
Print Assumptions controlled_aborted_return_from_trace.
Print Assumptions controller_reset_from_trace.

(* A12.g.20: derived root/dirty dispatch and consumed recycled prefixes. *)
Print Assumptions episode_trace_current_origin.
Print Assumptions phase_dirty_matches_roots.
Print Assumptions controlled_clean_from_trace.
Print Assumptions controller_finalization_from_trace.
Print Assumptions controller_recycled_publication.
Print Assumptions controller_recycled_boss_writer.
Print Assumptions actual_client_delivery_disarms.

(* A12.g.21: returned dirty errors consume outer, restoration and residual Drop. *)
Print Assumptions failed_owner_return_from_trace.
Print Assumptions dirty_error_rollback_from_trace.
Print Assumptions dirty_error_restore_outcome_from_trace.
Print Assumptions controller_recycled_boss_error_return.
Print Assumptions controller_publication_error_return.

(* A12.g.22: compulsory control erasure in every operational producer. *)
Print Assumptions publication_execution_control.
Print Assumptions reserved_execution_control.
Print Assumptions boundary_step_control.
Print Assumptions episode_step_control.
Print Assumptions episode_trace_control.
Print Assumptions episode_trace_reset_forgets.
Print Assumptions reconstructed_trace_opens.
Print Assumptions owned_abort_client_from_idle.
Print Assumptions controller_recycled_boss_error_return.
Print Assumptions controller_publication_error_return.

(* A12.g.23: marked prefixes; ordinary return integration remains open. *)
Print Assumptions operation_execution_trace.
Print Assumptions operation_execution_receipts.
Print Assumptions operation_execution_one_receipt.
Print Assumptions owner_return_cannot_be_silent.
Print Assumptions published_operation_execution.
Print Assumptions stopped_operation_execution.
Print Assumptions delimited_publication_is_actual_delivery.
Print Assumptions operation_then_continuation.
Print Assumptions published_then_resume.
Print Assumptions two_delimited_operations.
Print Assumptions controller_dispatch_prefix_from_trace.
Print Assumptions controller_finalization_from_trace.

(* A12.g.24: explicit ordinary delivery, consumed by all four producers. *)
Print Assumptions ordinary_delivery_execution.
Print Assumptions controller_ordinary_edge_is_delivery.
Print Assumptions beginning_another_operation_is_not_delivery.
Print Assumptions ordinary_delivery_no_second_return.
Print Assumptions ordinary_delivery_no_storage.
Print Assumptions completed_operation_trace.
Print Assumptions completed_operation_control.
Print Assumptions completed_publication_from_trace.
Print Assumptions completed_reset_from_trace.
Print Assumptions completed_error_then_success.
Print Assumptions delivered_owned_observation.
Print Assumptions joined_operation_has_no_owned_delivery.
Print Assumptions controlled_clean_from_trace.
Print Assumptions controlled_abort_from_trace.
Print Assumptions controller_recycled_boss_error_return.
Print Assumptions controller_publication_error_return.
Print Assumptions controller_finalization_from_trace.
Print Assumptions controller_error_then_success.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_control.

(* A12.g.25 partial: operational prepass and owned first-member prefixes. *)
Print Assumptions pair_prepass_execution.
Print Assumptions pair_prepass_selected.
Print Assumptions pair_prepass_duplicate_skips_second.
Print Assumptions pair_prepass_first_error_stops.
Print Assumptions owned_pair_entry_return.
Print Assumptions owned_pair_entry_then_operation.
Print Assumptions owned_pair_entry_dispatch.
Print Assumptions owned_pair_first_writer.
Print Assumptions owned_pair_first_recycling.
Print Assumptions operation_execution_trace.
Print Assumptions controller_finalization_from_trace.

(* A12.g.26: checked rejection, separate cleanup and body-error delivery. *)
Print Assumptions body_delivery_execution.
Print Assumptions body_error_blocks_finish.
Print Assumptions body_error_survives_abort_and_cleanup.
Print Assumptions body_error_finish_from_trace.
Print Assumptions attachment_rejection_return_from_trace.
Print Assumptions attachment_existing_identity_not_rejected.
Print Assumptions attachment_full_new_identity_rejected.
Print Assumptions owned_pair_first_attachment_rejection.
Print Assumptions owned_pair_second_attachment_rejection.
Print Assumptions local_writer_body_error_from_trace.
Print Assumptions rejected_attachment_reset_from_trace.
Print Assumptions delivered_body_error_prestate.
Print Assumptions body_error_then_success.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_control.
Print Assumptions a11_external_reserved_data_safety.

Print Assumptions owned_pair_first_body_failure.

(* A12.g.27: current-root transport and controlled frozen body return. *)
Print Assumptions frozen_body_finish_from_trace.
Print Assumptions operation_physical_body_return.
Print Assumptions owned_pair_first_frozen_body_return.
Print Assumptions owned_pair_second_frozen_body_return.
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_reset_forgets.

(* A12.g.28: acquisition failure, no token, actual body delivery. *)
Print Assumptions operation_acquisition_body_return.
Print Assumptions owned_pair_first_acquisition_return.
Print Assumptions owned_pair_second_acquisition_return.
Print Assumptions body_error_finish_from_trace_flash.
Print Assumptions operation_search_body_return.
Print Assumptions owned_pair_first_search_return.
Print Assumptions owned_pair_second_search_return.
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_raw.
Print Assumptions episode_trace_reset_forgets.

(* A12.g.29: local admission checks and non-returning search prefixes. *)
Print Assumptions checked_data_probe_execution_not_rejected.
Print Assumptions local_admission_error_classified.
Print Assumptions operation_numeric_body_return.
Print Assumptions owned_pair_first_numeric_return.
Print Assumptions owned_pair_second_numeric_return.
Print Assumptions operation_search_stop_from_trace.
Print Assumptions owned_pair_first_search_stop.
Print Assumptions owned_pair_second_search_stop.
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_reset_forgets.

(* A12.g.30: common trace transport, including historical services and boot. *)
Print Assumptions reserved_execution_pages.
Print Assumptions boundary_step_pages.
Print Assumptions episode_step_pages.
Print Assumptions episode_trace_pages.
Print Assumptions operation_ensure_protection_from_trace.
Print Assumptions operation_numeric_body_return.
Print Assumptions owned_pair_first_numeric_return.
Print Assumptions owned_pair_second_numeric_return.

(* A12.g.31: actual opening provenance, no root inferred from dependencies. *)
Print Assumptions before_change_unknown_no_call.
Print Assumptions episode_step_roots.
Print Assumptions episode_trace_roots.
Print Assumptions owned_open_roots_correspondence.
Print Assumptions owned_first_before_change.
Print Assumptions owned_second_before_change.
Print Assumptions before_change_skip_from_trace.
Print Assumptions owned_pair_first_writer.
Print Assumptions owned_pair_first_recycling.
Print Assumptions owned_pair_first_numeric_return.
Print Assumptions owned_pair_second_numeric_return.
Print Assumptions owned_pair_second_search_stop.

(* A12.g.32: coverage audit, not closure of the owned pair controller. *)
Print Assumptions selected_second_prepass_exec.
Print Assumptions selected_body_not_enforced_by_trace.
Print Assumptions selected_body_can_reach_clean_finalizer.

(* A12.g.33: operational owned-body marking, exact ordered attachments. *)
Print Assumptions owned_body_run_trace.
Print Assumptions owned_body_prefix_numeric.
Print Assumptions owned_body_success_order.
Print Assumptions owned_body_no_skipped_member.
Print Assumptions owned_erased_writer_prefix.
Print Assumptions owned_recycled_acquisition_prefix.
Print Assumptions owned_pending_writer_prefix.
Print Assumptions owned_empty_prepass_return.
Print Assumptions owned_single_prepared.
Print Assumptions owned_two_prepared.
Print Assumptions owned_prepared_rejection.
Print Assumptions owned_success_repeated_tag.
Print Assumptions owned_controller_body_accept.
Print Assumptions owned_failure_has_no_body_success.
Print Assumptions owned_body_history.

Print Assumptions owned_recycled_writer_prefix.

(* A12.g.34: all represented attachment/local exits in the marked body. *)
Print Assumptions identical_attachment_safe.
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_pages.
Print Assumptions episode_trace_roots.
Print Assumptions prepared_rejection_return_from_trace.
Print Assumptions owned_attach_dispatch.
Print Assumptions owned_single_checked.
Print Assumptions owned_two_checked.
Print Assumptions identical_attachment_effect.
Print Assumptions owned_numeric_refusal.
Print Assumptions owned_search_refusal.
Print Assumptions owned_search_interruption.
Print Assumptions owned_marked_prepared_error_return.
Print Assumptions owned_marked_local_error_return.
Print Assumptions owned_marked_before_change.
Print Assumptions owned_controller_body_accept.
Print Assumptions owned_body_success_order.
Print Assumptions owned_body_no_skipped_member.
Print Assumptions owned_success_repeated_tag.
Print Assumptions owned_failure_has_no_body_success.
Print Assumptions owned_body_history.

(* A12.g.35 partial: marked success close, explicit abort, interrupted prefix. *)
Print Assumptions owned_marked_success_finish.
Print Assumptions owned_marked_abort_finish.
Print Assumptions owned_marked_interruption_return.
Print Assumptions owned_marked_prepared_error_return.
Print Assumptions owned_marked_local_error_return.
Print Assumptions body_error_cannot_select_finish.
Print Assumptions marked_success_gate_no_skip.

(* A12.g.36 partial: Failed provenance and A11-consumed error boundary. *)
Print Assumptions owned_failed_provenance.
Print Assumptions data_writer_failed_result.
Print Assumptions owned_run_scope_context.
Print Assumptions owned_failed_observed.
Print Assumptions owned_marked_failed_boundary.

(* A12.g.36 completion for the represented marked-body outcomes. *)
Print Assumptions owned_control_sticky_bit.
Print Assumptions owned_abort_interleaved.
Print Assumptions owned_interleaved_abort_finish.
Print Assumptions owned_marked_failed_return.
Print Assumptions owned_marked_controller.

(* A12.g.37: interrupted local/external restoration, uniform dispatch, A10. *)
Print Assumptions owned_skipped_restore_no_cut.
Print Assumptions owned_marked_failed_cut.
Print Assumptions owned_marked_abort_cut.
Print Assumptions owned_marked_controller.
Print Assumptions owned_reset_boot_prefix.
Print Assumptions owned_failed_cut_repeated_boot.

(* A12.g.38: complete entry consumes the marked cleanup controller. *)
Print Assumptions owned_entry_marked_controller.

(* A12.g.39: external abort consumes failed restore responses. *)
Print Assumptions owned_marked_abort_restore_failure.
Print Assumptions owned_marked_controller.
Print Assumptions owned_entry_marked_controller.

(* A12.g.40 partial: acquisition consumed from the marked entry result. *)
Print Assumptions owned_entry_marked_recycling.

(* A12.g.41: owner continuations after BOSS acquisition, already selected. *)
Print Assumptions selected_search_error_return.
Print Assumptions selected_recycling_error_return.
Print Assumptions selected_recycling_interruption.
Print Assumptions selected_recycling_before_reserve_reset.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.42: checked probe and shared search interruptions at selected BOSS entry. *)
Print Assumptions operation_search_interrupted.
Print Assumptions episode_trace_numeric.
Print Assumptions selected_probe_error_return.
Print Assumptions selected_search_interruption.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.43 partial: Pages preflight derived at the produced BOSS entry. *)
Print Assumptions owned_entry_marked_recycling.

(* A12.g.44: consumed physical marker provenance. *)
Print Assumptions owned_body_run_marker.
Print Assumptions owned_marked_success_finish.
Print Assumptions owned_entry_marked_controller.
Print Assumptions owned_entry_marked_recycling.
Print Assumptions boot_rechecks_physical_marker.
Print Assumptions owned_body_reset_marker_recovery.

(* A12.g.45: all sixty constructors of the existing episode relation. *)
Print Assumptions reserved_execution_marker.
Print Assumptions boundary_step_marker.
Print Assumptions idle_member_marker.
Print Assumptions episode_step_marker_frame.
Print Assumptions episode_step_marker.
Print Assumptions episode_trace_marker_frame.
Print Assumptions episode_trace_marker.
Print Assumptions initialized_episode_trace_marker.
Print Assumptions episode_trace_marker_probe.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.46: runtime observation, all historical producers and BOSS consumer. *)
Print Assumptions runtime_initialized_probe_ready.
Print Assumptions runtime_initialized_probe_result.
Print Assumptions publication_execution_runtime.
Print Assumptions reserved_execution_runtime.
Print Assumptions boundary_step_runtime.
Print Assumptions episode_step_runtime.
Print Assumptions episode_trace_runtime.
Print Assumptions episode_trace_runtime_forgotten.
Print Assumptions boot_runtime_handoff.
Print Assumptions owned_entry_marked_recycling.

Print Assumptions selected_preallocation_error_return.
Print Assumptions selected_probe_error_return.
Print Assumptions selected_generation_overflow_return.

(* A12.g.48: all historical producers, computed overflow and marked consumer. *)
Print Assumptions next_generation_probe_ready.
Print Assumptions next_generation_probe_result.
Print Assumptions publication_execution_counter.
Print Assumptions reserved_execution_counter.
Print Assumptions boundary_step_counter.
Print Assumptions episode_step_counter_source.
Print Assumptions episode_step_counter.
Print Assumptions episode_trace_counter.
Print Assumptions episode_trace_counter_origin.
Print Assumptions boot_counter_reconstructed.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.49: consumed from erased and recycled acquisition. *)
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.50: owner/checker provenance consumed at both acquisition origins. *)
Print Assumptions active_single_outer_depth.
Print Assumptions boss_rehome_from_roots_numeric.
Print Assumptions boss_rehome_refusal_excluded.
Print Assumptions owned_marked_success_finish.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.51: executed rehome/cache, not a claim that the full suffix is closed. *)
Print Assumptions snapshot_program_executes.
Print Assumptions execute_written_rehome_cache.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.52: the executed rehome/cache prefix is an A11 episode. *)
Print Assumptions rehome_cached_safe.
Print Assumptions prepared_rehome_cache_post.
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_marker.
Print Assumptions episode_trace_counter.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.53: same computed/encoded next, executed after Detached. *)
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_counter.
Print Assumptions episode_trace_marker.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.54: both acquisition origins consume address and installation. *)
Print Assumptions episode_step_safe.
Print Assumptions episode_trace_numeric.
Print Assumptions episode_trace_counter.
Print Assumptions episode_trace_marker.
Print Assumptions episode_no_publication_transport.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.
From OxideSE.Registry Require Import FreerPreAppend.
Print Assumptions composed_boss_check.

(* A12.g.55: reached-flash check and owner failure consumers. *)
Print Assumptions installed_boss_validation_from_writer.
Print Assumptions installed_validation_error_return.
Print Assumptions installed_validation_cut_from_trace.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.56 *)
Print Assumptions mapped_erased_admission_forget.
Print Assumptions mapped_erased_admission_bound.
Print Assumptions erased_admission_alignment.
Print Assumptions episode_step_latest.
Print Assumptions episode_trace_latest.
Print Assumptions episode_step_latest_origin.
Print Assumptions episode_trace_latest_without_publication.
Print Assumptions idle_trace_open_latest.
Print Assumptions installed_validation_owner_from_trace.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* A12.g.57: successful validation consumes the append entry and suffixes. *)
Print Assumptions validated_append_suffixes_from_trace.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* J2: implemented transport and admission interfaces; full provenance remains open. *)
Print Assumptions episode_trace_allocation_reset.
Print Assumptions episode_trace_allocation_known.
Print Assumptions runtime_erased_admission_mapped.
Print Assumptions runtime_search_start_unique.
Print Assumptions operation_recycled_pair.
Print Assumptions operation_recycled_local_error_restart.
Print Assumptions owned_recycled_writer_prefix.
Print Assumptions owned_entry_marked_recycling.

(* J2 historical acquisition producers and real FoundErased. *)
Print Assumptions runtime_erased_admission_mapped.
Print Assumptions runtime_erased_advance_bounded.
Print Assumptions reserved_execution_allocation_value.
Print Assumptions two_reserved_successes_witness.
Print Assumptions episode_trace_allocation_known.
Print Assumptions found_erased_then_next_acquisition.
Print Assumptions outer_pair_then_suffix.
Print Assumptions outer_a_b_local_error_restart.
Print Assumptions owned_entry_marked_recycling.

(* J2: executed suffix, boot acquisition and marked RAM-cut consumers. *)
Print Assumptions recovered_runtime_search_inputs.
Print Assumptions client_finish_after_runtime.
Print Assumptions executed_client_runtime_prefix.
Print Assumptions resume_allocation_bounded_from_trace.
Print Assumptions recovered_found_erased_from_trace.
Print Assumptions erased_ram_cut_from_trace.
Print Assumptions append_runtime_cut_from_trace.
Print Assumptions owned_erased_ram_cut.
Print Assumptions owned_recycled_ram_cut.
Print Assumptions recycling_ram_cut_recovery.

(* J2 junctions: global mapping/provenance and synchronized continuation. *)
Print Assumptions initialized_allocation_origin.
Print Assumptions initialized_allocation_append_bound.
Print Assumptions reserved_execution_allocation_origin.
Print Assumptions boundary_step_allocation_origin.
Print Assumptions episode_step_allocation_origin.
Print Assumptions episode_trace_allocation_origin.
Print Assumptions episode_step_append_bound.
Print Assumptions episode_trace_append_bound.
Print Assumptions episode_trace_allocation_transport.
Print Assumptions runtime_search_calculation.
Print Assumptions owned_body_search_calculation.
Print Assumptions client_finish_from_runtime.
Print Assumptions certified_runtime_sync.
Print Assumptions validated_append_suffixes_from_trace.
Print Assumptions boss_acquisition_ram_cut.
Print Assumptions owned_entry_marked_recycling.

(* J3: reached BOSS writer failures, both acquisition origins. *)
Print Assumptions selected_frozen_writer_return.
Print Assumptions generated_pending_writer_from_trace.
Print Assumptions owned_entry_marked_recycling.

(* The preflight result gates the existing owner callback and its admissions. *)
Print Assumptions boss_search_inputs_runtime.
Print Assumptions boss_erased_admission_runtime.
Print Assumptions owned_entry_marked_recycling.

(* J3: actual service executions consumed through delivery, and reentry facts. *)
Print Assumptions episode_step_ordinary_latest.
Print Assumptions episode_trace_ordinary_latest.
Print Assumptions append_services_terminal.
Print Assumptions generated_writer_services_terminal.
Print Assumptions owner_invariants_trace.
Print Assumptions owned_entry_services_terminal.
Print Assumptions owned_entry_services_with_invariants.
Print Assumptions owner_completed_reset_reentry.
Print Assumptions owned_recovered_services_terminal.

(* J3: actual delivery guards, ordinary reentry and terminal internal cuts. *)
Print Assumptions completed_operation_owner_closed.
Print Assumptions controller_publication_restore_cut.
Print Assumptions owner_delivered_reentry.
Print Assumptions owned_returned_services_terminal.

(* Finite closure of marked owner calls and supplied recovery executions. *)
Print Assumptions owned_call_services_terminal.
Print Assumptions owned_schedule_run.
Print Assumptions owned_schedule_consumer.
Print Assumptions owned_calls_from_idle.
Print Assumptions owned_schedule_bind.
Print Assumptions delivered_observations_fold.

(* Replies are indexed by executed append/restore/finish services. *)
Print Assumptions deliver_ready_execution_observed.
Print Assumptions append_services_erase.
Print Assumptions append_services_refine.
Print Assumptions append_services_observed_terminal.
Print Assumptions append_reply_observation_exact.

(* Responses propagated through the owner and its existing finite induction. *)
Print Assumptions owner_terminal_forget.
Print Assumptions owner_response_receipts_exact.
Print Assumptions owner_response_logs_exact.
Print Assumptions owner_response_append_observation.
Print Assumptions restoration_services_refine.
Print Assumptions validation_services_erase.
Print Assumptions validation_services_refine.
Print Assumptions owned_call_services_erase.
Print Assumptions owned_call_services_terminal_at.

(* Same local replies retained through the owner schedule and its witness. *)
Print Assumptions marked_boss_requested.
Print Assumptions owned_entry_marked_controller_indexed.
Print Assumptions owner_terminal_forget_index.
Print Assumptions writer_tail_services_unindexed.
Print Assumptions boss_writer_services_unindexed.
Print Assumptions boss_acquisition_services_unindexed.
Print Assumptions boss_pipeline_services_unindexed.
Print Assumptions generated_writer_services_terminal_for.
Print Assumptions owned_entry_services_terminal_for.
Print Assumptions owned_entry_services_with_invariants_for.
Print Assumptions owned_services_from_finished_body.
Print Assumptions owned_call_services_unindexed.
Print Assumptions owned_call_services_terminal_for.
Print Assumptions response_requests_two_exact.
Print Assumptions unchanged_published_exits.
Print Assumptions owned_unchanged_then_published.
Print Assumptions owned_unchanged_then_published_from_body.

(* Indexed J3 composition witnesses. *)
Print Assumptions publication_receipt_destination.
Print Assumptions reserved_receipt_destination.
Print Assumptions boundary_receipt_destination.
Print Assumptions episode_receipt_destination.
Print Assumptions operation_published_destination.
Print Assumptions completed_published_destination.
Print Assumptions owner_reset_response_exit.
Print Assumptions reset_published_exits.
Print Assumptions recovered_published_schedule.
Print Assumptions owned_cut_recovered_then_published.
Print Assumptions published_pair_exits.
Print Assumptions owned_two_published.
Print Assumptions owned_append_restorecut_recovered_then_published.
Print Assumptions owned_preparation_cut_recovered_then_published.
Print Assumptions owned_publications_historical_reuse.

(* Ordinary local error: executed cleanup, exact delivery, derived reentry. *)
Print Assumptions body_error_cleanup_returned_from_trace.
Print Assumptions owned_marked_local_cleanup_returned.
Print Assumptions local_cleanup_mask_spec.
Print Assumptions owner_local_response_projects.
Print Assumptions owned_services_from_local_failed_body.
Print Assumptions local_error_published_exits.
Print Assumptions owned_local_error_then_published.
Print Assumptions owned_local_error_then_published_from_body.

From OxideSE.Registry Require Import OwnedDataComponent.
Print Assumptions owned_data_signature_equivalent.
Print Assumptions owned_data_component.
Print Assumptions owned_data_entry_reader_laws.
Print Assumptions owned_data_reentry.
Print Assumptions owned_data_uncertain_recovery.
Print Assumptions owned_data_boot_reentry.

Print Assumptions OwnedDataBinding.registry_signature_exact.
Print Assumptions registry_satisfies_signature.
