import LegionCore
open LegionCore
set_option pp.proofs false
#check @admit_full_T
#print axioms admit_full_T
#check @reach_inv
#print axioms reach_inv
#check @T1_admission_soundness
#print axioms T1_admission_soundness
#check @T2_effect_after_deps
#print axioms T2_effect_after_deps
#check @T2_evidence_while_eligible
#print axioms T2_evidence_while_eligible
#check @T2_close_after_deps
#print axioms T2_close_after_deps
#check @T2_causal_invariant
#print axioms T2_causal_invariant
#check @T3_resource_conservation
#print axioms T3_resource_conservation
#check @T3_over_capacity_refused
#print axioms T3_over_capacity_refused
#check @T4_claimed_irrelevant
#print axioms T4_claimed_irrelevant
#check @T4_permit_actor_bound
#print axioms T4_permit_actor_bound
#check @T4_identity_isolation
#print axioms T4_identity_isolation
#check @T4_no_credential
#print axioms T4_no_credential
#check @T5_stale_no_seat
#print axioms T5_stale_no_seat
#check @T5_unknown_no_seat
#print axioms T5_unknown_no_seat
#check @T5_order_independent
#print axioms T5_order_independent
#check @T5_ztl_T_needs_seats
#print axioms T5_ztl_T_needs_seats
#check @T5_distinct_origins
#print axioms T5_distinct_origins
#check @T5_closure_needs_verification
#print axioms T5_closure_needs_verification
#check @T6_epoch_binding
#print axioms T6_epoch_binding
#check @T6_epoch_revocation
#print axioms T6_epoch_revocation
#check @T6_not_running
#print axioms T6_not_running
#check @T7_exactly_once
#print axioms T7_exactly_once
#check @T8_recovery_preservation
#print axioms T8_recovery_preservation
#check @T8_retry_after_effect_refused
#print axioms T8_retry_after_effect_refused
#check @T8_fenced_never_executes
#print axioms T8_fenced_never_executes
#check @T8_fence_requires_no_effect
#print axioms T8_fence_requires_no_effect
#check @T8_crash_stutter
#print axioms T8_crash_stutter
#check @T9_completion_soundness
#print axioms T9_completion_soundness
#check @T10_population_independence
#print axioms T10_population_independence
#check @T11_mission_preserved
#print axioms T11_mission_preserved
#check @T11_immutable_without_authority
#print axioms T11_immutable_without_authority
#check @T12_spec_change_authority
#print axioms T12_spec_change_authority
#check @T12_epoch_changes
#print axioms T12_epoch_changes
#check @T12_execution_agent_cannot_amend
#print axioms T12_execution_agent_cannot_amend
#check @T12_change_requires_readmission
#print axioms T12_change_requires_readmission
#check @T13_admission_bound
#print axioms T13_admission_bound
#check @T13_effect_bound
#print axioms T13_effect_bound
#check @T13_judge_bound
#print axioms T13_judge_bound
#check @T13_foreign_receipt_rejected
#print axioms T13_foreign_receipt_rejected
#check @T13_other_contract_rejected
#print axioms T13_other_contract_rejected
#check @T14_nonvacuous_completion
#print axioms T14_nonvacuous_completion
#check @T15_replan_preserves_mission
#print axioms T15_replan_preserves_mission
#check @T15_plan_irrelevant_to_admission
#print axioms T15_plan_irrelevant_to_admission
#check @T15_replan_allowed
#print axioms T15_replan_allowed
#check @LegionCore.Journal.inv_fold
#print axioms LegionCore.Journal.inv_fold
#check @LegionCore.Journal.confirmed_ordered
#print axioms LegionCore.Journal.confirmed_ordered
#check @LegionCore.Journal.sat_witness
#print axioms LegionCore.Journal.sat_witness
#check @LegionCore.Journal.fold_append_prefix
#print axioms LegionCore.Journal.fold_append_prefix
#check @LegionCore.Journal.premature_never_counts
#print axioms LegionCore.Journal.premature_never_counts
#check @LegionCore.Journal.closed_grounded
#print axioms LegionCore.Journal.closed_grounded
#check @LegionCore.Journal.decision_deps_grounded
#print axioms LegionCore.Journal.decision_deps_grounded
