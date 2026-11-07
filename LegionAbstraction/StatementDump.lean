import LegionAbstraction
/-! Exact statements and axioms of the FORMAL-002/003/004 declarations (evidence dump; not part of the library). -/
open LegionAbstraction
#check @guards_rn
#check @admission_rn
#check @closedSet_rn
#check @decision_rn
#check @grounds_rn
#check @intern_inj
#check @intern_pos
#check @alpha_T_requires
#check @alpha_sound
#check @step_refines
#check @runtime_effect_admitted
#check @trace_effects_admitted
#check @ledger_continuity
#check @trace_once
#check @grun_one_create
#check @grun_one_capture
#check @dispatch_needs_lean
#check @uncertainty_sound
#check @judgeSpecB_iff
#check @journal_judge_grounded
#check @judge_ignores_contract_record
#check @amended_list_can_pass
#print axioms judgeSpecB_iff
#print axioms journal_judge_grounded
#print axioms judge_ignores_contract_record
#print axioms amended_list_can_pass
#print axioms decision_rn
#print axioms grounds_rn
#print axioms intern_inj
#print axioms alpha_sound
#print axioms step_refines
#print axioms trace_effects_admitted
#print axioms trace_once
#print axioms grun_one_create
#print axioms grun_one_capture
#print axioms uncertainty_sound
