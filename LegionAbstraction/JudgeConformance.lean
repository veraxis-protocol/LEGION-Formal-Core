import LegionAbstraction.Refinement
/-!
# LegionAbstraction.JudgeConformance — FORMAL-004: the executable completion check and the Lean completion spec

The Lean completion specification is `judgePass sp s` (Completion.lean): every mandatory obligation of the FROZEN
ORIGINAL specification `sp.tasks` is closed. T9 and T14 are stated against it. FORMAL-004 checks the executable Judge
against it by differential testing (`judge_conformance.py`). This file supplies the Lean side of that check:

* JC1  `judgeSpecB` is a Boolean, executable form of `judgePass`, and it decides it exactly;
* JC2  on a journal-derived state (closed set computed by the proved fold — what the pinned binary outputs), a
       `judgeSpecB` PASS means every mandatory original obligation is confirmed by the journal fold (causally ordered
       and owner-witnessed, J1/J2) or declared not applicable — the journal-level reading of T9;
* JC3  (executable T14) the completion verdict depends only on the frozen original tasks and the closed set: no
       runtime contract record, contract identity or version can change it;
* JC4  the attack T14 excludes is real: deleting an obligation from the list the check iterates can turn a FAIL into
       a PASS (so the executable Judge MUST be bound to the frozen original — tested as `amend_vacuous`).
-/

namespace LegionAbstraction
open LegionCore LegionCore.Journal

/-- Executable completion check: every mandatory task of the given (frozen) task list is in the closed set. -/
def judgeSpecB (tasks : List Task) (closed : List Nat) : Bool :=
  tasks.all (fun tk => !tk.mandatory || closed.contains tk.id)

/-- **JC1** — `judgeSpecB` decides the Lean completion specification. -/
theorem judgeSpecB_iff (sp : Spec) (s : State) : judgeSpecB sp.tasks s.closed = true ↔ judgePass sp s := by
  simp only [judgeSpecB, judgePass, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem]
  constructor
  · intro h tk hm hmand
    rcases h tk hm with h1 | h1
    · simp [hmand] at h1
    · exact h1
  · intro h tk hm
    by_cases hmand : tk.mandatory = true
    · exact Or.inr (h tk hm hmand)
    · left; simpa using hmand

/-- **JC2** — a PASS of the executable check on the journal-derived closed set is grounded in the journal. -/
theorem journal_judge_grounded (sp : Spec) (ts : List JTask) (rs : List Rec)
    (h : judgeSpecB sp.tasks (closedSet ts rs) = true) :
    ∀ tk ∈ sp.tasks, tk.mandatory = true →
      tk.id ∈ (fold ts rs).confirmed ∨ ∃ dt ∈ ts, dt.id = tk.id ∧ dt.na = true := by
  intro tk hm hmand
  have hj : judgePass sp { (init sp 0 0) with closed := closedSet ts rs } :=
    (judgeSpecB_iff sp { (init sp 0 0) with closed := closedSet ts rs }).mp h
  exact closed_grounded ts rs (hj tk hm hmand)

/-- **JC3 (executable T14)** — no runtime contract record, identity or version changes the completion verdict. -/
theorem judge_ignores_contract_record (sp : Spec) (s : State) (c : List Task) (h v : Nat) :
    judgePass sp { s with contract := c, chash := h, cver := v } ↔ judgePass sp s := Iff.rfl

/-- **JC4** — the vacuous-completion attack is real for a check that iterates a mutable list. -/
theorem amended_list_can_pass :
    ∃ (orig amended : List Task) (closed : List Nat),
      amended.Sublist orig ∧ judgeSpecB orig closed = false ∧ judgeSpecB amended closed = true := by
  refine ⟨[⟨1, 0, [], true, 0, true, 0, 0⟩, ⟨2, 0, [], true, 0, true, 0, 0⟩], [⟨1, 0, [], true, 0, true, 0, 0⟩], [1], ?_, ?_, ?_⟩
  · exact List.Sublist.cons₂ _ (List.Sublist.slnil.cons _)
  · decide
  · decide

end LegionAbstraction
