import LegionCore.MissionPreservation
import LegionCore.Countermodels
/-!
# LegionCore.ProofSpecBinding — T13 Proof-to-Spec Binding, T14 Non-vacuous Completion
(deliverable PROOF_SPEC_BINDING.lean)

Identities: H_mission = `Spec.mission` (canonical contract identity, frozen); H_proof / H_admission =
`Permit.mission` checked against `State.chash` by the CONTRACT guard inside the Lean decision itself;
H_effect = `Effect.mission` carried by every receipt; H_judge = the contract identity the Judge evaluates
against (`judgeVerdict`). Hashes are modelled as identities (A-H1: canonical-contract hashing is injective on
the contracts that occur; cryptographic collision resistance is NOT proved here).
-/

namespace LegionCore

/-- **T13a — admission (and the ZTL verdict computed inside it) is bound to the frozen contract identity.** -/
theorem T13_admission_bound {sp : Spec} {s : State} {r : Req} (h : admission .full sp s r = .T) :
    r.permit.mission = sp.mission ∧ s.chash = sp.mission ∧ s.cver = 0 ∧ ztl sp s r.task = .T := by
  obtain ⟨_, _, _, _, _, _, hm, _, _, _, _, _, _, _, _, hz, hc, hv⟩ := admit_full_T h
  exact ⟨hm, hc, hv, hz⟩

/-- **T13b — every native effect/receipt is bound to the frozen contract identity.** -/
theorem T13_effect_bound {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s) :
    ∀ e ∈ s.ledger, e.mission = sp.mission :=
  (reach_inv hr).bound

/-- The Judge's specification of a verdict for contract identity `h`: it evaluates against the independently
obtained frozen contract, and every receipt it relies on must carry the same identity. -/
def judgeVerdict (sp : Spec) (h : Nat) (s : State) : Prop :=
  h = sp.mission ∧ judgePass sp s ∧ ∀ e ∈ s.ledger, e.mission = h

/-- **T13c — H_proof = H_admission = H_effect = H_judge = H_mission.** In every reachable state, a Judge PASS
of the original contract is a PASS for exactly the mission identity, with every receipt bound to it. -/
theorem T13_judge_bound {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s)
    (hp : judgePass sp s) : judgeVerdict sp sp.mission s :=
  ⟨rfl, hp, (reach_inv hr).bound⟩

/-- **T13d — a receipt bound to another contract identity voids the Judge verdict for this mission.** -/
theorem T13_foreign_receipt_rejected {sp : Spec} {s : State} {h : Nat} {e : Effect} (he : e ∈ s.ledger)
    (hne : e.mission ≠ h) : ¬ judgeVerdict sp h s :=
  fun ⟨_, _, hall⟩ => hne (hall e he)

/-- **T13e — the Judge never accepts a verdict for a contract identity other than the frozen mission.** -/
theorem T13_other_contract_rejected {sp : Spec} {s : State} {h : Nat} (hne : h ≠ sp.mission) :
    ¬ judgeVerdict sp h s := fun ⟨hm, _⟩ => hne hm

/-- **T14 — Non-vacuous completion.** A Judge PASS is evaluated against O_original — never against the
runtime's (possibly amended) contract record — so it cannot be obtained by deleting obligations, weakening
criteria or substituting the objective: every original mandatory obligation is closed and VERIFIED by
independent evidence (an effect in the ledger read back, or accepted owner evidence while eligible). Holds in
every reachable state, including states after any authorized or attempted specification change. -/
theorem T14_nonvacuous_completion {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s)
    (hj : judgePass sp s) : ∀ o ∈ sp.tasks, o.mandatory = true →
      ∃ o', sp.task? o.id = some o' ∧ o.id ∈ s.closed ∧
        (o'.write = true → o.id ∈ s.verified ∧ ∃ e ∈ s.ledger, e.task = o.id ∧ e.mission = sp.mission) ∧
        (o'.write = false → o.id ∈ s.evidenced) := by
  intro o ho hm
  obtain ⟨o', h1, h2, _, h4, h5⟩ := T9_completion_soundness hr hj o ho hm
  refine ⟨o', h1, h2, fun hw => ?_, h5⟩
  obtain ⟨hv, e, he, het⟩ := h4 hw
  exact ⟨hv, e, he, het, (reach_inv hr).bound e he⟩

namespace Witness

def judgeOnRecordB (s : State) : Bool := s.contract.all (fun tk => !tk.mandatory || s.closed.contains tk.id)

-- T11/T12: drop SPEC AUTHORITY → an execution agent (credential 200) deletes the inconvenient obligation.
def cmT11 : List Cmd := [.start, .amend 200 [tA] 8]
def vT11 (s : State) : Bool := s.contract.length != sp2.tasks.length
theorem cm_T11 : check { specAuth := false } sp2 cmT11 vT11 = true := by decide
theorem cm_T11_full : check .full sp2 cmT11 vT11 = false := by decide

-- T13: drop the CONTRACT binding → an effect whose receipt is bound to another contract identity (999).
def p999 : Permit := { p1 with mission := 999 }
def cmT13 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p999, .actuate (rq p999)]
def vT13 (s : State) : Bool := s.ledger.any (fun e => e.mission != 7)
theorem cm_T13 : check { contract := false } sp2 cmT13 vT13 = true := by decide
theorem cm_T13_full : check .full sp2 cmT13 vT13 = false := by decide

-- T14: a Judge that reads the runtime's contract RECORD (instead of the frozen original) would PASS after an
-- agent deletes the write obligation, with no effect at all. Under the full Core the deletion is refused.
def cmT14 : List Cmd := [.start, .evidence 1 100, .close 1, .amend 200 [tA] 8]
def vT14 (s : State) : Bool := judgeOnRecordB s && s.ledger.isEmpty
theorem cm_T14 : check { specAuth := false } sp2 cmT14 vT14 = true := by decide
theorem cm_T14_full : check .full sp2 cmT14 vT14 = false := by decide

-- T14 robustness: even an AUTHORIZED weakening (spec authority 900) is not accepted by the original Judge.
def cmT14b : List Cmd := [.start, .evidence 1 100, .close 1, .amend 900 [tA] 8]
theorem t14_authorized_weakening_not_accepted :
    check .full sp2 cmT14b (fun s => judgeOnRecordB s && !judgePassB sp2 s) = true := by decide

-- T15 non-vacuity: under the full Core an execution agent replans and the mission still reaches a PASS.
def happyReplan : List Cmd :=
  [.start, .replan 200 [2, 1], .report rep, .evidence 1 100, .close 1, .replan 100 [1], .issue p1,
   .actuate (rq p1), .readback 2, .close 2]
theorem live_with_replan : check .full sp2 happyReplan (fun s => judgePassB sp2 s && s.ledger.length == 1) = true := by
  decide

end Witness
end LegionCore
