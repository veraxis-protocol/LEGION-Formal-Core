import LegionCore.SpecAuthority
/-!
# LegionCore.MissionPreservation — T11 Original Mission Preservation, T15 Plan Adaptation Without Goal
Mutation  (deliverable MISSION_PRESERVATION.lean)

O_original is `Spec.tasks` with identity `Spec.mission`, frozen before the run. The runtime's contract record
(`State.contract/chash/cver`) starts as O_original and can only be changed through T12's authorized channel.
-/

namespace LegionCore

/-- **T11 — Original Mission Preservation.** In every reachable state of the frozen epoch (contract version 0),
the contract the runtime holds IS the original: same obligations, same canonical identity. -/
theorem T11_mission_preserved {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s)
    (hv : s.cver = 0) : s.contract = sp.tasks ∧ s.chash = sp.mission :=
  (reach_inv hr).frozen hv

/-- **T11' — with no specification authority at all, the original mission is immutable for the whole run**,
whatever any agent, controller, tool or observer does. -/
theorem T11_immutable_without_authority {sp : Spec} {uid wid : Nat} (hna : sp.specAuthority = [])
    {s : State} (hr : Reach .full sp uid wid s) : s.contract = sp.tasks ∧ s.chash = sp.mission ∧ s.cver = 0 := by
  induction hr with
  | init => exact ⟨rfl, rfl, rfl⟩
  | step c _ hx ih =>
    rcases T12_spec_change_authority hx with ⟨h1, h2, h3⟩ | ⟨_, _, _, _, hc, _⟩
    · exact ⟨h1 ▸ ih.1, h2 ▸ ih.2.1, h3 ▸ ih.2.2⟩
    · rw [hna] at hc; cases hc

/-- **T15a — Plan adaptation without goal mutation.** Replanning never changes the original mission, its
identity, its version, the epoch or the issued authority. -/
theorem T15_replan_preserves_mission {sp : Spec} {s s' : State} {cred : Nat} {plan : List Nat}
    (h : exec .full sp s (.replan cred plan) = some s') :
    s'.contract = s.contract ∧ s'.chash = s.chash ∧ s'.cver = s.cver ∧ s'.epoch = s.epoch ∧
      s'.issued = s.issued ∧ s'.plan = plan := by
  simp [exec] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **T15b — admission is independent of the plan**: changing the plan changes no admission verdict. -/
theorem T15_plan_irrelevant_to_admission (g : Guards) (sp : Spec) (s : State) (r : Req) (p : List Nat) :
    admission g sp { s with plan := p } r = admission g sp s r := rfl

/-- **T15c — non-vacuity: execution agents CAN replan** (any admitted credential, at any time). -/
theorem T15_replan_allowed {sp : Spec} {s : State} {cred a : Nat} (ha : sp.actorOf cred = some a)
    (plan : List Nat) : exec .full sp s (.replan cred plan) = some { s with plan := plan } := by
  simp [exec, ha]

end LegionCore
