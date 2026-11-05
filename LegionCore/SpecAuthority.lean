import LegionCore.Authority
/-!
# LegionCore.SpecAuthority — T12 Specification Modification Authority  (deliverable SPEC_AUTHORITY_MODEL.lean)

The specification channel is modelled as an attack surface: ANY credential may attempt `amend`. Only a
credential in `Spec.specAuthority` succeeds, and a successful change always creates a new contract version
and a new epoch, revoking every issued permit. Assumption A-S1 (separation of duties) — execution-agent
credentials are not spec-authority credentials — is an explicit hypothesis, never an axiom.
-/

namespace LegionCore

/-- **T12 — Specification Modification Authority.** Any transition that changes the contract record (its
obligations, identity or version) is an `amend` by a credential holding specification authority, and it
creates a new contract version AND a new epoch, with all previously issued permits revoked. -/
theorem T12_spec_change_authority {sp : Spec} {s s' : State} {c : Cmd} (h : exec .full sp s c = some s') :
    (s'.contract = s.contract ∧ s'.chash = s.chash ∧ s'.cver = s.cver) ∨
    ∃ cred tasks hh, c = .amend cred tasks hh ∧ cred ∈ sp.specAuthority ∧
      s'.contract = tasks ∧ s'.chash = hh ∧ s'.cver = s.cver + 1 ∧ s'.epoch = s.epoch + 1 ∧ s'.issued = [] := by
  cases c with
  | amend cred tasks hh =>
    right; simp [exec, Guards.full] at h; obtain ⟨hc, rfl⟩ := h
    exact ⟨cred, tasks, hh, rfl, hc, rfl, rfl, rfl, rfl, rfl⟩
  | actuate r =>
    left; simp only [exec] at h
    split at h
    · split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  | evidence t cred =>
    left; simp only [exec] at h
    split at h
    · split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  | close t =>
    left; simp only [exec] at h
    split at h
    · repeat' split at h
      all_goals first | (cases h; exact ⟨rfl, rfl, rfl⟩) | cases h
    · cases h
  | start => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | terminate => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | bump => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | tick => left; simp only [exec] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  | crash => left; simp only [exec] at h; cases h; exact ⟨rfl, rfl, rfl⟩
  | issue p => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | report r => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | fence c => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | readback t => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩
  | replan cred plan => left; simp only [exec] at h; split at h <;> cases h; exact ⟨rfl, rfl, rfl⟩

/-- **T12a — the epoch changes on every authorized specification change.** -/
theorem T12_epoch_changes {sp : Spec} {s s' : State} {cred : Nat} {tasks : List Task} {hh : Nat}
    (h : exec .full sp s (.amend cred tasks hh) = some s') : s'.epoch ≠ s.epoch := by
  simp [exec, Guards.full] at h; obtain ⟨_, rfl⟩ := h; simp

/-- **T12b — execution agents hold no specification authority** (under separation of duties A-S1). -/
theorem T12_execution_agent_cannot_amend {sp : Spec} {s : State} {cred : Nat} {a : Nat}
    (hdisj : ∀ c, (sp.actorOf c).isSome = true → c ∉ sp.specAuthority) (ha : sp.actorOf cred = some a)
    (tasks : List Task) (hh : Nat) : exec .full sp s (.amend cred tasks hh) = none := by
  have hn := hdisj cred (by simp [ha])
  simp [exec, Guards.full, hn]

/-- **T12c — a specification change requires re-admission**: after any change, the frozen mission's admission
is closed — no permit, old or new, admits anything under the changed contract version. A changed contract is
a NEW mission that must be frozen and run on its own. -/
theorem T12_change_requires_readmission {sp : Spec} {s s' : State} {cred : Nat} {tasks : List Task} {hh : Nat}
    (h : exec .full sp s (.amend cred tasks hh) = some s') (r : Req) : admission .full sp s' r ≠ .T := by
  intro hA
  simp [exec, Guards.full] at h; obtain ⟨_, rfl⟩ := h
  have := (admit_full_T hA)
  simp at this

end LegionCore
