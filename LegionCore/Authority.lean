import LegionCore.SystemSafety
/-!
# LegionCore.Authority — T1 admission soundness, T4 identity/authority isolation, T6 epoch safety
-/

namespace LegionCore

/-- Only `actuate`, and only with an admission verdict T, changes the effect ledger. -/
theorem exec_ledger {g : Guards} {sp : Spec} {s s' : State} {c : Cmd} (h : exec g sp s c = some s') :
    s'.ledger = s.ledger ∨ ∃ r, c = .actuate r ∧ admission g sp s r = .T ∧ s'.ledger = effectOf sp r :: s.ledger := by
  cases c with
  | actuate r =>
    right; simp only [exec] at h
    by_cases hA : admission g sp s r = .T
    · cases htk : sp.task? r.task with
      | none => simp [hA, htk] at h
      | some tk => simp [hA, htk] at h; subst h; exact ⟨r, rfl, hA, rfl⟩
    · simp [hA] at h
  | evidence t cred =>
    left; simp only [exec] at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h
  | close t =>
    left; simp only [exec] at h
    split at h
    · repeat' split at h
      all_goals first | (cases h; rfl) | cases h
    · cases h
  | start => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | terminate => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | bump => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | tick => left; simp only [exec] at h; cases h; rfl
  | crash => left; simp only [exec] at h; cases h; rfl
  | issue p => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | report r => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | fence c => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | readback t => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | amend cred tasks hh => left; simp only [exec] at h; split at h <;> cases h <;> rfl
  | replan cred plan => left; simp only [exec] at h; split at h <;> cases h <;> rfl

/-- **T1 — Admission soundness.** Every effect created by any transition was created by an `actuate` whose
Lean admission verdict was T in the pre-state, with an authority-issued permit at the current epoch, while
RUNNING, by the owner of the task as determined from the admitted credential. -/
theorem T1_admission_soundness {sp : Spec} {s s' : State} {c : Cmd} {e : Effect}
    (h : exec .full sp s c = some s') (he : e ∈ s'.ledger) (hn : e ∉ s.ledger) :
    ∃ r, c = .actuate r ∧ e = effectOf sp r ∧ admission .full sp s r = .T ∧
      r.permit ∈ s.issued ∧ r.permit.epoch = s.epoch ∧ s.phase = .running ∧
      ∃ tk a, sp.task? r.task = some tk ∧ sp.actorOf r.cred = some a ∧ tk.owner = a ∧ e.actor = a := by
  rcases exec_ledger h with hl | ⟨r, rfl, hA, hl⟩
  · rw [hl] at he; exact absurd he hn
  · rw [hl] at he
    rcases List.mem_cons.mp he with rfl | he
    · obtain ⟨hrun, ⟨tk, a, htk, ha, how, _⟩, hiss, _, _, _, _, hep, _⟩ := admit_full_T hA
      exact ⟨r, rfl, rfl, hA, hiss, hep, hrun, tk, a, htk, ha, how, by simp [effectOf, ha]⟩
    · exact absurd he hn

/-- **T4a — the caller-supplied agent id is never consulted.** -/
theorem T4_claimed_irrelevant (g : Guards) (sp : Spec) (s : State) (r : Req) (x : Nat) :
    admission g sp s { r with claimed := x } = admission g sp s r := rfl

/-- **T4b — naming another agent in the permit does not transfer its authority**: the permit's actor must be
the agent of the admitted credential. -/
theorem T4_permit_actor_bound {sp : Spec} {s : State} {r : Req} {a : Nat}
    (ha : sp.actorOf r.cred = some a) (hne : r.permit.actor ≠ a) : admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, ⟨tk, a', _, ha', _, _, _, _, _, hpa⟩, _⟩ := admit_full_T hA
  rw [ha] at ha'; cases ha'; exact hne hpa

/-- **T4c — isolation**: an admitted credential of agent `a` never admits an action on a task `a` does not own. -/
theorem T4_identity_isolation {sp : Spec} {s : State} {r : Req} {a : Nat}
    (ha : sp.actorOf r.cred = some a) (hown : ∀ tk, sp.task? r.task = some tk → tk.owner ≠ a) :
    admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, ⟨tk, a', htk, ha', how, _⟩, _⟩ := admit_full_T hA
  rw [ha] at ha'; cases ha'; exact hown tk htk how

/-- **T4d — an unadmitted credential admits nothing.** -/
theorem T4_no_credential {sp : Spec} {s : State} {r : Req} (ha : sp.actorOf r.cred = none) :
    admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, ⟨tk, a, _, ha', _⟩, _⟩ := admit_full_T hA
  rw [ha] at ha'; cases ha'

/-- **T6a — epoch binding at the commit boundary**: a new effect is admitted only with a permit of the CURRENT
epoch, attempt identity (`uid`) and world instance (`wid`), while RUNNING. -/
theorem T6_epoch_binding {sp : Spec} {s s' : State} {c : Cmd} {e : Effect}
    (h : exec .full sp s c = some s') (he : e ∈ s'.ledger) (hn : e ∉ s.ledger) :
    ∃ r, c = .actuate r ∧ r.permit.epoch = s.epoch ∧ r.permit.uid = s.uid ∧ r.permit.wid = s.wid ∧
      r.permit.mission = sp.mission ∧ s.phase = .running := by
  obtain ⟨r, rfl, _, hA, _⟩ := T1_admission_soundness h he hn
  obtain ⟨hrun, _, _, _, _, _, hmis, hep, hu, hw, _⟩ := admit_full_T hA
  exact ⟨r, rfl, hep, hu, hw, hmis, hrun⟩

/-- **T6b — admission is not transferable across epochs**: after ANY lifecycle transition (start, bump,
terminate), no permit issued before it can admit anything. -/
theorem T6_epoch_revocation {sp : Spec} {uid wid : Nat} {s s' : State} {c : Cmd}
    (hr : Reach .full sp uid wid s) (hc : c = .start ∨ c = .bump ∨ c = .terminate)
    (h : exec .full sp s c = some s') {r : Req} (hp : r.permit ∈ s.issued) : admission .full sp s' r ≠ .T := by
  intro hA
  have hle := ((reach_inv hr).issuedOk r.permit hp).1
  obtain ⟨_, _, _, _, _, _, _, hep, _⟩ := admit_full_T hA
  rcases hc with rfl | rfl | rfl <;> simp [exec] at h <;> obtain ⟨_, rfl⟩ := h <;> simp at hep <;> omega

/-- **T6c — no admission outside RUNNING** (registered, or terminal after key destruction). -/
theorem T6_not_running {sp : Spec} {s : State} {r : Req} (hp : s.phase ≠ .running) : admission .full sp s r ≠ .T :=
  fun hA => hp (admit_full_T hA).1

end LegionCore
