import LegionCore.Transitions
/-!
# LegionCore.SystemSafety — the system invariant and its preservation by EVERY transition

`Inv` is proved for every reachable state of the full Core (`reach_inv`), by induction over arbitrary
interleavings of all `Cmd`s — including recovery (fence, readback, retry with a new command) and crash/lost
reply. The theorem families T1–T10 (Authority, Resources, Recovery, Completion) are corollaries.
-/

namespace LegionCore

theorem depsClosed_mono {s s' : State} {tk : Task} (h : ∀ x, x ∈ s.closed → x ∈ s'.closed)
    (hd : depsClosed s tk = true) : depsClosed s' tk = true := by
  simp [depsClosed] at *
  intro d hdm; exact h d (hd d hdm)

structure Inv (sp : Spec) (s : State) : Prop where
  cap         : ∀ k, s.used k ≤ sp.capOf k
  oncePerTask : ∀ t, (s.ledger.filter (fun e => e.task == t)).length ≤ 1
  oncePerCmd  : ∀ c, (s.ledger.filter (fun e => e.cmd == c)).length ≤ 1
  notFenced   : ∀ e ∈ s.ledger, e.cmd ∉ s.fenced
  effectOk    : ∀ e ∈ s.ledger, ∃ tk, sp.task? e.task = some tk ∧ tk.owner = e.actor ∧ depsClosed s tk = true
  verifiedOk  : ∀ t ∈ s.verified, ∃ e ∈ s.ledger, e.task = t
  closedOk    : ∀ t ∈ s.closed, ∃ tk, sp.task? t = some tk ∧ depsClosed s tk = true ∧
                  (tk.write = true → t ∈ s.verified) ∧ (tk.write = false → t ∈ s.evidenced)
  evidencedOk : ∀ t ∈ s.evidenced, ∃ tk, sp.task? t = some tk ∧ tk.write = false
  issuedOk    : ∀ p ∈ s.issued, p.epoch ≤ s.epoch ∧ p.uid = s.uid ∧ p.wid = s.wid
  terminalOk  : s.phase = .terminal → s.issued = []
  reportsKeyed : (s.reports.map (fun r => (r.source, r.task))).Nodup
  bound       : ∀ e ∈ s.ledger, e.mission = sp.mission
  frozen      : s.cver = 0 → s.contract = sp.tasks ∧ s.chash = sp.mission

theorem inv_init (sp : Spec) (uid wid : Nat) : Inv sp (init sp uid wid) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init]

/-- Adding an element that does not satisfy `p` keeps the filter. -/
theorem filter_cons_false {α} (p : α → Bool) (x : α) (l : List α) (h : p x = false) :
    (x :: l).filter p = l.filter p := by
  rw [List.filter_cons]; simp [h]

theorem inv_step {sp : Spec} {s s' : State} {c : Cmd} (hs : Inv sp s) (h : exec .full sp s c = some s') :
    Inv sp s' := by
  cases c with
  | start =>
    simp [exec] at h; obtain ⟨hp, rfl⟩ := h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, fun p hp' => by have := hs.issuedOk p hp'; exact ⟨show p.epoch ≤ s.epoch + 1 by omega, this.2⟩,
      by simp, hs.reportsKeyed, hs.bound, hs.frozen⟩
  | terminate =>
    simp [exec] at h; obtain ⟨hp, rfl⟩ := h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, by simp, by simp, hs.reportsKeyed, hs.bound, hs.frozen⟩
  | bump =>
    simp [exec] at h; obtain ⟨hp, rfl⟩ := h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, fun p hp' => by have := hs.issuedOk p hp'; exact ⟨show p.epoch ≤ s.epoch + 1 by omega, this.2⟩,
      by simp [hp], hs.reportsKeyed, hs.bound, hs.frozen⟩
  | tick =>
    simp [exec] at h; subst h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩
  | crash =>
    simp [exec] at h; subst h; exact hs
  | issue p =>
    simp [exec] at h; obtain ⟨⟨⟨⟨hp, he⟩, hu⟩, hw⟩, rfl⟩ := h
    refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, ?_, ?_, hs.reportsKeyed, hs.bound, hs.frozen⟩
    · intro q hq; simp at hq
      rcases hq with rfl | hq
      · exact ⟨by simp [he], hu, hw⟩
      · exact hs.issuedOk q hq
    · intro ht; simp [hp] at ht
  | report r =>
    simp [exec] at h; obtain ⟨hr, rfl⟩ := h
    refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, hs.issuedOk, hs.terminalOk, ?_, hs.bound, hs.frozen⟩
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨x, hx, hxk⟩ := List.mem_map.mp hm
      have := (List.mem_filter.mp hx).2
      simp at hxk; simp [hxk.1, hxk.2] at this
    · exact List.Nodup.sublist ((List.filter_sublist).map _) hs.reportsKeyed
  | fence cmd =>
    simp [exec, Guards.full] at h; obtain ⟨hn, rfl⟩ := h
    refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, ?_, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩
    intro e he hm; simp at hm
    rcases hm with hm | hm
    · exact hn e he hm
    · exact hs.notFenced e he hm
  | readback t =>
    simp [exec] at h; obtain ⟨⟨e0, he0, ht⟩, rfl⟩ := h
    refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, ?_, ?_,
      hs.evidencedOk, hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩
    · intro t' ht'; simp at ht'
      rcases ht' with rfl | ht'
      · exact ⟨e0, he0, ht⟩
      · exact hs.verifiedOk t' ht'
    · intro t' ht'
      obtain ⟨tk, h1, h2, h3, h4⟩ := hs.closedOk t' ht'
      exact ⟨tk, h1, h2, fun hw => List.mem_cons_of_mem _ (h3 hw), h4⟩
  | evidence t cred =>
    simp only [exec] at h
    cases htk : sp.task? t with
    | none => simp [htk] at h
    | some tk =>
      simp [htk, Guards.full] at h; obtain ⟨⟨⟨⟨hw, ha⟩, hp⟩, hd⟩, rfl⟩ := h
      refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, ?_, ?_,
        hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩
      · intro t' ht'
        obtain ⟨tk', h1, h2, h3, h4⟩ := hs.closedOk t' ht'
        exact ⟨tk', h1, h2, h3, fun hw' => List.mem_cons_of_mem _ (h4 hw')⟩
      · intro t' ht'; simp at ht'
        rcases ht' with rfl | ht'
        · exact ⟨tk, htk, hw⟩
        · exact hs.evidencedOk t' ht'
  | close t =>
    simp only [exec] at h
    cases htk : sp.task? t with
    | none => simp [htk] at h
    | some tk =>
      simp [htk, Guards.full] at h; obtain ⟨⟨hd, hk⟩, rfl⟩ := h
      have mono : ∀ x, x ∈ s.closed → x ∈ t :: s.closed := fun x hx => List.mem_cons_of_mem _ hx
      refine ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, ?_, hs.verifiedOk, ?_,
        hs.evidencedOk, hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩
      · intro e he
        obtain ⟨tk', h1, h2, h3⟩ := hs.effectOk e he
        exact ⟨tk', h1, h2, depsClosed_mono (s' := { s with closed := t :: s.closed }) mono h3⟩
      · intro t' ht'; simp at ht'
        rcases ht' with rfl | ht'
        · refine ⟨tk, htk, depsClosed_mono (s' := { s with closed := t' :: s.closed }) mono hd, ?_, ?_⟩
          · intro hw; simp [hw] at hk; exact hk
          · intro hw; simp [hw] at hk; exact hk
        · obtain ⟨tk', h1, h2, h3, h4⟩ := hs.closedOk t' ht'
          exact ⟨tk', h1, depsClosed_mono (s' := { s with closed := t :: s.closed }) mono h2, h3, h4⟩
  | actuate r =>
    simp only [exec] at h
    by_cases hA : admission .full sp s r = .T
    · cases htk : sp.task? r.task with
      | none => simp [hA, htk] at h
      | some tk =>
        simp [hA, htk] at h; subst h
        obtain ⟨_, ⟨tk0, a, htk0, ha, how, _, _, hdep, hcap, _⟩, _, _, _, _, hmis, _, _, _, _, hfen, hcmd,
          htask, _, _⟩ := admit_full_T hA
        rw [htk] at htk0; cases htk0
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs.closedOk, hs.evidencedOk, hs.issuedOk, hs.terminalOk,
          hs.reportsKeyed, ?_, hs.frozen⟩
        · intro k; simp only [bumpUse]; split
          · next hk => subst hk; exact hcap
          · exact hs.cap k
        · intro t
          by_cases ht : r.task = t
          · subst ht
            rw [List.filter_cons]
            have : s.ledger.filter (fun e => e.task == r.task) = [] :=
              List.filter_eq_nil_iff.mpr (fun y hy => by simpa using htask y hy)
            simp [effectOf, this]
          · rw [filter_cons_false _ _ _ (by simp [effectOf, ht])]; exact hs.oncePerTask t
        · intro c
          by_cases hc : r.cmd = c
          · subst hc
            rw [List.filter_cons]
            have : s.ledger.filter (fun e => e.cmd == r.cmd) = [] :=
              List.filter_eq_nil_iff.mpr (fun y hy => by simpa using hcmd y hy)
            simp [effectOf, this]
          · rw [filter_cons_false _ _ _ (by simp [effectOf, hc])]; exact hs.oncePerCmd c
        · intro e he; simp at he
          rcases he with rfl | he
          · simpa [effectOf] using hfen
          · exact hs.notFenced e he
        · intro e he; simp at he
          rcases he with rfl | he
          · exact ⟨tk, by simpa [effectOf] using htk, by simp [effectOf, ha, how], hdep⟩
          · exact hs.effectOk e he
        · intro t ht
          obtain ⟨e, he, het⟩ := hs.verifiedOk t ht
          exact ⟨e, List.mem_cons_of_mem _ he, het⟩
        · intro e he; simp at he
          rcases he with rfl | he
          · simpa [effectOf] using hmis
          · exact hs.bound e he
    · simp [hA] at h
  | amend cred tasks hh =>
    simp [exec, Guards.full] at h; obtain ⟨_, rfl⟩ := h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, by simp, by simp, hs.reportsKeyed, hs.bound, by simp⟩
  | replan cred plan =>
    simp [exec] at h; obtain ⟨_, rfl⟩ := h
    exact ⟨hs.cap, hs.oncePerTask, hs.oncePerCmd, hs.notFenced, hs.effectOk, hs.verifiedOk, hs.closedOk,
      hs.evidencedOk, hs.issuedOk, hs.terminalOk, hs.reportsKeyed, hs.bound, hs.frozen⟩

/-- **T8 (Recovery preservation) / system safety**: the invariant holds in every reachable state, under arbitrary
interleavings of all transitions, including fence/TOMBSTONE, readback/reconcile, retry, crash and lost reply. -/
theorem reach_inv {sp : Spec} {uid wid : Nat} {s : State} (h : Reach .full sp uid wid s) : Inv sp s := by
  induction h with
  | init => exact inv_init sp uid wid
  | step c _ hx ih => exact inv_step ih hx

end LegionCore
