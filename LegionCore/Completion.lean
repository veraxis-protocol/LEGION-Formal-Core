import LegionCore.Recovery
import LegionCore.Resources
/-!
# LegionCore.Completion — T2 causal preservation, T5 evidence non-promotion, T9 completion soundness,
T10 population independence
-/

namespace LegionCore

theorem depsClosed_mem {s : State} {tk : Task} (h : depsClosed s tk = true) : ∀ d ∈ tk.deps, d ∈ s.closed := by
  simpa [depsClosed] using h

/-! ## T2 — Causal preservation -/

/-- **T2a** — an effect is created only when every dependency of its task is CONFIRMED (closed) in the
pre-state. -/
theorem T2_effect_after_deps {sp : Spec} {s s' : State} {c : Cmd} {e : Effect}
    (h : exec .full sp s c = some s') (he : e ∈ s'.ledger) (hn : e ∉ s.ledger) :
    ∃ tk, sp.task? e.task = some tk ∧ ∀ d ∈ tk.deps, d ∈ s.closed := by
  obtain ⟨r, rfl, rfl, hA, _⟩ := T1_admission_soundness h he hn
  obtain ⟨_, ⟨tk, _, htk, _, _, _, _, hd, _⟩, _⟩ := admit_full_T hA
  exact ⟨tk, by simpa [effectOf] using htk, depsClosed_mem hd⟩

/-- **T2b** — closing evidence for a non-write obligation is accepted only while it is ELIGIBLE (all
dependencies confirmed); premature evidence is not recorded. -/
theorem T2_evidence_while_eligible {sp : Spec} {s s' : State} {t cred : Nat}
    (h : exec .full sp s (.evidence t cred) = some s') :
    ∃ tk, sp.task? t = some tk ∧ sp.actorOf cred = some tk.owner ∧ ∀ d ∈ tk.deps, d ∈ s.closed := by
  simp only [exec] at h
  cases htk : sp.task? t with
  | none => simp [htk] at h
  | some tk =>
    simp [htk, Guards.full] at h
    exact ⟨tk, rfl, h.1.1.1.2, depsClosed_mem (by simpa [depsClosed] using h.1.2)⟩

/-- **T2c** — an obligation is closed only after all its dependencies are closed. -/
theorem T2_close_after_deps {sp : Spec} {s s' : State} {t : Nat}
    (h : exec .full sp s (.close t) = some s') : ∃ tk, sp.task? t = some tk ∧ ∀ d ∈ tk.deps, d ∈ s.closed := by
  simp only [exec] at h
  cases htk : sp.task? t with
  | none => simp [htk] at h
  | some tk =>
    simp [htk, Guards.full] at h
    exact ⟨tk, rfl, depsClosed_mem (by simpa [depsClosed] using h.1.1)⟩

/-- **T2d** (invariant form) — in every reachable state every effect's dependencies are closed. -/
theorem T2_causal_invariant {sp : Spec} {uid wid : Nat} {s : State} (h : Reach .full sp uid wid s) :
    ∀ e ∈ s.ledger, ∃ tk, sp.task? e.task = some tk ∧ ∀ d ∈ tk.deps, d ∈ s.closed := by
  intro e he
  obtain ⟨tk, h1, _, h3⟩ := (reach_inv h).effectOk e he
  exact ⟨tk, h1, depsClosed_mem h3⟩

/-! ## T5 — Evidence non-promotion -/

/-- **T5a** — a stale (or future-dated) report never contributes a seat. -/
theorem T5_stale_no_seat (sp : Spec) (s : State) (r : Report) (t : Nat) (v : V) (hr : fresh sp s.now r = false) :
    votes sp { s with reports := r :: s.reports } t v = votes sp s t v := by
  simp [votes, hr]

/-- **T5b** — a Z (unknown / missing) report never contributes a T or F seat. -/
theorem T5_unknown_no_seat (sp : Spec) (s : State) (r : Report) (t : Nat) (v : V) (hz : r.value = .Z)
    (hv : v ≠ .Z) : votes sp { s with reports := r :: s.reports } t v = votes sp s t v := by
  have : (r.value == v) = false := by rw [hz]; cases v <;> simp_all
  simp [votes, this]

/-- **T5c** — the aggregate is order-independent (contrast: ZTL `ZLegion.merge` is order-dependent for ≥ 3
agents; LEGION does not use it). -/
theorem T5_order_independent (sp : Spec) (s s' : State) (hp : s.reports.Perm s'.reports) (hn : s.now = s'.now)
    (t : Nat) (v : V) : votes sp s t v = votes sp s' t v := by
  unfold votes; rw [hn]; exact (hp.filter _).length_eq

/-- **T5d** — a T verdict needs at least f + 1 seats for T and fewer than f + 1 for F (contradiction ⇒ not T). -/
theorem T5_ztl_T_needs_seats {sp : Spec} {s : State} {t : Nat} (h : ztl sp s t = .T) :
    sp.f + 1 ≤ votes sp s t .T ∧ votes sp s t .F < sp.f + 1 := by
  unfold ztl at h
  split at h
  · next hc => simpa using hc
  · split at h <;> cases h

theorem nodup_of_map {α β} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    exact ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map f h.2⟩

theorem map_source_nodup {L : List Report} {t : Nat} (hall : ∀ x ∈ L, x.task = t)
    (hk : (L.map (fun r => (r.source, r.task))).Nodup) : (L.map (fun r => r.source)).Nodup := by
  have : L.map (fun r => (r.source, r.task)) = (L.map (fun r => r.source)).map (fun x => (x, t)) := by
    rw [List.map_map]; exact List.map_congr_left (fun x hx => by simp [hall x hx])
  rw [this] at hk
  exact nodup_of_map _ hk

/-- **T5e — seats are distinct ORIGINS.** In every reachable state, a T verdict on task `t` is backed by at least
f + 1 pairwise-distinct sources each holding a fresh T report on `t`; reporters sharing one origin count once. -/
theorem T5_distinct_origins {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s) {t : Nat}
    (h : ztl sp s t = .T) :
    let L := s.reports.filter (fun r => r.task == t && r.value == .T && fresh sp s.now r)
    (L.map (fun r => r.source)).Nodup ∧ sp.f + 1 ≤ (L.map (fun r => r.source)).length := by
  intro L
  refine ⟨map_source_nodup (t := t) (fun x hx => by have hx2 := (List.mem_filter.mp hx).2; simp at hx2; exact hx2.1.1) ?_, ?_⟩
  · exact List.Nodup.sublist ((List.filter_sublist).map _) (reach_inv hr).reportsKeyed
  · rw [List.length_map]; exact (T5_ztl_T_needs_seats h).1

/-- **T5f — closure is never promoted without verification**: a closed WRITE obligation has an independently
read-back effect; verification is only reachable through an effect in the ledger. -/
theorem T5_closure_needs_verification {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s)
    {t : Nat} (ht : t ∈ s.closed) {tk : Task} (htk : sp.task? t = some tk) (hw : tk.write = true) :
    t ∈ s.verified ∧ ∃ e ∈ s.ledger, e.task = t := by
  obtain ⟨tk', h1, _, h3, _⟩ := (reach_inv hr).closedOk t ht
  rw [htk] at h1; cases h1
  exact ⟨h3 hw, (reach_inv hr).verifiedOk t (h3 hw)⟩

/-! ## T9 — Completion soundness -/

/-- The independent Judge's SPECIFICATION of a world PASS: every mandatory obligation closed. (The Python Judge
is frozen and not modelled; T9 is stated against this specification.) -/
def judgePass (sp : Spec) (s : State) : Prop := ∀ tk ∈ sp.tasks, tk.mandatory = true → tk.id ∈ s.closed

/-- **T9 — Completion soundness.** In every reachable state, a Judge PASS implies that every mandatory
obligation is closed with its dependencies closed, every WRITE obligation independently verified with an
effect in the ledger, and every non-write obligation backed by accepted closing evidence. -/
theorem T9_completion_soundness {sp : Spec} {uid wid : Nat} {s : State} (hr : Reach .full sp uid wid s)
    (hj : judgePass sp s) : ∀ tk ∈ sp.tasks, tk.mandatory = true →
      ∃ tk', sp.task? tk.id = some tk' ∧ tk.id ∈ s.closed ∧ (∀ d ∈ tk'.deps, d ∈ s.closed) ∧
        (tk'.write = true → tk.id ∈ s.verified ∧ ∃ e ∈ s.ledger, e.task = tk.id) ∧
        (tk'.write = false → tk.id ∈ s.evidenced) := by
  intro tk hm hmand
  have hc := hj tk hm hmand
  obtain ⟨tk', h1, h2, h3, h4⟩ := (reach_inv hr).closedOk tk.id hc
  exact ⟨tk', h1, hc, depsClosed_mem h2, fun hw => ⟨h3 hw, (reach_inv hr).verifiedOk _ (h3 hw)⟩, h4⟩

/-! ## T10 — Population independence -/

/-- **T10 — Population independence.** The system invariant (and hence T2–T9) holds for EVERY specification:
any finite set of agents and credentials, any finite task list and dependency relation, any capacities,
fault bound and freshness window. No statement in LegionCore fixes |agents| or a task name. -/
theorem T10_population_independence :
    ∀ (sp : Spec) (uid wid : Nat) (s : State), Reach .full sp uid wid s → Inv sp s :=
  fun _ _ _ _ h => reach_inv h

end LegionCore
