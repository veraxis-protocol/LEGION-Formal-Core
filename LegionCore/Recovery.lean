import LegionCore.Authority
/-!
# LegionCore.Recovery — T7 logical exactly-once, T8 recovery preservation
-/

namespace LegionCore

/-- **T7 — Logical exactly-once.** In every reachable state: each logical command (mission, task) has at most
one effect — even across retries with fresh command ids and epochs; each command id has at most one effect;
and no effect ever carries a fenced (TOMBSTONEd) command id. -/
theorem T7_exactly_once {sp : Spec} {uid wid : Nat} {s : State} (h : Reach .full sp uid wid s) :
    (∀ t, (s.ledger.filter (fun e => e.task == t)).length ≤ 1) ∧
    (∀ c, (s.ledger.filter (fun e => e.cmd == c)).length ≤ 1) ∧
    (∀ e ∈ s.ledger, e.cmd ∉ s.fenced) :=
  let i := reach_inv h; ⟨i.oncePerTask, i.oncePerCmd, i.notFenced⟩

/-- **T8a — Recovery preservation.** The full system invariant (T2–T7 and closure soundness) is preserved by
every transition, including fence/TOMBSTONE, readback/reconcile, retry, crash and lost reply. -/
theorem T8_recovery_preservation {sp : Spec} {s s' : State} {c : Cmd} (hs : Inv sp s)
    (h : exec .full sp s c = some s') : Inv sp s' := inv_step hs h

/-- **T8b — a retry after an effect is refused** (UNKNOWN outcome resolved by reconcile cannot re-execute). -/
theorem T8_retry_after_effect_refused {sp : Spec} {s : State} {r : Req} {e : Effect}
    (he : e ∈ s.ledger) (ht : e.task = r.task) : admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htask, _⟩ := admit_full_T hA
  exact htask e he ht

/-- **T8c — a fenced command is never executable.** -/
theorem T8_fenced_never_executes {sp : Spec} {s : State} {r : Req} (hf : r.cmd ∈ s.fenced) :
    admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfen, _⟩ := admit_full_T hA
  exact hfen hf

/-- **T8d — fencing requires proof of no effect**: a fence transition never fences an executed command. -/
theorem T8_fence_requires_no_effect {sp : Spec} {s s' : State} {c : Nat}
    (h : exec .full sp s (.fence c) = some s') : ∀ e ∈ s.ledger, e.cmd ≠ c := by
  simp [exec, Guards.full] at h; exact h.1

/-- **T8e — crash / lost reply is a stutter**: it changes nothing the Core relies on. -/
theorem T8_crash_stutter (g : Guards) (sp : Spec) (s : State) : exec g sp s .crash = some s := rfl

end LegionCore
