import LegionCore.SystemSafety
/-!
# LegionCore.Resources — T3 resource conservation over the generic capacity interface

`Spec.cap` / `Task.resKey` / `Task.demand` are the generic `Capacity` interface of SPEC §5: budgets,
inventory, partitions and rates are instances supplied as data. In the model the reservation and the commit
of one admitted action are a single atomic step (`actuate`), so `reserved = 0` between steps; the runtime's
two-phase reservation (R3–R5) is covered by the refinement argument (G3), not by this theorem.
-/

namespace LegionCore

/-- **T3 — Resource conservation.** In every reachable state, committed consumption never exceeds the
authorized capacity, for every resource key. -/
theorem T3_resource_conservation {sp : Spec} {uid wid : Nat} {s : State}
    (h : Reach .full sp uid wid s) (k : Nat) : s.used k ≤ sp.capOf k :=
  (reach_inv h).cap k

/-- An action whose demand would exceed remaining capacity is never admitted. -/
theorem T3_over_capacity_refused {sp : Spec} {s : State} {r : Req} {tk : Task}
    (htk : sp.task? r.task = some tk) (hover : sp.capOf tk.resKey < s.used tk.resKey + tk.demand) :
    admission .full sp s r ≠ .T := by
  intro hA
  obtain ⟨_, ⟨tk', _, htk', _, _, _, _, _, hcap, _⟩, _⟩ := admit_full_T hA
  rw [htk] at htk'; cases htk'; omega

end LegionCore
