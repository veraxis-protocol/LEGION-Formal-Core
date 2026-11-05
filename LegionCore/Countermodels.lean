import LegionCore.Completion
/-!
# LegionCore.Countermodels — non-vacuity

1. **Liveness witnesses** (the full Core is not vacuous): concrete runs of the FULL Core reach a Judge PASS with
   exactly one effect — for a 2-agent and a 100-agent population (T10).
2. **Countermodels** (each premise is necessary): for each theorem family, dropping its guard makes the
   prohibited state reachable, while the SAME command sequence under the full Core never reaches it.

All checks are closed `Bool` computations evaluated by the kernel (`decide`); `check_sound` turns them into
reachability statements.
-/

namespace LegionCore
namespace Witness

def tA : Task := { id := 1, owner := 10, deps := [], write := false, target := 0, mandatory := true,
                   resKey := 0, demand := 0 }
def tB : Task := { id := 2, owner := 20, deps := [1], write := true, target := 5, mandatory := true,
                   resKey := 0, demand := 3 }

def mkSpec (cap : Nat) (extra : List (Nat × Nat)) : Spec :=
  { mission := 7, tasks := [tA, tB], specAuthority := [900], idents := [(100, 10), (200, 20)] ++ extra, cap := [(0, cap)],
    f := 0, maxAge := 10 }

def sp2 : Spec := mkSpec 5 []
/-- 100 agents: the two workers plus 98 standby credentials. -/
def sp100 : Spec := mkSpec 5 ((List.range 98).map (fun i => (1000 + i, 5000 + i)))

def p1 : Permit := { pid := 1, uid := 1, wid := 2, mission := 7, epoch := 1, task := 2, cmd := 9, actor := 20,
                     target := 5, nonce := 1 }
def rq (p : Permit) (cmd : Nat := 9) (cred : Nat := 200) : Req :=
  { cred, claimed := 20, task := 2, target := 5, cmd, permit := p }
def rep : Report := { source := 1, task := 2, value := .T, time := 0 }

def check (g : Guards) (sp : Spec) (cs : List Cmd) (viol : State → Bool) : Bool :=
  match run g sp (init sp 1 2) cs with
  | some s => viol s
  | none   => false

theorem check_sound {g : Guards} {sp : Spec} {cs : List Cmd} {viol : State → Bool}
    (h : check g sp cs viol = true) : ∃ s, Reach g sp 1 2 s ∧ viol s = true := by
  unfold check at h
  split at h
  · next s hs => exact ⟨s, run_reach cs Reach.init hs, h⟩
  · cases h

def judgePassB (sp : Spec) (s : State) : Bool := sp.tasks.all (fun tk => !tk.mandatory || s.closed.contains tk.id)

def happy : List Cmd :=
  [.start, .report rep, .evidence 1 100, .close 1, .issue p1, .actuate (rq p1), .crash, .readback 2, .close 2]

/-! ## 1. Liveness: the full Core reaches a Judge PASS with exactly one effect -/

theorem live_2_agents : check .full sp2 happy (fun s => judgePassB sp2 s && s.ledger.length == 1) = true := by
  decide
theorem live_100_agents : check .full sp100 happy (fun s => judgePassB sp100 s && s.ledger.length == 1) = true := by
  decide

/-! ## 2. Countermodels: each guard is necessary -/

def anyEffectOn (s : State) (t : Nat) : Bool := s.ledger.any (fun e => e.task == t)

-- T1: drop the PERMIT premise → an effect without any authority-issued permit.
def p99 : Permit := { p1 with pid := 99 }
def cmT1 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .actuate (rq p99)]
def vT1 (s : State) : Bool := s.ledger.any (fun e => !(s.issued.any (fun p => p.pid == e.pid)))
theorem cm_T1 : check { permit := false } sp2 cmT1 vT1 = true := by decide
theorem cm_T1_full : check .full sp2 cmT1 vT1 = false := by decide

-- T2: drop DEPS → the write executes before its predecessor is confirmed.
def cmT2 : List Cmd := [.start, .report rep, .issue p1, .actuate (rq p1)]
def vT2 (s : State) : Bool := anyEffectOn s 2 && !s.closed.contains 1
theorem cm_T2 : check { deps := false } sp2 cmT2 vT2 = true := by decide
theorem cm_T2_full : check .full sp2 cmT2 vT2 = false := by decide

-- T3: drop CAPACITY → consumption exceeds capacity (demand 3 > capacity 2).
def spCap2 : Spec := mkSpec 2 []
def cmT3 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p1, .actuate (rq p1)]
def vT3 (s : State) : Bool := decide (spCap2.capOf 0 < s.used 0)
theorem cm_T3 : check { cap := false } spCap2 cmT3 vT3 = true := by decide
theorem cm_T3_full : check .full spCap2 cmT3 vT3 = false := by decide

-- T4: drop OWNER → agent 10 (credential 100) executes agent 20's task.
def p10 : Permit := { p1 with pid := 4, actor := 10 }
def cmT4 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p10, .actuate (rq p10 9 100)]
def vT4 (s : State) : Bool := s.ledger.any (fun e => e.task == 2 && e.actor != 20)
theorem cm_T4 : check { owner := false } sp2 cmT4 vT4 = true := by decide
theorem cm_T4_full : check .full sp2 cmT4 vT4 = false := by decide

-- T5a: drop ZTL → an effect with no fresh evidence seat at all.
def cmT5 : List Cmd := [.start, .evidence 1 100, .close 1, .issue p1, .actuate (rq p1)]
def vT5 (s : State) : Bool := anyEffectOn s 2 && votes sp2 s 2 .T == 0
theorem cm_T5 : check { ztl := false } sp2 cmT5 vT5 = true := by decide
theorem cm_T5_full : check .full sp2 cmT5 vT5 = false := by decide

-- T5b / T9: drop READBACK → a WRITE obligation closes (Judge PASS) with no effect at all.
def cmT9 : List Cmd := [.start, .evidence 1 100, .close 1, .close 2]
def vT9 (s : State) : Bool := judgePassB sp2 s && s.ledger.isEmpty
theorem cm_T9 : check { readback := false } sp2 cmT9 vT9 = true := by decide
theorem cm_T9_full : check .full sp2 cmT9 vT9 = false := by decide

-- T6: drop EPOCH → a permit issued in epoch 1 is used after the epoch moved to 2.
def cmT6 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p1, .bump, .actuate (rq p1)]
def vT6 (s : State) : Bool := s.ledger.any (fun e => e.epoch != s.epoch)
theorem cm_T6 : check { epoch := false } sp2 cmT6 vT6 = true := by decide
theorem cm_T6_full : check .full sp2 cmT6 vT6 = false := by decide

-- T7: drop ONCE → a retry with a NEW command id and NEW permit executes the same logical command twice
-- (per-command idempotency and nonce burning alone are insufficient).
def spCap10 : Spec := mkSpec 10 []
def p2 : Permit := { p1 with pid := 2, cmd := 10, nonce := 2 }
def cmT7 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p1, .actuate (rq p1),
                        .issue p2, .actuate (rq p2 10)]
def vT7 (s : State) : Bool := decide (2 ≤ (s.ledger.filter (fun e => e.task == 2)).length)
theorem cm_T7 : check { once := false } spCap10 cmT7 vT7 = true := by decide
theorem cm_T7_full : check .full spCap10 cmT7 vT7 = false := by decide

-- T8: drop FENCE-PROOF in recovery → an executed command is TOMBSTONEd (fenced) after its effect.
def cmT8 : List Cmd := [.start, .report rep, .evidence 1 100, .close 1, .issue p1, .actuate (rq p1), .fence 9]
def vT8 (s : State) : Bool := s.ledger.any (fun e => s.fenced.contains e.cmd)
theorem cm_T8 : check { fenceProof := false } sp2 cmT8 vT8 = true := by decide
theorem cm_T8_full : check .full sp2 cmT8 vT8 = false := by decide

end Witness
end LegionCore
