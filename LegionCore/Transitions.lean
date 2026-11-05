import LegionCore.Admission
/-!
# LegionCore.Transitions — the complete transition system of SPEC §3

Every runtime transition class appears as a `Cmd`. Nondeterminism (arbitrary interleaving of agents, the
authority, the world, observers, crashes) is the free choice of the next `Cmd`. Agents and observers are
Byzantine: `issue`, `report`, `actuate`, `fence`, `evidence` accept ANY arguments and only the guards decide.

| Cmd | SPEC |
|---|---|
| start / terminate / bump | R1 lifecycle (every transition bumps the epoch; terminal destroys issued permits) |
| issue p | R2 permit issuance (RUNNING, current epoch/uid/wid) |
| report r | E9 evidence report (Byzantine sources; one entry per (source, task), latest wins) |
| tick | clock |
| actuate r | X1 — the ONLY effect-creating transition (P7 boundary + R3–R5 commit) |
| fence c | recovery: TOMBSTONE/fence of a command with no effect |
| readback t | E8 independent readback → VERIFIED |
| evidence t cred | E1–E7 non-write closing evidence by the owner while ELIGIBLE |
| close t | C1–C5 obligation closure |
| crash | crash-stop / lost reply / restart of any process (A-P1): no state change |
| amend cred tasks h | specification change ATTEMPT by any credential (T11/T12): needs `specAuthority`; creates a new
  contract version AND a new epoch, revoking every issued permit (re-admission required) |
| replan cred plan | plan adaptation by an admitted execution agent (T15): never touches the contract |
-/

namespace LegionCore

inductive Cmd where
  | start
  | terminate
  | bump
  | tick
  | issue (p : Permit)
  | report (r : Report)
  | actuate (r : Req)
  | fence (cmd : Nat)
  | readback (t : Nat)
  | evidence (t : Nat) (cred : Nat)
  | close (t : Nat)
  | crash
  | amend (cred : Nat) (tasks : List Task) (h : Nat)
  | replan (cred : Nat) (plan : List Nat)
  deriving Repr

def effectOf (sp : Spec) (r : Req) : Effect :=
  { cmd := r.cmd, task := r.task, actor := (sp.actorOf r.cred).getD 0, epoch := r.permit.epoch,
    pid := r.permit.pid, mission := r.permit.mission }

def bumpUse (u : Nat → Nat) (key d : Nat) : Nat → Nat := fun k => if k = key then u k + d else u k

def exec (g : Guards) (sp : Spec) (s : State) : Cmd → Option State
  | .start => if s.phase == .registered then some { s with phase := .running, epoch := s.epoch + 1 } else none
  | .terminate =>
      if s.phase == .running then some { s with phase := .terminal, epoch := s.epoch + 1, issued := [] } else none
  | .bump => if s.phase == .running then some { s with epoch := s.epoch + 1 } else none
  | .tick => some { s with now := s.now + 1 }
  | .issue p =>
      if s.phase == .running && p.epoch == s.epoch && p.uid == s.uid && p.wid == s.wid
      then some { s with issued := p :: s.issued } else none
  | .report r =>
      if r.time == s.now
      then some { s with reports := r :: s.reports.filter (fun x => !(x.source == r.source && x.task == r.task)) }
      else none
  | .actuate r =>
      if admission g sp s r == .T then
        match sp.task? r.task with
        | some tk => some { s with ledger := effectOf sp r :: s.ledger,
                                   usedNonces := r.permit.nonce :: s.usedNonces,
                                   used := bumpUse s.used tk.resKey tk.demand }
        | none => none
      else none
  | .fence c =>
      if g.fenceProof && s.ledger.any (fun e => e.cmd == c) then none else some { s with fenced := c :: s.fenced }
  | .readback t => if s.ledger.any (fun e => e.task == t) then some { s with verified := t :: s.verified } else none
  | .evidence t cred =>
      match sp.task? t with
      | some tk =>
          if !tk.write && sp.actorOf cred == some tk.owner && s.phase == .running
             && (!g.closeDeps || depsClosed s tk)
          then some { s with evidenced := t :: s.evidenced } else none
      | none => none
  | .close t =>
      match sp.task? t with
      | some tk =>
          if (!g.closeDeps || depsClosed s tk)
             && (if tk.write then (!g.readback || s.verified.contains t) else s.evidenced.contains t)
          then some { s with closed := t :: s.closed } else none
      | none => none
  | .crash => some s
  | .amend cred tasks h =>
      if !g.specAuth || sp.specAuthority.contains cred
      then some { s with contract := tasks, chash := h, cver := s.cver + 1, epoch := s.epoch + 1, issued := [] }
      else none
  | .replan cred plan => if (sp.actorOf cred).isSome then some { s with plan := plan } else none

/-- Reachable states of the full transition system from `init`. -/
inductive Reach (g : Guards) (sp : Spec) (uid wid : Nat) : State → Prop where
  | init : Reach g sp uid wid (init sp uid wid)
  | step {s s' : State} (c : Cmd) : Reach g sp uid wid s → exec g sp s c = some s' → Reach g sp uid wid s'

/-- Executable run (used for concrete witnesses). -/
def run (g : Guards) (sp : Spec) (s : State) : List Cmd → Option State
  | []      => some s
  | c :: cs => match exec g sp s c with
               | some s' => run g sp s' cs
               | none    => none

theorem run_reach {g : Guards} {sp : Spec} {uid wid : Nat} :
    ∀ (cs : List Cmd) {s s' : State}, Reach g sp uid wid s → run g sp s cs = some s' → Reach g sp uid wid s'
  | [], s, s', hs, h => by simp [run] at h; exact h ▸ hs
  | c :: cs, s, s', hs, h => by
      simp only [run] at h
      cases hc : exec g sp s c with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some s1 => rw [hc] at h; exact run_reach cs (Reach.step c hs hc) h

end LegionCore
