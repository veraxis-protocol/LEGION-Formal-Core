import LegionCore.State
/-!
# LegionCore.Admission — evidence aggregation and the admission decision `admission : Spec → State → Req → V`

`admission` is the function executed by the runtime decision binary (`legion_decide`, Main.lean). It is the strong
Kleene conjunction of named guards; only `T` admits.
-/

namespace LegionCore

/-- A report counts only inside its freshness window (stale and future-dated reports are ignored). -/
def fresh (sp : Spec) (now : Nat) (r : Report) : Bool := r.time ≤ now && now ≤ r.time + sp.maxAge

/-- Seats for value `v` on task `t`: fresh entries with that value. Entries are unique per (source, task)
(`reports_keyed`, SystemSafety), so this counts distinct ORIGINS, never reporters. -/
def votes (sp : Spec) (s : State) (t : Nat) (v : V) : Nat :=
  (s.reports.filter (fun r => r.task == t && r.value == v && fresh sp s.now r)).length

/-- The ztl-swarm threshold rule (`ZSwarm.verdict`: earned iff ≥ f + 1 seats, opposite not earned). -/
def ztl (sp : Spec) (s : State) (t : Nat) : V :=
  if sp.f + 1 ≤ votes sp s t .T && votes sp s t .F < sp.f + 1 then .T
  else if sp.f + 1 ≤ votes sp s t .F && votes sp s t .T < sp.f + 1 then .F
  else .Z

def depsClosed (s : State) (tk : Task) : Bool := tk.deps.all (fun d => s.closed.contains d)

/-- The named guards. A disabled guard reads T (used only by countermodels). -/
def guards (g : Guards) (sp : Spec) (s : State) (r : Req) : List (String × V) :=
  let p := r.permit
  [ ("RUNNING",   if !g.running || s.phase == .running then .T else .F),
    ("IDENTITY",  if !g.identity then .T else (match sp.actorOf r.cred with | some _ => .T | none => .Z)),
    ("OWNER",     if !g.owner then .T else
                    (match sp.task? r.task, sp.actorOf r.cred with
                     | some tk, some a => if tk.owner == a then .T else .F
                     | none, _ => .F
                     | some _, none => .Z)),
    ("TARGET",    if !g.target then .T else
                    (match sp.task? r.task with
                     | some tk => if tk.write && tk.target == r.target then .T else .F
                     | none => .F)),
    ("PERMIT",    if !g.permit then .T else
                    if s.issued.contains p && p.task == r.task && p.cmd == r.cmd && p.target == r.target
                       && sp.actorOf r.cred == some p.actor then .T else .F),
    ("EPOCH",     if !g.epoch then .T else
                    if p.epoch == s.epoch && p.uid == s.uid && p.wid == s.wid then .T else .F),
    ("NONCE",     if !g.nonce then .T else if s.usedNonces.contains p.nonce then .F else .T),
    ("FRESH_CMD", if !g.freshCmd then .T else
                    if s.fenced.contains r.cmd || s.ledger.any (fun e => e.cmd == r.cmd) then .F else .T),
    ("ONCE",      if !g.once then .T else
                    if s.ledger.any (fun e => e.task == r.task) || s.closed.contains r.task then .F else .T),
    ("DEPS",      if !g.deps then .T else
                    (match sp.task? r.task with
                     | some tk => if depsClosed s tk then .T else .Z
                     | none => .F)),
    ("CAPACITY",  if !g.cap then .T else
                    (match sp.task? r.task with
                     | some tk => if s.used tk.resKey + tk.demand ≤ sp.capOf tk.resKey then .T else .F
                     | none => .F)),
    ("ZTL",       if !g.ztl then .T else ztl sp s r.task),
    ("CONTRACT",  if !g.contract then .T else
                    if p.mission == s.chash && s.chash == sp.mission && s.cver == 0 then .T else .F) ]

def admission (g : Guards) (sp : Spec) (s : State) (r : Req) : V := kandAll ((guards g sp s r).map Prod.snd)

/-- The admission verdict is T exactly when every named guard is T. -/
theorem admit_T_iff (g : Guards) (sp : Spec) (s : State) (r : Req) :
    admission g sp s r = .T ↔ ∀ x ∈ guards g sp s r, x.2 = .T := by
  unfold admission
  rw [kandAll_T]
  constructor
  · intro h x hx; exact h x.2 (List.mem_map_of_mem hx)
  · intro h v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact h x hx

/-- **Semantic characterization** of a full-Core admission: every condition the runtime boundary must enforce. -/
theorem admit_full_T {sp : Spec} {s : State} {r : Req} (h : admission .full sp s r = .T) :
    s.phase = .running ∧
    (∃ tk a, sp.task? r.task = some tk ∧ sp.actorOf r.cred = some a ∧ tk.owner = a ∧ tk.write = true ∧
      tk.target = r.target ∧ depsClosed s tk = true ∧ s.used tk.resKey + tk.demand ≤ sp.capOf tk.resKey ∧
      r.permit.actor = a) ∧
    r.permit ∈ s.issued ∧ r.permit.task = r.task ∧ r.permit.cmd = r.cmd ∧ r.permit.target = r.target ∧
    r.permit.mission = sp.mission ∧
    r.permit.epoch = s.epoch ∧ r.permit.uid = s.uid ∧ r.permit.wid = s.wid ∧
    r.permit.nonce ∉ s.usedNonces ∧
    r.cmd ∉ s.fenced ∧ (∀ e ∈ s.ledger, e.cmd ≠ r.cmd) ∧
    (∀ e ∈ s.ledger, e.task ≠ r.task) ∧ r.task ∉ s.closed ∧
    ztl sp s r.task = .T ∧ s.chash = sp.mission ∧ s.cver = 0 := by
  rw [admit_T_iff] at h
  simp [guards, Guards.full] at h
  cases htk : sp.task? r.task with
  | none => simp [htk] at h
  | some tk =>
    cases ha : sp.actorOf r.cred with
    | none => simp [htk, ha] at h
    | some a =>
      simp [htk, ha] at h
      obtain ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6, h7, h8, h10⟩, ⟨h11, h12, h13⟩, h14, ⟨h15, h16⟩,
        ⟨h17, h18⟩, h19, h20, h21, h22, h23, h24⟩ := h
      exact ⟨h1, ⟨tk, a, rfl, rfl, h2, h3, h4, h19, h20, h10.symm⟩, h5, h6, h7, h8, h22.trans h23, h11, h12, h13,
        h14, h15, fun e he => h16 e he, fun e he => h17 e he, h18, h21, h23, h24⟩

end LegionCore
