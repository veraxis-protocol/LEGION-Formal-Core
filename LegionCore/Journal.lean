import LegionCore.Admission
/-!
# LegionCore.Journal — causal closure computed IN LEAN from raw journal records (PE3 strengthening)

Before this module, the admission DEPS guard consumed a `closed` set produced by the Python `CausalRegistry`.
Here the STRUCTURAL closure semantics are a Lean fold over the raw, time-ordered journal (world log ∪ independent
readback ∪ gate refusals), with proofs:

* `confirmed_ordered`   — causal order: a task is confirmed only after every applicable dependency;
* `sat_witness`         — every satisfied (task, kind) has a matching journal record by the task owner;
* `fold_append_prefix`  — monotone: appending records never un-confirms anything (prefix-stable);
* `premature_never_counts` — a record ingested while its task was NOT eligible contributes nothing.

What remains a trusted per-record INPUT (computed by Python, listed explicitly): `Rec.ok` — the CONTENT verdict
(facts non-null / evidence predicates / success postcondition / recipient / wait event / reconcile found /
message content / receipt permit_verified / readback confirmed / epoch-identity of the record) and `JTask.na`
(activation: not applicable). Ordering, ownership, eligibility, kind mapping, the WRITE triplet identity match,
multi-kind completion, the refusal alternative and analysis-reference provenance are computed and proved here.
-/

namespace LegionCore
namespace Journal

inductive K where
  | read | analyze | communicate | wait | reconcile | done | refuse | write
  deriving DecidableEq, Repr

inductive RK where
  | obs | analysis | msg | wait | reconcile | done | refusal | effect | receipt | readback
  deriving DecidableEq, Repr

structure JTask where
  id    : Nat
  owner : Nat
  deps  : List Nat
  kinds : List K
  na    : Bool
  deriving DecidableEq, Repr

structure Rec where
  kind  : RK
  task  : Nat
  agent : Option Nat
  ok    : Bool
  eff   : Nat
  cmd   : Nat
  rid   : Nat
  refs  : List Nat
  deriving DecidableEq, Repr

structure FS where
  confirmed : List Nat
  sat       : List (Nat × K)
  obsAll    : List (Nat × Nat)          -- (rid, task) every observation seen
  obsOk     : List (Nat × Nat)          -- (rid, task) eligible, content-ok observations
  effects   : List (Nat × Nat × Nat)    -- (task, eff, cmd) accepted effect (at most one per task)
  receipts  : List (Nat × Nat × Nat)    -- (task, eff, cmd), by the owner or the system
  readbacks : List (Option Nat × Nat × Nat)  -- (task if the record names a known task, eff, cmd): independent readback
  deriving Repr

def FS.empty : FS := ⟨[], [], [], [], [], [], []⟩

def taskOf (ts : List JTask) (t : Nat) : Option JTask := ts.find? (fun x => x.id == t)

/-- A dependency counts if confirmed earlier, or if the dependency is not applicable. -/
def depOk (ts : List JTask) (conf : List Nat) (d : Nat) : Bool :=
  conf.contains d || (match taskOf ts d with | some dt => dt.na | none => false)

def eligible (ts : List JTask) (conf : List Nat) (tk : JTask) : Bool := tk.deps.all (depOk ts conf)

def kindOf : RK → Option K
  | .obs => some .read | .analysis => some .analyze | .msg => some .communicate | .wait => some .wait
  | .reconcile => some .reconcile | .done => some .done | _ => none

/-- Dependency chain (the task itself and transitive deps), bounded by `fuel` = number of tasks. -/
def chain (ts : List JTask) : Nat → List Nat → List Nat
  | 0, acc => acc
  | fuel + 1, acc =>
    let next := acc.flatMap (fun t => match taskOf ts t with | some tk => tk.deps | none => [])
    let acc' := acc ++ next.filter (fun t => !acc.contains t)
    if acc'.length == acc.length then acc else chain ts fuel acc'

/-- Analysis provenance (P0-12): ≥ 1 ref to an eligible confirmed in-chain observation, and no unknown or
out-of-chain ref (stale in-chain refs are tolerated). -/
def refsOk (ts : List JTask) (s : FS) (tk : JTask) (refs : List Nat) : Bool :=
  let ch := chain ts ts.length [tk.id]
  refs.any (fun r => s.obsOk.any (fun o => o.1 == r && ch.contains o.2)) &&
  refs.all (fun r => s.obsAll.any (fun o => o.1 == r && ch.contains o.2))

def ownerOk (tk : JTask) (a : Option Nat) : Bool := a == some tk.owner

/-- Ingest one record (no confirmation pass yet). -/
def ingest (ts : List JTask) (s : FS) (r : Rec) : FS :=
  match r.kind with
  | .receipt =>
    match taskOf ts r.task with
    | some tk => if r.ok && (r.agent == none || ownerOk tk r.agent)
                 then { s with receipts := (r.task, r.eff, r.cmd) :: s.receipts } else s
    | none => s
  | .readback =>
    if r.ok && r.agent == none then
      { s with readbacks := ((taskOf ts r.task).map (·.id), r.eff, r.cmd) :: s.readbacks } else s
  | .effect =>
    match taskOf ts r.task with
    | some tk =>
      if tk.kinds.contains .write && !tk.na && (r.agent == none || ownerOk tk r.agent) && r.ok
         && eligible ts s.confirmed tk && !(s.effects.any (fun e => e.1 == r.task))
      then { s with effects := (r.task, r.eff, r.cmd) :: s.effects } else s
    | none => s
  | .refusal =>
    match taskOf ts r.task with
    | some tk =>
      if tk.kinds.contains .refuse && !tk.na && r.ok && eligible ts s.confirmed tk
      then { s with sat := (r.task, .refuse) :: s.sat } else s
    | none => s
  | .obs =>
    let s1 := { s with obsAll := (r.rid, r.task) :: s.obsAll }
    match taskOf ts r.task with
    | some tk =>
      if ownerOk tk r.agent && !tk.na && r.ok && eligible ts s.confirmed tk then
        let s2 := { s1 with obsOk := (r.rid, r.task) :: s1.obsOk }
        if tk.kinds.contains .read then { s2 with sat := (r.task, .read) :: s2.sat } else s2
      else s1
    | none => s1
  | .analysis =>
    match taskOf ts r.task with
    | some tk =>
      if ownerOk tk r.agent && !tk.na && r.ok && tk.kinds.contains .analyze && eligible ts s.confirmed tk
         && refsOk ts s tk r.refs
      then { s with sat := (r.task, .analyze) :: s.sat } else s
    | none => s
  | k =>
    match kindOf k, taskOf ts r.task with
    | some kk, some tk =>
      if ownerOk tk r.agent && !tk.na && r.ok && tk.kinds.contains kk && eligible ts s.confirmed tk
      then { s with sat := (r.task, kk) :: s.sat } else s
    | _, _ => s

/-- WRITE is satisfied when the accepted effect has a receipt and a readback for the same (eff, cmd). -/
def writeDone (s : FS) (t : Nat) : Bool :=
  s.effects.any (fun e => e.1 == t && s.receipts.contains e &&
    s.readbacks.any (fun b => b.2 == e.2 && (b.1 == none || b.1 == some e.1)))

def kindDone (s : FS) (t : Nat) (k : K) : Bool :=
  if k == .write then writeDone s t else s.sat.contains (t, k)

def isDone (s : FS) (tk : JTask) : Bool :=
  s.sat.contains (tk.id, .refuse) && tk.kinds.contains .refuse ||
  (!tk.kinds.isEmpty && tk.kinds.all (kindDone s tk.id))

/-- Confirmation pass: append, in task order, every task that is done and not yet confirmed. -/
def confirmPass (ts : List JTask) (s : FS) : FS :=
  ts.foldl (fun acc tk => if !tk.na && isDone acc tk && !acc.confirmed.contains tk.id
                          then { acc with confirmed := acc.confirmed ++ [tk.id] } else acc) s

def step (ts : List JTask) (s : FS) (r : Rec) : FS := confirmPass ts (ingest ts s r)

def fold (ts : List JTask) (rs : List Rec) : FS := rs.foldl (step ts) FS.empty

/-- The closed set the admission DEPS guard uses: confirmed in the journal, or not applicable. -/
def closedSet (ts : List JTask) (rs : List Rec) : List Nat :=
  (fold ts rs).confirmed ++ (ts.filter (·.na)).map (·.id)

/-! ## Invariant and proofs -/

/-- Everything recorded as evidence was ELIGIBLE w.r.t. the CURRENT confirmed list (confirmed only grows). -/
structure Inv (ts : List JTask) (s : FS) : Prop where
  satElig : ∀ p ∈ s.sat, ∃ tk, taskOf ts p.1 = some tk ∧ eligible ts s.confirmed tk = true
  effElig : ∀ e ∈ s.effects, ∃ tk, taskOf ts e.1 = some tk ∧ eligible ts s.confirmed tk = true
  ordered : ∀ (pre : List Nat) (t : Nat) (post : List Nat), s.confirmed = pre ++ t :: post →
              ∃ tk, taskOf ts t = some tk ∧ eligible ts pre tk = true

theorem depOk_mono {ts : List JTask} {c c' : List Nat} (h : ∀ x, x ∈ c → x ∈ c') {d : Nat}
    (hd : depOk ts c d = true) : depOk ts c' d = true := by
  unfold depOk at *
  simp only [Bool.or_eq_true, List.contains_iff_mem] at *
  rcases hd with hd | hd
  · exact Or.inl (h d hd)
  · exact Or.inr hd

theorem eligible_mono {ts : List JTask} {c c' : List Nat} (h : ∀ x, x ∈ c → x ∈ c') {tk : JTask}
    (he : eligible ts c tk = true) : eligible ts c' tk = true := by
  unfold eligible at *
  simp only [List.all_eq_true] at *
  intro d hd; exact depOk_mono h (he d hd)

theorem inv_empty (ts : List JTask) : Inv ts FS.empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp; simp [FS.empty] at hp
  · intro e he; simp [FS.empty] at he
  · intro pre t post h; simp [FS.empty] at h

/-- `ingest` never touches `confirmed`, and every new sat/effect entry is eligible under it. -/
theorem ingest_confirmed (ts : List JTask) (s : FS) (r : Rec) : (ingest ts s r).confirmed = s.confirmed := by
  unfold ingest
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem inv_ingest {ts : List JTask} {s : FS} (hs : Inv ts s) (r : Rec) : Inv ts (ingest ts s r) := by
  have hc := ingest_confirmed ts s r
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    rw [hc]
    unfold ingest at hp
    split at hp
    · (repeat' split at hp) <;> exact hs.satElig p hp
    · (repeat' split at hp) <;> exact hs.satElig p hp
    · split at hp
      · (repeat' split at hp) <;> exact hs.satElig p hp
      · exact hs.satElig p hp
    · split at hp
      · next tk htk =>
        split at hp
        · next hcond =>
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp only [Bool.and_eq_true] at hcond
            exact ⟨tk, htk, hcond.2⟩
          · exact hs.satElig p hp
        · exact hs.satElig p hp
      · exact hs.satElig p hp
    · split at hp
      · next tk htk =>
        split at hp
        · next hcond =>
          simp only [Bool.and_eq_true] at hcond
          split at hp
          · simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact ⟨tk, htk, hcond.2⟩
            · exact hs.satElig p hp
          · exact hs.satElig p hp
        · exact hs.satElig p hp
      · exact hs.satElig p hp
    · split at hp
      · next tk htk =>
        split at hp
        · next hcond =>
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp only [Bool.and_eq_true] at hcond
            exact ⟨tk, htk, hcond.1.2⟩
          · exact hs.satElig p hp
        · exact hs.satElig p hp
      · exact hs.satElig p hp
    · split at hp
      · next kk tk _ htk =>
        split at hp
        · next hcond =>
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · simp only [Bool.and_eq_true] at hcond
            exact ⟨tk, htk, hcond.2⟩
          · exact hs.satElig p hp
        · exact hs.satElig p hp
      · exact hs.satElig p hp
  · intro e he
    rw [hc]
    unfold ingest at he
    split at he
    · (repeat' split at he) <;> exact hs.effElig e he
    · (repeat' split at he) <;> exact hs.effElig e he
    · split at he
      · next tk htk =>
        split at he
        · next hcond =>
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · simp only [Bool.and_eq_true] at hcond
            exact ⟨tk, htk, hcond.1.2⟩
          · exact hs.effElig e he
        · exact hs.effElig e he
      · exact hs.effElig e he
    · split at he
      · (repeat' split at he) <;> exact hs.effElig e he
      · exact hs.effElig e he
    · split at he
      · split at he
        · (repeat' split at he) <;> exact hs.effElig e he
        · exact hs.effElig e he
      · exact hs.effElig e he
    · split at he
      · (repeat' split at he) <;> exact hs.effElig e he
      · exact hs.effElig e he
    · split at he
      · (repeat' split at he) <;> exact hs.effElig e he
      · exact hs.effElig e he
  · intro pre t post h; rw [hc] at h; exact hs.ordered pre t post h

/-! ### Confirmation pass: only `confirmed` changes, and only by appending eligible tasks -/

def cstep (ts : List JTask) (acc : FS) (tk : JTask) : FS :=
  if !tk.na && isDone acc tk && !acc.confirmed.contains tk.id
  then { acc with confirmed := acc.confirmed ++ [tk.id] } else acc

theorem confirmPass_eq (ts : List JTask) (s : FS) : confirmPass ts s = ts.foldl (cstep ts) s := rfl

theorem cstep_fields (ts : List JTask) (acc : FS) (tk : JTask) :
    (cstep ts acc tk).sat = acc.sat ∧ (cstep ts acc tk).effects = acc.effects ∧
    (cstep ts acc tk).receipts = acc.receipts ∧ (cstep ts acc tk).readbacks = acc.readbacks ∧
    (cstep ts acc tk).obsOk = acc.obsOk ∧ (cstep ts acc tk).obsAll = acc.obsAll := by
  unfold cstep; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cstep_prefix (ts : List JTask) (acc : FS) (tk : JTask) :
    ∃ ex, (cstep ts acc tk).confirmed = acc.confirmed ++ ex := by
  unfold cstep; split
  · exact ⟨[tk.id], rfl⟩
  · exact ⟨[], by simp⟩

theorem cfold_fields (ts : List JTask) : ∀ (l : List JTask) (acc : FS),
    (l.foldl (cstep ts) acc).sat = acc.sat ∧ (l.foldl (cstep ts) acc).effects = acc.effects ∧
    (l.foldl (cstep ts) acc).receipts = acc.receipts ∧ (l.foldl (cstep ts) acc).readbacks = acc.readbacks ∧
    (l.foldl (cstep ts) acc).obsOk = acc.obsOk ∧ (l.foldl (cstep ts) acc).obsAll = acc.obsAll
  | [], acc => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | tk :: l, acc => by
    simp only [List.foldl]
    have ih := cfold_fields ts l (cstep ts acc tk)
    have hc := cstep_fields ts acc tk
    rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2] at ih
    exact ih

theorem cfold_prefix (ts : List JTask) : ∀ (l : List JTask) (acc : FS),
    ∃ extra, (l.foldl (cstep ts) acc).confirmed = acc.confirmed ++ extra
  | [], acc => ⟨[], by simp⟩
  | tk :: l, acc => by
    simp only [List.foldl]
    obtain ⟨ex, hex⟩ := cfold_prefix ts l (cstep ts acc tk)
    obtain ⟨e1, h1⟩ := cstep_prefix ts acc tk
    exact ⟨e1 ++ ex, by rw [hex, h1]; simp⟩

theorem snoc_split {l pre post : List Nat} {x t : Nat} (h : l ++ [x] = pre ++ t :: post) :
    (post = [] ∧ pre = l ∧ t = x) ∨ (∃ post', post = post' ++ [x] ∧ l = pre ++ t :: post') := by
  rcases List.eq_nil_or_concat post with rfl | ⟨L, b, rfl⟩
  · left
    have := List.append_inj' h rfl
    exact ⟨rfl, this.1.symm, by simpa using this.2.symm⟩
  · right
    have h' : l ++ [x] = (pre ++ t :: L) ++ [b] := by rw [h]; simp
    have := List.append_inj' h' rfl
    have hb : x = b := by simpa using this.2
    exact ⟨L, by rw [hb]; simp, this.1⟩

/-- A done task was eligible with respect to the CURRENT confirmed list. -/
theorem done_eligible {ts : List JTask} {s : FS} (hs : Inv ts s) {tk : JTask} (hd : isDone s tk = true) :
    ∃ tk', taskOf ts tk.id = some tk' ∧ eligible ts s.confirmed tk' = true := by
  unfold isDone at hd
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hd
  rcases hd with ⟨hr, _⟩ | ⟨hne, hall⟩
  · exact hs.satElig _ hr
  · cases hk : tk.kinds with
    | nil => simp [hk] at hne
    | cons k ks =>
      have hk1 := (List.all_eq_true.mp hall) k (by simp [hk])
      unfold kindDone at hk1
      split at hk1
      · unfold writeDone at hk1
        obtain ⟨e, he, hcond⟩ := List.any_eq_true.mp hk1
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨tk', h1, h2⟩ := hs.effElig e he
        exact ⟨tk', hcond.1.1 ▸ h1, h2⟩
      · simp only [List.contains_iff_mem] at hk1
        exact hs.satElig _ hk1

theorem inv_cfold (ts : List JTask) : ∀ (l : List JTask) (acc : FS), Inv ts acc → Inv ts (l.foldl (cstep ts) acc)
  | [], acc, h => h
  | tk :: l, acc, h => by
    simp only [List.foldl]
    apply inv_cfold ts l
    unfold cstep
    split
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have mono : ∀ x, x ∈ acc.confirmed → x ∈ acc.confirmed ++ [tk.id] := fun x hx => List.mem_append_left _ hx
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨tk', h1, h2⟩ := h.satElig p hp
        exact ⟨tk', h1, eligible_mono mono h2⟩
      · intro e he
        obtain ⟨tk', h1, h2⟩ := h.effElig e he
        exact ⟨tk', h1, eligible_mono mono h2⟩
      · intro pre t post hsplit
        rcases snoc_split hsplit with ⟨_, rfl, rfl⟩ | ⟨post', _, hl⟩
        · exact done_eligible h hc.1.2
        · exact h.ordered pre t post' hl
    · exact h

theorem inv_step {ts : List JTask} {s : FS} (hs : Inv ts s) (r : Rec) : Inv ts (step ts s r) := by
  unfold step; rw [confirmPass_eq]; exact inv_cfold ts ts _ (inv_ingest hs r)

theorem inv_foldl (ts : List JTask) : ∀ (rs : List Rec) (s : FS), Inv ts s → Inv ts (rs.foldl (step ts) s)
  | [], s, h => h
  | r :: rs, s, h => by simp only [List.foldl]; exact inv_foldl ts rs _ (inv_step h r)

theorem inv_fold (ts : List JTask) (rs : List Rec) : Inv ts (fold ts rs) := inv_foldl ts rs _ (inv_empty ts)

/-! ### J1 — causal order of confirmation -/

/-- **J1 (causal order).** Whatever the journal, a task is confirmed only after every one of its dependencies
is confirmed EARLIER in the confirmation order, or is not applicable. -/
theorem confirmed_ordered (ts : List JTask) (rs : List Rec) {pre : List Nat} {t : Nat} {post : List Nat}
    (h : (fold ts rs).confirmed = pre ++ t :: post) :
    ∃ tk, taskOf ts t = some tk ∧ ∀ d ∈ tk.deps, d ∈ pre ∨ ∃ dt, taskOf ts d = some dt ∧ dt.na = true := by
  obtain ⟨tk, h1, h2⟩ := (inv_fold ts rs).ordered pre t post h
  refine ⟨tk, h1, fun d hd => ?_⟩
  unfold eligible at h2
  have := (List.all_eq_true.mp h2) d hd
  unfold depOk at this
  simp only [Bool.or_eq_true, List.contains_iff_mem] at this
  rcases this with h | h
  · exact Or.inl h
  · right; revert h; cases taskOf ts d <;> simp

/-! ### J2 — every piece of evidence has a witness record in the journal -/

def kmatch : RK → K → Bool
  | .obs, .read | .analysis, .analyze | .msg, .communicate | .wait, .wait | .reconcile, .reconcile
  | .done, .done | .refusal, .refuse => true
  | _, _ => false

def SatW (ts : List JTask) (p : Nat × K) (r : Rec) : Prop :=
  r.task = p.1 ∧ r.ok = true ∧ kmatch r.kind p.2 = true ∧
  ∃ tk, taskOf ts p.1 = some tk ∧ (r.kind = .refusal ∨ r.agent = some tk.owner)

def EffW (e : Nat × Nat × Nat) (r : Rec) : Prop :=
  r.kind = .effect ∧ r.task = e.1 ∧ r.eff = e.2.1 ∧ r.cmd = e.2.2 ∧ r.ok = true

theorem ingest_sat_new {ts : List JTask} {s : FS} {r : Rec} {p : Nat × K} (h : p ∈ (ingest ts s r).sat) :
    p ∈ s.sat ∨ SatW ts p r := by
  unfold ingest at h
  split at h
  · (repeat' split at h) <;> exact Or.inl h
  · (repeat' split at h) <;> exact Or.inl h
  · split at h
    · (repeat' split at h) <;> exact Or.inl h
    · exact Or.inl h
  · next hk =>
    split at h
    · next tk htk =>
      split at h
      · next hc =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp only [Bool.and_eq_true] at hc
          exact Or.inr ⟨rfl, hc.1.2, by simp [hk, kmatch], tk, htk, Or.inl hk⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  · next hk =>
    split at h
    · next tk htk =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        split at h
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr ⟨rfl, hc.1.2, by simp [hk, kmatch], tk, htk,
              Or.inr (by simpa [ownerOk] using hc.1.1.1)⟩
          · exact Or.inl h
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  · next hk =>
    split at h
    · next tk htk =>
      split at h
      · next hc =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp only [Bool.and_eq_true] at hc
          exact Or.inr ⟨rfl, hc.1.1.1.2, by simp [hk, kmatch], tk, htk,
            Or.inr (by simpa [ownerOk] using hc.1.1.1.1.1)⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  · split at h
    · next kk tk hkk htk =>
      split at h
      · next hc =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp only [Bool.and_eq_true] at hc
          have km : ∀ rk, kindOf rk = some kk → kmatch rk kk = true := by
            intro rk; cases rk <;> cases kk <;> simp [kindOf, kmatch]
          exact Or.inr ⟨rfl, hc.1.1.2, km _ hkk, tk, htk, Or.inr (by simpa [ownerOk] using hc.1.1.1.1)⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h

theorem ingest_eff_new {ts : List JTask} {s : FS} {r : Rec} {e : Nat × Nat × Nat}
    (h : e ∈ (ingest ts s r).effects) : e ∈ s.effects ∨ EffW e r := by
  unfold ingest at h
  split at h
  · (repeat' split at h) <;> exact Or.inl h
  · (repeat' split at h) <;> exact Or.inl h
  · next hk =>
    split at h
    · split at h
      · next hc =>
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp only [Bool.and_eq_true] at hc
          exact Or.inr ⟨hk, rfl, rfl, rfl, hc.1.1.2⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  · split at h
    · (repeat' split at h) <;> exact Or.inl h
    · exact Or.inl h
  · split at h
    · split at h
      · (repeat' split at h) <;> exact Or.inl h
      · exact Or.inl h
    · exact Or.inl h
  · split at h
    · (repeat' split at h) <;> exact Or.inl h
    · exact Or.inl h
  · split at h
    · (repeat' split at h) <;> exact Or.inl h
    · exact Or.inl h

theorem foldl_witness (ts : List JTask) : ∀ (rs : List Rec) (s : FS),
    (∀ p ∈ (rs.foldl (step ts) s).sat, p ∈ s.sat ∨ ∃ r ∈ rs, SatW ts p r) ∧
    (∀ e ∈ (rs.foldl (step ts) s).effects, e ∈ s.effects ∨ ∃ r ∈ rs, EffW e r)
  | [], s => ⟨fun p hp => Or.inl hp, fun e he => Or.inl he⟩
  | r :: rs, s => by
    simp only [List.foldl]
    obtain ⟨ih1, ih2⟩ := foldl_witness ts rs (step ts s r)
    have hf := cfold_fields ts ts (ingest ts s r)
    refine ⟨fun p hp => ?_, fun e he => ?_⟩
    · rcases ih1 p hp with h | ⟨r', hr', hw⟩
      · unfold step at h; rw [confirmPass_eq, hf.1] at h
        rcases ingest_sat_new h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨r, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hw⟩
    · rcases ih2 e he with h | ⟨r', hr', hw⟩
      · unfold step at h; rw [confirmPass_eq, hf.2.1] at h
        rcases ingest_eff_new h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨r, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hw⟩

/-- **J2 (evidence witnesses).** Every satisfied (task, kind) of the fold is backed by a record in the journal for
that task, of the matching kind, with an accepted content verdict, by the task owner (refusals: by the gate);
every accepted effect is backed by an effect record with the same identity. -/
theorem sat_witness (ts : List JTask) (rs : List Rec) :
    (∀ p ∈ (fold ts rs).sat, ∃ r ∈ rs, SatW ts p r) ∧ (∀ e ∈ (fold ts rs).effects, ∃ r ∈ rs, EffW e r) := by
  obtain ⟨h1, h2⟩ := foldl_witness ts rs FS.empty
  exact ⟨fun p hp => (h1 p hp).resolve_left (by simp [FS.empty]),
         fun e he => (h2 e he).resolve_left (by simp [FS.empty])⟩

/-! ### J3 — monotone: appending records never un-confirms -/

theorem step_prefix (ts : List JTask) (s : FS) (r : Rec) : ∃ ex, (step ts s r).confirmed = s.confirmed ++ ex := by
  unfold step; rw [confirmPass_eq]
  obtain ⟨ex, hex⟩ := cfold_prefix ts ts (ingest ts s r)
  exact ⟨ex, by rw [hex, ingest_confirmed]⟩

theorem foldl_prefix (ts : List JTask) : ∀ (rs : List Rec) (s : FS),
    ∃ ex, (rs.foldl (step ts) s).confirmed = s.confirmed ++ ex
  | [], s => ⟨[], by simp⟩
  | r :: rs, s => by
    simp only [List.foldl]
    obtain ⟨e1, h1⟩ := step_prefix ts s r
    obtain ⟨e2, h2⟩ := foldl_prefix ts rs (step ts s r)
    exact ⟨e1 ++ e2, by rw [h2, h1]; simp⟩

/-- **J3 (monotonicity).** The confirmation order of a journal is a prefix of the confirmation order of any
extension of that journal: later records can only confirm more, never retract a confirmation. -/
theorem fold_append_prefix (ts : List JTask) (rs rs' : List Rec) :
    ∃ ex, (fold ts (rs ++ rs')).confirmed = (fold ts rs).confirmed ++ ex := by
  unfold fold; rw [List.foldl_append]; exact foldl_prefix ts rs' _

/-! ### J4 — premature evidence never counts -/

/-- **J4 (non-promotion of premature evidence).** A record ingested while its task is NOT eligible adds nothing to
the satisfied kinds, the accepted effects or the confirmed observations — even if its dependencies close later. -/
theorem premature_never_counts {ts : List JTask} {s : FS} {r : Rec} {tk : JTask} (htk : taskOf ts r.task = some tk)
    (hne : eligible ts s.confirmed tk = false) :
    (ingest ts s r).sat = s.sat ∧ (ingest ts s r).effects = s.effects ∧ (ingest ts s r).obsOk = s.obsOk := by
  unfold ingest
  split <;> (try simp only [htk, hne, Bool.and_false, Bool.false_and]) <;>
    (try split) <;> (try simp_all) <;> (try split) <;> simp_all

/-! ### J5 — link to the admission DEPS guard -/

/-- **J5.** Every member of the closed set the decision consumes is either confirmed by the journal fold (hence,
by J1/J2, causally ordered and witnessed by owner records) or declared not applicable. -/
theorem closed_grounded (ts : List JTask) (rs : List Rec) {d : Nat} (h : d ∈ closedSet ts rs) :
    d ∈ (fold ts rs).confirmed ∨ ∃ dt ∈ ts, dt.id = d ∧ dt.na = true := by
  unfold closedSet at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · right
    obtain ⟨dt, hdt, rfl⟩ := List.mem_map.mp h
    exact ⟨dt, (List.mem_filter.mp hdt).1, rfl, (List.mem_filter.mp hdt).2⟩

/-- **J6 (decision-level grounding).** If the compiled decision — admission over the closed set computed by the
journal fold — is T, then every dependency of the admitted task is confirmed by the journal fold (causally
ordered J1, witnessed J2) or declared not applicable. -/
theorem decision_deps_grounded {sp : Spec} {s : State} {r : Req} (ts : List JTask) (rs : List Rec)
    (h : admission .full sp { s with closed := closedSet ts rs } r = .T) :
    ∃ tk, sp.task? r.task = some tk ∧
      ∀ d ∈ tk.deps, d ∈ (fold ts rs).confirmed ∨ ∃ dt ∈ ts, dt.id = d ∧ dt.na = true := by
  obtain ⟨_, ⟨tk, _, htk, _, _, _, _, hd, _⟩, _⟩ := admit_full_T h
  refine ⟨tk, htk, fun d hdm => closed_grounded ts rs ?_⟩
  have hd' : ∀ x, x ∈ tk.deps → x ∈ closedSet ts rs := by simpa [depsClosed] using hd
  exact hd' d hdm

end Journal
end LegionCore