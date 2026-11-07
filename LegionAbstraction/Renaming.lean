import LegionCore
/-!
# LegionAbstraction.Renaming — FORMAL-002 (M1): the decision depends only on the EQUALITY of identifiers

The runtime adapter (`lean_admission.build_payload`) maps every runtime identifier string to a natural number by one
per-call interner and claims: "equality of identifiers is preserved exactly and nothing else about them is used".
This file proves the second half of that claim for the exact function the decider binary evaluates
(`Main.decideLine`: closed set by `Journal.closedSet`, then `admission .full`): applying ANY injective renaming `f`
to every identifier field of the payload leaves the verdict and every named ground unchanged, and renames the
reported closed set by `f`.

Identifier fields (renamed): task ids, agent/credential ids, targets, permit pid/uid/wid/mission/cmd/nonce/actor,
effect fields, fenced commands, used nonces, contract identity, journal task/agent/effect/command/record/ref ids.
Numeric fields (NOT renamed): epochs, clock, freshness window, fault bound, contract version, report source, resource
keys/demands/capacities, booleans and kinds.
-/

namespace LegionAbstraction
open LegionCore LegionCore.Journal

/-- Injectivity (stated locally; the project has no Mathlib). -/
def Inj (f : Nat → Nat) : Prop := ∀ a b, f a = f b → a = b

section
variable (f : Nat → Nat)

def rnTask (t : Task) : Task := { t with id := f t.id, owner := f t.owner, deps := t.deps.map f, target := f t.target }
def rnPermit (p : Permit) : Permit :=
  { p with pid := f p.pid, uid := f p.uid, wid := f p.wid, mission := f p.mission, task := f p.task, cmd := f p.cmd,
           actor := f p.actor, target := f p.target, nonce := f p.nonce }
def rnEffect (e : Effect) : Effect :=
  { e with cmd := f e.cmd, task := f e.task, actor := f e.actor, pid := f e.pid, mission := f e.mission }
def rnReport (r : Report) : Report := { r with task := f r.task }
def rnPair (p : Nat × Nat) : Nat × Nat := (f p.1, f p.2)
def rnSpec (sp : Spec) : Spec :=
  { sp with mission := f sp.mission, tasks := sp.tasks.map (rnTask f), specAuthority := sp.specAuthority.map f,
            idents := sp.idents.map (rnPair f) }
def rnState (s : State) : State :=
  { s with uid := f s.uid, wid := f s.wid, issued := s.issued.map (rnPermit f), usedNonces := s.usedNonces.map f,
           fenced := s.fenced.map f, ledger := s.ledger.map (rnEffect f), verified := s.verified.map f,
           evidenced := s.evidenced.map f, closed := s.closed.map f, reports := s.reports.map (rnReport f),
           contract := s.contract.map (rnTask f), chash := f s.chash, plan := s.plan.map f }
def rnReq (r : Req) : Req :=
  { cred := f r.cred, claimed := f r.claimed, task := f r.task, target := f r.target, cmd := f r.cmd,
    permit := rnPermit f r.permit }
def rnJTask (t : JTask) : JTask := { t with id := f t.id, owner := f t.owner, deps := t.deps.map f }
def rnRec (r : Rec) : Rec :=
  { r with task := f r.task, agent := r.agent.map f, eff := f r.eff, cmd := f r.cmd, rid := f r.rid,
           refs := r.refs.map f }
def rnFS (s : FS) : FS :=
  { confirmed := s.confirmed.map f, sat := s.sat.map (fun p => (f p.1, p.2)),
    obsAll := s.obsAll.map (rnPair f), obsOk := s.obsOk.map (rnPair f),
    effects := s.effects.map (fun e => (f e.1, f e.2.1, f e.2.2)),
    receipts := s.receipts.map (fun e => (f e.1, f e.2.1, f e.2.2)),
    readbacks := s.readbacks.map (fun b => (b.1.map f, f b.2.1, f b.2.2)) }

/-- The exact computation of `Main.decideLine` after parsing (closed set recomputed by the proved fold). -/
def decision (sp : Spec) (s : State) (r : Req) (ts : List JTask) (rs : List Rec) : V :=
  admission .full sp { s with closed := closedSet ts rs } r

def grounds (sp : Spec) (s : State) (r : Req) (ts : List JTask) (rs : List Rec) : List (String × V) :=
  guards .full sp { s with closed := closedSet ts rs } r
end

/-! ## Basic transfer lemmas -/

theorem mem_map_inj {α} {g : α → α} (hg : ∀ x y, g x = g y → x = y) (l : List α) (a : α) :
    g a ∈ l.map g ↔ a ∈ l :=
  ⟨fun h => by obtain ⟨x, hx, e⟩ := List.mem_map.mp h; exact hg _ _ e ▸ hx, fun h => List.mem_map_of_mem h⟩

theorem capOf_rn (f : Nat → Nat) (sp : Spec) (k : Nat) : (rnSpec f sp).capOf k = sp.capOf k := rfl

section
variable {f : Nat → Nat} (hf : Inj f)
include hf

theorem beq_rn (a b : Nat) : (f a == f b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨hf a b, fun h => h ▸ rfl⟩

theorem eq_rn (a b : Nat) : f a = f b ↔ a = b := ⟨hf a b, fun h => h ▸ rfl⟩

theorem contains_rn (l : List Nat) (a : Nat) : (l.map f).contains (f a) = l.contains a := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem]
  exact mem_map_inj hf l a

theorem rnPermit_inj : ∀ p q, rnPermit f p = rnPermit f q → p = q := by
  intro p q h
  cases p; cases q
  simp only [rnPermit, Permit.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp [hf _ _ h1, hf _ _ h2, hf _ _ h3, hf _ _ h4, h5, hf _ _ h6, hf _ _ h7, hf _ _ h8, hf _ _ h9, hf _ _ h10]

theorem lookup_rn (k : Nat) (l : List (Nat × Nat)) : lookup (f k) (l.map (rnPair f)) = (lookup k l).map f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map, rnPair, lookup]
    by_cases h : a = k
    · subst h; simp
    · have : f a ≠ f k := fun e => h (hf _ _ e)
      simp [h, this, ih]

theorem actorOf_rn (sp : Spec) (c : Nat) : (rnSpec f sp).actorOf (f c) = (sp.actorOf c).map f :=
  lookup_rn hf c sp.idents

theorem task?_rn (sp : Spec) (t : Nat) : (rnSpec f sp).task? (f t) = (sp.task? t).map (rnTask f) := by
  simp only [Spec.task?, rnSpec, List.find?_map]
  congr 2
  funext x
  simp [rnTask, beq_rn hf]

theorem depsClosed_rn (s : State) (tk : Task) : depsClosed (rnState f s) (rnTask f tk) = depsClosed s tk := by
  simp [depsClosed, rnState, rnTask, Function.comp_def, eq_rn hf]

theorem votes_rn (sp : Spec) (s : State) (t : Nat) (v : V) :
    votes (rnSpec f sp) (rnState f s) (f t) v = votes sp s t v := by
  simp only [votes, rnState, rnSpec, List.filter_map, List.length_map]
  congr 2
  funext r
  simp only [Function.comp_apply, rnReport, beq_rn hf, fresh]
  rfl

theorem ztl_rn (sp : Spec) (s : State) (t : Nat) : ztl (rnSpec f sp) (rnState f s) (f t) = ztl sp s t := by
  simp only [ztl, votes_rn hf]
  rfl

theorem optmap_beq_some (o : Option Nat) (a : Nat) : (o.map f == some (f a)) = (o == some a) := by
  cases o <;> simp [beq_rn hf]

/-! ## M1a — every named guard, hence the verdict, is invariant -/

theorem guards_rn (g : Guards) (sp : Spec) (s : State) (r : Req) :
    guards g (rnSpec f sp) (rnState f s) (rnReq f r) = guards g sp s r := by
  have e1 : (rnSpec f sp).task? (rnReq f r).task = (sp.task? r.task).map (rnTask f) := task?_rn hf sp r.task
  have e2 : (rnSpec f sp).actorOf (rnReq f r).cred = (sp.actorOf r.cred).map f := actorOf_rn hf sp r.cred
  have e3 : (rnState f s).issued.contains (rnReq f r).permit = s.issued.contains r.permit := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact mem_map_inj (rnPermit_inj hf) _ _
  have e5 : (Option.map f (sp.actorOf r.cred) == some (rnReq f r).permit.actor) = (sp.actorOf r.cred == some r.permit.actor) :=
    optmap_beq_some hf _ _
  have e6 : (rnState f s).usedNonces.contains (rnReq f r).permit.nonce = s.usedNonces.contains r.permit.nonce :=
    contains_rn hf _ _
  have e7 : (rnState f s).fenced.contains (rnReq f r).cmd = s.fenced.contains r.cmd := contains_rn hf _ _
  have e8 : (rnState f s).ledger.any (fun e => e.cmd == (rnReq f r).cmd) = s.ledger.any (fun e => e.cmd == r.cmd) := by
    simp only [rnState, List.any_map]; congr 1; funext e; simp only [Function.comp_apply, rnEffect, rnReq, beq_rn hf]
  have e9 : (rnState f s).ledger.any (fun e => e.task == (rnReq f r).task) = s.ledger.any (fun e => e.task == r.task) := by
    simp only [rnState, List.any_map]; congr 1; funext e; simp only [Function.comp_apply, rnEffect, rnReq, beq_rn hf]
  have e10 : (rnState f s).closed.contains (rnReq f r).task = s.closed.contains r.task := contains_rn hf _ _
  have e11 : ztl (rnSpec f sp) (rnState f s) (rnReq f r).task = ztl sp s r.task := ztl_rn hf _ _ _
  have b1 : ((rnReq f r).permit.task == (rnReq f r).task) = (r.permit.task == r.task) := beq_rn hf _ _
  have b2 : ((rnReq f r).permit.cmd == (rnReq f r).cmd) = (r.permit.cmd == r.cmd) := beq_rn hf _ _
  have b3 : ((rnReq f r).permit.target == (rnReq f r).target) = (r.permit.target == r.target) := beq_rn hf _ _
  have b4 : ((rnReq f r).permit.uid == (rnState f s).uid) = (r.permit.uid == s.uid) := beq_rn hf _ _
  have b5 : ((rnReq f r).permit.wid == (rnState f s).wid) = (r.permit.wid == s.wid) := beq_rn hf _ _
  have b6 : ((rnReq f r).permit.mission == (rnState f s).chash) = (r.permit.mission == s.chash) := beq_rn hf _ _
  have b7 : ((rnState f s).chash == (rnSpec f sp).mission) = (s.chash == sp.mission) := beq_rn hf _ _
  have b8 : (rnReq f r).permit.epoch = r.permit.epoch := rfl
  have b9 : (rnState f s).epoch = s.epoch := rfl
  have b10 : (rnState f s).phase = s.phase := rfl
  have b11 : (rnState f s).cver = s.cver := rfl
  simp only [guards, e1, e2, e3, e5, e6, e7, e8, e9, e10, e11, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]
  cases sp.task? r.task with
  | none => cases sp.actorOf r.cred <;> rfl
  | some tk =>
    cases sp.actorOf r.cred with
    | none =>
      simp only [Option.map, depsClosed_rn hf]
      simp only [rnTask, rnReq, beq_rn hf, capOf_rn]
      rfl
    | some a =>
      simp only [Option.map, depsClosed_rn hf]
      simp only [rnTask, rnReq, beq_rn hf, capOf_rn]
      rfl

theorem admission_rn (g : Guards) (sp : Spec) (s : State) (r : Req) :
    admission g (rnSpec f sp) (rnState f s) (rnReq f r) = admission g sp s r := by
  simp only [admission, guards_rn hf]

end

end LegionAbstraction
