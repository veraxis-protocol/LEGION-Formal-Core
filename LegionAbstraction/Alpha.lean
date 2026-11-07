import LegionAbstraction.JournalRenaming
/-!
# LegionAbstraction.Alpha — FORMAL-002 (M0, M2, M3): the runtime-to-model abstraction α of the world commit boundary

`lean_admission.build_payload` (Python, NOT verified) builds the decider input from the runtime boundary state.
This file states the SHAPE of that map as Lean definitions over raw runtime identifiers (strings) and proves what a
verdict T computed on α's output means for the RAW runtime facts. Each hypothesis below is one property of the
Python serializer; FORMAL-002 validates each one executably (`alpha_shape_check.py`, randomized + replayed).

* M0  the per-call interner (first occurrence ↦ index + 1) is injective on the identifiers it has seen and never
      produces 0;
* M2  under α's shape, T implies that the runtime's own permit verification succeeded (`pv`) and that the single
      world-origin gate value (gate facts ⊓ action binding, computed in Python) was T;
* M3  T implies the raw facts about the raw runtime strings: the request is bound to its permit (task, command,
      target, actor = authenticated agent), the attempt identity and the contract identity match, the nonce and the
      command are fresh, no recorded native effect has this command or this task, and the task is a WRITE task of
      the requesting agent with exactly this target. Equalities need the encoding to be injective; freshness
      (disequalities) needs only that it is a function.
-/

namespace LegionAbstraction
open LegionCore LegionCore.Journal

/-! ## M0 — the interner -/

/-- Python `Interner.__call__`: an identifier's code is its first-occurrence index plus one. -/
def internAt {κ} [BEq κ] (seen : List κ) (k : κ) : Nat := seen.idxOf k + 1

theorem idxOf_inj {κ} [BEq κ] [LawfulBEq κ] : ∀ {l : List κ} {a b : κ}, a ∈ l → b ∈ l → l.idxOf a = l.idxOf b → a = b
  | [], _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | c :: l, a, b, ha, hb, h => by
    simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq] at h
    by_cases hca : c = a <;> by_cases hcb : c = b
    · exact hca.symm.trans hcb
    · simp [hca, hcb] at h; exact h
    · simp [hca, hcb] at h; exact h.symm
    · simp [hca, hcb] at h
      have ha' : a ∈ l := by cases List.mem_cons.mp ha with | inl e => exact absurd e.symm hca | inr m => exact m
      have hb' : b ∈ l := by cases List.mem_cons.mp hb with | inl e => exact absurd e.symm hcb | inr m => exact m
      exact idxOf_inj ha' hb' h

/-- **M0** — interning is injective on the seen identifiers. -/
theorem intern_inj {κ} [BEq κ] [LawfulBEq κ] {seen : List κ} {a b : κ} (ha : a ∈ seen) (hb : b ∈ seen)
    (h : internAt seen a = internAt seen b) : a = b :=
  idxOf_inj ha hb (Nat.add_right_cancel h)

theorem intern_pos {κ} [BEq κ] (seen : List κ) (k : κ) : 0 < internAt seen k := Nat.succ_pos _

/-! ## Raw runtime vocabulary (strings) and α -/

abbrev Key := String × String

structure RawPermit where
  pid : String
  uid : String
  wid : String
  mission : String
  epoch : Nat
  task : String
  cmd : String
  actor : String
  target : String
  nonce : String

structure RawEffect where
  cmd : String
  task : String
  actor : String
  epoch : Nat
  pid : String
  mission : String

structure RawReq where
  agent : String
  task : String
  target : String
  cmd : String
  permit : RawPermit

structure RawTask where
  id : String
  owner : String
  deps : List String
  write : Bool
  target : String

section
variable (enc : Key → Nat)

def aPermit (p : RawPermit) : Permit :=
  { pid := enc ("permit", p.pid), uid := enc ("uid", p.uid), wid := enc ("wid", p.wid), mission := enc ("mission", p.mission),
    epoch := p.epoch, task := enc ("task", p.task), cmd := enc ("cmd", p.cmd), actor := enc ("agent", p.actor),
    target := enc ("target", p.target), nonce := enc ("nonce", p.nonce) }

def aEffect (e : RawEffect) : Effect :=
  { cmd := enc ("cmd", e.cmd), task := enc ("task", e.task), actor := enc ("agent", e.actor), epoch := e.epoch,
    pid := enc ("permit", e.pid), mission := enc ("mission", e.mission) }

def aReq (r : RawReq) : Req :=
  { cred := enc ("agent", r.agent), claimed := enc ("agent", r.agent), task := enc ("task", r.task),
    target := enc ("target", r.target), cmd := enc ("cmd", r.cmd), permit := aPermit enc r.permit }

def aTask (t : RawTask) : Task :=
  { id := enc ("task", t.id), owner := enc ("agent", t.owner), deps := t.deps.map (fun d => enc ("task", d)),
    write := t.write, target := enc ("target", t.target), mandatory := true, resKey := 0, demand := 0 }
end

/-- The shape of `build_payload`'s output (one property per conjunct; each is checked executably). -/
structure AlphaShape (enc : Key → Nat) (sp : Spec) (s : State) (r : Req) (rr : RawReq) (tasks : List RawTask)
    (agents : List String) (ledger : List RawEffect) (nonces fenced : List String) (uid wid chash mission : String)
    (pv : Bool) (gv : V) : Prop where
  req      : r = aReq enc rr
  tasks    : sp.tasks = tasks.map (aTask enc)
  idents   : sp.idents = agents.map (fun a => (enc ("agent", a), enc ("agent", a)))
  mission  : sp.mission = enc ("mission", mission)
  f0       : sp.f = 0
  issued   : s.issued = (if pv then [r.permit] else [])
  reports  : s.reports = [{ source := 0, task := r.task, value := gv, time := 1 }]
  now      : s.now = 1
  ledger   : s.ledger = ledger.map (aEffect enc)
  nonces   : s.usedNonces = nonces.map (fun n => enc ("nonce", n))
  fenced   : s.fenced = fenced.map (fun c => enc ("cmd", c))
  uid      : s.uid = enc ("uid", uid)
  wid      : s.wid = enc ("wid", wid)
  chash    : s.chash = enc ("mission", chash)

/-! ## M2 -/

theorem votes_single (sp : Spec) (s : State) (t : Nat) (v gv : V) (hr : s.reports = [{ source := 0, task := t, value := gv, time := 1 }])
    (hn : s.now = 1) : votes sp s t v = if gv = v then 1 else 0 := by
  simp only [votes, hr, hn, fresh]
  cases gv <;> cases v <;> simp

/-- **M2** — under α's shape, a T verdict requires the runtime permit verification and the world gate value. -/
theorem alpha_T_requires {enc sp s r rr tasks agents ledger nonces fenced uid wid chash mission pv gv}
    (h : AlphaShape enc sp s r rr tasks agents ledger nonces fenced uid wid chash mission pv gv)
    {ts : List JTask} {rs : List Rec} (hT : decision sp s r ts rs = .T) : pv = true ∧ gv = .T := by
  have hT' : admission .full sp { s with closed := closedSet ts rs } r = .T := hT
  obtain ⟨_, _, hiss, _, _, _, _, _, _, _, _, _, _, _, _, hz, _, _⟩ := admit_full_T hT'
  dsimp only at hiss
  refine ⟨?_, ?_⟩
  · cases pv
    · simp [h.issued] at hiss
    · rfl
  · have hz' := T5_ztl_T_needs_seats hz
    have hv := votes_single sp { s with closed := closedSet ts rs } r.task .T gv h.reports h.now
    rw [hv, h.f0] at hz'
    by_cases hg : gv = .T
    · exact hg
    · simp [hg] at hz'

/-! ## M3 -/

theorem lookup_diag (enc : Key → Nat) (agents : List String) (k : Nat) (a : Nat)
    (h : lookup k (agents.map (fun x => (enc ("agent", x), enc ("agent", x)))) = some a) :
    a = k ∧ ∃ x ∈ agents, enc ("agent", x) = k := by
  induction agents with
  | nil => simp [lookup] at h
  | cons x l ih =>
    simp only [List.map, lookup] at h
    by_cases hx : enc ("agent", x) = k
    · simp [hx] at h; exact ⟨h.symm, x, List.mem_cons_self, hx⟩
    · simp [hx] at h
      obtain ⟨h1, y, hy, hy'⟩ := ih h
      exact ⟨h1, y, List.mem_cons_of_mem _ hy, hy'⟩

/-- **M3 — raw soundness of a T verdict.** -/
theorem alpha_sound {enc sp s r rr tasks agents ledger nonces fenced uid wid chash mission pv gv}
    (henc : ∀ a b, enc a = enc b → a = b)
    (h : AlphaShape enc sp s r rr tasks agents ledger nonces fenced uid wid chash mission pv gv)
    {ts : List JTask} {rs : List Rec} (hT : decision sp s r ts rs = .T) :
    pv = true ∧ gv = .T ∧
    rr.permit.task = rr.task ∧ rr.permit.cmd = rr.cmd ∧ rr.permit.target = rr.target ∧ rr.permit.actor = rr.agent ∧
    rr.agent ∈ agents ∧
    rr.permit.uid = uid ∧ rr.permit.wid = wid ∧ rr.permit.mission = mission ∧ chash = mission ∧
    rr.permit.nonce ∉ nonces ∧ rr.cmd ∉ fenced ∧ (∀ e ∈ ledger, e.cmd ≠ rr.cmd ∧ e.task ≠ rr.task) ∧
    (∃ t ∈ tasks, t.id = rr.task ∧ t.owner = rr.agent ∧ t.write = true ∧ t.target = rr.target) := by
  obtain ⟨hpv, hgv⟩ := alpha_T_requires h hT
  have hT' : admission .full sp { s with closed := closedSet ts rs } r = .T := hT
  obtain ⟨_, ⟨tk, a, htk, ha, hown, hw, htgt, _, _, hact⟩, _, hpt, hpc, hptg, hpm, _, hpu, hpw, hnon, hfen, hled, hled2,
    _, _, hch, _⟩ := admit_full_T hT'
  dsimp only at hpu hpw hnon hfen hled hled2 hch
  have hr := h.req
  rw [h.uid] at hpu; rw [h.wid] at hpw; rw [h.chash, h.mission] at hch; rw [h.mission] at hpm
  rw [h.nonces] at hnon; rw [h.fenced] at hfen; rw [h.ledger] at hled hled2
  simp only [Spec.actorOf, h.idents] at ha
  simp only [Spec.task?, h.tasks] at htk
  subst hr
  simp only [aReq, aPermit] at hpt hpc hptg hpm hpu hpw hnon hfen hled hled2 htk ha hact htgt
  have inj : ∀ {x y : Key}, enc x = enc y → x = y := fun e => henc _ _ e
  obtain ⟨ha1, x, hx, hxe⟩ := lookup_diag enc agents _ _ ha
  refine ⟨hpv, hgv, (Prod.mk.inj (inj hpt)).2, (Prod.mk.inj (inj hpc)).2, (Prod.mk.inj (inj hptg)).2,
    (Prod.mk.inj (inj (hact.trans ha1))).2, ((Prod.mk.inj (inj hxe)).2 ▸ hx), (Prod.mk.inj (inj hpu)).2,
    (Prod.mk.inj (inj hpw)).2, (Prod.mk.inj (inj hpm)).2, (Prod.mk.inj (inj hch)).2, ?_, ?_, ?_, ?_⟩
  · intro hm; exact hnon (List.mem_map_of_mem hm)
  · intro hm; exact hfen (List.mem_map_of_mem hm)
  · intro e he
    have h1 := hled (aEffect enc e) (List.mem_map_of_mem he)
    have h2 := hled2 (aEffect enc e) (List.mem_map_of_mem he)
    simp only [aEffect] at h1 h2
    exact ⟨fun c => h1 (by rw [c]), fun c => h2 (by rw [c])⟩
  · simp only [List.find?_map] at htk
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp htk
    have hmem := List.mem_of_find?_eq_some ht
    have hid := List.find?_some ht
    simp only [Function.comp_apply, aTask, beq_iff_eq] at hid
    refine ⟨t, hmem, (Prod.mk.inj (inj hid)).2, ?_, ?_, ?_⟩
    · have : enc ("agent", t.owner) = enc ("agent", rr.agent) := by
        simp only [aTask] at hown; rw [hown, ha1]
      exact (Prod.mk.inj (inj this)).2
    · simpa [aTask] using hw
    · simp only [aTask] at htgt; exact (Prod.mk.inj (inj htgt)).2

end LegionAbstraction
