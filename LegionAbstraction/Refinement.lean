import LegionAbstraction.Alpha
/-!
# LegionAbstraction.Refinement — FORMAL-003: runtime steps of the qualified execution boundary refine model steps

**World commit boundary** (`world_server._actuate` + `LeanGatedWorld`). A runtime step is recorded as its decider input
(α-encoded: spec, boundary state, journal, request), its outcome, and the NATIVE_EFFECT records it appended
(α-encoded). The *boundary discipline* is what the runtime enforces (FORMAL-001: a new effect only with a single-use
ticket minted after `legion_decide` answered T for exactly this action; the effect record carries exactly the request's
command/task/agent/permit epoch/permit id/mission). Uncertain outcomes (lost reply, failed finalize, crash after the
effect) are effect-creating outcomes: the effect is durable even though the caller cannot know it.

* RF1  every disciplined runtime step is a step of the model (`exec .full`): `actuate r` when it created an effect,
       the stutter `crash` otherwise, with exactly the runtime's ledger delta and nonce consumption;
* RF2  over a trace of disciplined steps with log continuity, every runtime effect was admitted by the full Core in its
       pre-state, and the runtime ledger never holds two effects of one task (from an initially empty ledger);
* RF3  **external-effect uncertainty** (Commerce Gateway): over ANY trace of the gateway's effect lifecycle and for
       EVERY resolution of the provider's uncertain outcomes, each effect id has at most one create dispatch and at most
       one capture dispatch, every dispatch is preceded by a Lean-T attestation for that effect's exact intent in the
       same step, and a provider capture can exist only for a dispatched (hence admitted) capture.

What is NOT established here: that the Python code implements this step relation. That link is the boundary
discipline (FORMAL-001 enforcement and census) plus executable trace conformance (`refinement_conformance.py`) over the
recorded runs.
-/

namespace LegionAbstraction
open LegionCore LegionCore.Journal

/-! ## World commit boundary -/

inductive Outcome where
  | refused | applied | duplicate | lostReply | unknown | crashBefore | crashAfter
  deriving DecidableEq, Repr

/-- Effect-creating outcomes: the NATIVE_EFFECT record is durable (possibly unknown to the caller). -/
def Outcome.creates : Outcome → Bool
  | .applied | .lostReply | .unknown | .crashAfter => true
  | _ => false

structure RStep where
  sp : Spec
  s : State
  r : Req
  ts : List JTask
  rs : List Rec
  outcome : Outcome
  newEffects : List Effect

def RStep.pre (x : RStep) : State := { x.s with closed := closedSet x.ts x.rs }

/-- The boundary discipline enforced at runtime (FORMAL-001). -/
def RStep.disciplined (x : RStep) : Prop :=
  (x.outcome.creates = true → decision x.sp x.s x.r x.ts x.rs = .T ∧ x.newEffects = [effectOf x.sp x.r]) ∧
  (x.outcome.creates = false → x.newEffects = [])

/-- **RF1 — step refinement.** -/
theorem step_refines (x : RStep) (h : x.disciplined) :
    ∃ c s', exec .full x.sp x.pre c = some s' ∧ s'.ledger = x.newEffects ++ x.pre.ledger ∧
      (x.outcome.creates = true → c = .actuate x.r ∧ s'.usedNonces = x.r.permit.nonce :: x.pre.usedNonces) ∧
      (x.outcome.creates = false → c = .crash ∧ s' = x.pre) := by
  cases hc : x.outcome.creates
  · refine ⟨.crash, x.pre, rfl, ?_, fun e => absurd e (by simp), fun _ => ⟨rfl, rfl⟩⟩
    rw [h.2 hc]; rfl
  · obtain ⟨hT, he⟩ := h.1 hc
    have hA : admission .full x.sp x.pre x.r = .T := hT
    obtain ⟨_, ⟨tk, _, htk, _⟩, _⟩ := admit_full_T hA
    have hex : exec .full x.sp x.pre (.actuate x.r) = some { x.pre with ledger := effectOf x.sp x.r :: x.pre.ledger, usedNonces := x.r.permit.nonce :: x.pre.usedNonces, used := bumpUse x.pre.used tk.resKey tk.demand } := by
      simp [exec, hA, htk]
    exact ⟨_, _, hex, by rw [he]; rfl, fun _ => ⟨rfl, rfl⟩, fun e => absurd e (by simp)⟩

/-- RF1 consequence: a runtime effect exists only with every full-Core admission condition true in its pre-state. -/
theorem runtime_effect_admitted (x : RStep) (h : x.disciplined) {e : Effect} (he : e ∈ x.newEffects) :
    x.outcome.creates = true ∧ e = effectOf x.sp x.r ∧ admission .full x.sp x.pre x.r = .T := by
  cases hc : x.outcome.creates
  · rw [h.2 hc] at he; simp at he
  · obtain ⟨hT, hn⟩ := h.1 hc
    rw [hn] at he
    exact ⟨rfl, List.mem_singleton.mp he, hT⟩

/-- Log continuity between consecutive decisions: the next decision's ledger is the previous ledger plus the effects
the previous step appended (up to order: the runtime appends, the model prepends; every guard reads the ledger only
through membership). -/
def Continuous : List RStep → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y.s.ledger.Perm (x.newEffects ++ x.s.ledger) ∧ Continuous (y :: rest)

/-- All effects the trace appended (in order of steps). -/
def appended : List RStep → List Effect
  | [] => []
  | x :: rest => x.newEffects ++ appended rest

/-- **RF2 — every effect of the trace was admitted in its pre-state**. -/
theorem trace_effects_admitted (tr : List RStep) (hd : ∀ x ∈ tr, x.disciplined) {e : Effect} (he : e ∈ appended tr) :
    ∃ x ∈ tr, x.outcome.creates = true ∧ e = effectOf x.sp x.r ∧ admission .full x.sp x.pre x.r = .T := by
  induction tr with
  | nil => simp [appended] at he
  | cons x rest ih =>
    simp only [appended, List.mem_append] at he
    cases he with
    | inl h1 => exact ⟨x, List.mem_cons_self, runtime_effect_admitted x (hd x List.mem_cons_self) h1⟩
    | inr h2 =>
      obtain ⟨y, hy, hy'⟩ := ih (fun z hz => hd z (List.mem_cons_of_mem _ hz)) h2
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- The ledger at the last step equals (up to order) the initial ledger plus every appended effect except the last
step's own. -/
theorem ledger_continuity : ∀ (tr : List RStep) (x : RStep), Continuous (x :: tr) →
    ∀ y ∈ (x :: tr).getLast? , (y.newEffects ++ y.s.ledger).Perm (appended (x :: tr) ++ x.s.ledger)
  | [], x, _, y, hy => by
    simp at hy; subst hy; simp [appended]
  | z :: rest, x, ⟨hzx, hc⟩, y, hy => by
    have hy' : y ∈ (z :: rest).getLast? := by simpa [List.getLast?_cons_cons] using hy
    have ih := ledger_continuity rest z hc y hy'
    refine ih.trans ?_
    simp only [appended, List.append_assoc]
    have h1 := (hzx.append_left (appended rest)).append_left z.newEffects
    refine h1.trans ?_
    rw [List.perm_iff_count]; intro a; simp only [List.count_append]; omega

theorem once_step (y : RStep) (hy : y.disciplined) (hn : (y.s.ledger.map (·.task)).Nodup) :
    ((y.newEffects ++ y.s.ledger).map (·.task)).Nodup := by
  cases hcr : y.outcome.creates
  · rw [hy.2 hcr]; simpa using hn
  · obtain ⟨hT, he⟩ := hy.1 hcr
    have hA : admission .full y.sp y.pre y.r = .T := hT
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hon, _⟩ := admit_full_T hA
    rw [he]
    simp only [List.singleton_append, List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun e hem het => hon e hem ?_, hn⟩
    simp [effectOf] at het; exact het

/-- **RF2 — at most one effect per task**: over a disciplined, continuous trace whose first decision-time ledger has
distinct tasks (e.g. is empty), the runtime ledger after every step has pairwise distinct task ids. -/
theorem trace_once : ∀ (tr : List RStep) (x : RStep), (∀ y ∈ x :: tr, y.disciplined) → Continuous (x :: tr) →
    (x.s.ledger.map (·.task)).Nodup → ∀ y ∈ x :: tr, ((y.newEffects ++ y.s.ledger).map (·.task)).Nodup
  | [], x, hd, _, h0, y, hy => by
    simp at hy; subst hy; exact once_step y (hd y List.mem_cons_self) h0
  | z :: rest, x, hd, hc, h0, y, hy => by
    obtain ⟨hzx, hc'⟩ := hc
    have hx := once_step x (hd x List.mem_cons_self) h0
    cases List.mem_cons.mp hy with
    | inl e => subst e; exact hx
    | inr hy' =>
      exact trace_once rest z (fun u hu => hd u (List.mem_cons_of_mem _ hu)) hc' ((hzx.map _).nodup_iff.mpr hx) y hy'

/-! ## RF3 — external effects under provider uncertainty (Commerce Gateway) -/

/-- Gateway effect states (`commerce_adapter/gateway.py`). -/
inductive GS where
  | reserved | createInFlight | approvalPending | approved | captureInFlight | reconciliationPending
  | captureConfirmed | failedHeld | failedReleased
  deriving DecidableEq, Repr

/-- Gateway events for one effect id. `dispatchCreate`/`dispatchCapture` are the two external POSTs; each carries the
Lean attestation the Gateway checked in the same transaction (`lean = true` iff a T attestation bound to the exact
intent was present). `readback s` is any reconciliation by authenticated GETs, which may move the state anywhere the
provider's (uncertain) truth allows — it never dispatches. -/
inductive GEv where
  | dispatchCreate (lean : Bool)
  | dispatchCapture (lean : Bool)
  | readback (to : GS)
  deriving DecidableEq, Repr

structure GSt where
  st : GS
  captureStarted : Bool
  creates : Nat      -- create POSTs dispatched
  captures : Nat     -- capture POSTs dispatched
  deriving DecidableEq, Repr

def GSt.init : GSt := ⟨.reserved, false, 0, 0⟩

/-- The Gateway's transition rules (create: only from RESERVED, never retried; capture: only from APPROVED with
`capture_started` unset, which then never resets; readback never moves back to RESERVED/APPROVED once capture started). -/
def gstep (g : GSt) : GEv → Option GSt
  | .dispatchCreate lean =>
      if g.st = .reserved ∧ lean = true then some { g with st := .createInFlight, creates := g.creates + 1 } else none
  | .dispatchCapture lean =>
      if g.st = .approved ∧ g.captureStarted = false ∧ lean = true
      then some { g with st := .captureInFlight, captureStarted := true, captures := g.captures + 1 } else none
  | .readback to =>
      if to = .reserved then none
      else if g.captureStarted = true ∧ to = .approved then none
      else some { g with st := to }

def grun (g : GSt) : List GEv → Option GSt
  | [] => some g
  | e :: es => (gstep g e).bind (fun g' => grun g' es)

theorem gstep_creates_le {g g' : GSt} {e : GEv} (h : gstep g e = some g') :
    g'.creates ≤ g.creates + 1 ∧ (g'.creates = g.creates + 1 → g.st = .reserved ∧ e = .dispatchCreate true) ∧
    (g.st ≠ .reserved → g'.creates = g.creates) ∧ g'.st ≠ .reserved := by
  cases e with
  | dispatchCreate lean =>
    simp only [gstep] at h; split at h
    · rename_i hc; cases h; simp_all
    · cases h
  | dispatchCapture lean =>
    simp only [gstep] at h; split at h
    · rename_i hc; cases h; simp_all
    · cases h
  | readback to =>
    simp only [gstep] at h; split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2; cases h; simp_all

/-- **RF3a — at most one create dispatch per effect id**, over any trace and any provider outcomes. -/
theorem grun_one_create : ∀ (es : List GEv) (g g' : GSt), grun g es = some g' →
    (g.st ≠ .reserved → g'.creates = g.creates) ∧ g'.creates ≤ g.creates + 1
  | [], g, g', h => by simp [grun] at h; subst h; simp
  | e :: es, g, g', h => by
    simp only [grun, Option.bind_eq_some_iff] at h
    obtain ⟨g1, h1, h2⟩ := h
    obtain ⟨hle, hinc, hkeep, hnr⟩ := gstep_creates_le h1
    have ih := grun_one_create es g1 g' h2
    have e1 := ih.1 hnr
    refine ⟨fun hg => by rw [e1, hkeep hg], ?_⟩
    omega

theorem gstep_captures {g g' : GSt} {e : GEv} (h : gstep g e = some g') :
    (g.captureStarted = true → g'.captureStarted = true ∧ g'.captures = g.captures) ∧
    g'.captures ≤ g.captures + 1 ∧ (g'.captures = g.captures + 1 → e = .dispatchCapture true ∧ g.st = .approved) ∧
    (g'.captures ≠ g.captures → g'.captureStarted = true) := by
  cases e with
  | dispatchCreate lean =>
    simp only [gstep] at h; split at h
    · cases h; simp_all
    · cases h
  | dispatchCapture lean =>
    simp only [gstep] at h; split at h
    · rename_i hc; cases h; simp_all
    · cases h
  | readback to =>
    simp only [gstep] at h; split at h
    · cases h
    · split at h
      · cases h
      · cases h; simp_all

/-- **RF3b — at most one capture dispatch per effect id**, over any trace and any provider outcomes, and a capture
dispatch is only ever made with a Lean-T attestation. -/
theorem grun_one_capture : ∀ (es : List GEv) (g g' : GSt), grun g es = some g' →
    (g.captureStarted = true → g'.captures = g.captures) ∧ g'.captures ≤ g.captures + 1
  | [], g, g', h => by simp [grun] at h; subst h; simp
  | e :: es, g, g', h => by
    simp only [grun, Option.bind_eq_some_iff] at h
    obtain ⟨g1, h1, h2⟩ := h
    obtain ⟨hcs, hle, _, hstart⟩ := gstep_captures h1
    have ih := grun_one_capture es g1 g' h2
    refine ⟨fun hg => by obtain ⟨a, b⟩ := hcs hg; rw [ih.1 a, b], ?_⟩
    by_cases hch : g1.captures = g.captures
    · rw [← hch]; exact ih.2
    · have := ih.1 (hstart hch); omega

theorem dispatch_needs_lean {g g' : GSt} {lean : Bool} :
    (gstep g (.dispatchCreate lean) = some g' → lean = true) ∧ (gstep g (.dispatchCapture lean) = some g' → lean = true) := by
  constructor <;> intro h <;> simp only [gstep] at h <;> split at h <;> simp_all

/-- Provider-side worlds consistent with a gateway trace: the provider may or may not have applied each dispatched
POST (uncertain outcome), and applies nothing that was not dispatched. -/
def consistentCaptures (g : GSt) (providerCaptures : Nat) : Prop := providerCaptures ≤ g.captures

/-- **RF3c — uncertainty soundness.** From a fresh reservation, for every trace and EVERY provider world consistent with
it, the provider holds at most one capture for the effect, and holds one only if a Lean-attested capture dispatch
happened. -/
theorem uncertainty_sound (es : List GEv) (g' : GSt) (h : grun GSt.init es = some g') (n : Nat)
    (hc : consistentCaptures g' n) : n ≤ 1 ∧ (n = 1 → ∃ e ∈ es, e = .dispatchCapture true) := by
  have h1 := (grun_one_capture es GSt.init g' h).2
  simp [GSt.init] at h1
  refine ⟨by unfold consistentCaptures at hc; omega, fun hn => ?_⟩
  -- some step raised `captures` from 0: it was a Lean-attested capture dispatch
  have key : ∀ (es : List GEv) (g g' : GSt), grun g es = some g' → g.captures < g'.captures →
      ∃ e ∈ es, e = .dispatchCapture true := by
    intro es
    induction es with
    | nil => intro g g' h hlt; simp [grun] at h; subst h; omega
    | cons e es ih =>
      intro g g' h hlt
      simp only [grun, Option.bind_eq_some_iff] at h
      obtain ⟨g1, h1, h2⟩ := h
      obtain ⟨_, hle, hinc, _⟩ := gstep_captures h1
      by_cases hc1 : g1.captures = g.captures + 1
      · exact ⟨e, List.mem_cons_self, (hinc hc1).1⟩
      · have : g.captures < g'.captures := hlt
        obtain ⟨e', he', hee⟩ := ih g1 g' h2 (by
          have := (grun_one_capture es g1 g' h2)
          omega)
        exact ⟨e', List.mem_cons_of_mem _ he', hee⟩
  unfold consistentCaptures at hc
  exact key es GSt.init g' h (by simp [GSt.init]; omega)

end LegionAbstraction
