import LegionAbstraction.Renaming
/-!
# LegionAbstraction.JournalRenaming — FORMAL-002 (M1b/M1c): the journal closure and the complete decision of
`legion_decide` are invariant under injective renaming of identifiers
-/

namespace LegionAbstraction
open LegionCore LegionCore.Journal

theorem optmap_beq_none (f : Nat → Nat) (o : Option Nat) : (o.map f == none) = (o == none) := by
  cases o <;> rfl

section
variable {f : Nat → Nat} (hf : Inj f)
include hf

theorem taskOf_rn (ts : List JTask) (t : Nat) :
    taskOf (ts.map (rnJTask f)) (f t) = (taskOf ts t).map (rnJTask f) := by
  simp only [taskOf, List.find?_map]
  congr 2
  funext x
  simp [rnJTask, beq_rn hf]

theorem depOk_rn (ts : List JTask) (conf : List Nat) (d : Nat) :
    depOk (ts.map (rnJTask f)) (conf.map f) (f d) = depOk ts conf d := by
  simp only [depOk, contains_rn hf, taskOf_rn hf]
  cases taskOf ts d <;> rfl

theorem eligible_rn (ts : List JTask) (conf : List Nat) (tk : JTask) :
    eligible (ts.map (rnJTask f)) (conf.map f) (rnJTask f tk) = eligible ts conf tk := by
  simp only [eligible, rnJTask, List.all_map]
  congr 1
  funext d
  simp only [Function.comp_apply, depOk_rn hf]

theorem ownerOk_rn (tk : JTask) (a : Option Nat) : ownerOk (rnJTask f tk) (a.map f) = ownerOk tk a := by
  simp only [ownerOk, rnJTask]; exact optmap_beq_some hf a tk.owner

theorem chain_rn (ts : List JTask) : ∀ (n : Nat) (acc : List Nat),
    chain (ts.map (rnJTask f)) n (acc.map f) = (chain ts n acc).map f := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    -- `chain` elaborates its inner `match` to the shared matcher `depOk.match_1`; it is named explicitly so that the
    -- rewrite below matches the goal syntactically.
    have hnext : (acc.map f).flatMap (fun t => depOk.match_1 (fun _ => List Nat) (taskOf (ts.map (rnJTask f)) t)
          (fun tk => tk.deps) (fun _ => []))
        = (acc.flatMap (fun t => depOk.match_1 (fun _ => List Nat) (taskOf ts t) (fun tk => tk.deps) (fun _ => []))).map f := by
      rw [List.flatMap_map, List.map_flatMap]
      congr 1
      funext t
      simp only [taskOf_rn hf]
      cases taskOf ts t <;> rfl
    have hfil : ∀ l : List Nat, (l.map f).filter (fun t => !(acc.map f).contains t)
        = (l.filter (fun t => !acc.contains t)).map f := by
      intro l
      rw [List.filter_map]
      congr 2
      funext t
      simp only [Function.comp_apply, contains_rn hf]
    simp only [chain]
    rw [hnext, hfil, ← List.map_append]
    simp only [List.length_map]
    split <;> rename_i h <;> simp only [h, ↓reduceIte, ih]

theorem refsOk_rn (ts : List JTask) (s : FS) (tk : JTask) (refs : List Nat) :
    refsOk (ts.map (rnJTask f)) (rnFS f s) (rnJTask f tk) (refs.map f) = refsOk ts s tk refs := by
  have hch : chain (ts.map (rnJTask f)) (ts.map (rnJTask f)).length [(rnJTask f tk).id]
      = (chain ts ts.length [tk.id]).map f := by
    rw [List.length_map]; exact chain_rn hf ts ts.length [tk.id]
  simp only [refsOk, hch, rnFS, List.any_map, List.all_map]
  congr 1
  · congr 1; funext x; simp only [Function.comp_apply, List.any_map, rnPair]
    congr 1; funext o; obtain ⟨o1, o2⟩ := o; simp only [Function.comp_apply, rnPair, beq_rn hf, contains_rn hf]
  · congr 1; funext x; simp only [Function.comp_apply, List.any_map, rnPair]
    congr 1; funext o; obtain ⟨o1, o2⟩ := o; simp only [Function.comp_apply, rnPair, beq_rn hf, contains_rn hf]

theorem effects_any_rn (s : FS) (t : Nat) :
    ((rnFS f s).effects.any (fun e => e.1 == f t)) = s.effects.any (fun e => e.1 == t) := by
  simp only [rnFS, List.any_map]; congr 1; funext e; simp only [Function.comp_apply, beq_rn hf]

omit hf in
theorem rnFS_ite (c : Prop) [Decidable c] (a b : FS) : rnFS f (if c then a else b) = if c then rnFS f a else rnFS f b := by
  split <;> rfl

omit hf in
@[simp] theorem rnJTask_kinds (tk : JTask) : (rnJTask f tk).kinds = tk.kinds := rfl
omit hf in
@[simp] theorem rnJTask_na (tk : JTask) : (rnJTask f tk).na = tk.na := rfl
omit hf in
@[simp] theorem rnJTask_id (tk : JTask) : (rnJTask f tk).id = f tk.id := rfl
omit hf in
@[simp] theorem rnFS_confirmed (s : FS) : (rnFS f s).confirmed = s.confirmed.map f := rfl

theorem ingest_rn (ts : List JTask) (s : FS) (r : Rec) :
    ingest (ts.map (rnJTask f)) (rnFS f s) (rnRec f r) = rnFS f (ingest ts s r) := by
  obtain ⟨kind, task, agent, ok, eff, cmd, rid, refs⟩ := r
  have hT := taskOf_rn hf ts task
  cases kind <;> simp only [ingest, rnRec, kindOf] <;> rw [hT] <;> cases htk : taskOf ts task <;>
    simp only [Option.map_some, Option.map_none, rnJTask_kinds, rnJTask_na, rnJTask_id, rnFS_confirmed, ownerOk_rn hf, eligible_rn hf,
      refsOk_rn hf, optmap_beq_none, effects_any_rn hf, rnFS_ite] <;>
    (repeat' (split <;> rename_i h <;> simp only [h, ↓reduceIte, Bool.false_eq_true])) <;> rfl

theorem pair_beq_rn (a b c d : Nat) : ((f a, f b) == (f c, f d)) = ((a, b) == (c, d)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Prod.mk.injEq, eq_rn hf]

theorem writeDone_rn (s : FS) (t : Nat) : writeDone (rnFS f s) (f t) = writeDone s t := by
  have hrc : ∀ e : Nat × Nat × Nat, (s.receipts.map (fun e => (f e.1, f e.2.1, f e.2.2))).contains (f e.1, f e.2.1, f e.2.2)
      = s.receipts.contains e := by
    intro e
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    refine mem_map_inj (g := fun e : Nat × Nat × Nat => (f e.1, f e.2.1, f e.2.2)) ?_ _ _
    intro x y h
    obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
    simp only [Prod.mk.injEq] at h
    simp [hf _ _ h.1, hf _ _ h.2.1, hf _ _ h.2.2]
  simp only [writeDone, rnFS, List.any_map]
  congr 1; funext e
  simp only [Function.comp_apply, beq_rn hf, hrc, List.any_map]
  congr 2; funext b
  simp only [Function.comp_apply, pair_beq_rn hf, optmap_beq_none, optmap_beq_some hf]

theorem sat_contains_rn (s : FS) (t : Nat) (k : K) :
    (rnFS f s).sat.contains (f t, k) = s.sat.contains (t, k) := by
  have hinj : ∀ x y : Nat × K, (fun p : Nat × K => (f p.1, p.2)) x = (fun p : Nat × K => (f p.1, p.2)) y → x = y := by
    intro x y h
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    simp only [Prod.mk.injEq] at h
    simp [hf _ _ h.1, h.2]
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, rnFS]
  exact mem_map_inj (g := fun p : Nat × K => (f p.1, p.2)) hinj s.sat (t, k)

theorem kindDone_rn (s : FS) (t : Nat) (k : K) : kindDone (rnFS f s) (f t) k = kindDone s t k := by
  simp only [kindDone]
  split
  · exact writeDone_rn hf s t
  · exact sat_contains_rn hf s t k

theorem isDone_rn (s : FS) (tk : JTask) : isDone (rnFS f s) (rnJTask f tk) = isDone s tk := by
  have hk : kindDone (rnFS f s) (f tk.id) = kindDone s tk.id := funext (kindDone_rn hf s tk.id)
  simp only [isDone, rnJTask_kinds, rnJTask_id, hk, sat_contains_rn hf]

theorem confirmPass_fold_rn : ∀ (l : List JTask) (acc : FS),
    (l.map (rnJTask f)).foldl (fun acc tk => if !tk.na && isDone acc tk && !acc.confirmed.contains tk.id
                          then { acc with confirmed := acc.confirmed ++ [tk.id] } else acc) (rnFS f acc)
    = rnFS f (l.foldl (fun acc tk => if !tk.na && isDone acc tk && !acc.confirmed.contains tk.id
                          then { acc with confirmed := acc.confirmed ++ [tk.id] } else acc) acc)
  | [], acc => rfl
  | tk :: l, acc => by
    simp only [List.map_cons, List.foldl_cons]
    have hc : (rnFS f acc).confirmed.contains (rnJTask f tk).id = acc.confirmed.contains tk.id := by
      simp only [rnFS, rnJTask]; exact contains_rn hf _ _
    have hn : (rnJTask f tk).na = tk.na := rfl
    rw [isDone_rn hf, hc, hn]
    split
    · have : { rnFS f acc with confirmed := (rnFS f acc).confirmed ++ [(rnJTask f tk).id] }
          = rnFS f { acc with confirmed := acc.confirmed ++ [tk.id] } := by
        simp [rnFS, rnJTask, List.map_append]
      rw [this]; exact confirmPass_fold_rn l _
    · exact confirmPass_fold_rn l acc

theorem confirmPass_rn (ts : List JTask) (s : FS) :
    confirmPass (ts.map (rnJTask f)) (rnFS f s) = rnFS f (confirmPass ts s) :=
  confirmPass_fold_rn hf ts s

theorem step_rn (ts : List JTask) (s : FS) (r : Rec) :
    step (ts.map (rnJTask f)) (rnFS f s) (rnRec f r) = rnFS f (step ts s r) := by
  simp only [step, ingest_rn hf, confirmPass_rn hf]

theorem fold_rn (ts : List JTask) : ∀ (rs : List Rec) (acc : FS),
    (rs.map (rnRec f)).foldl (step (ts.map (rnJTask f))) (rnFS f acc) = rnFS f (rs.foldl (step ts) acc)
  | [], _ => rfl
  | r :: rs, acc => by
    simp only [List.map_cons, List.foldl_cons, step_rn hf]
    exact fold_rn ts rs _

/-- **M1b** — the journal closure computed by the proved fold commutes with injective renaming. -/
theorem closedSet_rn (ts : List JTask) (rs : List Rec) :
    closedSet (ts.map (rnJTask f)) (rs.map (rnRec f)) = (closedSet ts rs).map f := by
  have h0 : FS.empty = rnFS f FS.empty := rfl
  simp only [closedSet, fold, List.map_append]
  rw [h0, fold_rn hf]
  congr 1
  rw [List.filter_map, List.map_map, List.map_map]
  rfl

/-- **M1c (decision invariance)** — the verdict computed by `legion_decide` (`Main.decideLine` after parsing) is
the same for every injective renaming of the identifiers in its input. -/
theorem decision_rn (sp : Spec) (s : State) (r : Req) (ts : List JTask) (rs : List Rec) :
    decision (rnSpec f sp) (rnState f s) (rnReq f r) (ts.map (rnJTask f)) (rs.map (rnRec f)) = decision sp s r ts rs := by
  have : { rnState f s with closed := closedSet (ts.map (rnJTask f)) (rs.map (rnRec f)) }
      = rnState f { s with closed := closedSet ts rs } := by
    rw [closedSet_rn hf]; rfl
  simp only [decision, this, admission_rn hf]

/-- The named grounds reported by the binary are identical as well. -/
theorem grounds_rn (sp : Spec) (s : State) (r : Req) (ts : List JTask) (rs : List Rec) :
    grounds (rnSpec f sp) (rnState f s) (rnReq f r) (ts.map (rnJTask f)) (rs.map (rnRec f)) = grounds sp s r ts rs := by
  have : { rnState f s with closed := closedSet (ts.map (rnJTask f)) (rs.map (rnRec f)) }
      = rnState f { s with closed := closedSet ts rs } := by
    rw [closedSet_rn hf]; rfl
  simp only [grounds, this, guards_rn hf]

end

end LegionAbstraction
