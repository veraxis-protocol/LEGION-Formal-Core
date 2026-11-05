/-!
# LegionCore.State — the formal LEGION Core state `S = (A, W, O, D, E, R, P, X, J)`

Generic over every finite agent population and every finite task graph (T10). There are no world constants.

| SPEC component | here |
|---|---|
| A agents, identities, authority | `Spec.idents` (credential ↦ agent), `Task.owner` |
| W world | abstracted: only the effect ledger and the closure facts the Core decides on |
| O obligations | `Spec.tasks` (`Task.mandatory`, `Task.write`), `State.closed` |
| D dependencies | `Task.deps` |
| E evidence | `State.reports` (one entry per (source, task), latest wins), `State.evidenced`, `State.verified` |
| R resources, epochs | `State.used`, `Spec.cap`, `State.phase/epoch/uid/wid`, `State.issued` |
| P proposals, admissions | `Req`, `admission` (Admission.lean) |
| X native effects | `State.ledger`, `State.fenced`, `State.usedNonces` |
| J verdicts | `judgePass` (Completion.lean): the Judge's specification, not its Python |
-/

namespace LegionCore

/-- Three-valued verdict: T admitted, F refuted, Z not decided. Only T may reach a consequential effect. -/
inductive V where
  | T | F | Z
  deriving DecidableEq, Repr, Inhabited

/-- Strong Kleene conjunction (the same table as ZTL's `kand`, bridged in LegionBridge). -/
def kand : V → V → V
  | .F, _  => .F
  | _, .F  => .F
  | .T, .T => .T
  | _, _   => .Z

def kandAll : List V → V
  | []      => .T
  | v :: vs => kand v (kandAll vs)

theorem kand_T {a b : V} : kand a b = .T ↔ a = .T ∧ b = .T := by
  cases a <;> cases b <;> decide

theorem kandAll_T (vs : List V) : kandAll vs = .T ↔ ∀ v ∈ vs, v = .T := by
  induction vs with
  | nil => simp [kandAll]
  | cons v vs ih => simp [kandAll, kand_T, ih]

/-- One public task (= one obligation). `resKey`/`demand` instantiate the generic capacity interface. -/
structure Task where
  id        : Nat
  owner     : Nat
  deps      : List Nat
  write     : Bool
  target    : Nat
  mandatory : Bool
  resKey    : Nat
  demand    : Nat
  deriving DecidableEq, Repr

def lookup (k : Nat) : List (Nat × Nat) → Option Nat
  | []          => none
  | (a, b) :: r => if a = k then some b else lookup k r

/-- Static, FROZEN mission specification (from the public world spec + policy), fixed before the run.
`mission` is the canonical contract identity H_mission (assumption A-H1: the canonical-contract hash is
injective on the contracts that occur). `tasks` is O_original. `specAuthority` lists the only credentials that
may change the specification (assumption A-S1: disjoint from execution-agent credentials). -/
structure Spec where
  mission : Nat
  tasks   : List Task
  specAuthority : List Nat
  idents  : List (Nat × Nat)   -- admitted credential ↦ agent (A-K1: credentials are not shared)
  cap     : List (Nat × Nat)   -- resource key ↦ authorized capacity (absent ⇒ 0)
  f       : Nat                -- evidence fault bound (policy, never caller input)
  maxAge  : Nat                -- evidence freshness window
  deriving Repr

def Spec.task? (sp : Spec) (t : Nat) : Option Task := sp.tasks.find? (fun x => x.id == t)
def Spec.actorOf (sp : Spec) (cred : Nat) : Option Nat := lookup cred sp.idents
def Spec.capOf (sp : Spec) (k : Nat) : Nat := (lookup k sp.cap).getD 0

inductive Phase where
  | registered | running | terminal
  deriving DecidableEq, Repr

/-- An authority permit. Membership in `State.issued` models a valid MAC (assumption A-C1). -/
structure Permit where
  pid     : Nat
  uid     : Nat
  wid     : Nat
  mission : Nat
  epoch   : Nat
  task    : Nat
  cmd     : Nat
  actor   : Nat
  target  : Nat
  nonce   : Nat
  deriving DecidableEq, Repr

structure Effect where
  cmd   : Nat
  task  : Nat
  actor : Nat
  epoch : Nat
  pid   : Nat
  mission : Nat   -- H_effect: contract identity the receipt is bound to
  deriving DecidableEq, Repr

/-- An evidence report. `source` is the underlying independent ORIGIN (not the reporter): reporters that share
one origin share one `source` id and therefore one seat (SPEC D4). -/
structure Report where
  source : Nat
  task   : Nat
  value  : V
  time   : Nat
  deriving DecidableEq, Repr

structure State where
  phase      : Phase
  uid        : Nat
  wid        : Nat
  epoch      : Nat
  now        : Nat
  issued     : List Permit
  usedNonces : List Nat
  fenced     : List Nat
  ledger     : List Effect
  verified   : List Nat
  evidenced  : List Nat
  closed     : List Nat
  reports    : List Report
  used       : Nat → Nat
  contract   : List Task   -- the contract record held by the runtime (starts as O_original)
  chash      : Nat         -- its canonical identity
  cver       : Nat         -- contract version; 0 = the frozen original
  plan       : List Nat    -- the collective's current plan (ordering / chosen means): freely revisable

def init (sp : Spec) (uid wid : Nat) : State :=
  { phase := .registered, uid, wid, epoch := 0, now := 0, issued := [], usedNonces := [], fenced := [],
    ledger := [], verified := [], evidenced := [], closed := [], reports := [], used := fun _ => 0,
    contract := sp.tasks, chash := sp.mission, cver := 0, plan := [] }

/-- A consequential proposal. `claimed` is the caller-supplied agent id: it is carried but never consulted. -/
structure Req where
  cred    : Nat
  claimed : Nat
  task    : Nat
  target  : Nat
  cmd     : Nat
  permit  : Permit
  deriving DecidableEq, Repr

/-- Which admission premises are enforced. `Guards.full` is the Core; the others exist only to build the
countermodels (dropping a premise must make a prohibited state reachable). -/
structure Guards where
  running   : Bool := true
  identity  : Bool := true
  owner     : Bool := true
  target    : Bool := true
  permit    : Bool := true
  epoch     : Bool := true
  nonce     : Bool := true
  freshCmd  : Bool := true
  once      : Bool := true
  deps      : Bool := true
  cap       : Bool := true
  ztl       : Bool := true
  closeDeps : Bool := true
  readback  : Bool := true
  fenceProof : Bool := true
  contract  : Bool := true   -- admission bound to the frozen contract identity (T13)
  specAuth  : Bool := true   -- specification changes need separate authority (T11/T12)
  deriving DecidableEq, Repr

def Guards.full : Guards := {}

end LegionCore
