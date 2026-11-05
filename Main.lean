import LegionCore
import Lean.Data.Json
/-!
# legion_decide — the authoritative admission decision, compiled from `LegionCore.admission .full`

Protocol: one JSON object per stdin line → one JSON object per stdout line.
  in : {"spec": Spec, "state": State, "req": Req}   (all identifiers already interned to Nat by the adapter)
  out: {"verdict": "T"|"F"|"Z", "grounds": [[name, "T"|"F"|"Z"], ...], "error"?: string}
Any malformed input yields verdict "Z" (fail closed): only "T" may reach an effect.
The verdict is EXACTLY `admission Guards.full sp s r` — the function T1–T15 are proved about.
-/

open Lean LegionCore

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
def natF (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?
def boolF (j : Json) (k : String) : Except String Bool := do (← field j k).getBool?
def strF (j : Json) (k : String) : Except String String := do (← field j k).getStr?
def arrF (j : Json) (k : String) : Except String (Array Json) := do (← field j k).getArr?
def natList (j : Json) (k : String) : Except String (List Nat) := do
  let a ← arrF j k; (a.toList.mapM fun x => x.getNat?)
def pairList (j : Json) (k : String) : Except String (List (Nat × Nat)) := do
  let a ← arrF j k
  a.toList.mapM fun x => do
    let p ← x.getArr?
    if h : p.size = 2 then pure ((← p[0].getNat?), (← p[1].getNat?)) else throw s!"{k}: pair expected"

def parseV : String → Except String V
  | "T" => pure .T | "F" => pure .F | "Z" => pure .Z | v => throw s!"bad V {v}"
def showV : V → String | .T => "T" | .F => "F" | .Z => "Z"

def parseTask (j : Json) : Except String Task := do
  pure { id := ← natF j "id", owner := ← natF j "owner", deps := ← natList j "deps", write := ← boolF j "write",
         target := ← natF j "target", mandatory := ← boolF j "mandatory", resKey := ← natF j "resKey",
         demand := ← natF j "demand" }

def parsePermit (j : Json) : Except String Permit := do
  pure { pid := ← natF j "pid", uid := ← natF j "uid", wid := ← natF j "wid", mission := ← natF j "mission",
         epoch := ← natF j "epoch", task := ← natF j "task", cmd := ← natF j "cmd", actor := ← natF j "actor",
         target := ← natF j "target", nonce := ← natF j "nonce" }

def parseEffect (j : Json) : Except String Effect := do
  pure { cmd := ← natF j "cmd", task := ← natF j "task", actor := ← natF j "actor", epoch := ← natF j "epoch",
         pid := ← natF j "pid", mission := ← natF j "mission" }

def parseReport (j : Json) : Except String Report := do
  pure { source := ← natF j "source", task := ← natF j "task", value := ← parseV (← strF j "value"),
         time := ← natF j "time" }

def parsePhase : String → Except String Phase
  | "registered" => pure .registered | "running" => pure .running | "terminal" => pure .terminal
  | p => throw s!"bad phase {p}"

def parseSpec (j : Json) : Except String Spec := do
  pure { mission := ← natF j "mission", tasks := ← ((← arrF j "tasks").toList.mapM parseTask),
         specAuthority := ← natList j "specAuthority", idents := ← pairList j "idents", cap := ← pairList j "cap",
         f := ← natF j "f", maxAge := ← natF j "maxAge" }

def parseState (j : Json) : Except String State := do
  let used ← pairList j "used"
  pure { phase := ← parsePhase (← strF j "phase"), uid := ← natF j "uid", wid := ← natF j "wid",
         epoch := ← natF j "epoch", now := ← natF j "now",
         issued := ← ((← arrF j "issued").toList.mapM parsePermit), usedNonces := ← natList j "usedNonces",
         fenced := ← natList j "fenced", ledger := ← ((← arrF j "ledger").toList.mapM parseEffect),
         verified := [], evidenced := [], closed := ← natList j "closed",
         reports := ← ((← arrF j "reports").toList.mapM parseReport),
         used := fun k => (lookup k used).getD 0,
         contract := [], chash := ← natF j "chash", cver := ← natF j "cver", plan := [] }

def parseK : String → Except String Journal.K
  | "READ" => pure .read | "ANALYZE" => pure .analyze | "COMMUNICATE" => pure .communicate
  | "WAIT" => pure .wait | "RECONCILE" => pure .reconcile | "DONE" => pure .done
  | "REFUSE" => pure .refuse | "WRITE" => pure .write | k => throw s!"bad kind {k}"

def parseRK : String → Except String Journal.RK
  | "obs" => pure .obs | "analysis" => pure .analysis | "msg" => pure .msg | "wait" => pure .wait
  | "reconcile" => pure .reconcile | "done" => pure .done | "refusal" => pure .refusal
  | "effect" => pure .effect | "receipt" => pure .receipt | "readback" => pure .readback
  | k => throw s!"bad record kind {k}"

def parseJTask (j : Json) : Except String Journal.JTask := do
  pure { id := ← natF j "id", owner := ← natF j "owner", deps := ← natList j "deps",
         kinds := ← ((← arrF j "kinds").toList.mapM fun x => do parseK (← x.getStr?)), na := ← boolF j "na" }

def parseRec (j : Json) : Except String Journal.Rec := do
  let agent ← match (← field j "agent") with
    | Json.null => pure none
    | x => pure (some (← x.getNat?))
  pure { kind := ← parseRK (← strF j "kind"), task := ← natF j "task", agent, ok := ← boolF j "ok",
         eff := ← natF j "eff", cmd := ← natF j "cmd", rid := ← natF j "rid", refs := ← natList j "refs" }

def parseReq (j : Json) : Except String Req := do
  pure { cred := ← natF j "cred", claimed := ← natF j "claimed", task := ← natF j "task",
         target := ← natF j "target", cmd := ← natF j "cmd", permit := ← parsePermit (← field j "permit") }

def decideLine (line : String) : String :=
  let parsed : Except String (Spec × State × Req × List Journal.JTask × List Journal.Rec) := do
    let j ← Json.parse line
    let jr ← field j "journal"
    pure (← parseSpec (← field j "spec"), ← parseState (← field j "state"), ← parseReq (← field j "req"),
          ← ((← arrF jr "tasks").toList.mapM parseJTask), ← ((← arrF jr "records").toList.mapM parseRec))
  match parsed with
  | .error e => (Json.mkObj [("verdict", "Z"), ("grounds", Json.arr #[]), ("error", e)]).compress
  | .ok (sp, s0, r, ts, rs) =>
    -- PE3 strengthening: the closed set is computed HERE, by the proved Lean fold over the raw journal;
    -- any `closed` supplied in the state is ignored.
    let s := { s0 with closed := Journal.closedSet ts rs }
    let gs := guards .full sp s r
    let v := admission .full sp s r
    (Json.mkObj [("verdict", showV v),
      ("grounds", Json.arr (gs.toArray.map fun (n, x) => Json.arr #[n, showV x])),
      ("closed", Json.arr ((Journal.closedSet ts rs).toArray.map fun (n : Nat) => toJson n))]).compress

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := line.trimRight
  if l.isEmpty then loop stdin stdout else
  stdout.putStrLn (decideLine l)
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
