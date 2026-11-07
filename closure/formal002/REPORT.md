# FORMAL-002 — Runtime-to-model abstraction: formalization, proofs, serializer validation

**Verdict: T.** α is formalized, its critical mapping properties are proved, and the executable serializer was validated against them.

The correspondence between the Python serializer and the Lean α is **not** proved. It is established by executable validation. Per-record journal content verdicts (`Rec.ok`) and activation (`JTask.na`) remain trusted Python inputs (PE3 residual).

## Sources

**Lean:** library `LegionAbstraction` in LEGION R2 `formal/LegionCore/LegionAbstraction/` (branch `formal-closure-001`, commit `386341b`).
- Lean 4.29.1 on Windows; no Mathlib.
- The qualified decider binary is unchanged: `legion_decide.exe` sha256 `99cda684…ade73a`, rebuilt from the same sources. The new library is not imported by `LegionCore` or `Main`.

**Validation:** `tests/legion_struct/causal_007/alpha_shape_check.py` (same commit), run in WSL Python 3.12.3 against the pinned binary through interop.

## Proof statements (exact text: `FORMAL002_003_STATEMENTS_AND_AXIOMS.txt`)

| Id | Lean | Statement |
|---|---|---|
| M1a | `guards_rn`, `admission_rn` | For every injective `f : ℕ → ℕ`, renaming every identifier field of (Spec, State, Req) leaves every named guard, and hence the verdict, unchanged |
| M1b | `closedSet_rn` | The proved journal fold commutes with renaming: `closedSet (ts.map rn) (rs.map rn) = (closedSet ts rs).map f` |
| M1c | `decision_rn`, `grounds_rn` | The complete computation of `legion_decide` after parsing (closure by the fold, then `admission .full`) returns the same verdict and the same named grounds for every injective renaming. *The decision depends only on equality of identifiers.* |
| M0 | `intern_inj`, `intern_pos` | The adapter's interner model (first occurrence ↦ index + 1) is injective on the seen identifiers and never emits 0 |
| M2 | `alpha_T_requires` | Under α's shape (`AlphaShape`), T implies the runtime permit verification succeeded (`pv = true`) and the single world-origin gate value, which combines gate facts and action binding, was T |
| M3 | `alpha_sound` | With an injective encoding of (namespace, string) keys, T implies these raw-string facts: <ul><li>the permit's task, command, target and actor equal the request's</li><li>the requesting agent is a role agent</li><li>the permit's attempt uid and world id equal the runtime's</li><li>the permit's mission equals the frozen mission, and the runtime contract identity equals it</li><li>the nonce is unused and the command is not fenced</li><li>no recorded native effect has this command or this task</li><li>the task is a WRITE task of this agent with exactly this target</li></ul> |

Axioms: `propext`, `Quot.sound` and `Classical.choice` only, with 0 `sorry`. Identifier-renaming invariance holds for the closure fold over all 10 journal record kinds.

## Serializer validation (`FORMAL002_ALPHA_VALIDATION.json`, seed 20261107)

| Check | Result |
|---|---|
| V1 AlphaShape: all 14 conjuncts checked through the per-call intern table on 1,500 randomized boundary states (13 worlds plus a dependency-free synthetic world; verdicts 902 F, 427 Z, 171 T) | **0 violations**; interner injective and never 0 |
| V2 M1 through the real binary: 5 random injective renamings (into [0, 2⁴⁰)) of every identifier position, for each of the 1,500 generated payloads and the 28 recorded ones | **0 mismatches** in verdict, grounds or renamed closed set (7,640 renamed decisions) |
| M3 raw conclusions evaluated on raw runtime values for all 171 T verdicts | **0 violations** |
| V3 replay of 28 recorded qualification payloads (13 worlds, G4-B) | **28/28** verdicts identical; recorded shape 0 violations |

Smoke runs: only the third smoke run's output survives (`FORMAL002_ALPHA_VALIDATION_smoke.json`); the first two were overwritten. Both produced no T verdict (all-F, then a contract-version generator bug, 26 designed-valid requests all `CONTRACT=F`). The generator was corrected; nothing in the system under test changed.

## Uncovered assumptions and residuals

- **Correspondence between Python `build_payload` and Lean α:** validated, not proved. The interner model, M0, is a Lean model of the Python algorithm.
- **Global extension:** M1 is stated for globally injective renamings. Python's interner is injective on its domain; extending a finite injection to a global one is standard but not mechanized here.
- **PE3 residual:** `Rec.ok` (per-record content validity) and `JTask.na` (activation) are trusted Python inputs, as before.
- **PE1 is unchanged:** the JSON parse layer of `Main.lean`, the Lean compiler and the C toolchain are trusted. V2/V3 exercise them on 7,640 + 28 inputs.
