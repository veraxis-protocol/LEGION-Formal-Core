# FORMAL-004 — Executable Judge conformance to the Lean completion specification (T9, T14)

**Verdict: T.** The executable qualification Judge was differentially tested against the Lean completion specification on all 13 qualification runs plus targeted mutations. It agreed in **61/61** cases, with **0** T9 violations and **0** T14 violations.

The Judge's Python is **not** proved correct. Conformance is established by differential testing against a Lean-defined, Lean-computed reference.

## Sources

| Part | Location |
|---|---|
| Lean | LEGION R2 `formal/LegionCore/LegionAbstraction/JudgeConformance.lean` (commit `73660d1`, branch `formal-closure-001`) |
| Differential | `tests/legion_struct/causal_007/judge_conformance.py` and `formal_closure/judge_rerun.sh` (same commit) |
| Judge under test, unchanged | The recorded G4-B qualification pipeline: `STRUCTURAL_001/code/judge_s1` (S1 `legion_judge`) behind `CAUSAL_007/code/adapter_s2/struct_adapter.py` with `struct_profile.json`, hidden frozen original contracts and the per-run `REGISTRATION.json` |
| Lean reference | `judgePass` over `Journal.closedSet` of the run's raw journal (`WORLD_LOG`, `GATE_COMMITS`, `READBACK`), computed by the pinned `legion_decide` (sha256 `99cda684…`) |

## Proof statements (exact text: `FORMAL002_003_004_STATEMENTS_AND_AXIOMS.txt`)

| Id | Lean | Statement |
|---|---|---|
| JC1 | `judgeSpecB_iff` | The executable Boolean check `judgeSpecB sp.tasks s.closed` decides `judgePass sp s` (the spec T9 and T14 are stated against) |
| JC2 | `journal_judge_grounded` | A PASS of the check on the journal-derived closed set means every mandatory obligation of the frozen original is confirmed by the proved journal fold (causally ordered and owner-witnessed, J1/J2) or declared not applicable. This is the journal-level reading of T9. |
| JC3 | `judge_ignores_contract_record` | Executable T14: no runtime contract record, contract identity or version changes the completion verdict |
| JC4 | `amended_list_can_pass` | The attack T14 excludes is real: deleting an obligation from the list a check iterates can turn FAIL into PASS. So the executable Judge must be bound to the frozen original. |

Axioms: `propext` and `Quot.sound`. JC3 and JC4 use no axioms. There are 0 `sorry`.

## Differential result (`FORMAL004_JUDGE_CONFORMANCE.json`)

Mutations of each run:

| Mutation | Change |
|---|---|
| `orig` | none |
| `no_readback` | Independent readback journals emptied |
| `no_observation` | All OBSERVATION records removed |
| `drop_effect` | The last NATIVE_EFFECT and its RECEIPT removed |
| `amend_vacuous` | (T14 attack) The `drop_effect` run, plus the contract given to the Judge with exactly that obligation deleted |

Worlds without writes (AMB, SEA) have no effect mutations. That gives 61 cases.

| Measure | Result |
|---|---|
| Original runs: Judge PASS and Lean PASS | **13/13** |
| Judge verdict = PASS exactly when Lean `judgePass` | **61/61** |
| **T9 violations** (Judge PASS that the Lean spec does not support) | **0** |
| **T14 violations** (Judge PASS on an amended contract) | **0** — all 11 `amend_vacuous` cases were rejected (`INVALID_TEST`: contract hash bound by the registration; A2A: `FAIL`) |
| Judge stricter than the spec | 0 |

In the two worlds without write obligations, `no_readback` correctly stays PASS on both sides.

**Preserved failure:** the first differential run crashed after the first world. The runner had selected a hidden `.attempt_registry` directory as a run. This is a harness defect; no verdict was involved. Run directory selection was fixed and the full run repeated.

## Uncovered assumptions and residuals

- **Implementation:** the Judge's Python implementation is not proved. Conformance is differential over 13 real runs and 48 mutations, not exhaustive.
- **`judgePass` covers closure of mandatory obligations only.** The Judge also checks properties outside this spec: goal and forbidden-state predicates on the final world state, provider/model causation, budgets and claims. Those are not covered by T9/T14 and are not claimed here.
- **Lean reference assumptions:** it uses Python content verdicts (`Rec.ok`) and activation (`JTask.na`), as in FORMAL-002 (PE3 residual).
- **Judge re-runs** used the recorded pipeline outside its namespace sandbox. The inputs were the same, and the original verdicts were reproduced 13/13.
