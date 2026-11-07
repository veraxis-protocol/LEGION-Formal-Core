# FORMAL-005 — Clean build, axiom audit, independent replay, 13-world qualification, negative testing, immutable evidence manifest

**Verdict: T, with one declared F.** The native `legion_decide` binary is **not byte-reproducible**: its bytes depend on the build path. The generated C and the behaviour are reproducible.

## Sources

- LEGION R2 `formal-closure-001`:
  - closure runtime `d4b0f83`, frozen into the qualification stage (`dirty=0`);
  - evidence commit `5693acc`, plus this report's commit.
- LEGION-Commerce `claude/formal-closure-001` `61dd814`.
- Public clones for Federation `9d2a32a`, Marketplace `906ec0f` and LEGION Core `d083c44`.
- Lean 4.29.1 on Windows, no Mathlib. Pinned decider sha256 `99cda684…ade73a`.

## 1. Clean Lean build

| Check | Result |
|---|---|
| `git archive` of the Lean project, then `lake build` in a fresh directory (`CLEAN_BUILD.log`) | **exit 0**, 40 jobs, 25 s |
| Second clean build at a different path | exit 0 |
| All generated C (`.lake/build/ir/**/*.c`), qualified build vs both clean builds | **byte-identical** |
| Native binary | **F (byte level):** clean builds produce `afc43e90…` and `48ad3457…`; the qualified binary is `99cda684…`. Only the native compile and link output depends on the path; this was already noted for v1.0.0. |
| Behaviour on 4,033 inputs (28 recorded payloads, 4,000 perturbations, 5 malformed lines; verdicts 834 T, 2,452 F, 747 Z) | **0 differing output lines** for both rebuilds (`DECIDER_FUNCTIONAL_EQUIVALENCE.json`) |

**Consequence (blocker for owner decision):** the runtime pins the decider by sha256 (FORMAL-001 B-R2-1). A third party's rebuild is therefore refused, failing closed, unless the owner adds its hash to the pin set. I did not change the pin.

## 2. Axiom audit

- **v1.0.0 declarations:** `AxiomAudit.lean` in the clean build is identical to the qualified `AXIOM_AUDIT.txt`.
- **Closure declarations:** the 22 headline closure statements (`STATEMENTS_CLEAN.txt`) depend on `propext`, `Quot.sound` and `Classical.choice` only, or on no axiom.
- **Forbidden constructs:** 0 `sorryAx`. A source scan for `sorry`, `axiom`, `native_decide`, `unsafe` and `implemented_by` over `LegionCore`, `LegionAbstraction` and the roots is **CLEAN**.

## 3. Independent replay

- **Recorded qualification:** all 28 recorded G4-B decisions replayed through the pinned binary with exact `sha256(payload, answer)` matches (FORMAL-003). The same 28 payloads are also part of the 4,033-input equivalence test above, so both independent rebuilds reproduce them too.
- **Judge:** all 13 recorded Judge verdicts were reproduced by re-running the unchanged pipeline (FORMAL-004).

## 4. 13-world qualification of the closure runtime

This is a fresh execution: no historical PASS was reused.

**Setup**
- The driver is `f005_campaign.py`, derived from the G4-B driver by substituting output and name prefixes only.
- The stage is a frozen copy of R2 `d4b0f83`, which includes all FORMAL-001 closures: `LeanGatedWorld`, the decider pin, the answer-channel check and the event check.
- The source manifest was checked before and after every world.
- Each world used 100 registered workers, real NIM agents, and the independent Judge in its isolated namespace, with the T13 contract-binding check.

**Result:** **13/13 PASS** (`QUALIFICATION_LEDGER.json`, `QUALIFICATION_CAMPAIGN.log`).

| Measure | Result |
|---|---|
| Judge verdicts | 13 PASS, 0 issues |
| Contract binding | 13 BOUND |
| Native effects | 27 |
| Lean T decisions | 28 (NOI: 2 T, 1 effect; the second T led to a non-applied write) |
| Workers per world | 100 |
| Stage source | unchanged |

**Trace conformance** of the new runs to the FORMAL-003 refinement hypotheses (`QUALIFICATION_TRACE_CONFORMANCE.json`): 13 runs, 27 effects, **28/28** decision digests replayed exactly, **0** violations.

## 5. Negative testing

| Suite | Result |
|---|---|
| R2 commit boundary (G2/G4 boundary, world negatives, commit boundary, E6E) | 60/61 before and after the closure. The one failure, `test_n6_replay_denied_and_positive_applies`, is identical on the baseline; it is a legacy permit without Lean binding and is preserved. |
| R2 FORMAL-001 closure tests | 9/9 |
| Commerce | FORMAL-001 negatives 6/6 (2/6 with 3 forbidden POSTs before the closure); sandbox admission 22/22; LMF-007 6/6; A04 42/42; bridge 19/19; gateway uncertainty conformance 6/6 |
| Federation | world cases **52/52** (13 worlds × P/N/R/A) |
| Marketplace | negatives **25/25**, 0 forbidden effects. The first attempt was invalid because of a harness `PYTHONPATH` error before any test ran; its log is preserved. |

## 6. Immutable evidence manifest

- `closure/CLOSURE_MANIFEST.json` holds the sha256 of every new proof source and every closure evidence file in the public repository. It is tagged with release `v1.1.0`.
- Each Dropbox deposit (`FORMAL_CLOSURE_20261107/FORMAL-00N/`) carries its own `EVIDENCE_HASHES.sha256`.

## Uncovered assumptions and blockers

- **Byte reproducibility:** the decider binary is not byte-reproducible, so the pin rejects third-party rebuilds (owner decision).
- **Runtime is private:** the qualification and conformance evidence depends on the private LEGION runtime and can only be checked by its holder. The public repository pins the outputs by hash.
- **Commerce A03 re-acceptance:** the production profile fails closed until the operator re-signs the A03 acceptance.
- **Federation/Marketplace effects:** their simulated effects remain outside the Lean boundary.
- **No payment was made** in any FORMAL work order.
