# FORMAL-001 — Consequential-effect path census and bypass closure

**Verdict: T for the qualified execution boundary. F for Federation/Marketplace simulated world effects, which are outside the Lean boundary and explicitly not claimed.**

PE2 (gating completeness) is now supported by a complete static census plus runtime enforcement and negative tests. It is **not** a Lean theorem: Python control flow is not modelled in Lean.

## Scope

The **qualified execution boundary** consists of two parts.

| Part | Where | Effect |
|---|---|---|
| (a) World commit boundary | `tests/legion_struct/world_server.py` `/actuate` in the qualified LEGION runtime (R2) | Simulated world effects of the 13 worlds |
| (b) External-effect boundary | Commerce `commerce_adapter/gateway.py` | PayPal Sandbox order create and capture POSTs |

Both are gated by the compiled `legion_decide`, which computes `LegionCore.admission .full`. Its sha256 is `99cda684…ade73a`; it is built with Lean 4.29.1 from Formal-Core `f5ea79c`, which is identical to R2 `formal/LegionCore`.

## Source commits

| Repo | Base | FORMAL-001 head |
|---|---|---|
| LEGION R2 (local branch `formal-closure-001`; the runtime is not public) | `30c7ef1` | `4c14810` |
| LEGION-Commerce (local branch `claude/formal-closure-001`) | `0f397ec` | `0da8501` (closure in `a7436df`) |
| LEGION-Federation (`main`, unchanged) | `9d2a32a` | `9d2a32a` |
| LEGION-Marketplace (`main`, unchanged) | `906ec0f` | `906ec0f` |

## Method

1. `effect_census.py` is an AST scan of every call site of every effect primitive in the four scanned roots (the primitive list is `SINKS`). It covers 124 sites under 110 keys and records the enclosing function. Reflective calls (`eval`, `exec`, `__import__`, `importlib`, `getattr` with a non-literal name) are counted as sinks of their own.
2. `make_classification.py` holds the reviewed rules. Every key must match exactly one rule; explicit keys take precedence over patterns.
3. The census verdict is defined as follows:
   - **T** if every site is classified, no classification is stale, every file parsed and nothing is `BYPASS_OPEN`.
   - **F** if any site is `BYPASS_OPEN`.
   - **Z** otherwise.

   **Result: T** (`EFFECT_PATH_CENSUS.json`, per-file sha256 included).
4. Every effect-creating class was then tested dynamically against the real decider. The tests ran on the code before and after each closure.

| Class | Keys |
|---|---|
| LEAN_GATED | 3 (R2 `/actuate` write; Gateway create POST; Gateway capture POST) |
| PRIMITIVE_INTERNAL | 8 |
| SIMULATED_OUTSIDE_LEAN_BOUNDARY | 4 (Federation simulated world writes and admin event injection) |
| EXOGENOUS_WORLD_DYNAMICS | 4 |
| ANSWER_RECORD | 1 |
| SEPARATE_TEST_WORLD | 3 |
| READ_ONLY_EXTERNAL | 2 |
| AUTH_TOKEN_EXCHANGE | 1 |
| MODEL_INFERENCE | 6 |
| LOOPBACK_IPC | 26 |
| PROCESS_TOOLING | 34 |
| FAULT_INJECTION_OR_EXIT | 9 |
| REFLECTIVE_REVIEWED | 9 |

## Bypasses found and closed

| Id | Bypass (before) | Closure | Evidence (before → after) |
|---|---|---|---|
| **B-COM-1** | The A04 CLI (`python -m commerce_adapter create/capture`) used the base `Admission`. That admission accepts a signed permit which merely **claims** `lean_rule_earned: true, verdict: "T"`; no Lean decision is computed at the gate. | `Gateway.require_lean`. Every POST to a non-`MOCK_ONLY` provider needs the Lean-T attestation produced by the admission check in the **same transaction**, bound to `digest(intent)`. The attestation is single use. | FAIL: dispatched, 1 POST → PASS: `LEAN_ADMISSION_REQUIRED`, 0 POST, state stays RESERVED |
| **B-COM-2** | The v1 bridge, with sources that are not qualified, computes only a Python Core plus a ZTL witness. It does not compute `admission .full`. | `lean_attestation()` returns None unless a qualified `legion_decide` verdict is present. The Gateway therefore refuses. | FAIL: no mechanism → PASS |
| G-1 | Attestation for another intent | Bound to the intent digest | FAIL: 1 POST → PASS: 0 POST |
| G-2 | Cached or stale verdict reused at a later gate | `check()` clears the attestation before every admission run | FAIL: 1 POST → PASS: 0 POST |
| **B-R2-1** | `legion_decide` was chosen by the `LEGION_DECIDE_BIN` path, so any binary answering T was accepted. | Pinned sha256; any other binary means Lean is unavailable (verdict Z), so no effect. | Unpinned binary and 1-byte-modified copy both refused; the pinned binary is accepted |
| **B-R2-2** | Only control flow in `_actuate` stood between `WORLD.call_write` and a new effect. | `LeanGatedWorld`: a new-effect write needs a single-use ticket. The ticket is minted only after verdict T for exactly (command_id, tool, target, args). Idempotent replays need no ticket and create no effect. | No ticket, other args, other command or reused ticket → 403 with no state change |
| **B-R2-3** | `/analyze` writes `state.answers` without Lean. It would become an effect channel if any rule read answers; none of the 13 worlds does. | A world whose preconditions, effects, derived rules, events or gate facts read `answers` is refused at start. | 13/13 worlds clean; a mutated world is rejected |
| **B-R2-4** (latent) | Pinned `World.fire` falls back to the **caller's** event dict for an unknown id, so caller-invented effects could be applied. | `LeanGatedWorld.fire` accepts spec events only. | An invented event cannot fire |

Not a bypass, but recorded:
- `CausalHost` builds its own in-memory `World` (`SEPARATE_TEST_WORLD`). It is unreachable from all 10 qualified runtime entry points (import-closure test).

## Test logs

**R2** (WSL Python 3.12.3, pytest 9.1.1, real decider through interop):

| Run | Result |
|---|---|
| `FORMAL001_R2_CLOSURE_TESTS.log` | 9/9 |
| `R2_BOUNDARY_REGRESSION_BEFORE.log` (boundary, world negatives, commit boundary, E6E) | 60 passed, 1 failed |
| `..._AFTER.log` | 60 passed, 1 failed |

The 1 failure in both runs is the same test, `test_n6_replay_denied_and_positive_applies`. It fails identically on the baseline because its legacy permit has no Lean binding, so `/actuate` correctly refuses it. It is pre-existing and preserved, not fixed here.

**Commerce** (Windows `.venv`, Python 3.14.7):

| Suite | Before closure | After closure |
|---|---|---|
| A04 gateway | 42/42 | 42/42 |
| Bridge | 18/19 (`CORE_RUNTIME_TIMEOUT` under load) | 19/19 |
| `formal001_negatives` | 2/6, 3 forbidden POSTs | 6/6, 0 forbidden POSTs |
| Sandbox admission | — | 22/22 |
| LMF-007 negatives | — | 6/6 |

Two invalid runs are kept and labelled:
- one run of the A04 and bridge suites made with the wrong interpreter (no dependencies);
- one bridge run invalidated because I stashed the sources while it was running.

## Uncovered assumptions and residuals

- **TCB-1:** the census is complete relative to `SINKS`, the scanned roots and non-reflective static dispatch. Code modification, monkeypatching outside the reviewed shims, and OS-level tampering are out of scope.
- **Decider pin TOCTOU:** the binary is hashed, then executed by path. A writer of that path between hash and exec is not excluded.
- **`MOCK_ONLY` exemption:** test doubles that declare `evidence_mode == "MOCK_ONLY"` are exempt from `require_lean`. The flag is self-declared by the provider object (TCB-1).
- **A03 re-acceptance:** the production profile pins `commerce_adapter` source hashes in the signed acceptance. Changing `gateway.py` means the production profile now fails closed with `A03_ADAPTER_CORRESPONDENCE` until the operator re-signs the acceptance. The sandbox-demo-v1 profile is unaffected.
- **Federation/Marketplace:** their world writes are SIMULATED and admitted by the federation-edge T/F/Z policy, which is tested but not Lean-proved. **Verdict F with respect to mandatory Lean admission.** They are not part of the claimed boundary.
  - Their only external effect, PayPal, runs through the Lean-gated Gateway.
  - Federation admin event endpoints still pass caller input to the pinned `World.fire` (operator token only).
- **The gating proof is not mechanized.** PE2 is now an exhaustive census plus enforcement plus tests. A Lean theorem about Python control flow would need a verified Python semantics.
