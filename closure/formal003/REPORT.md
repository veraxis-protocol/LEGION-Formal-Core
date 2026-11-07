# FORMAL-003 — Runtime-step to model-step refinement at the qualified execution boundary, including external-effect uncertainty

**Verdict: T for the stated refinement theorems and for trace conformance of every recorded run.**

That the Python code implements the abstract step relation is **not** proved. It rests on the FORMAL-001 boundary discipline (enforcement plus census) and on executable trace conformance.

## Sources

| Part | Location | Commit |
|---|---|---|
| Lean | LEGION R2 `formal/LegionCore/LegionAbstraction/Refinement.lean` | `386341b` |
| R2 trace conformance | `tests/legion_struct/causal_007/refinement_conformance.py` | `386341b` |
| Commerce | `commerce_adapter/gateway.py` (`LEAN_ATTESTED` journal event), `commerce_demo/formal003_conformance.py` | `61dd814` (branch `claude/formal-closure-001`) |

## Proof statements

**World commit boundary.** A runtime `/actuate` step is recorded as `RStep`: the α-encoded decider input, an `Outcome` and the appended `NATIVE_EFFECT` records.
- The outcomes are refused, applied, duplicate, lostReply, unknown (finalize failed), crashBefore and crashAfter.
- Effect-creating outcomes are applied, lostReply, unknown and crashAfter: the effect is durable even when the caller cannot know it.
- `RStep.disciplined`: an effect-creating outcome implies decision T and new effects = `[effectOf sp r]`; any other outcome implies no new effect. This is exactly what FORMAL-001 enforces.

| Id | Lean | Statement |
|---|---|---|
| RF1 | `step_refines` | Every disciplined step is a model step. When the step created an effect, `exec .full sp pre (.actuate r) = some s'` with `s'.ledger = newEffects ++ pre.ledger` and the nonce consumed. Otherwise the step is `crash`, a stutter with `s' = pre`. |
| RF1′ | `runtime_effect_admitted` | Every runtime effect equals `effectOf sp r` and `admission .full` was T in its exact pre-state |
| RF2 | `trace_effects_admitted`, `ledger_continuity`, `trace_once` | Over a disciplined trace with log continuity (each decision's ledger is a permutation of the previous ledger plus its appended effects):<ul><li>every appended effect was admitted in its pre-state;</li><li>the ledger is the initial ledger plus all appended effects;</li><li>task ids in the runtime ledger are pairwise distinct after every step (exactly once per task).</li></ul> |

**External effects under uncertainty (Commerce Gateway).** `gstep` is the Gateway's per-effect lifecycle:
- create only from RESERVED, with a Lean-T attestation;
- capture only from APPROVED, with `capture_started` unset and a Lean-T attestation;
- reconciliation readbacks never return to RESERVED, nor to APPROVED once capture has started.

| Id | Lean | Statement |
|---|---|---|
| RF3a/b | `grun_one_create`, `grun_one_capture` | Over **any** event trace, an effect id is dispatched for create at most once and for capture at most once |
| RF3c | `dispatch_needs_lean` | Every dispatch carries a Lean-T attestation |
| RF3c | `uncertainty_sound` | For **every** provider world consistent with the trace (each dispatched POST may or may not have taken effect; nothing undispatched did), the provider holds at most one capture. It holds one only if a Lean-attested capture dispatch occurred. |

Axioms: `propext`, `Quot.sound` and `Classical.choice` only, with 0 `sorry` (`FORMAL002_003_STATEMENTS_AND_AXIOMS.txt`).

## Trace conformance (executable)

**R2 recorded runs** (13 worlds, G4-B qualification; `FORMAL003_R2_TRACE_CONFORMANCE.json`):

| Check | Result |
|---|---|
| Native effects / Lean decisions | 27 / 28 |
| D1/D2: every effect bound by `lean_decision_sha256` to a prior T decision for the same command, task, agent and permit; effect is `effectOf`-consistent with the payload; mission equal | All |
| D3: re-running the pinned decider on each logged payload reproduces `sha256(payload, answer)` exactly | **28/28** |
| D4: no effect after a non-T decision | Holds |
| D5: continuity (payload ledger size = prior effects) | Holds |
| D6: tasks and commands distinct | Holds |
| Violations | **0** |

**Commerce Gateway** (`FORMAL003_GATEWAY_CONFORMANCE.json`):
- Six provider-uncertainty scenarios against a non-mock stub with the real decider. Each scenario retries create and capture twice after the uncertain step, which the Gateway must not re-dispatch.

  | Scenario | Result |
  |---|---|
  | normal | CAPTURE_CONFIRMED |
  | lost create reply | RECONCILIATION_PENDING |
  | lost capture reply | Uncertain, then resolved by readback to CAPTURE_CONFIRMED |
  | capture pending | RECONCILIATION_PENDING |
  | capture declined | FAILED_HELD |
  | never approved | APPROVAL_PENDING |

  All scenarios satisfy C1–C5: at most one create POST and one capture POST per effect at the provider; every POST is immediately preceded by `LEAN_ATTESTED` for the exact intent digest; capture only from an APPROVED readback after CAPTURE_INTENT; CAPTURE_CONFIRMED only by readback; and the journal replays through the executable mirror of `gstep`.
- The recorded LMF-007 PayPal Sandbox ledger (4 effects, pre-closure) satisfies C1, C3, C4 and C5. C2 is **NOT_LOGGED** there, because the attestation event did not exist yet.
- **Preserved failure:** conformance run 1 failed `lost_capture_reply` because of a **checker defect**: `NETWORK_ERROR` carries no `operation`, and the checker defaulted it to "create". The provider had received exactly 1 create and 1 capture POST. The checker now infers the operation from the preceding `*_INTENT`. The run-1 output is kept as `..._run1_CHECKER_DEFECT_network_error_op.json`.

**Regressions after adding the `LEAN_ATTESTED` journal event:** A04 42/42, sandbox admission 22/22, LMF-007 negatives 6/6, FORMAL-001 negatives 6/6.

## Uncovered assumptions and residuals

- **Implementation link:** the Python implementation of `RStep` and `gstep` is validated (census, enforcement, conformance), not proved.
- **Continuity is a hypothesis:** an append-only world log and an α ledger built from it. It is checked on recorded runs (D5), not proved for the OS or filesystem.
- **Non-boundary model steps** (report, tick, close, readback, evidence) are not related to runtime steps here. RF2 is a statement over the boundary's own steps, not a full `Reach`-from-init simulation of the whole runtime.
- **Provider behaviour** is modelled only as "a dispatched POST may or may not take effect". Real PayPal semantics are not verified. No live PayPal call was made in FORMAL-003.
