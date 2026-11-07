# Proof scope: LEGION Formal Core v1.0.0, with the v1.1.0 closure release

Four kinds of statement are kept strictly apart. Only category 1 is established by this repository.

## 1. Lean-proved mathematical properties (this repository)
Machine-checked by the Lean 4.29.1 kernel. They depend only on `propext`, `Quot.sound` and `Classical.choice`.
The 52 audited declarations, with exact statements, are in `PROOF_MANIFEST.json` and
`qualified/THEOREM_STATEMENTS.txt`:

- T1–T10: system safety of the Core model (see README).
- T11–T15: specification integrity (ADDENDUM-001).
- J1–J6: causal closure computed from the raw journal, grounded in the admission decision.
- Kernel-evaluated countermodels (every guard is necessary) and liveness witnesses.

Explicit model hypotheses, stated in the theorems and never as axioms:

| Id | Hypothesis |
|---|---|
| A-C1 | Permit MACs are unforgeable: only authority-issued permits verify, modelled as membership in `issued` |
| A-H1 | Canonical mission hashing is injective on the contracts that occur, modelled as identity |
| A-S1 | Execution-agent credentials are not specification-authority credentials (hypothesis of T12b) |

## 2. Runtime properties supported by differential and integration testing (NOT proved here)
This evidence comes from the LEGION qualification (FORMAL-CORE-001). It is finite, and it is **not** a proof:

- The compiled decision agrees with an independent oracle on 12,000 generated adversarial cases: 0 mismatches,
  0 attacks admitted.
- Lean closure equals the reference registry on 174/174 historical journal prefixes. On 2 × 3,000 generated
  journals, every difference was classified, with 0 unexplained.
- 27/27 historical effects were admitted by the boundary abstraction.
- 18 boundary tests, 26 world-specific negatives and 7 specification-integrity negatives passed against the real
  commit boundary.
- A live 13-world qualification produced 13/13 Judge PASS, 27 effects each bound to a Lean T decision, 0
  unauthorized and 0 duplicates.

These results require the LEGION runtime and private qualification evidence. They are **external evidence**:
they are not reproducible from this repository alone and are not part of its claims.

## 3. Unproved proof-to-execution obligations (retained explicitly)
| Id | Obligation | Status |
|---|---|---|
| PE1 | The executable computes `admission .full` | Compiled from the proved definition. Trusts the Lean compiler, the C toolchain and the unverified JSON layer in `Main.lean` |
| **PE2** | Every new runtime effect passes the Lean gate for that exact action (gating completeness) | **Not formally proved.** Code inspection plus tests |
| **PE3** | The runtime-to-model abstraction is faithful | **Only partly proved.** Dependency closure is proved here (J1–J6). Per-record content verdicts (`Rec.ok`), activation (`JTask.na`) and the rest of the abstraction are trusted inputs |
| **PE4** | Each runtime step refines a model step | **Not proved** |

### Closure release v1.1.0 (FORMAL-001 … FORMAL-005, 2026-11-07): status of PE1–PE4

The v1.0.0 statements above are unchanged. v1.1.0 adds the separate library `LegionAbstraction` (not imported by
`LegionCore` or `Main`; the decider binary is unchanged) and closure evidence in `closure/`.

| Id | What v1.1.0 adds | What it still does NOT establish |
|---|---|---|
| PE1 | <ul><li>Two clean rebuilds generate C that is byte-identical to the qualified build.</li><li>The rebuilt binaries give byte-identical outputs on 4,033 inputs.</li><li>The axiom audit is identical to the qualified one.</li></ul> | <ul><li>The native binary is not byte-reproducible (its bytes depend on the build path).</li><li>The Lean compiler, the C toolchain and the JSON layer of `Main.lean` remain trusted.</li></ul> |
| PE2 | <ul><li>A complete static census of every effect-primitive call site in the runtime, Commerce, Federation and Marketplace sources: 124 sites, 0 unclassified, 0 open bypasses.</li><li>Four bypasses closed in the runtime with enforcement, each with before/after negative tests: the A04 signed-claim permit, the v1 bridge without the qualified decider, the unpinned decider binary, and world writes without a Lean ticket.</li></ul> | <ul><li>Not a Lean theorem: Python control flow is not modelled.</li><li>Federation/Marketplace simulated world effects are outside the Lean boundary (F) and are not claimed.</li></ul> |
| PE3 | <ul><li>M1 (`decision_rn`, `grounds_rn`, `closedSet_rn`): the decision, its grounds and the journal closure depend only on the equality of identifiers.</li><li>M0: the interner model is injective.</li><li>M2/M3 (`alpha_T_requires`, `alpha_sound`): the meaning of T for the raw runtime strings under α's shape.</li><li>Python's serializer satisfies α's shape on 1,500 randomized states, 7,640 renamed decisions through the binary and 28 recorded payloads, with 0 violations.</li></ul> | <ul><li>The Python serializer is not proved to equal Lean α; it is validated.</li><li>`Rec.ok` and `JTask.na` remain trusted inputs.</li></ul> |
| PE4 | <ul><li>RF1/RF2 (`step_refines`, `trace_effects_admitted`, `trace_once`): every disciplined boundary step is a model step, including uncertain outcomes.</li><li>RF3 (`grun_one_create`, `grun_one_capture`, `uncertainty_sound`): under provider uncertainty, at most one create and one capture per effect, each Lean-attested, for every resolution of the uncertainty.</li><li>Trace conformance: 13 recorded runs with 28/28 decision digests replayed; 6 gateway uncertainty scenarios; the recorded PayPal Sandbox ledger.</li></ul> | <ul><li>That the Python implements the step relations: validated, not proved.</li><li>Non-boundary model steps are not simulated.</li><li>Provider semantics are abstracted.</li></ul> |
| Judge | <ul><li>JC1–JC4 (`judgeSpecB_iff`, `journal_judge_grounded`, `judge_ignores_contract_record`, `amended_list_can_pass`).</li><li>The unchanged qualification Judge agrees with Lean `judgePass` on 61/61 runs and mutations, with 0 T9 and 0 T14 violations.</li></ul> | <ul><li>The Judge's Python is not proved.</li><li>Judge checks beyond obligation closure (goal predicates, causation, budgets) are not covered by T9/T14.</li></ul> |

**Consequence:** citing this repository supports the claim *"the admission decision gating consequential
effects is compiled from Lean definitions whose safety properties are machine-checked over the model"*. It does
**not** support *"LEGION's runtime is fully formally verified"*.

## 4. Trusted assumptions and external components
- Lean kernel, Lean compiler, bundled C toolchain; the JSON parse layer (`Main.lean`).
- The runtime abstraction, content validators and activation logic (Python, in LEGION; not published here).
- Operating system, process isolation, monotonic clocks, journal append atomicity.
- Cryptographic primitives (HMAC-SHA256, SHA-256), assumed per A-C1 / A-H1.
- Out of scope entirely: LLM reasoning, world/environment dynamics, network behaviour, production payment
  processing, third-party integrations and physical actuators.
- The LEGION qualification ran in a TEST security posture (HMAC seal fallback, unverified workload-identity
  header). T4 therefore does not establish authenticity of runtime identities.
