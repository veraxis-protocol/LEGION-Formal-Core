# Proof scope: LEGION Formal Core v1.0.0

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
