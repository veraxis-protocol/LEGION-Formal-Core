# LEGION Formal Core

LEGION Formal Core is a Lean 4 model of the LEGION collective-execution Core. It contains machine-checked proofs
of its safety properties and the **admission decision** that the LEGION runtime compiles and runs at its
consequential-action boundary.

This repository is **proof-only**. It contains no LEGION runtime, CAGE, payment adapters or application code.
It is the immutable, versioned reference that LEGION-100 and LEGION Commerce cite for "what is mathematically
proved about the Core".

- Toolchain: `leanprover/lean4:v4.29.1` (Lean core only; no Mathlib, no external Lean dependencies)
- Release: `v1.0.0`
- Qualified source: LEGION `formal-core-r2` (qualified runtime `d9d38cd6fd9e93e002b0b5d5135377ce1d33d8c8`).
  Every `.lean` file here is byte-identical to the qualified proof manifest.
- License: PolyForm Noncommercial 1.0.0 (see `LICENSE`, `NOTICE`, `PROVENANCE.md`)

## Closure release v1.1.0 (2026-11-07)

v1.1.0 closes the proof-to-execution obligations as far as they can be closed without a verified Python semantics.
**No v1.0.0 `.lean` source changed, and the qualified decider binary is the same.** The one changed v1.0.0 file is `lakefile.toml`, which gains the new library target. The release adds:

- **`LegionAbstraction/`**, a separate Lean library. Its 22 headline statements (`qualified/CLOSURE_STATEMENTS_AND_AXIOMS.txt`), proved with 38 supporting lemmas, cover:
  - the runtime-to-model abstraction α: the decision, its grounds and the journal closure are invariant under identifier renaming, and a T verdict has a defined meaning for the raw runtime strings;
  - runtime-step refinement, including uncertain outcomes and provider uncertainty;
  - conformance of the executable Judge to the T9/T14 completion specification.

  The statements were written to close specific obligations, not to increase the theorem count.
- **`closure/`**, with five work-order reports, each giving its T/F/Z verdict, source commits, proof statements, uncovered assumptions, test logs and blockers:
  - FORMAL-001: effect-path census and bypass closure;
  - FORMAL-002: abstraction;
  - FORMAL-003: refinement;
  - FORMAL-004: Judge conformance;
  - FORMAL-005: build, audit, replay and qualification.

  It also holds the census tool and the cited evidence (`closure/CLOSURE_MANIFEST.json`).

See `PROOF_SCOPE.md`, which has a PE1–PE4 status table, for exactly what is and is not established. Python code, cryptography, PayPal and physical-world behaviour are **not** proved by any theorem here.

## What is proved (Lean 4 kernel-checked)

All of the following are quantified over **every reachable state** of a transition system that includes
recovery, crash and lost reply, specification-change attempts and replanning. They hold for **every** finite
agent population and task graph.

| Family | Property |
|---|---|
| T1 | Admission soundness: every effect comes from an `actuate` whose admission verdict was T, with an issued permit at the current epoch, by the task owner |
| T2 | Causal preservation: effects, closing evidence and closure happen only after dependencies are confirmed |
| T3 | Resource conservation over a generic capacity interface |
| T4 | Identity / authority isolation: caller-supplied ids are never consulted; permits bound to the credential's agent |
| T5 | Evidence non-promotion: stale/unknown reports add no seat; order-independent; T needs ≥ f+1 distinct origins; closure needs verification |
| T6 | Epoch safety: admission only at the current epoch; every lifecycle step revokes earlier permits |
| T7 | Logical exactly-once: ≤ 1 effect per logical command and per command id; fenced commands never execute |
| T8 | Recovery preservation: the system invariant survives every transition, including fence, reconcile, retry and crash |
| T9 | Completion soundness: a Judge PASS (specification) implies every mandatory obligation is closed and verified |
| T10 | Population independence |
| T11–T15 | Original mission preservation; spec changes only by separate authority with a new epoch; proof-to-spec binding (H_admission = H_effect = H_judge = H_mission); non-vacuous completion; replanning without goal mutation |
| J1–J6 | Causal closure computed from the raw journal: causal order, owner-record witnesses, monotonicity, premature evidence never counts, grounding of the admission DEPS guard |

Each family has a **countermodel**: dropping its guard makes the prohibited state reachable. The countermodels
are kernel-evaluated in `LegionCore/Countermodels.lean` and `LegionCore/ProofSpecBinding.lean`. Liveness
witnesses show the full Core reaches a Judge PASS with 2 and with 100 agents.

**Axioms.** Every audited declaration depends only on Lean's standard axioms `propext`, `Quot.sound` and
`Classical.choice`, or on none. There is no `sorry`, no `native_decide` and no custom axiom. The proofs are
**not** axiom-free: they use these three standard axioms.

## What this does NOT establish

Read `PROOF_SCOPE.md` before citing these results. In short:

- The proofs are about the **model** and the admission function. The LEGION runtime is **not** fully formally
  verified:
  - **PE2**, that every runtime effect passes the Lean gate, is not proved.
  - **PE3**, the runtime-to-model abstraction, is only partly proved.
  - **PE4**, runtime-step-to-model-step refinement, is not proved.
- Cryptography is modelled, not proved: permit MACs as unforgeable (A-C1), mission hashes as injective (A-H1).
- Nothing here proves LLM reasoning, world dynamics, payment APIs, third-party integrations or physical/production
  actuators correct.
- T9/T14 are proved against the Judge's *specification* (`judgePass`), not against a Judge implementation.

## How LEGION-100 and LEGION Commerce reference these proofs

Cite the immutable tag and the theorem name, for example
`LEGION-Formal-Core@v1.0.0 : LegionCore.T7_exactly_once`.
`PROOF_MANIFEST.json` lists every theorem with its exact elaborated statement, axioms and source SHA-256. A
consumer should cite the statement, not a paraphrase, together with the scope limits in `PROOF_SCOPE.md`. The
runtime's executable decision (`legion_decide`, built from `Main.lean`) computes `LegionCore.admission .full`,
the function T1–T15 are proved about.

## Verify it yourself

```
git clone https://github.com/veraxis-protocol/LEGION-Formal-Core.git
cd LEGION-Formal-Core && git checkout v1.0.0
lake build
lake env lean AxiomAudit.lean
lake env lean StatementDump.lean
```
See `REPRODUCE.md` for the exact expected results and the byte-level comparison against `qualified/`.

## Layout

| Path | Content |
|---|---|
| `LegionCore/State.lean` … `Completion.lean` | state, admission, transitions, system invariant, T1–T10 |
| `LegionCore/SpecAuthority.lean`, `MissionPreservation.lean`, `ProofSpecBinding.lean` | T11–T15 |
| `LegionCore/Journal.lean` | J1–J6 journal causal closure |
| `LegionCore/Countermodels.lean` | non-vacuity witnesses |
| `Main.lean` | `legion_decide`: JSON front-end to `admission .full` over `Journal.closedSet` |
| `AxiomAudit.lean`, `StatementDump.lean` | audit entry points |
| `PROOF_MANIFEST.json` | qualified manifest (verbatim) |
| `qualified/` | the qualified audit outputs, for byte comparison |

## Related repositories

| Repository | Role | License |
|---|---|---|
| [LEGION Deal Rescue](https://github.com/veraxis-protocol/LEGION-Deal-Rescue) | Merchant application built on this stack: seven-party deals, independent Judge, PayPal Sandbox payments | Apache-2.0 |
| [LEGION](https://github.com/veraxis-protocol/LEGION) | LEGION Core runtime: worlds, admission, independent Judge | PolyForm Noncommercial 1.0.0 |
| [LEGION-Formal-Core](https://github.com/veraxis-protocol/LEGION-Formal-Core) | Lean 4 model of single-collective admission and completion | PolyForm Noncommercial 1.0.0 |
| [LEGION-Federation](https://github.com/veraxis-protocol/LEGION-Federation) | Independent owners' collectives: disclosure policy, signed commitments, multi-party contracts | PolyForm Noncommercial 1.0.0 |
| [LEGION-Marketplace](https://github.com/veraxis-protocol/LEGION-Marketplace) | Intent publication, discovery, end-to-end harness | PolyForm Noncommercial 1.0.0 |
| [LEGION-Commerce](https://github.com/veraxis-protocol/LEGION-Commerce) | PayPal Sandbox adapter, admission bridge, payment orchestration | no license file |
