# Provenance and file-level licensing: LEGION Formal Core v1.0.0

All published files are original works created for Veraxis in the LEGION formal-core work orders
(WO-LEGION-FORMAL-CORE-001, ADDENDUM-001, WO-LEGION-FORMAL-PUBLISH-001). They were committed on the LEGION
`formal-core-r2` branch and are licensed under **PolyForm Noncommercial 1.0.0** (`LICENSE`), with the required
notice in `NOTICE`.

No third-party source code is included. The Lean files import only Lean core (`Lean.Data.Json` in `Main.lean`).
No Mathlib, no ZTL, no CAGE and no LEGION runtime code is vendored. The Lean toolchain (Apache-2.0) is
downloaded by elan at build time and is not redistributed here.

Source files are kept byte-identical to the qualified proof manifest, so they carry no per-file license header.
This table is the file-level license record.

| File | Origin | License |
|---|---|---|
| `LegionCore/State.lean`, `Admission.lean`, `Transitions.lean`, `SystemSafety.lean`, `Authority.lean`, `Resources.lean`, `Recovery.lean`, `Completion.lean`, `Countermodels.lean`, `Journal.lean`, `SpecAuthority.lean`, `MissionPreservation.lean`, `ProofSpecBinding.lean` | original, Veraxis | PolyForm-Noncommercial-1.0.0 |
| `LegionCore.lean`, `Main.lean`, `AxiomAudit.lean`, `StatementDump.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | original, Veraxis | PolyForm-Noncommercial-1.0.0 |
| `PROOF_MANIFEST.json`, `qualified/AXIOM_AUDIT.txt`, `qualified/THEOREM_STATEMENTS.txt` | generated from the above by Lean / the qualification tooling | PolyForm-Noncommercial-1.0.0 |
| `README.md`, `PROOF_SCOPE.md`, `REPRODUCE.md`, `PROVENANCE.md`, `NOTICE`, `.gitattributes`, `.gitignore` | original, Veraxis | PolyForm-Noncommercial-1.0.0 |
| `LICENSE` | PolyForm Noncommercial License 1.0.0 text, verbatim from https://polyformproject.org/licenses/noncommercial/1.0.0 (the same file as LEGION's `LICENSE`) | license text |

**References, not copies.** Comments name the ZTL / ztl-swarm threshold rule and strong-Kleene conjunction. The
Core reimplements these standard definitions independently; no ZTL source is copied or imported.
