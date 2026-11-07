# Reproducing LEGION Formal Core v1.0.0

Everything here needs only public sources. No access to Veraxis machines, private runtime data or credentials is
required.

## Requirements
- `git`
- elan (the Lean toolchain manager), from https://github.com/leanprover/elan. Lake installs the pinned toolchain
  `leanprover/lean4:v4.29.1` automatically from `lean-toolchain`.
- Linux, macOS or Windows. `lake build` also compiles the `legion_decide` executable, which needs the C toolchain
  bundled with Lean (no system compiler is required).

## 1. Fetch the exact release
```
git clone https://github.com/veraxis-protocol/LEGION-Formal-Core.git
cd LEGION-Formal-Core
git checkout v1.0.0
git rev-parse HEAD          # must equal the commit the v1.0.0 tag points to (see the release notes)
```
On Windows, add `-c core.autocrlf=false` to the clone so that line endings, and therefore file hashes, stay
byte-exact. `.gitattributes` also marks every file `-text`.

## 2. Check source correspondence with the qualified manifest
`PROOF_MANIFEST.json` → `source_sha256` holds the qualified SHA-256 of every proof source.
```
python3 - <<'EOF'
import hashlib, json
m = json.load(open("PROOF_MANIFEST.json"))
bad = [f for f, h in m["source_sha256"].items() if hashlib.sha256(open(f, "rb").read()).hexdigest() != h]
print(len(m["source_sha256"]), "files,", len(bad), "mismatches", bad)
EOF
```
Expected: `19 files, 0 mismatches`.

## 3. Build
```
lake build
```
Expected: `Build completed successfully` (33 jobs on a clean checkout of v1.0.0; 40 jobs from v1.1.0 on, which also
builds `LegionAbstraction`), exit code 0.

## 4. Axiom audit and exact statements
```
lake env lean AxiomAudit.lean   > axiom_audit.out    2>&1; echo "exit=$?"
lake env lean StatementDump.lean > statements.out    2>&1; echo "exit=$?"
diff --strip-trailing-cr axiom_audit.out qualified/AXIOM_AUDIT.txt        && echo AUDIT_IDENTICAL
diff --strip-trailing-cr statements.out  qualified/THEOREM_STATEMENTS.txt && echo STATEMENTS_IDENTICAL
grep -cE "^'LegionCore\." statements.out                  # 52
grep -E "sorryAx|ofReduceBool|trustCompiler" axiom_audit.out statements.out || echo "NO_NONSTANDARD_AXIOMS"
```
Expected:
- both exit codes 0;
- `AUDIT_IDENTICAL` and `STATEMENTS_IDENTICAL`;
- `52`;
- `NO_NONSTANDARD_AXIOMS`;
- every axiom line lists a subset of `propext`, `Quot.sound` and `Classical.choice`, or says it depends on none.

The files in `qualified/` are the immutable qualification artefacts, byte-exact. They were generated on Windows
and therefore use CRLF line endings, so compare them line-wise with `--strip-trailing-cr`. The content
(statements, axiom lists) contains no paths and is identical across machines. On Windows PowerShell use
`Compare-Object (Get-Content a) (Get-Content b)`, which is line-based.

## 5. Source scan
```
grep -rnE "\bsorry\b|^\s*axiom\b|native_decide|\bunsafe\b|implemented_by" LegionCore *.lean || echo CLEAN
```
Expected: `CLEAN`.

## What is NOT reproducible from this repository
Runtime conformance (differentials against the LEGION runtime, boundary tests, and the live 13-world
qualification) requires the LEGION runtime and private qualification evidence. It is external evidence (see
`PROOF_SCOPE.md` §2). Reproducing it is not part of reproducing these proofs.

## 6. Closure release v1.1.0 (`LegionAbstraction`)
Check out `v1.1.0` instead of `v1.0.0`, then:
```
lake build                                                       # 40 jobs, exit 0
lake env lean LegionAbstraction/StatementDump.lean > closure.out 2>&1; echo "exit=$?"
diff --strip-trailing-cr closure.out qualified/CLOSURE_STATEMENTS_AND_AXIOMS.txt && echo CLOSURE_IDENTICAL
grep -E "sorryAx|ofReduceBool|trustCompiler" closure.out || echo "NO_NONSTANDARD_AXIOMS"
grep -rnE "\bsorry\b|^\s*axiom\b|native_decide|\bunsafe\b|implemented_by" LegionAbstraction || echo CLEAN
python3 -c "import hashlib,json;m=json.load(open('closure/CLOSURE_MANIFEST.json'));b=[f for f,h in {**m['proof_sources_sha256'],**m['evidence_sha256']}.items() if hashlib.sha256(open(f,'rb').read()).hexdigest()!=h];print(len(b),'mismatches',b)"
```
Expected: exit 0, `CLOSURE_IDENTICAL`, `NO_NONSTANDARD_AXIOMS`, `CLEAN`, `0 mismatches`.

On v1.1.0, the v1.0.0 checks (steps 2-5) hold with one declared exception. Step 2 reports exactly **1 mismatch:
`lakefile.toml`**, which gains the `LegionAbstraction` library target; its v1.1.0 hash is in `CLOSURE_MANIFEST.json`.
Every `.lean` file and `lean-toolchain` of v1.0.0 is byte-identical.

The executable validations in `closure/` (census, serializer validation, trace and Judge conformance, the 13-world
qualification) ran against the private LEGION runtime and are external evidence, as in section 2 of `PROOF_SCOPE.md`.
Their scripts are cited by commit in each report; their outputs are hash-pinned in `closure/CLOSURE_MANIFEST.json`.
