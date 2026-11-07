"""Assemble LEGION-Formal-Core v1.1.0 (closure release) from the qualified R2 sources and the closure evidence.

Copies the LegionAbstraction library byte-exactly from R2 `formal-closure-001`, adds the evidence the reports cite,
and writes closure/CLOSURE_MANIFEST.json (sha256 of every proof source and every evidence file)."""
import hashlib
import json
import shutil
from pathlib import Path

PUB = Path(r"C:\Users\Administrator\LEGION_FORMAL_PUBLISH")
R2 = Path(r"C:\Users\Administrator\LEGION_R2")
LC = R2 / "formal/LegionCore"
FC = R2 / "formal_closure"
CO = Path(r"C:\Users\Administrator\Documents\ChatGPT\Hackathons\LEGION-Commerce-Q002")
EV = PUB / "closure" / "evidence"


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    # proof sources (byte-exact)
    shutil.rmtree(PUB / "LegionAbstraction", ignore_errors=True)
    shutil.copytree(LC / "LegionAbstraction", PUB / "LegionAbstraction")
    for f in ("LegionAbstraction.lean", "lakefile.toml"):
        shutil.copy2(LC / f, PUB / f)
    for f in ("LegionCore.lean", "Main.lean", "lean-toolchain"):
        assert sha(LC / f) == sha(PUB / f), f"{f} differs from the published v1.0.0 source"
    for p in (LC / "LegionCore").glob("*.lean"):
        assert sha(p) == sha(PUB / "LegionCore" / p.name), p.name
    shutil.copy2(FC / "f005" / "STATEMENTS_CLEAN.txt", PUB / "qualified" / "CLOSURE_STATEMENTS_AND_AXIOMS.txt")
    # evidence cited by the reports
    shutil.rmtree(EV, ignore_errors=True)
    EV.mkdir(parents=True)
    items = {
        "formal002/FORMAL002_ALPHA_VALIDATION.json": FC / "FORMAL002_ALPHA_VALIDATION.json",
        "formal003/FORMAL003_R2_TRACE_CONFORMANCE.json": FC / "FORMAL003_R2_TRACE_CONFORMANCE.json",
        "formal003/FORMAL003_GATEWAY_CONFORMANCE.json": CO / "formal003_evidence/FORMAL003_GATEWAY_CONFORMANCE.json",
        "formal003/FORMAL003_GATEWAY_CONFORMANCE_run1_CHECKER_DEFECT.json":
            CO / "formal003_evidence/FORMAL003_GATEWAY_CONFORMANCE_run1_CHECKER_DEFECT_network_error_op.json",
        "formal004/FORMAL004_JUDGE_CONFORMANCE.json": FC / "FORMAL004_JUDGE_CONFORMANCE.json",
        "formal001/FORMAL001_COMMERCE_NEGATIVES.json": CO / "formal001_evidence/FORMAL001_COMMERCE_NEGATIVES.json",
        "formal001/FORMAL001_COMMERCE_NEGATIVES_BEFORE_CLOSURE.json": CO / "formal001_evidence/FORMAL001_COMMERCE_NEGATIVES_BEFORE_CLOSURE.json",
        "formal001/FORMAL001_R2_CLOSURE_TESTS.log": FC / "FORMAL001_R2_CLOSURE_TESTS.log",
        "formal001/R2_BOUNDARY_REGRESSION_BEFORE.log": FC / "R2_BOUNDARY_REGRESSION_BEFORE.log",
        "formal001/R2_BOUNDARY_REGRESSION_AFTER.log": FC / "R2_BOUNDARY_REGRESSION_AFTER.log",
        "formal005/DECIDER_FUNCTIONAL_EQUIVALENCE.json": FC / "f005/DECIDER_FUNCTIONAL_EQUIVALENCE.json",
        "formal005/CLEAN_BUILD.log": FC / "f005/CLEAN_BUILD.log",
        "formal005/CLEAN_BUILD_IR_C_SHA256.txt": FC / "f005/CLEAN_BUILD_IR_C_SHA256.txt",
        "formal005/QUALIFIED_BUILD_IR_C_SHA256.txt": FC / "f005/QUALIFIED_BUILD_IR_C_SHA256.txt",
        "formal005/AXIOM_AUDIT_CLEAN.txt": FC / "f005/AXIOM_AUDIT_CLEAN.txt",
        "formal005/FEDERATION_WORLD_CASES.log": FC / "f005/fed_world_cases.log",
        "formal005/MARKETPLACE_NEGATIVES.log": FC / "f005/market_negatives.log",
        "formal005/MARKETPLACE_NEGATIVES_INVALID_pythonpath.log": FC / "f005/market_negatives_INVALID_pythonpath.log",
    }
    for name in ("QUALIFICATION_LEDGER.json", "QUALIFICATION_CAMPAIGN.log", "QUALIFICATION_TRACE_CONFORMANCE.json"):
        p = FC / "f005" / name
        if p.exists():
            items["formal005/" + name] = p
    for dst, src in items.items():
        (EV / dst).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, EV / dst)
    proof = {str(p.relative_to(PUB)).replace("\\", "/"): sha(p) for p in sorted(PUB.glob("LegionAbstraction/*.lean"))}
    proof["LegionAbstraction.lean"] = sha(PUB / "LegionAbstraction.lean")
    proof["lakefile.toml"] = sha(PUB / "lakefile.toml")
    evidence = {str(p.relative_to(PUB)).replace("\\", "/"): sha(p) for p in sorted((PUB / "closure").rglob("*")) if p.is_file()
                and p.name != "CLOSURE_MANIFEST.json"}
    manifest = {"release": "v1.1.0 (closure)", "lean_toolchain": "leanprover/lean4:v4.29.1",
                "legion_decide_qualified_sha256": "99cda684f29afba33e69b8f4811d754c499987c30c07ac1c67f19ec250ade73a",
                "decider_sources_unchanged_since_v1.0.0": True,
                "r2_closure_head": "formal-closure-001 (private runtime; commits cited in each WO report)",
                "proof_sources_sha256": proof, "evidence_sha256": evidence}
    (PUB / "closure" / "CLOSURE_MANIFEST.json").write_text(json.dumps(manifest, indent=1, sort_keys=True))
    print(json.dumps({"proof_sources": len(proof), "evidence_files": len(evidence)}))


if __name__ == "__main__":
    main()
