"""Fix the FORMAL-002 smoke-run wording, build patch sets and deposit FORMAL-002 and FORMAL-003 evidence."""
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
R2 = Path(r"C:\Users\Administrator\LEGION_R2")
CO = Path(r"C:\Users\Administrator\Documents\ChatGPT\Hackathons\LEGION-Commerce-Q002")
TMP = Path(r"C:\Users\ADMINI~1\AppData\Local\Temp\claude\f1")

p = HERE / "formal002" / "REPORT.md"
s = p.read_text(encoding="utf-8")
a = ("The smoke runs are preserved (`FORMAL002_ALPHA_VALIDATION_smoke.json`). The first two runs produced no T verdict at all "
     "(all-F, then a contract-version generator bug); the generator was corrected, nothing in the system under test changed.")
b = ("Smoke runs: only the third smoke run's output survives (`FORMAL002_ALPHA_VALIDATION_smoke.json`); the first two were "
     "overwritten. Both produced no T verdict (all-F, then a contract-version generator bug, 26 designed-valid requests all "
     "`CONTRACT=F`). The generator was corrected; nothing in the system under test changed.")
if a in s:
    p.write_text(s.replace(a, b), encoding="utf-8")
    print("FORMAL-002 report wording fixed")

for name, repo, rng in (("r2p2", R2, "4c14810..386341b"), ("cop3", CO, "0da8501..61dd814")):
    out = TMP / name
    shutil.rmtree(out, ignore_errors=True)
    subprocess.run(["git", "-C", str(repo), "format-patch", "-q", rng, "-o", str(out)], check=True)


def deposit(*args):
    subprocess.run([sys.executable, str(HERE / "deposit.py"), *map(str, args)], check=True)


fc = R2 / "formal_closure"
deposit("FORMAL-002", HERE / "formal002" / "WO_VERDICT.json", HERE / "formal002" / "REPORT.md",
        f"{R2 / 'formal/LegionCore/LegionAbstraction'}=lean/LegionAbstraction",
        f"{R2 / 'formal/LegionCore/lakefile.toml'}=lean/lakefile.toml",
        fc / "FORMAL002_003_STATEMENTS_AND_AXIOMS.txt", fc / "FORMAL002_ALPHA_VALIDATION.json",
        fc / "FORMAL002_ALPHA_VALIDATION_smoke.json", R2 / "tests/legion_struct/causal_007/alpha_shape_check.py",
        f"{TMP / 'r2p2'}=r2_patches")
deposit("FORMAL-003", HERE / "formal003" / "WO_VERDICT.json", HERE / "formal003" / "REPORT.md",
        f"{R2 / 'formal/LegionCore/LegionAbstraction/Refinement.lean'}=lean/Refinement.lean",
        fc / "FORMAL002_003_STATEMENTS_AND_AXIOMS.txt", fc / "FORMAL003_R2_TRACE_CONFORMANCE.json",
        R2 / "tests/legion_struct/causal_007/refinement_conformance.py",
        f"{CO / 'formal003_evidence'}=commerce_logs", CO / "commerce_demo/formal003_conformance.py",
        f"{TMP / 'cop3'}=commerce_patches")
