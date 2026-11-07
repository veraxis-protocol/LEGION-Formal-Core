"""Deposit FORMAL-004 evidence."""
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
R2 = Path(r"C:\Users\Administrator\LEGION_R2")
TMP = Path(r"C:\Users\ADMINI~1\AppData\Local\Temp\claude\f1")
out = TMP / "r2p4"
shutil.rmtree(out, ignore_errors=True)
subprocess.run(["git", "-C", str(R2), "format-patch", "-q", "386341b..73660d1", "-o", str(out)], check=True)
fc = R2 / "formal_closure"
subprocess.run([sys.executable, str(HERE / "deposit.py"), "FORMAL-004", str(HERE / "formal004" / "WO_VERDICT.json"),
                str(HERE / "formal004" / "REPORT.md"),
                f"{R2 / 'formal/LegionCore/LegionAbstraction/JudgeConformance.lean'}=lean/JudgeConformance.lean",
                str(fc / "FORMAL002_003_004_STATEMENTS_AND_AXIOMS.txt"), str(fc / "FORMAL004_JUDGE_CONFORMANCE.json"),
                str(R2 / "tests/legion_struct/causal_007/judge_conformance.py"), str(fc / "judge_rerun.sh"),
                f"{out}=r2_patches"], check=True)
