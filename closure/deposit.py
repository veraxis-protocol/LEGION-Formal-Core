"""Copy one WO's evidence into Dropbox\\PayPal\\FORMAL_CLOSURE_20261107\\<WO>\\ and write EVIDENCE_HASHES.sha256.
Usage: python deposit.py <WO> <verdict.json> <src>[=<dest-name>] ...   (directories are copied recursively)"""
import hashlib
import json
import shutil
import sys
from pathlib import Path

DEST = Path(r"C:\Users\Administrator\Dropbox\PayPal\FORMAL_CLOSURE_20261107")


def main():
    wo, verdict = sys.argv[1], Path(sys.argv[2])
    d = DEST / wo
    d.mkdir(parents=True, exist_ok=True)
    shutil.copy2(verdict, d / "WO_VERDICT.json")
    for item in sys.argv[3:]:
        src, _, name = item.partition("=")
        src = Path(src)
        target = d / (name or src.name)
        if src.is_dir():
            shutil.copytree(src, target, dirs_exist_ok=True, ignore=shutil.ignore_patterns("__pycache__", ".lake"))
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, target)
    lines = []
    for p in sorted(d.rglob("*")):
        if p.is_file() and p.name != "EVIDENCE_HASHES.sha256":
            lines.append(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(d).as_posix()}")
    (d / "EVIDENCE_HASHES.sha256").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"deposited": str(d), "files": len(lines)}))


if __name__ == "__main__":
    main()
