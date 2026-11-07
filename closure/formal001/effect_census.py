"""FORMAL-001 consequential-effect path census (static, AST-based, fail-on-unclassified).

Enumerates EVERY call site of every effect primitive in the scanned source trees, records its enclosing
function, and joins it with a reviewed classification table. The census verdict is
  T  every site classified, no stale classification, no BYPASS_OPEN, every file parsed
  F  at least one site classified BYPASS_OPEN
  Z  otherwise (unclassified site, stale table, unparseable file): the census is not complete.

Completeness is RELATIVE to the primitive list (SINKS) and the scanned roots; both are recorded in the output.
Reflective calls (eval/exec/__import__/importlib/getattr with a non-literal name) are their own sink kind so
that they cannot silently hide a primitive.

Usage: python effect_census.py --config census_config.json --classification classification.json --out OUT.json
"""
import argparse
import ast
import hashlib
import json
import subprocess
import sys
from pathlib import Path

SINKS = {
    # world-state mutation primitives (R2 world engine; pinned Core World used by Federation)
    "call_write": "WORLD_WRITE", "_apply_effects": "WORLD_WRITE", "_apply_prepared": "WORLD_WRITE",
    "_run_derived": "WORLD_WRITE", "fire": "WORLD_EXOGENOUS", "analyze": "WORLD_ANSWER_RECORD",
    # external network
    "urlopen": "NETWORK", "post": "NETWORK", "put": "NETWORK", "delete": "NETWORK", "patch": "NETWORK",
    "_wire": "NETWORK", "request": "NETWORK", "HTTPConnection": "NETWORK", "HTTPSConnection": "NETWORK",
    "create_connection": "NETWORK",
    # process execution
    "Popen": "PROCESS", "run": "PROCESS", "check_call": "PROCESS", "check_output": "PROCESS", "system": "PROCESS",
    "_exit": "PROCESS",
    # reflective (can hide any primitive)
    "eval": "REFLECTIVE", "exec": "REFLECTIVE", "__import__": "REFLECTIVE", "import_module": "REFLECTIVE",
}
RECV = {"run": {"subprocess"}, "post": {"requests", "session", "httpx", "client"},
        "put": {"requests", "session", "httpx", "client"}, "delete": {"requests", "session", "httpx", "client"},
        "patch": {"requests", "session", "httpx", "client"}, "system": {"os"}, "_exit": {"os"}}


def tail(node):
    parts = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
    elif isinstance(node, ast.Call):
        parts.append("<call>")
    elif isinstance(node, ast.Subscript):
        parts.append("<subscript>")
    return list(reversed(parts))


class Scan(ast.NodeVisitor):
    def __init__(self, rel, src):
        self.rel, self.src, self.stack, self.hits = rel, src.splitlines(), [], []

    def visit_FunctionDef(self, n):
        self.stack.append(n.name)
        self.generic_visit(n)
        self.stack.pop()
    visit_AsyncFunctionDef = visit_FunctionDef
    visit_ClassDef = visit_FunctionDef

    def visit_Call(self, n):
        t = tail(n.func)
        if t:
            name = t[-1]
            kind = SINKS.get(name)
            if kind:
                recv = t[-2].lower() if len(t) > 1 else ""
                ok = True
                if name in RECV:
                    ok = recv in RECV[name]
                if name == "request":
                    ok = len(t) > 1 and recv not in ("urllib",)
                if name in ("fire", "analyze"):
                    ok = len(t) > 1 and recv in ("world", "self", "w", "<call>")
                if ok:
                    self.add(n, kind, ".".join(t))
            if name == "call" and len(n.args) >= 3 and isinstance(n.args[2], ast.Constant) \
                    and n.args[2].value in ("POST", "PUT", "DELETE", "PATCH"):
                self.add(n, "NETWORK", ".".join(t) + f"[{n.args[2].value}]")
            if name == "Request" and any(k.arg in ("data", "method") for k in n.keywords):
                self.add(n, "NETWORK", ".".join(t) + "[data/method]")
            if name == "getattr" and len(n.args) >= 2 and not isinstance(n.args[1], ast.Constant):
                self.add(n, "REFLECTIVE", "getattr(<dynamic>)")
        self.generic_visit(n)

    def add(self, n, kind, callee):
        line = self.src[n.lineno - 1].strip() if n.lineno - 1 < len(self.src) else ""
        fn = ".".join(self.stack) or "<module>"
        self.hits.append({"file": self.rel, "line": n.lineno, "function": fn, "kind": kind, "callee": callee,
                          "code": line[:200], "key": f"{self.rel}::{fn}::{callee}"})


def scan_root(name, root, include, exclude):
    root = Path(root)
    files = set()
    for pat in include:
        files |= {p for p in root.glob(pat) if p.is_file()}
    out, scanned, errors = [], [], []
    for p in sorted(files):
        rel = p.relative_to(root).as_posix()
        if any(rel.startswith(x) for x in exclude) or "/__pycache__/" in rel:
            continue
        try:
            src = p.read_text(encoding="utf-8-sig")
            tree = ast.parse(src)
        except Exception as exc:
            errors.append({"file": rel, "error": repr(exc)})
            continue
        scanned.append({"file": rel, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()})
        s = Scan(rel, src)
        s.visit(tree)
        for h in s.hits:
            h["repo"] = name
            h["key"] = f"{name}:{h['key']}"
        out += s.hits
    return out, scanned, errors


def git_head(root):
    try:
        r = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True)
        d = subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"],
                           capture_output=True, text=True)
        return {"head": r.stdout.strip(), "dirty_tracked_files": len([x for x in d.stdout.splitlines() if x.strip()])}
    except Exception:
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True)
    ap.add_argument("--classification", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    cfg = json.loads(Path(a.config).read_text())
    table = json.loads(Path(a.classification).read_text())["classes"]
    sites, roots = [], []
    for r in cfg["roots"]:
        hits, scanned, errs = scan_root(r["name"], r["path"], r["include"], r.get("exclude", []))
        roots.append({"name": r["name"], "path": r["path"], "git": git_head(r["path"]), "files_scanned": len(scanned),
                      "files": scanned, "parse_errors": errs, "include": r["include"], "exclude": r.get("exclude", []),
                      "boundary_role": r.get("boundary_role")})
        sites += hits
    keys = {}
    for s in sites:
        keys.setdefault(s["key"], []).append(s)
    rows, unclassified, open_bypass = [], [], []
    for k, ss in sorted(keys.items()):
        c = table.get(k)
        row = {"key": k, "sites": [{"line": s["line"], "code": s["code"]} for s in ss], "kind": ss[0]["kind"],
               "repo": ss[0]["repo"], "file": ss[0]["file"], "function": ss[0]["function"]}
        if c is None:
            row["class"] = "UNCLASSIFIED"
            unclassified.append(k)
        else:
            row.update(c)
            if c["class"] == "BYPASS_OPEN":
                open_bypass.append(k)
        rows.append(row)
    stale = sorted(set(table) - set(keys))
    by_class = {}
    for r in rows:
        by_class[r["class"]] = by_class.get(r["class"], 0) + 1
    perr = any(r["parse_errors"] for r in roots)
    tval = "F" if open_bypass else ("T" if not unclassified and not stale and not perr else "Z")
    res = {"schema": "legion.formal001.census.v1", "verdict": tval, "sink_primitives": SINKS, "roots": roots,
           "site_count": len(sites), "key_count": len(rows), "by_class": by_class, "unclassified": unclassified,
           "stale_classifications": stale, "open_bypasses": open_bypass, "rows": rows,
           "classification_sha256": hashlib.sha256(Path(a.classification).read_bytes()).hexdigest(),
           "scope_note": "Static census relative to SINKS and the scanned roots. Non-reflective dynamic dispatch, code "
                         "modification and OS-level tampering are out of scope (trusted code base assumption TCB-1)."}
    Path(a.out).write_text(json.dumps(res, indent=1))
    print(json.dumps({"verdict": tval, "sites": len(sites), "keys": len(rows), "by_class": by_class,
                      "unclassified": len(unclassified), "stale": len(stale), "open_bypasses": open_bypass}))
    return 0 if tval == "T" else 1


if __name__ == "__main__":
    sys.exit(main())
