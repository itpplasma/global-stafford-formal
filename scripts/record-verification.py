#!/usr/bin/env python3
"""Write docs/verification-results.json from an independent-clone replay.

Usage: scripts/record-verification.py <replay_dir> <commit>

`replay_dir` must contain the logs written by the replay commands
(`cache.log`, `build.log`, `verify.log`, `bootstrap.log`,
`verify-palomar.log`) and the clone at `<replay_dir>/gsf` with its
`.lake/verification/*.log` and `.lake/palomar-tools/revisions.txt`.
The record fixes the commit, dependency pins, tool revisions, commands,
exit statuses and SHA-256 hashes of every log.
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

replay = Path(sys.argv[1]).resolve()
commit = sys.argv[2]
clone = replay / "gsf"
root = Path(__file__).resolve().parent.parent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exit_code(log: Path, key: str) -> int:
    text = log.read_text(encoding="utf-8", errors="replace")
    match = re.search(rf"^{key}=(\d+)$", text, re.M)
    if not match:
        raise SystemExit(f"{log}: missing {key}")
    return int(match.group(1))


head = subprocess.check_output(["git", "-C", str(clone), "rev-parse", "HEAD"], text=True).strip()
if head != commit:
    raise SystemExit(f"clone HEAD {head} is not the requested commit {commit}")
status = subprocess.check_output(["git", "-C", str(clone), "status", "--porcelain"], text=True)
if status.strip():
    raise SystemExit("clone working tree is not clean")

manifest = json.loads((clone / "lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
toolchain = (clone / "lean-toolchain").read_text().strip()
revisions = dict(
    line.split(" ", 1) for line in (clone / ".lake/palomar-tools/revisions.txt").read_text().splitlines() if line.strip()
)

logs = {
    "cache": (replay / "cache.log", None),
    "build": (replay / "build.log", "build_exit"),
    "verify": (replay / "verify.log", "verify_exit"),
    "bootstrap": (replay / "bootstrap.log", "bootstrap_exit"),
    "verify-palomar": (replay / "verify-palomar.log", "palomar_exit"),
}
checks = {}
for name, (log, key) in logs.items():
    checks[name] = {
        "log": str(log.name),
        "sha256": sha(log),
        "exit": exit_code(log, key) if key else 0,
    }

axioms_log = clone / ".lake/verification/axioms.log"
axiom_text = axioms_log.read_text()
endpoints = {}
for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", axiom_text, re.S):
    endpoints[name] = sorted(x.strip() for x in body.split(",") if x.strip())
comparator_log = clone / ".lake/verification/comparator.log"
comparator_text = comparator_log.read_text()
imports = {}
for module in ("Challenge", "Solution"):
    text = (clone / f".lake/verification/{module}-imports.log").read_text()
    imports[module] = len(re.findall(r"^IMPORT ", text, re.M))

record = {
    "repository": "itpplasma/global-stafford-formal",
    "commit": commit,
    "replay": "fresh clone from origin, isolated from every working checkout and from the research repository",
    "lean_toolchain": toolchain,
    "dependency_pins": pins,
    "palomar_tools": revisions,
    "commands": [
        "lake exe cache get",
        "lake build",
        "scripts/verify.sh",
        "scripts/bootstrap-palomar-tools.sh",
        "scripts/verify-palomar.sh",
    ],
    "checks": checks,
    "endpoint_axioms": endpoints,
    "loaded_modules": imports,
    "comparator": {
        "config": "comparator.json",
        "compared_declaration": "GlobalStaffordChallenge.universalStatement",
        "nanoda_accepts": "nanoda kernel accepts the solution" in comparator_text,
        "lean_kernel_accepts": "Lean default kernel accepts the solution" in comparator_text,
        "okay": "Your solution is okay!" in comparator_text,
        "log_sha256": sha(comparator_log),
    },
    "evidence_sha256": {
        "axioms.log": sha(axioms_log),
        "Challenge-imports.log": sha(clone / ".lake/verification/Challenge-imports.log"),
        "Solution-imports.log": sha(clone / ".lake/verification/Solution-imports.log"),
    },
}
for name, check in checks.items():
    if check["exit"] != 0:
        raise SystemExit(f"replay step {name} failed with exit {check['exit']}")
if not (record["comparator"]["okay"] and record["comparator"]["nanoda_accepts"] and record["comparator"]["lean_kernel_accepts"]):
    raise SystemExit("Comparator did not accept the solution")
out = root / "docs/verification-results.json"
out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
print(f"wrote {out}; report sha256 {sha(out)}")
