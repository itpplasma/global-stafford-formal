#!/usr/bin/env bash
# Full verification of the Global Stafford formalization.
#
#   scripts/verify.sh            full audit (Phase III endpoints; fails until Phase II closes)
#   scripts/verify.sh --phase-i  Phase I audit: build, source audit, Phase I endpoint axioms
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

mode=${1:-full}
log_dir=.lake/verification
mkdir -p "$log_dir"
python3 scripts/check-submission-modules.py >"$log_dir/module-resolution.log" 2>&1

python3 scripts/check-layout.py >"$log_dir/layout.log" 2>&1

python3 - <<'PY'
import json
import re
import tomllib
from pathlib import Path

expected_toolchain = "leanprover/lean4:v4.33.0"
expected_mathlib = "db584cd6d46c92f209a44c0f1c829460d327499d"
expected = {
    "algebraicAnalysis": ("https://github.com/itpplasma/algebraic-analysis.git",
                          "4aae47967f6ba02ffe2f639ab06564c9a9d1ecc8"),
    "stafford38Formal": ("https://github.com/itpplasma/stafford38-formal.git",
                         "e77e176c381ca2d6b20c030f9227f1b031415d2e"),
}

toolchain = Path("lean-toolchain").read_text(encoding="utf-8").strip()
if toolchain != expected_toolchain:
    raise SystemExit(f"unexpected Lean toolchain: {toolchain!r}")
with Path("lakefile.toml").open("rb") as handle:
    lakefile = tomllib.load(handle)
requires = {item["name"]: item for item in lakefile.get("require", [])}
with Path("lake-manifest.json").open(encoding="utf-8") as handle:
    manifest = json.load(handle)
packages = {item["name"]: item for item in manifest.get("packages", [])}
if requires["mathlib"].get("rev") != expected_mathlib or packages["mathlib"].get("rev") != expected_mathlib:
    raise SystemExit("Mathlib pin mismatch")
for name, (url, rev) in expected.items():
    req = requires[name]
    pkg = packages[name]
    if req.get("git") != url or req.get("rev") != rev:
        raise SystemExit(f"{name} lakefile pin mismatch: {req}")
    if pkg.get("rev") != rev or pkg.get("inputRev") != rev:
        raise SystemExit(f"{name} manifest pin mismatch: {pkg}")
    if not re.fullmatch(r"[0-9a-f]{40}", rev):
        raise SystemExit(f"{name} must be pinned by a full commit")
print("pins: Lean v4.33.0, Mathlib", expected_mathlib[:8],
      *[f"{n} {r[:8]}" for n, (_, r) in expected.items()])
PY

mapfile -t modules < <(python3 - <<'PY'
from pathlib import Path
for path in sorted(Path('GlobalStafford').rglob('*.lean')):
    print('.'.join(path.with_suffix('').parts))
PY
)
if [ "${#modules[@]}" -gt 0 ]; then
  lake build "${modules[@]}" GlobalStafford >"$log_dir/build.log" 2>&1
else
  lake build GlobalStafford >"$log_dir/build.log" 2>&1
fi
# The shared AlgebraicAnalysis pin must keep the upstream Weyl development building.
lake build Stafford38.FoundationClosure Stafford38.LocalizedDifferentialCorollaries \
  >"$log_dir/upstream-build.log" 2>&1

python3 - "$mode" <<'PY'
import re
import sys
from pathlib import Path

mode = sys.argv[1]

def code_without_comments_or_strings(text: str) -> str:
    out, i, depth, in_string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i):
                depth -= 1; i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2
            elif text[i] == '"':
                out.append(" "); in_string = False; i += 1
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                out.extend(" " * (len(text) - i)); break
            out.extend(" " * (end - i)); i = end
        elif text.startswith("/-", i):
            out.extend("  "); depth = 1; i += 2
        elif text[i] == '"':
            out.append(" "); in_string = True; i += 1
        else:
            out.append(text[i]); i += 1
    if depth or in_string:
        raise SystemExit("unterminated Lean comment or string during source audit")
    return "".join(out)

excluded = {".git", ".lake"}
challenge = Path("GlobalStaffordChallenge.lean")
if challenge.read_bytes() != Path("Challenge.lean").read_bytes():
    raise SystemExit("unique submission Challenge differs from the frozen statement")
code = code_without_comments_or_strings(challenge.read_text(encoding="utf-8"))
if re.findall(r"\b(?:sorry|admit)\b", code) != ["sorry"]:
    raise SystemExit("Challenge.lean must contain exactly one deliberate sorry and no admit")
imports = re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", code)
if any(not (i.startswith("Mathlib.") or i == "Mathlib") for i in imports):
    raise SystemExit(f"Challenge imports must be Mathlib only: {imports}")
solution = code_without_comments_or_strings(Path("GlobalStaffordSolution.lean").read_text(encoding="utf-8"))
if any(n == "Challenge" or n.startswith("Challenge.")
       for n in re.findall(r"(?m)^\s*import\s+([^\s]+)\s*$", solution)):
    raise SystemExit("Solution.lean must not import Challenge")

# Registered holes (Phase I/II development only).
plan = Path("PLAN.md").read_text(encoding="utf-8")
holes_block = re.search(r"open_holes:\s*(\[.*?\]|\n(?:\s+- .*\n)*)", plan)
registered = set()
if holes_block and holes_block.group(1).strip() != "[]":
    for line in holes_block.group(1).splitlines():
        m = re.search(r"-\s*([^\s:]+\.lean)", line)
        if m:
            registered.add(m.group(1))
for path in Path(".").rglob("*.lean"):
    if path in {challenge, Path("Challenge.lean")} or any(part in excluded for part in path.parts):
        continue
    text = code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    hole = re.search(r"\b(?:sorry|admit)\b", text)
    if hole:
        if mode == "full" or str(path) not in registered:
            line = text.count("\n", 0, hole.start()) + 1
            raise SystemExit(f"proof hole in {path}:{line} ({'unregistered' if str(path) not in registered else 'full mode'})")
    if re.search(r"(?m)^\s*axiom\s+", text):
        raise SystemExit(f"project axiom declaration in {path}")
    if re.search(r"\bnative_decide\b|Lean\.ofReduceBool", text):
        raise SystemExit(f"forbidden proof mechanism in {path}")
print("source audit passed")
PY

if [ "$mode" = "--phase-i" ]; then
  endpoints_file=docs/phase-i-endpoints.txt
else
  endpoints_file=docs/endpoints.txt
fi
if [ -f "$endpoints_file" ]; then
  {
    echo "import GlobalStafford"
    [ "$mode" = "full" ] && echo "import GlobalStaffordSolution"
    sed 's/^/#print axioms /' "$endpoints_file"
  } >"$log_dir/AxiomAudit.lean"
  lake env lean --trust=0 "$log_dir/AxiomAudit.lean" >"$log_dir/axioms.log" 2>&1
  python3 - "$log_dir/axioms.log" "$endpoints_file" <<'PY'
import re
import sys
from pathlib import Path
text = Path(sys.argv[1]).read_text(encoding="utf-8")
expected = {l.strip() for l in Path(sys.argv[2]).read_text().splitlines() if l.strip()}
allowed = {"propext", "Quot.sound", "Classical.choice"}
found = {}
for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", text, re.S):
    found[name] = {x.strip() for x in body.split(",") if x.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
missing = expected - found.keys()
if missing:
    raise SystemExit("missing axiom reports: " + ", ".join(sorted(missing)))
for name in sorted(expected):
    extra = found[name] - allowed
    if extra:
        raise SystemExit(f"{name} uses forbidden axioms: {sorted(extra)}")
if re.search(r"sorryAx|admitAx|Lean\.ofReduceBool|(^|\n)[^\n]*error:", text):
    raise SystemExit("axiom log contains a forbidden proof mechanism or an error")
print(f"axiom audit: {len(expected)} declarations use only {sorted(allowed)}")
PY
else
  echo "no endpoint list at $endpoints_file yet; axiom audit skipped"
fi

if [ "$mode" = "full" ]; then
  lake build GlobalStaffordChallenge >"$log_dir/challenge-build.log" 2>&1
  lake build GlobalStaffordSolution >"$log_dir/solution-build.log" 2>&1
  bash scripts/check-import-closure.sh GlobalStaffordChallenge
  bash scripts/check-import-closure.sh GlobalStaffordSolution
  if [ -d tests ] && ls tests/*.lean >/dev/null 2>&1; then
    : > "$log_dir/consumers.log"
    for source in tests/*.lean; do
      lake env lean --trust=0 "$source" >>"$log_dir/consumers.log" 2>&1
    done
    if grep -Eq 'sorryAx|admitAx|Lean\.ofReduceBool|(^|:) error:' "$log_dir/consumers.log"; then
      echo "consumer audit failed; see $log_dir/consumers.log" >&2
      exit 1
    fi
  fi
fi

echo "verify.sh ($mode) passed"
