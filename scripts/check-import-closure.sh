#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
case "${1:-}" in GlobalStaffordChallenge|GlobalStaffordSolution) module=$1 ;; *) exit 2 ;; esac
mkdir -p .lake/verification
audit=".lake/verification/${module}Imports.lean"
log=".lake/verification/${module}-imports.log"
cat > "$audit" <<LEAN
import $module
import Lean.Elab.Command
run_cmd do
  let env ← Lean.getEnv
  for name in env.header.moduleNames do
    Lean.logInfo m!"IMPORT {name}"
LEAN
lake env lean --trust=0 "$audit" > "$log" 2>&1
python3 - "$module" "$log" <<'PY'
import json
import re
import sys
from pathlib import Path

target, log = sys.argv[1:]
names = re.findall(r'^IMPORT (\S+)$', Path(log).read_text(), re.M)
if target not in names:
    raise SystemExit('loaded-environment audit did not report its target')
if target == 'GlobalStaffordSolution':
    forbidden = [n for n in names if n in {'Challenge', 'GlobalStaffordChallenge'} or n.startswith(('Challenge.', 'GlobalStaffordChallenge.'))]
else:
    # Mathlib is Palomar's allowlisted root. Its committed dependency manifest
    # determines the allowed package closure; AlgebraicAnalysis is excluded.
    manifest = json.loads(Path('.lake/packages/mathlib/lake-manifest.json').read_text())
    packages = {'mathlib'} | {p['name'] for p in manifest['packages']}
    packages.discard('algebraicAnalysis'); packages.discard('stafford38Formal')
    allowed = set()
    for package in packages:
        root = Path('.lake/packages') / package
        for path in root.rglob('*.lean'):
            relative = path.relative_to(root)
            if not any(part.startswith('.') for part in relative.parts):
                allowed.add('.'.join(relative.with_suffix('').parts))
    forbidden = [n for n in names if n != 'GlobalStaffordChallenge'
                 and n.split('.')[0] not in {'Init', 'Lean', 'Std'}
                 and n not in allowed]
if forbidden:
    raise SystemExit(f'{target} has forbidden transitive imports: {forbidden}')
print(f'{target}: audited {len(names)} loaded modules')
PY
