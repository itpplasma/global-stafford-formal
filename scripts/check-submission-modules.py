#!/usr/bin/env python3
"""Check Lake resolves the submission modules to this project's source files."""
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
config = json.loads((root / 'comparator.json').read_text())
source_path = subprocess.check_output(
    ['lake', 'env', 'printenv', 'LEAN_SRC_PATH'], cwd=root, text=True
).strip()
for field in ('challenge_module', 'solution_module'):
    module = config[field]
    suffix = Path(*module.split('.')).with_suffix('.lean')
    expected = (root / suffix).resolve()
    resolved = None
    for entry in source_path.split(os.pathsep):
        if not entry:
            continue
        candidate = Path(entry) / suffix
        if not candidate.is_absolute():
            candidate = root / candidate
        if candidate.exists():
            resolved = candidate.resolve()
            break
    if resolved != expected:
        raise SystemExit(f'{module} resolves to {resolved}, expected {expected}')
    print(f'{module}: {resolved.relative_to(root)}')
