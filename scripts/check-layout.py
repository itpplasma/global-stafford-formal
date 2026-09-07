#!/usr/bin/env python3
"""Resolve every source import against this checkout or its pinned dependencies."""
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / 'lake-manifest.json').read_text())
packages = [root / '.lake/packages' / p['name'] for p in manifest['packages']]
core = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip()) / 'lib/lean'
sources = sorted(root.glob('*.lean'))
for folder in ['GlobalStafford', 'GlobalStaffordTest', 'tests']:
    sources.extend(sorted((root / folder).rglob('*.lean')))
missing = []
count = 0

def code_only(text):
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

for source in sources:
    for name in re.findall(r'^\s*(?:public )?import\s+(\S+)', code_only(source.read_text()), re.M):
        relative = Path(*name.split('.'))
        local = root / relative.with_suffix('.lean')
        external = any((p / relative.with_suffix('.lean')).is_file() for p in packages)
        if not local.is_file() and not external and not (core / relative.with_suffix('.olean')).is_file():
            missing.append(f'{source.relative_to(root)}: {name}')
        count += 1
if missing:
    raise SystemExit('Unresolved imports:\n' + '\n'.join(missing))
print(f'Resolved {count} imports in {len(sources)} local Lean files')
