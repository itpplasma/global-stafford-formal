#!/usr/bin/env bash
# Build the companion from repository sources, then record artifact hashes.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$repo_root"
latexmk -cd -lualatex -interaction=nonstopmode -halt-on-error \
  docs/dossier/global-stafford-dossier.tex
python3 - <<'PY'
import hashlib, json, re, subprocess
from pathlib import Path
folder = Path('docs/dossier')
log = (folder / 'global-stafford-dossier.log').read_text()
if re.search(r'Overfull|Missing character|undefined references|LaTeX Warning: Reference', log):
    raise SystemExit('PDF has layout, font or reference errors; inspect its log')
paths = ['Challenge.lean', 'Solution.lean',
         'GlobalStafford/Assembly/ChallengeTransport.lean',
         'docs/proof-map/map.tex', 'docs/dossier/global-stafford-dossier.tex',
         'docs/verification-results.json', 'docs/dossier/global-stafford-dossier.pdf']
record = {
    'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'tracked_patch_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD', '--binary'])).hexdigest(),
    'artifacts': {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},
    'scope': 'PDF build provenance; does not replace the formal verification report',
}
(folder / 'build-manifest.json').write_text(json.dumps(record, indent=2) + '\n')
print('Dossier build and source hashes recorded in docs/dossier/build-manifest.json')
PY
