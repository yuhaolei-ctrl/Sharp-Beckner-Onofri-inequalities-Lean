#!/usr/bin/env python3
"""Print a revision-pinned Arena test descriptor; does not submit or run it."""
import argparse
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--revision', required=True)
args = p.parse_args()
if not re.fullmatch('[0-9a-f]{40}', args.revision):
    raise SystemExit('Provide a full public Git commit hash.')
c = json.loads((root / 'comparator-paper2.json').read_text())
print(json.dumps({
    'description': 'Beckner–Onofri: 257 baseline targets and 5 paper-2 bridges. '
                   'Formal proof corpus only; not a claim of complete paper-2 semantic coverage.',
    'url': 'https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean',
    'ref': 'main', 'rev': args.revision,
    'pre-build': 'python3 scripts/setup_dependencies.py',
    'module': c['solution_module'], 'export-decls': c['theorem_names'],
    'outcome': 'accept'
}, indent=2))
