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
baseline = json.loads((root / 'comparator.json').read_text())['theorem_names']
primitives = ['Nat', 'String', 'String.ofList', 'Char', 'Char.ofNat', 'List',
              'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
primitives += ['Nat.' + n for n in ('add', 'sub', 'mul', 'pow', 'gcd', 'div', 'mod',
                                  'beq', 'ble', 'land', 'lor', 'xor', 'shiftLeft', 'shiftRight')]
roots = list(dict.fromkeys(c['theorem_names'] + c['permitted_axioms'] + primitives))
print(json.dumps({
    'description': f'Beckner–Onofri: {len(baseline)} baseline targets and '
                   f"{len(c['theorem_names']) - len(baseline)} paper-2 targets. "
                   'Formal proof corpus; independent natural-language review is a separate task.',
    'url': 'https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean',
    'ref': 'main', 'rev': args.revision,
    'pre-build': 'python3 scripts/setup_dependencies.py',
    'module': c['solution_module'], 'export-decls': roots,
    'outcome': 'accept'
}, indent=2))
