#!/usr/bin/env python3
"""Structural checks, not a decision procedure for informal/formal equivalence."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from proof_source_audit import forbidden_hits

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--paper', type=Path)
args = parser.parse_args()
config = json.loads((ROOT / 'comparator-paper2.json').read_text())
targets = config['theorem_names']
baseline_targets = json.loads((ROOT / 'comparator.json').read_text())['theorem_names']
increment_targets = json.loads((ROOT / 'comparator-paper2-increment.json').read_text())['theorem_names']
assert len(targets) == len(set(targets))
assert targets == baseline_targets + increment_targets
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
mapping = json.loads((ROOT / 'audit/paper2_statement_map.json').read_text())
assert len(mapping['rows']) == mapping['assertion_count'] == 51
assert len({r['source_label'] for r in mapping['rows']}) == 51
assert sum(r['text_changed'] for r in mapping['rows']) == 28
for row in mapping['rows']:
    assert row['lean_targets'] and set(row['lean_targets']) <= set(targets), row['source_label']
proofs = [p for d in ('BecknerOnofri', 'Legacy') for p in (ROOT / d).rglob('*.lean')]
proofs += [ROOT / 'Solution.lean']
proofs += [p for p in ROOT.glob('Paper2*.lean') if p.name != 'Paper2Challenge.lean']
errors = []
for p in proofs:
    text = p.read_text()
    errors.extend(f'{p.relative_to(ROOT)}:{line}: {token}'
                  for line, token in forbidden_hits(text))
    if re.search(r'^import\s+(?:Challenge|Paper2Challenge)\b', text, re.M):
        errors.append(f'Proof imports trusted challenge: {p.relative_to(ROOT)}')
manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
for name, expected in manifest.items():
    actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    if actual != expected:
        errors.append(f'Source digest mismatch: {name}')
baseline = json.loads((ROOT / 'audit/baseline_source_manifest.json').read_text())
for name, expected in baseline.items():
    if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
        errors.append(f'Frozen baseline changed: {name}')
def headers(path):
    return {s.split()[0]: s for s in re.findall(
        r'^theorem ([\s\S]*?) := by', path.read_text(), re.M)}
challenge_headers = headers(ROOT / 'Paper2Challenge.lean')
if (set('BecknerOnofri.Paper2.' + n for n in challenge_headers) != set(increment_targets)
        or challenge_headers != headers(ROOT / 'Paper2Proofs.lean')):
    errors.append('Paper-2 trusted/proof declaration headers differ')
if args.paper:
    data = args.paper.read_bytes()
    assert hashlib.sha256(data).hexdigest() == mapping['paper2_sha256']
    tex = data.decode()
    blocks = {}
    for m in re.finditer(r'\\begin\{(thm|lemma|prop|cor)\}(.*?)\\end\{\1\}', tex, re.S):
        for lab in re.findall(r'\\label\{([^}]+)\}', m.group(2)):
            blocks[lab] = m.group(2)[m.group(2).index('\\label{' + lab + '}'):].strip()
    for row in mapping['rows']:
        assert blocks[row['source_label']] == row['paper2_statement_tex'], row['source_label']
if errors:
    raise SystemExit('\n'.join(errors))
print(json.dumps({'structural_audit': 'passed', 'proof_files_scanned': len(proofs),
                  'registered_targets': len(targets), 'paper2_results': 51,
                  'changed_statement_bodies': 28,
                  'paper_bytes_verified': bool(args.paper),
                  'independent_semantic_certification': False}, indent=2))
