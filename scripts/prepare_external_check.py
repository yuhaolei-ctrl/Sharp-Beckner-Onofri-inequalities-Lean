#!/usr/bin/env python3
"""Validate a captured proof export before independent-kernel replay."""
import gzip
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
out = root / 'external-check'
record = json.loads((out / 'certificate-export.json').read_text())
config = json.loads((root / 'comparator-paper2.json').read_text())
assert record['module'] == 'Paper2Solution'
assert record['exit_code'] == 0
assert record['source_manifest_sha256'] == hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()
args = record['arguments']
assert args[:2] == ['Paper2Solution', '--']
assert set(config['theorem_names']) <= set(args[2:])
archive = out / 'solution.ndjson.gz'
with archive.open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest() == record['gzip_sha256']
digest = hashlib.sha256()
size = 0
with gzip.open(archive, 'rb') as src, (out / 'solution.ndjson').open('wb') as dst:
    while chunk := src.read(1024 * 1024):
        digest.update(chunk)
        size += len(chunk)
        dst.write(chunk)
assert digest.hexdigest() == record['export_sha256']
assert size == record['bytes']
# Confirm that the actual export declares every requested root, not just that
# the recorded command requested it. The full expression graph is checked by Nanoda.
names = {0: ''}
declared = set()
with (out / 'solution.ndjson').open('rb') as src:
    for line in src:
        if b'"ie":' in line or b'"il":' in line:
            continue
        row = json.loads(line)
        if 'in' in row:
            item = row.get('str', row.get('num', {}))
            parent = names.get(item.get('pre', 0), '?')
            component = item.get('str', str(item.get('num', item.get('i', '?'))))
            names[row['in']] = parent + ('.' if parent else '') + component
        elif 'inductive' in row:
            for group in ('types', 'ctors', 'recs'):
                declared.update(names[item['name']] for item in row['inductive'][group])
        else:
            for kind in ('def', 'thm', 'axiom', 'opaque', 'quot'):
                if kind in row:
                    declared.add(names[row[kind]['name']])
assert set(config['theorem_names']) <= declared
# This pinned Nanoda version uses String.ofList (see its NameCache), not String.mk.
required_primitives = {'Nat', 'String', 'String.ofList', 'Char', 'Char.ofNat', 'List',
                       'Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'}
assert required_primitives <= declared, sorted(required_primitives - declared)
(out / 'declared-targets.json').write_text(json.dumps(config['theorem_names'], indent=2) + '\n')
settings = json.loads((root / 'verification/nanoda-config.json').read_text())
settings['pp_declars'] = config['theorem_names']
settings['pp_output_path'] = str(out / 'checked-targets.txt')
settings['unknown_pp_declar_hard_error'] = True
settings['pp_options'] = {'proofs': False}
(out / 'nanoda-config.json').write_text(json.dumps(settings, indent=2) + '\n')
print(json.dumps({'validated_export_sha256': digest.hexdigest(),
                  'source_commit': record['source_commit'],
                  'target_count': len(config['theorem_names']),
                  'source_manifest_sha256': record['source_manifest_sha256']}, indent=2))
