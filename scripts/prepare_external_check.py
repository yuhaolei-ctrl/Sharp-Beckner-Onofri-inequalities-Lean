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
