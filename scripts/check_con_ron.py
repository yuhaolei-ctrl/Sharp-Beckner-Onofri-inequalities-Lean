#!/usr/bin/env python3
"""Run pinned, unmodified con-ron on the exact published certificate locally."""
import argparse
import datetime
import gzip
import hashlib
import json
import re
import resource
import shutil
import subprocess
import sys
import time
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--checker', type=Path, required=True, help='Built con-ron source checkout')
parser.add_argument('--evidence', type=Path, required=True, help='New output directory')
parser.add_argument('--workers', type=int, choices=[1, 4], default=1)
args = parser.parse_args()
checkout = args.checker.resolve()
binary = checkout / 'target/release/con-ron'
revision = '2e3486617cee878f796d8133c481e239696132fe'
assert subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip() == revision
assert not subprocess.check_output(['git', '-C', str(checkout), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(name, value):
    (out / name).write_text(json.dumps(value, indent=2) + '\n')


proof = root / 'external-check/solution.ndjson'
record = json.loads((root / 'verification/certificate-export.json').read_text())
inventory = json.loads((root / 'verification/solution-inventory.json').read_text())
config = json.loads((root / 'verification/certified-comparator.json').read_text())
assert digest(proof) == record['export_sha256'] == inventory['export_sha256']
assert proof.stat().st_size == record['bytes'] == inventory['bytes']
assert digest(root / 'verification/certified-source-manifest.json') == record['source_manifest_sha256']
assert set(inventory['axioms']) == set(config['permitted_axioms'])
out = args.evidence.resolve()
out.mkdir(parents=True, exist_ok=False)
save('certificate-export.json', record)
save('solution-inventory.json', inventory)
save('declared-targets.json', config['theorem_names'])
save('declared-axioms.json', inventory['axioms'])
(out / 'checker-binary.sha256').write_text(digest(binary) + '  con-ron\n')
shutil.copy2(checkout / 'Cargo.lock', out / 'checker-Cargo.lock')
arguments = ['--verified', f'--jobs={args.workers}', '--progress=10000']
save('runtime-settings.json', {'checker_revision': revision, 'source_patch': None,
     'mode': 'verified', 'num_threads': args.workers, 'arguments': arguments,
     'pins': 'checker-embedded defaults', 'certificate_recompiled': False,
     'platform': sys.platform})
controls = []
for name, expected in [('valid', 0), ('invalid', 1)]:
    path = out / (name + '.ndjson')
    path.write_bytes(gzip.decompress((root / f'tests/kernel_controls/{name}.ndjson.gz').read_bytes()))
    run = subprocess.run([str(binary), *arguments, str(path)], capture_output=True, text=True)
    text = run.stdout + run.stderr
    controls.append({'control': name, 'exit_code': run.returncode, 'output': text})
    save('controls.json', controls)
    assert run.returncode == expected, controls[-1]
    if name == 'valid':
        assert re.search(r'^con-ron: accepted [0-9]+ declarations \(--verified\)$', text, re.M)


def no_core():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


start = datetime.datetime.now(datetime.timezone.utc).isoformat()
t0 = time.monotonic()
with (out / 'con-ron.log').open('w') as log:
    run = subprocess.run([str(binary), *arguments, str(proof)], stdout=log,
                         stderr=subprocess.STDOUT, preexec_fn=no_core)
result = {'exit_code': run.returncode, 'target_count': len(config['theorem_names']),
          'started_utc': start, 'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'elapsed_seconds': time.monotonic() - t0,
          'proof_export_sha256': record['export_sha256'], 'mode': 'full con-ron verified replay'}
save('result.json', result)
print(json.dumps(result), flush=True)
if run.returncode != 0:
    sys.exit(1)
match = re.search(r'^con-ron: accepted ([0-9]+) declarations \(--verified\)$',
                  (out / 'con-ron.log').read_text(), re.M)
assert match and int(match[1]) == inventory['declaration_record_count']
