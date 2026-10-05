#!/usr/bin/env python3
"""Pin the small replay project; no manuscript sources or proof terms are changed."""
import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--comparator', type=Path, default=root / '.tools/comparator')
args = parser.parse_args()
comp = args.comparator.resolve()
revision = '07bc4ea40f2266dcb861820a2ec1fa3244ed307f'

def checkout(url, rev, path):
    if not path.exists():
        subprocess.run(['git', 'clone', '--no-checkout', url, str(path)], check=True)
        subprocess.run(['git', '-C', str(path), 'checkout', '--detach', rev], check=True)
    assert subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip() == rev
    assert not subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()

comp.parent.mkdir(parents=True, exist_ok=True)
checkout('https://github.com/leanprover/comparator', revision, comp)
packages = json.loads((comp / 'lake-manifest.json').read_text())['packages']
expected = {'lean4export': '4e7915201d3f9f04470d9eae002fa695f7cdc589',
            'Lean4Checker': 'b7398199245524275543dec6113229c9bb4902e5'}
assert {p['name']: p['rev'] for p in packages} == expected
paths = []
for p in packages:
    path = comp / '.lake/packages' / p['name']
    path.parent.mkdir(parents=True, exist_ok=True)
    checkout(p['url'], p['rev'], path)
    paths.append((p['name'], path))
paths.append(('Comparator', comp))
project = root / '.tools/replay'
project.mkdir(parents=True, exist_ok=True)
shutil.copyfile(root / 'verification/tools/ReplayExports.lean', project / 'ReplayExports.lean')
(project / 'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
s = 'name = "CertificateReplay"\n'
for name, path in paths:
    s += '\n[[require]]\nname = ' + json.dumps(name) + '\npath = ' + json.dumps(str(path)) + '\n'
s += '\n[[lean_exe]]\nname = "replay-exports"\nroot = "ReplayExports"\n'
(project / 'lakefile.toml').write_text(s)

out = root / 'external-check'
record = json.loads((out / 'challenge-export.json').read_text())
solution = json.loads((out / 'certificate-export.json').read_text())
config = json.loads((root / 'comparator-paper2.json').read_text())
assert record['module'] == 'Paper2Challenge' and record['exit_code'] == 0
assert record['source_commit'] == solution['source_commit']
assert record['source_manifest_sha256'] == solution['source_manifest_sha256']
assert record['source_manifest_sha256'] == hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()
assert record['arguments'][:2] == ['Paper2Challenge', '--']
assert set(config['theorem_names']) <= set(record['arguments'][2:])
with (out / 'challenge.ndjson.gz').open('rb') as f:
    assert hashlib.file_digest(f, 'sha256').hexdigest() == record['gzip_sha256']
digest = hashlib.sha256()
size = 0
with gzip.open(out / 'challenge.ndjson.gz', 'rb') as src, (out / 'challenge.ndjson').open('wb') as dst:
    while chunk := src.read(1024 * 1024):
        digest.update(chunk)
        size += len(chunk)
        dst.write(chunk)
assert digest.hexdigest() == record['export_sha256'] and size == record['bytes']
print(json.dumps({'comparator_revision': revision, 'dependencies': expected,
                  'challenge_export_sha256': digest.hexdigest(),
                  'solution_export_sha256': solution['export_sha256'],
                  'registered_targets': len(config['theorem_names'])}, indent=2))
