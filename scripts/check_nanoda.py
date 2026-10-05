#!/usr/bin/env python3
"""Export exactly the configured theorem closure and run a supplied Nanoda binary."""
import argparse
import datetime
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--binary', required=True, type=Path)
p.add_argument('--configuration', default='comparator-paper2.json')
args = p.parse_args()
config = json.loads((ROOT / args.configuration).read_text())
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out = ROOT / 'verification/runs' / ('nanoda-' + stamp)
out.mkdir(parents=True)
export = out / 'proof.ndjson'
exporter = ROOT / 'vendor/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'
# Include the kernel primitives also explicitly requested by Comparator.
primitives = ['Nat', 'String', 'String.mk', 'Char', 'Char.ofNat', 'List', 'Quot',
              'Quot.mk', 'Quot.lift', 'Quot.ind', 'Nat.add', 'Nat.sub', 'Nat.mul',
              'Nat.pow', 'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble',
              'Nat.land', 'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList']
cmd = ['./scripts/lake', 'env', str(exporter), config['solution_module'], '--',
       *config['theorem_names'], *config['permitted_axioms'], *primitives]
with export.open('wb') as f, (out / 'export.log').open('w') as log:
    result = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=log)
record = {'configuration': args.configuration, 'targets': config['theorem_names'],
          'export_exit_code': result.returncode, 'checker_exit_code': None,
          'binary_sha256': hashlib.sha256(args.binary.read_bytes()).hexdigest()}
(out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')
if result.returncode:
    raise SystemExit(result.returncode)
with export.open('rb') as f:
    record['export_sha256'] = hashlib.file_digest(f, 'sha256').hexdigest()
with export.open('rb') as f, (out / 'checker.log').open('w') as log:
    result = subprocess.run([str(args.binary.resolve()), str(ROOT / 'verification/nanoda-config.json')],
                            stdin=f, stdout=log, stderr=subprocess.STDOUT)
record['checker_exit_code'] = result.returncode
(out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'Nanoda exit code: {result.returncode}; records: {out}')
raise SystemExit(result.returncode)
