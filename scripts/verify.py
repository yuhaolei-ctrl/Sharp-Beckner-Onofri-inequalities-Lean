#!/usr/bin/env python3
"""Run the selected checks and preserve actual exit codes and source identities.
Pass --comparator for the full, potentially long, 269-target kernel replay.
"""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('--comparator', action='store_true')
p.add_argument('--development', action='store_true')
args = p.parse_args()
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out = ROOT / 'verification/runs' / stamp
out.mkdir(parents=True)
record = {'started_utc': stamp, 'checks': {},
          'manifest_sha256': hashlib.sha256((ROOT / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()}


def run(name, cmd):
    log = out / (name + '.log')
    print(f'Running {name}; log: {log}', flush=True)
    with log.open('w') as f:
        code = subprocess.run(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT).returncode
    record['checks'][name] = {'exit_code': code, 'command': cmd,
                              'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    (out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')
    if code:
        raise SystemExit(f'{name} failed with exit {code}; inspect {log}')
    return log.read_text()


run('structural', ['python3', 'scripts/audit.py'])
run('build', ['./scripts/lake', 'build', 'Challenge', 'Solution'])
axioms = run('axioms', ['./scripts/lake', 'env', 'lean', 'AxiomAudit.lean'])
rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axioms)
config = json.loads((ROOT / 'comparator.json').read_text())
assert len(rows) == len(config['theorem_names'])
assert {name for name, _ in rows} == set(config['theorem_names'])
assert {a.strip() for _, row in rows for a in row.split(',') if a.strip()} <= set(config['permitted_axioms'])
if args.comparator:
    cmd = ['./scripts/check-comparator.sh']
    if args.development:
        cmd.append('--development')
    cmd.append('comparator.json')
    text = run('comparator', cmd)
    assert 'Lean default kernel accepts the solution' in text
    assert 'Your solution is okay!' in text
print(f'Completed requested checks; results: {out / "results.json"}')
