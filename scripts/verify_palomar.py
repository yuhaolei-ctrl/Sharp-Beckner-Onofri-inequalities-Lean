#!/usr/bin/env python3
"""Build, audit and optionally replay one exact Palomar candidate entry."""
import argparse
import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('config', type=Path)
parser.add_argument('--comparator', action='store_true')
parser.add_argument('--development', action='store_true',
                    help='Explicitly disable the Linux sandbox for a local development check')
args = parser.parse_args()
config_path = (ROOT / args.config).resolve()
config_path.relative_to(ROOT)
config = json.loads(config_path.read_text())
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
out = ROOT / 'verification/runs' / (stamp + '-' + config_path.stem)
out.mkdir(parents=True)
record = {'config': str(config_path.relative_to(ROOT)),
          'config_sha256': hashlib.sha256(config_path.read_bytes()).hexdigest(),
          'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
          'local_development_mode': args.development, 'checks': {},
          'palomar_registration': False, 'status': 'running'}
source_names = subprocess.check_output(
    ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
    cwd=ROOT).decode().split('\0')
source_inventory = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                    for name in sorted(set(source_names))
                    if name and (ROOT / name).is_file()}
(out / 'source-inventory.json').write_text(json.dumps(source_inventory, indent=2) + '\n')
record['source_inventory_sha256'] = hashlib.sha256(
    (out / 'source-inventory.json').read_bytes()).hexdigest()
record['git_commit'] = subprocess.check_output(
    ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()


def save():
    (out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')


def run(name, command):
    log = out / (name + '.log')
    print(f'{name}: {log}', flush=True)
    with log.open('w') as stream:
        code = subprocess.run(command, cwd=ROOT, stdout=stream,
                              stderr=subprocess.STDOUT).returncode
    record['checks'][name] = {'exit_code': code,
                              'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()}
    if code:
        record['status'] = 'failed'
    save()
    if code:
        raise SystemExit(f'{name} failed (exit {code}); evidence preserved at {out}')
    return log.read_text()


run('structure', ['python3', 'scripts/audit_palomar.py'])
run('build', ['./scripts/lake', 'build', config['challenge_module'], config['solution_module']])
audit = out / 'Axioms.lean'
audit.write_text('module\n\npublic import ' + config['solution_module'] + '\n\n' +
                 '\n'.join('#print axioms ' + name for name in config['theorem_names']) + '\n')
output = run('axioms', ['./scripts/lake', 'env', 'lean', str(audit)])
rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
axioms_ok = (len(rows) == len(config['theorem_names']) and
             {name for name, _ in rows} == set(config['theorem_names']) and
             all(set(a.strip() for a in row.split(',') if a.strip()) <=
                 set(config['permitted_axioms']) for _, row in rows))
record['checks']['axioms']['targets_and_axioms_validated'] = axioms_ok
if not axioms_ok:
    record['status'] = 'failed'
    save()
    raise SystemExit('Missing axiom-audit targets or unpermitted axiom; see ' + str(out))
save()
if args.comparator:
    command = ['./scripts/lake', 'comparator', '--config', str(config_path)]
    if args.development:
        command.append('--inadvisably-no-sandbox')
    run('comparator', command)
changed = [name for name, digest in source_inventory.items()
           if not (ROOT / name).is_file() or
           hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest]
final_names = {name for name in subprocess.check_output(
    ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
    cwd=ROOT).decode().split('\0') if name and (ROOT / name).is_file()}
changed.extend(sorted(final_names - set(source_inventory)))
record['source_unchanged'] = not changed
record['status'] = ('passed' if args.comparator else 'build_and_axioms_passed') if not changed else 'failed'
save()
if changed:
    raise SystemExit('Source changed during verification: ' + ', '.join(changed))
print(json.dumps(record, indent=2))
