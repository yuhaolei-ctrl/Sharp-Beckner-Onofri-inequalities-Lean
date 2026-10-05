#!/usr/bin/env python3
"""Validate final receipts; ongoing, failed and resource-limited runs cannot pass.
Hosted artifacts need run.json from gh run view. A local Comparator receipt
needs its actual result.json, comparator.log, and the captured export records.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--nanoda', type=Path)
parser.add_argument('--eink0rn', type=Path)
official = parser.add_mutually_exclusive_group(required=True)
official.add_argument('--comparator', type=Path)
official.add_argument('--local-comparator', type=Path)
args = parser.parse_args()
if not (args.nanoda or args.eink0rn):
    parser.error('At least one completed independent-kernel receipt is required.')
config = json.loads((root / 'comparator-paper2.json').read_text())
manifest_hash = hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()
expected_proof = json.loads((root / 'verification/current/certificate-export.json').read_text())
expected_challenge = json.loads((root / 'verification/current/challenge-export.json').read_text())


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def base(path, hosted=True):
    if hosted:
        run = json.loads((path / 'run.json').read_text())
        assert run['status'] == 'completed' and run['conclusion'] == 'success', run
        assert all(j['conclusion'] == 'success' for j in run['jobs'])
        result = {'run_id': run['databaseId'], 'run_url': run['url'],
                  'workflow_commit': run['headSha'], 'conclusion': run['conclusion']}
    else:
        run = json.loads((path / 'result.json').read_text())
        assert run['exit_code'] == 0 and run['target_count'] == len(config['theorem_names'])
        result = {'local_result': run, 'conclusion': 'success'}
    proof = json.loads((path / 'certificate-export.json').read_text())
    assert proof == expected_proof
    assert proof['source_manifest_sha256'] == manifest_hash
    assert proof['exit_code'] == 0 and proof['module'] == 'Paper2Solution'
    declared = json.loads((path / 'declared-targets.json').read_text())
    assert declared == config['theorem_names']
    if (path / 'declared-axioms.json').exists():
        assert set(json.loads((path / 'declared-axioms.json').read_text())) == set(config['permitted_axioms'])
    result['evidence_sha256'] = {p.name: digest(p) for p in sorted(path.iterdir()) if p.is_file()}
    return result


independent = {}
if args.nanoda:
    record = base(args.nanoda)
    settings = json.loads((args.nanoda / 'nanoda-config.json').read_text())
    assert settings['pp_declars'] == config['theorem_names']
    assert settings['unknown_pp_declar_hard_error'] is True
    assert settings['unsafe_permit_all_axioms'] is False
    assert set(settings['permitted_axioms']) == set(config['permitted_axioms'])
    assert (args.nanoda / 'checked-targets.txt').stat().st_size > 0
    text = (args.nanoda / 'nanoda.log').read_text()
    match = re.search(r'Checked ([0-9]+) declarations with no errors', text)
    assert match, 'Missing independent-kernel acceptance'
    record['worker_threads'] = settings['num_threads']
    record['checked_declarations'] = int(match[1])
    assert record['checked_declarations'] >= len(config['theorem_names'])
    if (args.nanoda / 'runtime-settings.json').exists():
        record['runtime_settings'] = json.loads((args.nanoda / 'runtime-settings.json').read_text())
    record['checker_revision'] = '4c544ed4099c8227f07d5de77ad1e69fb0740a27'
    independent['nanoda'] = record

if args.eink0rn:
    record = base(args.eink0rn)
    settings = json.loads((args.eink0rn / 'runtime-settings.json').read_text())
    assert settings['checker_revision'] == '31a9e3a1347d0544e8362fabea0ac669b41afbbb'
    assert settings['source_patch'] is None and settings['enforce_mutual_univ'] is True
    assert settings['pin_std'] == 'error' and settings['nat_accel'] == 'canonical'
    text = (args.eink0rn / 'eink0rn.log').read_text()
    assert re.search(r'^ACCEPT\s*$', text, re.M), 'Missing eink0rn acceptance'
    controls = json.loads((args.eink0rn / 'controls.json').read_text())
    assert [(r['control'], r['exit_code']) for r in controls] == [('valid', 0), ('invalid', 1)]
    for r, expected in zip(controls, ['ACCEPT', 'REJECT']):
        assert re.search('^' + expected + r'\s*$', r['output'], re.M)
    record['runtime_settings'] = settings
    independent['eink0rn'] = record

path = args.comparator or args.local_comparator
comparator = base(path, hosted=bool(args.comparator))
challenge = json.loads((path / 'challenge-export.json').read_text())
assert challenge == expected_challenge
assert challenge['source_commit'] == expected_proof['source_commit']
text = (path / 'comparator.log').read_text()
for marker in ('Lean default kernel accepts the solution', 'Your solution is okay!'):
    assert marker in text, marker
if args.comparator:
    for marker in ('Comparator accepts all registered statements and reachable definitions.',
                   'Comparator accepts axiom dependencies.'):
        assert marker in text, marker
    match = re.search(r'Solution parsed: ([0-9]+) declarations\.', text)
    assert match and int(match[1]) >= len(config['theorem_names'])
    comparator['parsed_declarations'] = int(match[1])
    comparator['driver'] = 'verification/tools/ReplayExports.lean'
else:
    comparator['driver'] = 'unmodified upstream Comparator CLI; development adapter'
comparator['checker_revision'] = '07bc4ea40f2266dcb861820a2ec1fa3244ed307f'

print(json.dumps({'external_machine_checks': 'passed',
                  'registered_targets': len(config['theorem_names']),
                  'proof_source_commit': expected_proof['source_commit'],
                  'source_manifest_sha256': manifest_hash,
                  'proof_export_sha256': expected_proof['export_sha256'],
                  'challenge_export_sha256': expected_challenge['export_sha256'],
                  'independent_kernels': independent, 'comparator': comparator,
                  'independent_natural_language_review': False}, indent=2))
