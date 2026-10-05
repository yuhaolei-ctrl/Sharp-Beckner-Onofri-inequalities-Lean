#!/usr/bin/env python3
"""Validate downloaded Actions evidence; never infer success from an ongoing run.
Each input directory must include run.json from `gh run view --json ...` and
the corresponding Actions artifact. Prints a summary only after both pass.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--nanoda', type=Path, required=True)
parser.add_argument('--comparator', type=Path, required=True)
args = parser.parse_args()
config = json.loads((root / 'comparator-paper2.json').read_text())
manifest_hash = hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest()
expected_proof = json.loads((root / 'verification/current/certificate-export.json').read_text())
expected_challenge = json.loads((root / 'verification/current/challenge-export.json').read_text())


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def base(path):
    run = json.loads((path / 'run.json').read_text())
    assert run['status'] == 'completed' and run['conclusion'] == 'success', run
    assert all(j['conclusion'] == 'success' for j in run['jobs'])
    proof = json.loads((path / 'certificate-export.json').read_text())
    assert proof == expected_proof
    assert proof['source_manifest_sha256'] == manifest_hash
    assert proof['exit_code'] == 0 and proof['module'] == 'Paper2Solution'
    declared = json.loads((path / 'declared-targets.json').read_text())
    assert declared == config['theorem_names']
    return {'run_id': run['databaseId'], 'run_url': run['url'],
            'workflow_commit': run['headSha'], 'conclusion': run['conclusion'],
            'evidence_sha256': {p.name: digest(p) for p in sorted(path.iterdir()) if p.is_file()}}


nanoda = base(args.nanoda)
settings = json.loads((args.nanoda / 'nanoda-config.json').read_text())
assert settings['pp_declars'] == config['theorem_names']
assert settings['unknown_pp_declar_hard_error'] is True
assert settings['unsafe_permit_all_axioms'] is False
assert set(settings['permitted_axioms']) == set(config['permitted_axioms'])
assert (args.nanoda / 'checked-targets.txt').stat().st_size > 0
text = (args.nanoda / 'nanoda.log').read_text()
match = re.search(r'Checked ([0-9]+) declarations with no errors', text)
assert match, 'Missing independent-kernel acceptance'
nanoda['worker_threads'] = settings['num_threads']
nanoda['checked_declarations'] = int(match[1])
assert nanoda['checked_declarations'] >= len(config['theorem_names'])
if (args.nanoda / 'runtime-settings.json').exists():
    nanoda['runtime_settings'] = json.loads((args.nanoda / 'runtime-settings.json').read_text())
nanoda['checker_revision'] = '4c544ed4099c8227f07d5de77ad1e69fb0740a27'

comparator = base(args.comparator)
challenge = json.loads((args.comparator / 'challenge-export.json').read_text())
assert challenge == expected_challenge
assert challenge['source_commit'] == expected_proof['source_commit']
text = (args.comparator / 'comparator.log').read_text()
for marker in ('Comparator accepts all registered statements and reachable definitions.',
               'Comparator accepts axiom dependencies.',
               'Lean default kernel accepts the solution', 'Your solution is okay!'):
    assert marker in text, marker
match = re.search(r'Solution parsed: ([0-9]+) declarations\.', text)
assert match
comparator['parsed_declarations'] = int(match[1])
assert comparator['parsed_declarations'] >= len(config['theorem_names'])
comparator['checker_revision'] = '07bc4ea40f2266dcb861820a2ec1fa3244ed307f'
comparator['driver'] = 'verification/tools/ReplayExports.lean'

print(json.dumps({'external_machine_checks': 'passed',
                  'registered_targets': len(config['theorem_names']),
                  'proof_source_commit': expected_proof['source_commit'],
                  'source_manifest_sha256': manifest_hash,
                  'proof_export_sha256': expected_proof['export_sha256'],
                  'challenge_export_sha256': expected_challenge['export_sha256'],
                  'nanoda': nanoda, 'comparator': comparator,
                  'independent_natural_language_review': False}, indent=2))
