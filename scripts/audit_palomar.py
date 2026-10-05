#!/usr/bin/env python3
"""Local structural preflight, not Palomar acceptance or semantic certification."""
import json
import re
import subprocess
from pathlib import Path

from proof_source_audit import code_only, forbidden_hits

ROOT = Path(__file__).resolve().parents[1]
errors = []


def require(condition, message):
    if not condition:
        errors.append(message)


names = subprocess.check_output(
    ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
    cwd=ROOT).decode().split('\0')
paths = sorted({ROOT / name for name in names if name})
require(sum(p.stat().st_size for p in paths if p.is_file() and not p.is_symlink())
        <= 500 * 1024**2, 'Repository exceeds 500 MiB')
for path in paths:
    if path.suffix != '.lean':
        continue
    require(not path.is_symlink(), f'Symlinked Lean source: {path}')
    text = path.read_text()
    require(len(text.splitlines()) <= 10000, f'Overlong source: {path}')
    code = code_only(text)
    require(code.lstrip().startswith('module\n'), f'Missing module header: {path}')
    rel = path.relative_to(ROOT)
    deliberate_challenge = path.name.endswith('Challenge.lean')
    control = rel.parts[:2] == ('tests', 'comparator_controls')
    if not deliberate_challenge and not control:
        for line, token in forbidden_hits(text):
            errors.append(f'{rel}:{line}: forbidden proof token {token}')

metadata = json.loads((ROOT / 'formalization.yaml').read_text())
require(metadata['project']['license'] == 'Apache-2.0', 'Metadata license mismatch')
require('Apache License' in (ROOT / 'LICENSE').read_text(), 'Missing Apache license text')
require(metadata['project']['authors'] == ['Yuhao Lei', 'Matthew Rosenzweig'],
        'Author metadata differs from author instructions')
require(metadata['project']['responsible_maintainers'] == metadata['project']['authors'],
        'Maintainer metadata differs from author instructions')
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
for package in manifest['packages']:
    require(package['type'] == 'git', f'Non-Git dependency: {package["name"]}')
    require(re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')),
            f'Unpinned dependency: {package["name"]}')
    require(re.fullmatch(r'https://github\.com/[^/?#]+/[^/?#]+', package.get('url', '')),
            f'Unsupported dependency URL: {package["name"]}')

entries = []
for config_path in sorted((ROOT / 'Palomar').glob('comparator-*.json')):
    config = json.loads(config_path.read_text())
    require(set(config) <= {'challenge_module', 'solution_module', 'theorem_names',
                           'definition_names', 'permitted_axioms', 'enable_nanoda'},
            f'Unexpected Comparator keys: {config_path}')
    require(set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'},
            f'Unexpected axiom policy: {config_path}')
    challenge = ROOT / (config['challenge_module'].replace('.', '/') + '.lean')
    solution = ROOT / (config['solution_module'].replace('.', '/') + '.lean')
    text = challenge.read_text()
    require(len(text.encode()) <= 100 * 1024 and len(text.splitlines()) <= 1000,
            f'Challenge exceeds Palomar limits: {challenge}')
    imports = re.findall(r'^public import (\S+)', text, re.M)
    require(imports and all(m.startswith('Mathlib.') for m in imports),
            f'Project-specific Challenge import: {challenge}')
    declared = re.findall(r'^theorem (\w+)', text, re.M)
    require({'BecknerOnofri.Target.' + name for name in declared} == set(config['theorem_names']),
            f'Compared statement inventory mismatch: {challenge}')
    require(config['challenge_module'] not in solution.read_text(),
            f'Solution imports its Challenge: {solution}')
    entries.append({'config': str(config_path.relative_to(ROOT)),
                    'lines': len(text.splitlines()), 'bytes': len(text.encode()),
                    'targets': len(declared)})
if errors:
    raise SystemExit('\n'.join(errors))
print(json.dumps({'structural_preflight': 'passed', 'entries': entries,
                  'proof_build_verified': False, 'palomar_acceptance': False}, indent=2))
