#!/usr/bin/env python3
"""Fetch exact source revisions. Never overwrite an existing checkout."""
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def ensure(url, rev, path):
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'clone', '--no-checkout', url, str(path)], check=True)
        subprocess.run(['git', '-C', str(path), 'checkout', '--detach', rev], check=True)
    head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain',
                                     '--untracked-files=no'], text=True).strip()
    if head != rev or dirty:
        raise SystemExit(f'Refusing changed dependency: {path}; expected {rev}, got {head}')


for pin in json.loads((ROOT / 'dependencies.json').read_text()):
    ensure(pin['url'], pin['rev'], ROOT / 'vendor' / pin['name'])
comparator = ROOT / 'vendor/comparator'
for pin in json.loads((comparator / 'lake-manifest.json').read_text())['packages']:
    ensure(pin['url'], pin['rev'], comparator / '.lake/packages' / pin['name'])
print('All dependency revisions match; no compiler or proof check was performed.')
