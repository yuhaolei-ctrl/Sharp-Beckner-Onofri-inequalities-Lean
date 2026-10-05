#!/usr/bin/env python3
"""Check a filename/import-only reorganization against the frozen certificate.
The only composition is union of the original Challenge declarations and the
12 additions, and adding the Proofs import to the original Solution.
"""
import gzip
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERTIFIED_SHA256 = 'f7f23b1a9a2aeaafbbc61b1fa7e430fe0eb43ab3416413026df975a41fe71ff2'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def frozen_sources():
    raw = (ROOT / 'verification/certified-source-manifest.json').read_bytes()
    assert sha(raw) == CERTIFIED_SHA256, 'Certified manifest changed'
    manifest = json.loads(raw)
    with gzip.open(ROOT / 'verification/certified-layout-sources.json.gz', 'rt') as f:
        originals = json.load(f)
    result = {}
    for name, expected in manifest.items():
        data = originals[name].encode() if name in originals else (ROOT / name).read_bytes()
        assert sha(data) == expected, f'Certified source changed: {name}'
        result[name] = data
    return result


def reorganized(originals):
    modules = {Path(n).stem: Path(n).stem.replace('Paper2', '')
               for n in originals if '/' not in n and n.endswith('.lean') and 'Paper2' in n}
    def imports(data):
        return re.sub(r'(?m)^import (\w+)$',
                      lambda m: 'import ' + modules.get(m[1], m[1]), data.decode()).encode()
    result = {}
    for name, data in originals.items():
        if name in ('Paper2Challenge.lean', 'Paper2Solution.lean', 'comparator.json'):
            continue
        dest = name.replace('Paper2', '').replace('-paper2', '')
        if name.endswith('.lean'):
            data = imports(data)
        elif name.startswith('comparator-'):
            # Keep target names and all other bytes untouched.
            for old, new in [('Paper2Challenge', 'Challenge'), ('Paper2Solution', 'Solution')]:
                data = data.replace(('"' + old + '"').encode(), ('"' + new + '"').encode())
        elif name == 'lakefile.toml':
            text = data.decode()
            for old in ('Paper2Challenge', 'Paper2Solution'):
                text = text.replace('[[lean_lib]]\nname = "' + old + '"\n\n', '')
            for old, new in modules.items():
                text = text.replace('name = "' + old + '"', 'name = "' + new + '"')
            data = text.encode()
        assert dest not in result, dest
        result[dest] = data
    added = re.sub(r'\A(?:import [^\n]+\n)+', '', originals['Paper2Challenge.lean'].decode())
    result['Challenge.lean'] = b'import Definitions\n' + originals['Challenge.lean'] + added.encode()
    assert originals['Paper2Solution.lean'].decode().strip() == 'import Solution\nimport Paper2Proofs'
    result['Solution.lean'] = b'import Proofs\n' + originals['Solution.lean']
    return result


def validate():
    originals = frozen_sources()
    expected = reorganized(originals)
    manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
    assert manifest == {n: sha(d) for n, d in expected.items()}, 'Current manifest differs from allowed reorganization'
    for name, data in expected.items():
        assert (ROOT / name).read_bytes() == data, f'Unexpected source edit: {name}'
    for name in originals.keys() - expected.keys():
        assert not (ROOT / name).exists(), f'Obsolete entry remains: {name}'
    for snapshot, original in [('certified-comparator.json', 'comparator-paper2.json'),
                               ('certified-baseline-comparator.json', 'comparator.json')]:
        assert (ROOT / 'verification' / snapshot).read_bytes() == originals[original]
    baseline = json.loads((ROOT / 'audit/baseline_source_manifest.json').read_text())
    for name, digest in baseline.items():
        assert sha(originals[name]) == digest, f'Frozen baseline changed: {name}'
    return {'source_layout': 'passed', 'current_source_files': len(expected),
            'certified_manifest_sha256': CERTIFIED_SHA256,
            'change_scope': 'module filenames/imports, entrypoint merge, comparator module fields, library names',
            'public_theorem_identifiers_preserved': True,
            'independent_replay_scope': 'original frozen exports; current layout checked separately'}


if __name__ == '__main__':
    print(json.dumps(validate(), indent=2))
