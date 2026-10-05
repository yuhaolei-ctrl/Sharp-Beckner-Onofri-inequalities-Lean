#!/usr/bin/env python3
"""Inventory actual export bytes; this is not a proof checker."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('export', type=Path)
args = parser.parse_args()
names = {0: ''}
declared = set()
axioms = set()
digest = hashlib.sha256()
size = 0
records = 0
with args.export.open('rb') as src:
    for line in src:
        digest.update(line)
        size += len(line)
        if b'"ie":' in line or b'"il":' in line:
            continue
        row = json.loads(line)
        if 'in' in row:
            item = row.get('str', row.get('num', {}))
            parent = names[item.get('pre', 0)]
            component = item.get('str', str(item.get('num', item.get('i', '?'))))
            names[row['in']] = parent + ('.' if parent else '') + component
        elif 'inductive' in row:
            records += 1
            for group in ('types', 'ctors', 'recs'):
                declared.update(names[item['name']] for item in row['inductive'][group])
        else:
            for kind in ('def', 'thm', 'axiom', 'opaque', 'quot'):
                if kind in row:
                    records += 1
                    name = names[row[kind]['name']]
                    declared.add(name)
                    if kind == 'axiom':
                        axioms.add(name)
print(json.dumps({'export_sha256': digest.hexdigest(), 'bytes': size,
                  'declaration_record_count': records,
                  'declaration_count': len(declared),
                  'declaration_names_sha256': hashlib.sha256(
                      ''.join(n + '\n' for n in sorted(declared)).encode()).hexdigest(),
                  'axioms': sorted(axioms)}, indent=2))
