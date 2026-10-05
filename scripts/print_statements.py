#!/usr/bin/env python3
"""Print actual elaborated target types and key definition bodies for human review.
This is a readable compiler query, not an independent semantic verdict.
"""
import datetime
import hashlib
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
out = root / 'verification/runs/statement-query'
out.mkdir(parents=True, exist_ok=True)
definitions = [
    'BecknerOnofri.HighDim.ProbabilityDensity',
    'BecknerOnofri.HighDim.ProbabilityDensity.FiniteEntropy',
    'BecknerOnofri.HighDim.entropy',
    'BecknerOnofri.HighDim.extendedEntropy',
    'BecknerOnofri.HighDim.spectralEnergy',
    'BecknerOnofri.HighDim.InCriticalSobolev',
    'BecknerOnofri.HighDim.potentialEnergy',
    'BecknerOnofri.Paper2.negativeSobolevEnergy',
    'BecknerOnofri.Paper2.negativeSobolevFourierSeries',
    'BecknerOnofri.Paper2.Periodization.coordinatePartial',
    'BecknerOnofri.Paper2.Periodization.mixed',
    'BecknerOnofri.Paper2.Physical.coordinateMeasure',
    'BecknerOnofri.Paper2.Physical.spatialMeasure',
    'BecknerOnofri.Paper2.Physical.smoothCoreProfile',
    'BecknerOnofri.Paper2.Physical.core',
    'BecknerOnofri.Paper2.Physical.formClosure',
    'BecknerOnofri.Paper2.Physical.formPairing',
    'BecknerOnofri.Paper2.Physical.operatorGraph',
    'BecknerOnofri.Paper2.Physical.SpectralPowerGraph',
    'BecknerOnofri.Paper2.Physical.torusPower',
    'BecknerOnofri.Paper2.Physical.FractionalIntertwining',
]
source = ('import Solution\nset_option format.width 100\nset_option pp.fullNames true\n'
          + '\n'.join('#check ' + n for n in config['theorem_names']) + '\n'
          + '\n'.join('#print ' + n for n in definitions) + '\n')
p = out / 'PrintStatements.lean'
p.write_text(source)
result = subprocess.run([str(root / 'scripts/lake'), 'env', 'lean', str(p)],
                        cwd=root, capture_output=True, text=True)
text = result.stdout + result.stderr
(out / 'statements.txt').write_text(text)
record = {'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'exit_code': result.returncode,
          'target_count': len(config['theorem_names']),
          'definition_count': len(definitions),
          'source_manifest_sha256': hashlib.sha256((root / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest(),
          'output_sha256': hashlib.sha256(text.encode()).hexdigest(),
          'independent_semantic_review': False}
(out / 'statement-query.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
raise SystemExit(result.returncode)
