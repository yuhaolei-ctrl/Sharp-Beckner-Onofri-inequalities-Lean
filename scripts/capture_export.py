#!/usr/bin/env python3
"""Transparent exporter wrapper: preserve the exact bytes handed to Comparator.
Set COMPARATOR_LEAN4EXPORT to this script before check-comparator.sh.
No export rewriting, filtering or acceptance inference is performed.
"""
import datetime
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
exe = ROOT / 'vendor/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
module = sys.argv[1] if len(sys.argv) > 1 else 'unknown'
assert module in {'Challenge', 'Solution'}
out = ROOT / 'verification/runs' / ('export-' + stamp)
out.mkdir(parents=True)
record = {'module': module, 'arguments': sys.argv[1:],
          'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
          'source_manifest_sha256': hashlib.sha256((ROOT / 'SOURCE_MANIFEST.json').read_bytes()).hexdigest(),
          'exporter_binary_sha256': hashlib.sha256(exe.read_bytes()).hexdigest(),
          'exit_code': None, 'started_utc': stamp}
(out / 'provenance.json').write_text(json.dumps(record, indent=2) + '\n')
started = time.monotonic()
proc = subprocess.Popen([str(exe), *sys.argv[1:]], cwd=ROOT, stdout=subprocess.PIPE)
digest = hashlib.sha256()
size = 0
with (out / 'proof.ndjson').open('wb') as f:
    while chunk := proc.stdout.read(1024 * 1024):
        f.write(chunk)
        digest.update(chunk)
        size += len(chunk)
        sys.stdout.buffer.write(chunk)
sys.stdout.buffer.flush()
record.update(exit_code=proc.wait(), export_sha256=digest.hexdigest(), bytes=size,
              elapsed_seconds=time.monotonic() - started)
(out / 'provenance.json').write_text(json.dumps(record, indent=2) + '\n')
raise SystemExit(record['exit_code'])
