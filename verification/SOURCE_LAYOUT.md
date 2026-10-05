# Source layout and certificate provenance

The current public entries are `Challenge.lean` and `Solution.lean`, with all
269 roots registered in `comparator.json`. The former separate entries have
been merged and removed. Definitions and proof modules use filenames without
the old manuscript prefix. Public theorem names, including the internal
`BecknerOnofri.Paper2` namespace, are preserved.

## What was verified

The completed official Comparator and independent con-ron checks certify the
exact exported bytes from proof-source commit
`d561980e2b10e1c431e1a1656a025bd41e7270dd`. Their original receipts, module
identifiers and digests have not been rewritten. The frozen source manifest
has SHA-256 `f7f23b1a9a2aeaafbbc61b1fa7e430fe0eb43ab3416413026df975a41fe71ff2`.
It is preserved as `certified-source-manifest.json`; the corresponding full
and baseline configurations are `certified-comparator.json` and
`certified-baseline-comparator.json`.

`../scripts/source_layout.py` checks the frozen manifest against that fixed
digest, reconstructs every certified source file (using the small
`certified-layout-sources.json.gz` archive for former root files), and checks
all original source hashes. It then applies only fixed import/module renames,
merges the challenge declarations, adds the proof-module import to Solution,
and updates module fields in configurations and library declarations. The
result must equal every file and hash in the current `../SOURCE_MANIFEST.json`.
It also verifies the unchanged 257-target baseline against its original
manifest and rejects any remaining obsolete entry file.

The new layout is compiled separately and all 269 roots undergo an axiom
audit. This does not claim that an export under the new module paths has had
another independent-kernel replay. Module renaming can change compiler-private
names even when public theorem identifiers and proof text are preserved.

## Reproduce

From the repository root:

```sh
python3 scripts/source_layout.py
python3 scripts/verify.py
python3 scripts/validate_external_evidence.py \
  --con-ron verification/current/con-ron-hosted \
  --local-comparator verification/current/comparator-local
```

The first two commands check the current layout; the last checks the actual
frozen replay receipts. Fresh exports use `Challenge` and `Solution`.
Published-archive replay tools explicitly use the certified manifest and
configuration instead of assigning a new source identity to historical bytes.

The release's display title and tag are updated independently of the frozen
certificate assets. The original packaging manifest and receipts retain their
historical names and hashes. The former tag remains available in Git history.

Actual [build and axiom results](current/source-layout/results.json),
[source equivalence result](current/source-layout/layout-validation.json),
and [frozen evidence revalidation](current/source-layout/frozen-evidence-validation.json)
are preserved separately. The build log is gzip-compressed; its receipt
records both compressed and original log hashes.
