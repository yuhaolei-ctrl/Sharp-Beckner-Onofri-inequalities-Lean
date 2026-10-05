# Certificate verification

## Current source

`python3 scripts/verify.py` runs the structural checks, Lean build and axiom
audit. `python3 scripts/audit.py --paper /path/to/manuscript.tex` additionally
checks the manuscript digest and the hashes of its 51 labelled statements.

The source manifest records the current Lean sources and build configuration.
`python3 scripts/source_layout.py` checks the exact allowed filename/import
changes and entrypoint merge against the frozen certified source. The
`certified-*` files and `baseline-source-manifest.json` support that check.
Public theorem identifiers have been preserved.

## Published exports

Download `solution.ndjson.gz`, `certificate-export.json`,
`challenge.ndjson.gz`, and `challenge-export.json` from the
[certificate release](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/releases/tag/verified-20261005)
into `external-check/`. With Lean 4.32.0 on PATH, run:

```sh
python3 scripts/prepare_external_check.py
python3 scripts/prepare_comparator_replay.py
lake -d .tools/replay build replay-exports
.tools/replay/.lake/build/bin/replay-exports verification/certified-comparator.json \
  external-check/challenge.ndjson external-check/solution.ndjson
```

The preparation checks source/export identities and declared targets. Replay
uses the pinned Comparator algorithms. Independent checkers are available as
manual GitHub Actions workflows. Choose **Run workflow**, branch `main`, and
certificate release `verified-20261005`; **Re-run jobs** uses the original
run's revision rather than the latest workflow.

The Nanoda workflow defaults to one worker and 8 GiB of additional swap.
Changes to its workflow or process supervisor on `main` also launch a fresh
replay of `verified-20261005`, so resource fixes are tested at their new commit.
The supervisor samples memory every second, records progress every minute,
and stops with a failed receipt before both available RAM and free swap fall
below 1 GiB, or after 5.5 hours. This leaves time to upload diagnostic evidence
instead of losing it when the runner shuts down. Only an exit-zero complete
checker receipt with resolved targets counts as acceptance. The checker also
has to accept the valid control and reject the damaged proof before replay.

Nanoda run `37281025130`, attempt 2, replayed the old commit `b10b843` without
additional swap. It reached
`BecknerOnofri.HighDim.ScalarCertificate.CertifiedMinorant.hullAccepted._proof_1_1`;
its RSS rose from about 7.8 to 14.7 GiB before the runner shutdown and exit 143.
Memory pressure is the suspected cause; the available log does not contain
an OOM-killer report or a proof rejection. A rerun of that old run still uses
the old workflow and is not a test of the resource fix.

Con-ron has accepted the full export in verified mode. Lean4Lean is an
additional replay, derived from the official kernel implementation. Its
workflow uses larger finite reduction limits and still requires valid-proof
acceptance and damaged-proof rejection. Only a complete successful replay
counts as acceptance. See [STATUS.json](STATUS.json) for recorded results.

## Evidence

Full logs belong in Actions artifacts or release assets, not in the source
tree. The release's `verification-evidence.tar.gz` preserves the original
completed checks; historical failed attempts also remain in Git history.
Use an external or ignored directory when collecting new evidence.

For downloaded con-ron and local Comparator evidence directories:

```sh
python3 scripts/validate_external_evidence.py \
  --con-ron /path/to/con-ron-evidence \
  --local-comparator /path/to/comparator-evidence
```

Hosted evidence must include `run.json` from `gh run view RUN_ID --json
 databaseId,url,headSha,status,conclusion,jobs`. The validator binds successful
receipts to the frozen export metadata in this directory. It does not certify
natural-language correspondence. Independent replay of the frozen exports
must not be described as replay of a new export under renamed modules.
