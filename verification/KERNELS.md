# Kernel validation

The official Lean kernel and Nanoda are different implementations. Comparator's
default-kernel replay is an additional replay by the **official** kernel, not
itself an independent kernel. The historical configuration disables Nanoda.

The current checker source is pinned to Nanoda
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with Rust 1.90.0.
The first runtime patch followed Arena's 256 MiB worker-stack recipe. The full
certificate exceeded that stack: run 37266167712 aborted with a stack overflow,
exit 134, after 1:07:44; its peak resident memory was 13,158,032 KiB. This was a
runtime failure, not a successful check or a proof-rejection diagnostic.
The four-worker run using the same limit was cancelled before replacement.

`scripts/patch_nanoda_runtime.py` now raises worker stacks to **1 GiB** and adds
optional per-worker declaration-name traces. The upstream declaration checker,
inference, equality and axiom rules remain unchanged. The complete source diff
and checker binary digest are included in each artifact. Trace files are written
only when `NANODA_TRACE_DIR` is set; they make a later runtime failure locatable.
The valid/invalid proof controls and exact-once trace inventory are recorded in
`current/nanoda-runtime-control/`. They do not replace the full-corpus check.

The default remains two workers to limit memory use. Both worker choices use a
strict three-axiom allow-list.
`unpermitted_axiom_hard_error=false` only skips unused exported axioms; a proof
referring to one still fails. `unsafe_permit_all_axioms` remains false.

```sh
git clone https://github.com/ammkrn/nanoda_lib .tools/nanoda
git -C .tools/nanoda checkout 4c544ed4099c8227f07d5de77ad1e69fb0740a27
python3 scripts/patch_nanoda_runtime.py .tools/nanoda
cargo build --release --locked --manifest-path .tools/nanoda/Cargo.toml
python3 scripts/check_nanoda.py --binary .tools/nanoda/target/release/nanoda_bin
```

The published certificate is also checked by the manual `independent-kernel.yml`
GitHub Actions workflow on a separate Linux host. It verifies the source manifest,
compressed and raw hashes, and actual presence of all 269 target declarations, then
builds the pinned Nanoda checker. Its pretty-printer must resolve all registered
target names after checking the complete export. The first CI attempt failed
before kernel checking because its output file had not been initialized; that
attempt and later outcomes remain visible in `STATUS.json` and Actions.

The proof export is large. The script records source configuration, exact target
list, exporter result, binary digest, export digest and checker exit code.
The current `STATUS.json` distinguishes the actual baseline check from any
unexecuted full paper-2 check. Never replace an uncompleted run by this recipe.

Alternatively set `enable_nanoda` to true in a separately named Comparator
configuration and set `COMPARATOR_NANODA` to the absolute binary path. This
checks matching and both kernels in one workflow.

The control fixture in `tests/comparator_controls` has a matching true theorem
and a different true theorem under the same name. The matching configuration
must be accepted by both kernels; the mismatch must be rejected by Comparator.
These are tool checks, not acceptance of the Beckner–Onofri corpus.

## Lean Kernel Arena

Primary documentation:
[Arena](https://arena.lean-lang.org/),
[contribution interface](https://github.com/leanprover/lean-kernel-arena),
[Nanoda recipe](https://github.com/leanprover/lean-kernel-arena/blob/master/checkers/nanoda.yaml),
[test schema](https://github.com/leanprover/lean-kernel-arena/blob/master/schemas/test.json).

Generate a proposed module test after publication:

```sh
python3 scripts/arena_test.py --revision "$(git rev-parse HEAD)" > beckner-onofri.yaml
```

JSON syntax is valid YAML. The descriptor pins the source revision and runs the
dependency bootstrap before exporting only the registered declarations.
Arena's exporter/Lean version must be compatible with Lean 4.32.0; migrating
this certificate to another toolchain requires a separate checked change.
The descriptor is preparation for an external run, not a submitted or accepted
Arena result. No Arena pull request or website entry has been created.

## Replaying published exports without rebuilding the manuscript

The certificate release also contains `challenge.ndjson.gz` and
`challenge-export.json`. These are the exact challenge bytes exported by the
full upstream Comparator run; both manifests identify the same proof-source
commit and source digest.

`comparator-replay.yml` validates both archives, pins Comparator, Lean4Checker
and the exporter, and builds `verification/tools/ReplayExports.lean`. This small
driver calls the upstream `compareAt`, `checkAxioms` and official-kernel `replay'`
functions unchanged. It reads file streams instead of holding both exports as
strings, and emits progress messages. This is a separate replay driver, not a
claim that the upstream CLI was modified. It does not perform the optional
Nanoda check; that is the separate independent-kernel workflow.

The driver is checked on a matching true statement and a different true
statement under the same name; results are in `current/replay-controls.json`.
No successful control run substitutes for acceptance of the 269-target corpus.
The public workflow logs distinguish the two runs.

After downloading the four release assets to `external-check/`, with Lean
4.32.0 on PATH:

```sh
python3 scripts/prepare_external_check.py
python3 scripts/prepare_comparator_replay.py
lake -d .tools/replay build replay-exports
.tools/replay/.lake/build/bin/replay-exports comparator-paper2.json \
  external-check/challenge.ndjson external-check/solution.ndjson
```

The source manifest, challenge and solution digests are checked before replay.
The comparator library checks equality of reachable definitions, so a changed
meaning cannot be hidden behind an unchanged theorem name.

Downloaded final Actions artifacts can be checked together with
`scripts/validate_external_evidence.py --nanoda DIR --comparator DIR`. Each
directory must also contain `run.json`, obtained with `gh run view RUN_ID
--json databaseId,url,headSha,status,conclusion,jobs`. The validator requires
completed successful runs, acceptance messages, exact source/export identities,
and the registered declaration inventory. It does not certify prose semantics.

## Additional independent Haskell implementation

The optional `eink0rn.yml` workflow checks the same raw export with
[eink0rn](https://github.com/Timeroot/eink0rn), revision
`31a9e3a1347d0544e8362fabea0ac669b41afbbb`, the revision named by its
[Arena recipe](https://github.com/leanprover/lean-kernel-arena/blob/master/checkers/eink0rn.yaml).
It builds the unmodified checker from source and preserves compiler/build output
and the binary digest. `--enforce-mutual-univ`, `--pin-std=error`, and
`--nat-accel=canonical` are explicit; the deliberately unsound `always`
arithmetic mode is never used. All exported axiom names must be exactly the
three registered standard axioms. The workflow checks a valid fixture and a
fixture with a deliberately damaged proof before checking the complete export.

This is an additional implementation with its own documented theory and
compatibility choices; see its `SPEC.md`. It is not represented as the official
Lean kernel, nor is its source review a new metatheoretic soundness proof.
An `ACCEPT` is recorded only after the complete run returns successfully;
resource limits, checker faults and rejections remain distinguished.
