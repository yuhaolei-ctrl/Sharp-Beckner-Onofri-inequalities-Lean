# Kernel validation

## Completed certificate

The full official Comparator CLI replay passed for all 269 targets. The
independent, unmodified con-ron checker then accepted the same exact export in
`--verified` mode: **1,027,308 records**, exit 0, 2:30:01 elapsed, hosted run
[37300905046](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/runs/37300905046).
The raw source/export identities and actual positive/negative controls match.
The preparation step checks that every registered root occurs in the raw
export and that its complete axiom inventory is the three permitted names.
The artifact's empty `checked-targets.txt` is an unused Nanoda pretty-printer
placeholder from the shared preparation helper; con-ron acceptance is the
complete record check in `con-ron.log`, not that placeholder.
The [combined validation result](current/final-kernel-validation.json) is
reproduced by:

```sh
python3 scripts/validate_external_evidence.py \
  --con-ron verification/current/con-ron-hosted \
  --local-comparator verification/current/comparator-local
```

The proof source is frozen at `d561980e2b10e1c431e1a1656a025bd41e7270dd`;
later commits add documentation, checker tooling and evidence. The local
duplicate con-ron run was stopped only after the hosted full acceptance and
combined validation passed. Its actual signal/exit receipt is preserved in
`current/con-ron-local-interrupted/`; it is not a second acceptance.
The following sections retain the complete attempt history and reproduction
instructions. No independent human semantic approval or Arena listing is claimed.

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

Run 37271984661, with two 1 GiB workers, ended with exit 143. GitHub supplied
no further termination cause and skipped artifact preservation. Its full log
and annotations are retained; it did not report a mathematical rejection.
The last live trace entries were declarations 570476 and 570241.

The next run uses **one worker** to reduce concurrent memory use. The runtime
adapter dispatches that worker through the same explicitly allocated 1 GiB
stack path; inference and checking rules remain unchanged. Its valid/invalid
controls and exact-once 536-declaration trace inventory are recorded in
`current/nanoda-single-worker-control/`. All worker choices use a strict
three-axiom allow-list.
The single-worker hosted run (37281025130) ultimately failed because GitHub
lost contact with its runner. GitHub supplied no checker exit code, finished
log or artifact; the actual run state and annotation are retained in
`current/nanoda-attempt-37281025130/`. It is not an independent acceptance.
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
unexecuted full manuscript check. Never replace an uncompleted run by this recipe.

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
.tools/replay/.lake/build/bin/replay-exports verification/certified-comparator.json \
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

Run 37272652155 reached GitHub's six-hour limit without complete acceptance.
Its final progress reports 522,206 declarations and a prolonged reduction of
`Spin.CandidateBatch0120.candidate1923._proof_1`. The complete workflow log,
actual timeout annotation and uploaded evidence are preserved in
`current/eink0rn-attempt-37272652155/`. No checker exit code or mathematical
rejection is inferred from this platform cancellation.

The evidence validator also accepts `--eink0rn DIR` for a completed eink0rn
artifact, or both independent implementations when both completed. Use
`--local-comparator DIR` instead of `--comparator DIR` for an actual completed
upstream CLI receipt. The acceptance requirement is a completed full official
Comparator replay and at least one completed independent implementation;
unsuccessful optional implementations remain explicitly recorded.

A separately recorded two-worker retry can add 8 GiB of swap on its disposable
GitHub runner. This supplies memory headroom without changing any proof or
checking rule. The workflow preserves the host memory/swap settings. The prior
exit-143 cause remains unspecified; this resource variant is not a diagnosis.
That retry, run 37284776024, also ended with exit 143 at 10:37:17 UTC. GitHub
again skipped all artifact steps and reported no further cause. Its complete
workflow log and annotations are in `current/nanoda-attempt-37284776024/`.
It did not complete independent verification.

The full 269-target upstream Comparator CLI completed successfully on macOS at
2026-10-05 09:49:48 UTC. `current/comparator-local/` preserves its actual result,
complete log, both export identities and capture provenance. This is a full
official-kernel replay in development mode; it does not claim Linux isolation.

The final receipt validator accepts `--local-nanoda DIR` for a complete local
independent replay, with the actual exit record, acceptance message, checker
configuration, exact export identity and all registered target names resolved.
The same acceptance conditions apply to local and hosted kernels.
The attempted local two-worker Nanoda run was deliberately interrupted at
11:15:45 UTC after prolonged swapping on declarations 570241 and 570476;
the requested signal and actual wrapper result are retained in
`current/nanoda-local-interrupted/`. It did not pass. The redundant hosted
Comparator replay separately hit GitHub's six-hour limit after accepting
formal statements, reachable definitions and axioms. Its final workflow log
and partial artifact are in `current/comparator-hosted-timeout/`; full official
acceptance comes from the successful local upstream CLI run above.

`current/solution-inventory.json` inventories the actual raw export: 1,029,606
declarations, including dependencies. Reproduce it with
`python3 scripts/audit_export_inventory.py external-check/solution.ndjson`.
This inventory script does not check proofs. The final validator requires the
Nanoda acceptance count to equal the complete export count; it rejects messages
that report skipped axioms. When compressed worker traces are present, it also
requires every index exactly once and the exact exported declaration-name set.
Trace entries alone never establish acceptance because they precede checking.

## Additional Lean4Lean replay

The optional `lean4lean.yml` workflow uses the unmodified
[Arena-pinned Lean4Lean](https://github.com/digama0/lean4lean/tree/bce3448115f7819fc12d647fadd3bb090666637e)
revision `bce3448115f7819fc12d647fadd3bb090666637e`. As its authors and Arena
explain, this implementation is derived directly from the official C++ kernel;
it is not an independently designed kernel. It is therefore recorded separately
from Nanoda and eink0rn, and is not accepted by the independent-evidence validator.

The checker builds with its own pinned Lean 4.33.0-rc2 runtime; it reads the exact
existing Lean 4.32.0 export without recompiling the manuscript. The workflow
first accepts the valid control and rejects the damaged proof control. Any
cross-version incompatibility or unfinished replay is recorded as such, never
as acceptance. The upstream import driver recreates quotient primitives,
regenerates inductive constructors/recursors and checks their exported forms;
its reported count is a replay-operation count, not the raw declaration count.
The first full attempt (37300200036) hit the checker's deterministic reduction
limit at `HeatCertificate.Panels0177.e060903`; its compact actual evidence is
preserved. Controls accepted the valid proof and reported a declaration type
mismatch for the damaged proof, with extra pretty-printer diagnostics.
The retry increases the documented finite `whnf`, `whnfEager` and `lazyDelta`
fuel limits to 10,000,000, 100,000,000 and 1,000,000. These runtime limits do not
change checking rules. They are recorded alongside the exact invocation.
That optional retry (37301154501) was deliberately cancelled after the complete
independent con-ron acceptance and combined evidence validation passed. It is
not a Lean4Lean acceptance. Its actual run state, controls and unfinished log
are preserved in `current/lean4lean-cancelled-37301154501/`.

## Independent con-ron verified mode

The `con-ron.yml` workflow uses the unmodified
[Arena-pinned con-ron](https://github.com/leanprover/con-ron/tree/2e3486617cee878f796d8133c481e239696132fe)
revision `2e3486617cee878f796d8133c481e239696132fe`, Rust 1.90.0, four workers,
and **`--verified`**, with its embedded default prelude and arithmetic pins.
The `--trusted` mode is never used. The raw export and registered roots are
validated before replay, and correct/damaged proof controls must pass first.

Con-ron is a Rust implementation of con-leche's checker, with different term
storage and caching. Its upstream project supplies refinement and consistency
theorems via Aeneas; its driver and parser are outside those theorems. This task
does not claim to have independently audited or rebuilt that metatheory.

The exact export contains 1,027,308 declaration **records**, representing
1,029,606 named declarations. An inductive block is one record but introduces
several names. Con-ron's final accepted count must equal the former; Nanoda's
count must equal the latter. `scripts/validate_external_evidence.py --con-ron
DIR --local-comparator DIR` requires a completed successful hosted run,
verified-mode acceptance of every record, exact certificate identity, the
fixed checker settings and actual control results. A decline, error or partial
run cannot satisfy it.

For a local run without the hosted job's wall-time limit, build the same pinned
checker and run `python3 scripts/check_con_ron.py --checker /path/to/con-ron
--evidence /new/evidence/directory --workers 1`. The helper verifies the clean
source checkout and raw certificate hash, runs the controls, and records the
checker's direct process exit (without a timing-command wrapper). Its input
is `external-check/solution.ndjson`, prepared as above. The final validator's
`--local-con-ron DIR` option requires the actual completed local receipt and
the same full verified-mode acceptance conditions; it also permits the
four-worker invocation. An ongoing local run has no final receipt and cannot
pass validation.

## Current source layout and frozen replay evidence

Published export receipts retain their original module names and source digest.
Replay preparation and receipt validation therefore use
`verification/certified-source-manifest.json` and
`verification/certified-comparator.json`. Fresh exports use the unified
`Challenge`/`Solution` modules and `comparator.json`.
Run `python3 scripts/source_layout.py` to verify the exact allowed reorganization;
see [SOURCE_LAYOUT.md](SOURCE_LAYOUT.md) for the separate verification scopes.

## Restarting Lean4Lean after a failed old run

GitHub's **Re-run jobs** uses the original run's commit. Re-running commit
`0edcab2` therefore still uses the default reduction limits, even though `main`
has the larger finite limits. Its second attempt on October 5 again stopped
at `BecknerOnofri.HighDim.EntropyTail.HeatCertificate.Panels0177.e060903`
with `(kernel) deterministic timeout`; that is a resource-limit failure,
not a reported declaration type mismatch.

To use the correction, open **Actions → Additional Lean4Lean certificate
replay → Run workflow**, choose `main`, and select certificate release
`verified-20261005`. Equivalently:

```sh
gh workflow run lean4lean.yml --ref main -f certificate_release=verified-20261005
```

The checker still checks the entire exact export, with unchanged logical rules
and valid/damaged proof controls. Only an exit code of zero plus the checker's
final acceptance message counts as success. The workflow now prints the
checker log tail on failure as well, so the error is visible in the Actions log.
Historical failed attempts remain recorded.
