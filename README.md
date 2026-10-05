# Sharp Beckner–Onofri inequalities: Lean certificate

Lean **4.32.0**, mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`.

This repository formalizes the October 3 manuscript with 269 registered targets,
combining the 257-target September 27 certificate and 12 additional targets.
The adaptation now includes the literal physical-coordinate Friedrichs
intertwining and local uniform convergence of every derivative of the original
periodization series. The 51 formal result environments are the declared
coverage scope; proof-route estimates and remarks outside that set are listed
separately. Final checker outcomes are recorded in [STATUS.json](verification/STATUS.json).
See [the Chinese audit](AUDIT_ZH.md) and [the 51-result statement map](audit/STATEMENT_MAP.md).

**Completed within this 51-result scope:** all 269 registered targets pass the
full upstream Comparator replay and an independent con-ron `--verified` replay.
The [combined evidence validation](verification/current/final-kernel-validation.json)
binds both results to the same source manifest and exact proof export.

The current source uses unified `Challenge.lean` and `Solution.lean` entrypoints.
The former split entrypoints have been removed; public theorem identifiers
(including `BecknerOnofri.Paper2`) remain unchanged. The independent replay
receipts refer to the frozen exported certificate. The deterministic
[source-layout audit](scripts/source_layout.py) checks the filename/import changes
and entrypoint merge against that certificate; the current layout has a separate
build and axiom audit. See [source layout provenance](verification/SOURCE_LAYOUT.md).

## Challenge → Solution → Comparator

| Scope | Trusted statements | Proofs | Configuration |
|---|---|---|---|
| All 269 targets | `Challenge.lean` | `Solution.lean`, `Proofs.lean` | `comparator.json` |
| Only the 12 additions | same | same | `comparator-increment.json` |
| Seven new analysis/coordinate targets | same | same | `comparator-analysis.json` |

The `sorry` terms in the trusted challenges are statement placeholders.
Solutions do not import challenges. Transitive proof axioms must be confined
to `propext`, `Quot.sound`, and `Classical.choice`; `sorryAx` and
`Lean.trustCompiler` are not permitted.

Dimensions 1–10 use the **same workflow**. `LowDimensionRaw` and
`LowDimensionConsequences` connect the current raw density/Sobolev definitions
to proofs in `Legacy`. `Legacy` is a historical namespace, not an assumed
external theorem. Its finite rational certificates use `decide +kernel` and
proved semantic bridges; Python search output is not admitted as an axiom.

## Reproduce

Install the toolchain specified by `lean-toolchain`, or set
`LEAN_RUNTIME_BIN` to the `bin` directory of Lean 4.32.0. Python 3.11 or newer, Git and
a C toolchain are needed. Cold compilation is substantial; the local check
reuses existing build caches and is not a fresh-machine rebuild claim.

```sh
python3 scripts/setup_dependencies.py
./scripts/lake build Challenge Solution
./scripts/lake env lean AxiomAudit.lean
python3 scripts/audit.py
```

Dependencies are fetched at the immutable revisions in `dependencies.json`.
No dependency checkout, compiler, build cache, or multi-gigabyte proof export
is committed. To rebuild Comparator and its exporter:

```sh
(cd vendor/comparator && lake build comparator lean4export)
./scripts/check-comparator.sh --development comparator.json
```

On macOS, development mode has **no Linux Landrun isolation**. It still checks
formal statement/definition matching, permitted axioms, and official-kernel
replay. Genuine sandbox checking requires Linux and the upstream Comparator
Landrun/systemd setup. These security scopes must not be conflated.

`python3 scripts/verify.py --comparator --development` collects logs and exit
codes under a fresh `verification/runs/` directory. Omitting `--comparator`
does not perform the external kernel replay.

## Evidence and scope

The [completed certificate release](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/releases/tag/verified-20261005) contains the exact Challenge and Solution exports, verification evidence and SHA-256 checksums.
The [full 269-target upstream Comparator replay](verification/current/comparator-local/result.json) passed the official Lean kernel on October 5; its [complete log](verification/current/comparator-local/comparator.log) is preserved. The [independent con-ron run](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/runs/37300905046) then accepted all **1,027,308 declaration records** in verified mode, with exit status 0, after 2:30:01. These records represent 1,029,606 named declarations, including the complete dependencies of all 269 roots. Its [actual receipt and log](verification/current/con-ron-hosted) include the pinned unmodified checker, exact export identity, valid-proof acceptance and damaged-proof rejection.

Failed, timed-out and deliberately retired redundant checks remain separately
recorded in [STATUS.json](verification/STATUS.json). In particular, Nanoda and
eink0rn did not complete independent acceptance; they are not presented as passes.
See [the replay instructions](verification/KERNELS.md#replaying-published-exports-without-rebuilding-the-manuscript) to check the exports without recompiling the whole manuscript.

Read [verification/STATUS.json](verification/STATUS.json) for actual outcomes,
including unsuccessful or unfinished runs. Historical whole-257 Comparator
acceptance is preserved separately from current checks. An increment passing
is not described as a new whole-269 run.

The manuscript source is identified by SHA-256
`c65fcf8972bb53f49c34350cfd28975d757f67733d74ec7c3e9886eec0adcdc9`.
The statement snapshot records its exact 51 labelled results; 28 differ from
the earlier manuscript after whitespace normalization. To check a local copy:

```sh
python3 scripts/audit.py --paper /path/to/sharp_beckner_onofri_flat_torus.tex
```

The source delta review is an implementing-assistant review, **not independent
external semantic certification**. Comparator compares Lean with Lean; neither
it nor a second kernel decides whether natural-language mathematics was
encoded correctly. [EXTERNAL_REVIEW.md](EXTERNAL_REVIEW.md) supplies a review
packet with source/definition crosswalks and reviewer questions.

Independent-kernel instructions and version pins are in
[verification/KERNELS.md](verification/KERNELS.md). The Lean Kernel Arena is a
benchmark framework, not an automatic certificate for this project. No Arena
acceptance or website listing is claimed.
