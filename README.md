# Sharp Beckner–Onofri inequalities: Lean certificate

Lean **4.32.0**, mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`.

This repository preserves the 257-target September 27 certificate and adds a
separate adaptation layer for the October 3 manuscript (“paper 2”).
The adaptation now includes the literal physical-coordinate Friedrichs
intertwining and local uniform convergence of every derivative of the original
periodization series. The 51 formal result environments are the declared
coverage scope; proof-route estimates and remarks outside that set are listed
separately. Final checker outcomes are recorded in [STATUS.json](verification/STATUS.json).
See [the Chinese audit](AUDIT_ZH.md) and [the 51-result statement map](audit/PAPER2_STATEMENT_MAP.md).

## Challenge → Solution → Comparator

| Scope | Trusted statements | Proofs | Configuration |
|---|---|---|---|
| Original 257 targets | `Challenge.lean` | `Solution.lean` and imported modules | `comparator.json` |
| Original targets plus 12 paper-2 targets | `Paper2Challenge.lean` | `Paper2Solution.lean`, `Paper2Proofs.lean` | `comparator-paper2.json` |
| Only the 12 additions | same | same | `comparator-paper2-increment.json` |
| Seven new analysis/coordinate targets | same | same | `comparator-paper2-analysis.json` |

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
`LEAN_RUNTIME_BIN` to the `bin` directory of Lean 4.32.0. Python 3, Git and
a C toolchain are needed. Cold compilation is substantial; the local check
reuses existing build caches and is not a fresh-machine rebuild claim.

```sh
python3 scripts/setup_dependencies.py
./scripts/lake build Paper2Challenge Paper2Solution
./scripts/lake env lean AxiomAuditPaper2.lean
python3 scripts/audit.py
```

Dependencies are fetched at the immutable revisions in `dependencies.json`.
No dependency checkout, compiler, build cache, or multi-gigabyte proof export
is committed. To rebuild Comparator and its exporter:

```sh
(cd vendor/comparator && lake build comparator lean4export)
./scripts/check-comparator.sh --development comparator-paper2.json
```

On macOS, development mode has **no Linux Landrun isolation**. It still checks
formal statement/definition matching, permitted axioms, and official-kernel
replay. Genuine sandbox checking requires Linux and the upstream Comparator
Landrun/systemd setup. These security scopes must not be conflated.

`python3 scripts/verify.py --comparator --development` collects logs and exit
codes under a fresh `verification/runs/` directory. Omitting `--comparator`
does not perform the external kernel replay.

## Evidence and scope

The [downloadable certificate](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/releases/tag/certificate-20261005-d561980) contains the exact Challenge and Solution exports with SHA-256 provenance.
The public [Nanoda run](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/runs/37266167712) and [Comparator replay](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/runs/37267009000) provide machine logs. Their final outcomes must be read from the runs and status record.
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
