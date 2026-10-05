# Sharp Beckner–Onofri inequalities — Palomar adaptation

Authors and maintainers: Yuhao Lei and Matthew Rosenzweig. Apache-2.0.

This branch migrates the existing proof development to **Lean 4.35.0-rc2**
and its matching pinned Mathlib revision. It is a work in progress, not a
Palomar registration or a verified replacement for the original certificate.
Current results are recorded in [verification/STATUS.json](verification/STATUS.json).

## Candidate entries

Each entry has a self-contained mathematical Challenge importing only Mathlib.
Its Solution imports the proof development, never the Challenge.

| Subject | Comparator configuration | Claims |
| --- | --- | ---: |
| Dimensions 1–10: sharp inequalities, equality and thresholds | `Palomar/comparator-lowdim.json` | 9 |
| Dimensions at least 12: sharp inequalities and full-mode onset | `Palomar/comparator-highdim.json` | 10 |
| Dimension 11: explicit competitor and first-order transition | `Palomar/comparator-eleven.json` | 11 |

Select exactly one configuration when submitting an entry. The root
`comparator.json` retains the original 269-target development; it is not a
Palomar submission configuration. The original 51-result development remains
in the repository. These first three candidate entries advertise its principal
theorems, not every supporting lemma. `statements.json` records the larger
manuscript mapping; `formalization.yaml` discloses scope and known differences.

For Haar probability measure on the unit flat torus, the density statements
compare entropy with the extended Fourier energy
`sum (|k|^(-d) * |rho_hat(k)|^2)` over nonzero integer frequencies. For
dimensions 1–10 the coefficient is `d / sigma_d`, where
`sigma_d = 2 * pi^(d/2) / Gamma(d/2)`; for dimensions at least 12 it is `1/2`.
The corresponding potential inequalities and sharp coefficients are included.
Equality is classified by the conformal family in dimension one and by constants
in the other dimensions covered by these two entries. The high-dimensional
entry also describes the full-mode branch, its translation orbit and Sobolev
profile, and the quadratic pressure onset. The dimension-eleven entry places
the global transition strictly between `3543/200` and `2063/100`, below the
spectral threshold, and states coexistence and nondifferentiability of the
pressure and defect. Each configuration names the precise formal claims it
advertises; compilation of the migrated proofs is still in progress.

## Build

Install the toolchain in `lean-toolchain`, or set `LEAN_RUNTIME_BIN` to that
toolchain's `bin` directory. Git dependencies are fixed by `lake-manifest.json`.

```sh
./scripts/lake exe cache get
python3 scripts/audit_palomar.py
./scripts/lake build Palomar.LowDimChallenge Palomar.HighDimChallenge Palomar.ElevenChallenge
./scripts/lake build Palomar.LowDimSolution Palomar.HighDimSolution Palomar.ElevenSolution
```

Statement placeholders are intentional. A successful Challenge build alone is
not proof verification. The migrated Solutions must build and pass Comparator
and independent kernel replay before this branch can be called verified.
The GitHub structural-preflight job checks layout and metadata only.
See [verification instructions](verification/README.md) for the full checks.

## Provenance

The mathematical source is *Sharp Beckner–Onofri inequalities on the flat
torus: coefficients, defects, and phase transitions*, by Yuhao Lei and
Matthew Rosenzweig, manuscript dated 1 October 2026.

The [original certificate release](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/releases/tag/verified-20261005)
records checks of the pre-migration Lean 4.32.0 source. Those results do not
certify this branch. The module-system migration keeps the existing internal
mathematical declaration names. Dependencies retain their own licences.
