# Sharp Beckner–Onofri inequalities

Lean formalization of 51 formal results, with 269 registered proof targets.
Requires **Lean 4.32.0** and the pinned dependencies in
[dependencies.json](dependencies.json).

## Build

```sh
python3 scripts/setup_dependencies.py
./scripts/lake build Challenge Solution
./scripts/lake env lean AxiomAudit.lean
python3 scripts/audit.py
```

Install the toolchain in `lean-toolchain`, or set `LEAN_RUNTIME_BIN` to its
`bin` directory. Dependency setup requires Git, Python 3.11 or newer, and
network access. Building requires the Lean toolchain and a C toolchain.

## Proof structure

- `Challenge.lean`: the statements to prove.
- `Solution.lean`: the complete proof entrypoint.
- `BecknerOnofri/`, `Legacy/`, and the root proof modules: definitions and proofs.
- `comparator.json`: all 269 targets and their permitted axioms.
- [statements.json](statements.json): manuscript labels mapped to Lean targets.

Challenge statements use `sorry` as placeholders. Solutions do not import
Challenge, and their transitive axioms are restricted to `Classical.choice`,
`Quot.sound`, and `propext`. Dimensions 1–10 use the same verification workflow;
`Legacy/` contains checked proofs, including finite certificates evaluated with
`decide +kernel`.

## Verify

```sh
python3 scripts/verify.py
```

This checks source integrity, builds both entrypoints and audits all target
axioms. To run the full Comparator after building its pinned tools:

```sh
(cd vendor/comparator && lake build comparator lean4export)
python3 scripts/verify.py --comparator --development
```

Development mode checks statements, definitions, axioms and the official
kernel, but does not provide Linux sandbox isolation. Generated logs are
written to the ignored `verification/runs/` directory.

The [published certificate](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/releases/tag/verified-20261005)
passed complete official Comparator replay and an independent
[con-ron verified replay](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/runs/37300905046).
These results concern the frozen exported certificate. The unified source
layout has a separate build and an exact source-correspondence check.
See [verification instructions](verification/README.md) and
[check status](verification/STATUS.json).

## Scope

The 51-result scope excludes the counterexample in Remark 5.6 and a separate
proof of the displayed cutoff-rate estimate; the latter is replaced by proved
form-norm convergence. Independent review of the correspondence between the
manuscript and the Lean statements remains outstanding. No Kernel Arena
listing or acceptance is claimed.
