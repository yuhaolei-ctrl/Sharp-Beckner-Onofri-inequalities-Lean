# Sharp Beckner–Onofri inequalities on the flat torus

[![CI](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/yuhaolei-ctrl/Sharp-Beckner-Onofri-inequalities-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of

> Yuhao Lei and Matthew Rosenzweig, *Sharp Beckner–Onofri inequalities on the flat torus:
> coefficients, defects, and phase transitions* (manuscript, 6 October 2026).

The paper finds the sharp coefficient $A$ and the optimal defect $C_d(A)$ in the periodic
Beckner–Onofri inequality on the unit torus $\mathbb{T}^d$,

$$
\log \int_{\mathbb{T}^d} e^{u-\bar u}\, dm \le A\, \lVert u \rVert_{\dot H^{d/2}}^2 + C_d(A),
$$

and in its dual, the periodic logarithmic Hardy–Littlewood–Sobolev inequality.

## Main results

- **Theorem 1.1** ($1 \le d \le 10$): the sharp coefficient is fixed by concentration,
  and the equality cases are the conformal family on the circle and constants for
  $2 \le d \le 10$.
- **Theorem 1.2** ($d = 11$): a first-order phase transition occurs before spectral
  instability, with explicit bounds $17.715 < \beta_{\mathrm{gm}}(11) < 20.630$.
- **Theorem 1.3** ($d \ge 12$): the sharp coefficient is fixed by the first Fourier shell,
  only constants attain equality, and the onset branch is described explicitly.

All three theorems are stated in [`Challenge.lean`](Challenge.lean) as 28 Lean
declarations, using only Mathlib definitions, and proved in [`Solution.lean`](Solution.lean).
The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Verify it yourself

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get              # download prebuilt Mathlib
lake build Challenge Solution   # build the statements and the proofs
./scripts/verify-comparator.sh  # Linux, needs bubblewrap
```

The last command runs [Comparator](https://github.com/leanprover/comparator). It checks
that `Solution` proves exactly the statements of `Challenge` and replays every proof in
three independent kernels: Lean's own kernel, NanoDa and con-ron. A full run takes about
15 minutes on a 10-core machine. On a 16 GB machine, set `LEAN_NUM_THREADS=4` for the build.

`./scripts/extra-kernels.sh` replays the same proofs in two more kernels, con-leche
(from which con-ron was ported) and Lean4Lean. All five kernels are rated sound and complete by the
[Lean Kernel Arena](https://arena.lean-lang.org/). Each accepted all of the roughly 71,300 exported
declarations (Lean v4.35.0-rc2 toolchain, 7 October 2026):

| Kernel | Run by | Time | Memory |
|---|---|---|---|
| Lean (official) | Comparator | part of the 15-minute run | under 7 GB |
| NanoDa | Comparator | 2 min | 7 GB |
| con-ron | Comparator | 9 min with 1 worker | 3 GB with 1 worker |
| con-leche | `extra-kernels.sh` | 5 min with 6 workers | 6.5 GB |
| Lean4Lean | `extra-kernels.sh` | 11 min | 2 GB |

## Repository layout

| Path | Contents |
|---|---|
| `Challenge.lean` | The 28 theorem statements, with Mathlib-only definitions |
| `Solution.lean` | The same statements, proved from the library |
| `BecknerOnofri/`, `Legacy/` | The proof development |
| `BecknerOnofri/PaperResults.lean` | Lean counterparts of the numbered results of the paper |
| `CORRESPONDENCE.md` | Paper-to-Lean map and every difference between printed and formal statements |
| `comparator.json`, `formalization.yaml` | Configuration for Comparator and the Palomar registry |

## Computer-assisted steps

The finite computations of the paper (lattice sums in Propositions 3.1 and 4.6 and
Lemma 5.13, and the certificates in Lemmas 5.17, 5.19 and 5.20) are evaluated by the Lean
kernel with `decide +kernel`. Each checker has a proved soundness lemma. No
`native_decide` or external computation is used.

## Contributing

Issues and pull requests are welcome, especially simplifications of proofs and moves of
general lemmas toward Mathlib. Run `python3 scripts/check-lean-sources.py` and
`python3 scripts/check_vocabulary.py` before opening a pull request.

The paper was written by its two authors. The Lean code was written by AI agents
(OpenAI Codex, Claude Code) under the direction of Yuhao Lei. It has not yet been reviewed
independently by a human.

## License

Apache 2.0; see [`LICENSE`](LICENSE). The paper itself is not part of this repository.
