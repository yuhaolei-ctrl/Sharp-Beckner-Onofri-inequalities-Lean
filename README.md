# Sharp Beckner–Onofri inequalities on the flat torus

A machine-checked Lean 4 formalization of the manuscript

> Yuhao Lei and Matthew Rosenzweig, *Sharp Beckner–Onofri inequalities on the flat torus:
> coefficients, defects, and phase transitions* (manuscript, version of 6 October 2026).

It determines the sharp coefficient and the optimal additive defect in the periodic
Beckner–Onofri inequality

$$\log\int_{\mathbb T^d} e^{u-\bar u}\,dm_d \;\le\; A\,\|u\|_{\dot H^{d/2}}^2 + C_d(A)$$

and in its dual, the periodic logarithmic Hardy–Littlewood–Sobolev inequality, on the unit
flat torus $\mathbb T^d=\mathbb R^d/\mathbb Z^d$. Under $A = 1/(2 c_d\beta)$ the defect
$C_d(A)$ is the pressure $P_d(\beta)$ of the attractive logarithmic gas.

| Dimension | Result | Lean (in `Challenge.lean`) |
|---|---|---|
| $1\le d\le 10$ | Sharp coefficient $A_c(d)=1/(4dc_d)$; $\beta_{gm}(d)=2d$; conformal equality family on the circle, constants only for $2\le d\le 10$ (Theorem 1.1) | `low_dim_*`, `circle_*_eq_iff` |
| $d = 11$ | First-order transition: $\mathrm{Ent}(\rho_*)<14.4088$, $\tfrac{(2\pi)^{11}}2\|\rho_*\|^2_{\dot H^{-11/2}}>14.4753$, $17.715<\beta_{gm}(11)<20.630<\beta_s(11)<22$, coexistence, corners of $P_{11}$ and $C_{11}$ (Theorem 1.2) | `eleven_*` |
| $d\ge 12$ | Sharp coefficient $A_s(d)=1/(2(2\pi)^d)$; $\beta_{gm}(d)=\beta_s(d)$; constants only; full $d$-mode onset branch and quadratic detachment of $P_d$ and $C_d$ (Theorem 1.3) | `high_dim_*`, `kappa_pos` |

- **28 declarations** state Theorems 1.1–1.3 in `Challenge.lean`, which imports only Mathlib.
- **No `sorry`** outside the intentional statement placeholders of `Challenge.lean`, and
  **no custom axiom**: every proof uses only `propext`, `Classical.choice` and `Quot.sound`.
- The numbered results of the manuscript have formal counterparts in
  `BecknerOnofri/PaperResults.lean`; [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps each of
  them to its Lean declarations and records every difference between printed and formal
  statements.
- Lean `v4.35.0-rc2`, Mathlib at the `v4.35.0-rc2` bump (pinned in `lake-manifest.json`).

## Repository map

| Path | Role |
|---|---|
| `Challenge.lean` | The statement surface: Mathlib-only definitions and the 28 theorems, each with `sorry` |
| `Solution.lean` | The same 28 statements, proved from the library |
| `comparator.json` | The Comparator configuration (all 28 declarations, standard axioms only) |
| `BecknerOnofri/Statement.lean` | The library's copy of the Challenge vocabulary (checked identical by `scripts/check_vocabulary.py`) |
| `BecknerOnofri/`, `Legacy/` | The proof development (`Legacy` is a historical namespace of the same development) |
| `BecknerOnofri/PaperResults.lean` | Formal counterparts of the numbered results of the manuscript (not on the Comparator path) |
| `CORRESPONDENCE.md` | Manuscript ↔ Lean map and the differences between printed and formal statements |
| `formalization.yaml` | Palomar metadata: provenance, scope, automation and review |

## Reading the statement

`Challenge.lean` restates every definition it uses, with a docstring giving its
mathematical meaning. The conventions are:

* $\mathbb T^d$ carries normalized Haar measure $m_d$ and
  $\hat f(k)=\int f e^{-2\pi i k\cdot x}\,dm_d$.
* `spectralEnergy ρ` $=\sum_{k\ne0}|k|^{-d}|\hat\rho(k)|^2=(2\pi)^d\|\rho\|^2_{\dot H^{-d/2}}$,
  and `spectralThreshold d` $=\beta_s(d)=(2\pi)^d/c_d=2\pi^{d/2}/\Gamma(d/2)$, so that
  $c_d\|\rho\|^2_{\dot H^{-d/2}}$ is `spectralEnergy ρ / spectralThreshold d`.
* `potentialEnergy u` $=\|u\|^2_{\dot H^{d/2}}=\sum_{k\ne0}(2\pi|k|)^d|\hat u(k)|^2$ and
  `InCriticalSobolev u` is $u\in H^{d/2}(\mathbb T^d)$.
* `pressure d β` and `coefficientDefect d A` are $P_d(\beta)$ and $C_d(A)$ with values in
  the extended reals; `VariationalCurves.globalTransition d` is
  $\beta_{gm}(d)=\sup\{\beta\ge0:P_d(\beta)=0\}$.
* Inequalities for arbitrary densities use `extendedEntropy`, which equals $\mathrm{Ent}(\rho)$
  for finite entropy and $+\infty$ otherwise; equality cases for densities assume finite
  entropy, as in the manuscript. Equalities of functions hold almost everywhere.
* The Euclidean profile of Theorem 1.2 is written with $C_{11}=122880/\pi^6$;
  `eleven_profile_constant` proves $C_{11}=\Gamma(11)/(\pi^{11/2}\Gamma(11/2))$.

## Computer-assisted steps

Every finite computation of the manuscript is checked by the Lean kernel through
`decide +kernel` on a Boolean checker with a proved soundness lemma; no `native_decide` and
no external computation is used. The main ones are:

* Propositions 3.1 and 4.6, $1\le n\le21$: the coefficients $p_q$, $q\le64$, of
  $(b+2\sum_j\binom{2n}{n+j}z^{j^2})^d$ are computed by truncated convolution and the
  remaining mass $4^{dn}-\sum_q p_q$ is charged the weight $65^{-d/2}$ ($3\le d\le11$).
* Lemma 5.13, $3\le n\le50$: the shell polynomial $(b+2\sum_j\binom{2n}{n+j}z^{j^2})^{12}$ is
  computed exactly below a truncation radius, and the remaining polynomial mass is charged
  the weight $Q^{-6}$; $n>50$ follows from the Gaussian bound with $J_{12}<3.29$.
* Lemma 5.17: the Bernstein-coefficient certificate for $\gamma\ge\psi$.
* Lemma 5.19: the 220 vertices of the curvature polytope and the corrector.
* Lemma 5.20: the Taylor-model certificate for $\mathcal B(t)>t^4/200$.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get          # Mathlib build cache
lake build Challenge Solution
```

On a machine with 16 GB of memory set `LEAN_NUM_THREADS=4` to limit the number of parallel
jobs.

Comparator checks that `Solution` proves exactly the statements of `Challenge` with the
permitted axioms, replaying the proofs through Lean's kernel and the toolchain's bundled
NanoDa and con-ron kernels (Linux, with `bubblewrap` installed):

```sh
./scripts/verify-comparator.sh
```

A full local Comparator run (Apple M-series, 10 cores) takes about 15 minutes. On the export
of all 28 theorems, con-ron needs about 3 GB with one worker and about 1.5 GB more per
additional worker (about 12 GB with 8 workers); NanoDa (4 threads) needs about 7 GB and
100 seconds.

`python3 scripts/check-lean-sources.py` checks the Palomar source requirements (every
Lean file uses the module system and has at most 10,000 lines), and
`python3 scripts/check_vocabulary.py` checks that the library's statement vocabulary is a
verbatim copy of the Challenge's.

## Scope

Formalized: Theorems 1.1, 1.2 and 1.3 in full on the Comparator surface, and the numbered
lemmas, propositions and corollaries in the library. Not formalized: the counterexample of
Remark 5.6 and the displayed cutoff rate in the proof of Lemma 2.9. Some proofs follow a
different, complete route; see [`CORRESPONDENCE.md`](CORRESPONDENCE.md).

The manuscript was written by its two authors; the Lean development was produced by AI
agents (OpenAI Codex, Claude Code) under the direction of Yuhao Lei. An agent-assisted
statement audit has been carried out; no independent human review has been completed.

## Palomar

This repository is prepared for the [Palomar registry](https://palomar-registry.org/).
Submissions go through the [submission form](https://submit.palomar-registry.org/) with a
full commit SHA and the path `comparator.json`.

## License

Apache 2.0; see [`LICENSE`](LICENSE). The manuscript itself is not part of this repository.
