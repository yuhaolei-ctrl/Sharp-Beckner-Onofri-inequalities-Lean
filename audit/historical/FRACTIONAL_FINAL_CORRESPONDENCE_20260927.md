# September 21 Lemma fractional: statement and proof audit

Source: `beckner_onofri_full_manuscript_20260921T180354Z/sharp_beckner_onofri_flat_torus.tex`, lines1245–1382. The companion PDF is the user-selected September21 manuscript.

The source-facing declaration is `BecknerOnofri.Target.fractional_intertwining`, whose trusted proposition is `Friedrichs.MixedSpatial.FractionalIntertwining d` in `MixedFractionalStatementDefinitions.lean`. It quantifies over every real profile U that is `ContDiffOn ℝ ∞` on the closed cosine cube, every nonzero natural multi-index and every real s>0. No Fourier decay, global extension, operator-domain membership, symmetry of a selected optimizer or positivity premise is imposed.

## Exact meaning of the statement

- `cosineLift U` is the prescribed U(cos θ), with unit-circle coordinates x and angular coordinates θ=2πx. `angularPower s` has the explicitly asserted Fourier multiplier |k|^(2s), with no spurious factor (2π)^(2s).
- The conclusion constructs a closed-cube smooth profile Us representing this very P^s u. Thus its derivative is not an unrelated existential function.
- `derivativeList α` repeats each coordinate α_i times; `derivativeList_count` proves the exact count. `SmoothEulerStatement.mixedPartial` uses actual iterated within-Frechet coordinate derivatives on the closed cube. The canonical order is a representation of the ordinary smooth multi-index derivative.
- `coordinateMeasure` is unscaled Lebesgue on (0,π) for α_i>0 and on the full fundamental interval (0,2π] for α_i=0. The latter carries periodic core profiles and all sine and cosine modes; it is not a Neumann half-interval restriction. Original coordinate labels are retained by the finite product measure.
- `operatorGraph` is independently defined from the literal closure of the spatial quadratic-form core, with actual derivatives and multiplication by sqrt(α_i(α_i−1))/sin θ_i. The square of this multiplier is the source potential. `mixed_spatial_form_closability` proves uniqueness of the derivative/potential components in the closure.
- `mixed_spatial_spectral_identification` proves both directions of equality between this actual graph and the full mixed-basis multiplier. `mixed_spatial_selfadjoint` proves equality with the adjoint graph. Both allow zero coordinates of α.
- `SpectralPowerGraph` applies the real power of these eigenvalues on this complete orthonormal basis. `spectralPowerGraph_one` identifies its first power with the actual spatial graph; `spectralPowerGraph_domain` proves exactly the weighted-l2 domain, and uniqueness/closedness are proved. Existence of f,g in this graph therefore states domain membership and the desired image equality, not a conditional assertion about an assumed domain.
- The two actual L2 representatives f,g are asserted almost everywhere equal to wα∂αU and wα∂αUs, respectively. This is the correct equality notion for the source unbounded L2 operator.

## Proof correspondence

| Source step | Lean proof |
|---|---|
| Differentiated Chebyshev/Jacobi identity and sin-power conjugation | Existing Jacobi polynomial/conjugation modules; `MixedChebyshevEigenvectors` |
| Smooth cutoffs at each active boundary face | `MixedProfileFormDomain`, actual product cutoffs and form-norm convergence |
| Integration by parts followed by form-test density | `PeriodicWeakEquation`, `MixedProfileOperator`, `MixedClosedFormTests` |
| Actual eigenvectors of the Friedrichs realization | `MixedFullEigenvectors`, `MixedCoordinateNormalization`, `MixedSpatialSpectrum` |
| Spectral calculus | Full periodic Parseval and cosine/sine basis, Jacobi coordinate basis, `ProductL2Totality`, `MixedTensorBasis`, `MixedSpectralPowers` |
| Rapid cosine coefficients from smoothness | `SmoothTorusFourierDecay`, `SmoothCosinePower` |
| Polynomial derivative bounds and summable graph-norm series | Existing differentiated-Chebyshev bounds, `MixedAngularSeries`, `MixedAngularPowers` |
| Closedness of the fractional power | `spectralPowerGraph_hasSum` and `MixedAngularPowers.positive_intertwining` |
| Original arbitrary smooth U, all multi-indices | `MixedFractionalIntertwining`, `MixedDerivativeList`, `MixedFractionalPaper` |

The core source route is preserved. Two implementation details differ: cutoff convergence is proved by dominated convergence rather than exporting the displayed O(δ^(2m−1)) numerical rate; the smooth cosine series is indexed by integer Fourier frequencies rather than first merging equal absolute frequencies into a natural-index series. Absolute convergence proves the same sum and limit. Affine transport from [0,1]^d to [-1,1]^d introduces 2^|α|, which is explicitly cancelled in `scaled_vector_ae`.

The formal proof also supplies the full inactive odd spectral sectors to justify the whole mixed Friedrichs realization, even though the particular cosine inputs lie in its even sector. This fills in the spectral-calculus justification; it is not an additional hypothesis.

## Verification

The final auxiliary theorem `MixedSpatial.fractional_intertwining` compiled successfully: `verification/friedrichs_mixed_fractional_paper_build.log` (4183 jobs). Printed axiom dependencies are exactly `propext`, `Classical.choice`, `Quot.sound`. Current root-target build, exact axiom audit and Comparator results are recorded separately in `verification/active_checkpoint.json`; this note does not substitute an auxiliary build for full validation.

Root257 build and exact257 axiom audit passed. The final255–257 Comparator increment passed with default Lean kernel replay, exit0: `verification/comparator_fractional_increment.log`. The current whole257 Comparator also passed with default Lean kernel replay, exit0: `verification/comparator_full_manuscript_257.log`.
