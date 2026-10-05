# Dimension-independent analytic reuse

This tree contains a dependency closure of an earlier actual Lean formalization. Project module and namespace roots have been changed from `BecknerOnofri`, `TorusEndpoint`, and `D10` to `Legacy.BecknerOnofri`, `Legacy.TorusEndpoint`, and `Legacy.D10`. Mathlib modules are unchanged. `SOURCE_PROVENANCE.json` records the original path and SHA-256 of each copied file.

The analytical modification is confined to the heat-Green majorant and propagated hypotheses:

1. `ThetaDecayAllDimensions.lean` proves, for every natural dimension `d`, a theta-tail bound with the finite constant
   `C_d = (sum i < d, theta(pi)^i) * exp(pi) * (theta(pi) - 1)`.
2. `GreenHeatBounds.lean` uses `C_d` in its small-time image bound, replacing the old dimension-ten constant.
3. `GreenHeatPointwise.lean` uses the same `C_d` in the image integral. The logarithmic singularity coefficient remains exactly one; the additive regular constant may depend on `d`.
4. `GreenHeatIntegrability.lean` and `GreenExponentialIntegrability.lean` carry these bounds to the actual Fourier Green kernel in every positive dimension.
5. `SubcriticalRoughBound.lean` obtains the actual rough exponential inequality from proved density pairing and truncated Gibbs variational bounds, with no assumed endpoint or optimizer.
6. The dimension-upper-bound parameters in `SubcriticalCounterexample`, `SubcriticalPrimalDual`, `SubcriticalDensityCompactness`, `PolarizationSelection`, and `SteinerSelection` only propagated that rough-bound restriction. Those parameters and their corresponding call arguments have been removed.

The remaining copied low-dimensional statements are retained as originally proved. They are not promoted to general-dimensional endpoint theorems. In particular the imported file named `Endpoint.lean` provides definitions and the previously proved dimension-one case; no full high-dimensional endpoint result is assumed by the generic chain.

`BecknerOnofri/GenericAttainment.lean` exposes the resulting integrability, logarithmic bound, attainment, and Steiner-selection theorems on the actual Fourier Sobolev objects. A separate bridge module connects those objects to the current challenge's raw function definitions.

An import-only cleanup replaces the former `LatticePolynomialBridge` dependency with `SobolevLatticeBoxes`, a direct finite product of integer intervals. The compactness argument uses only its proved coordinate membership criterion. Eight unused finite-polynomial modules were omitted; their original source identities remain available in the original package. This avoids rebuilding unrelated low-dimensional numeric tables.


The generic cosine-representation extension adds the actual Euler profile,
Jacobi polynomial/heat/Mellin operator, weighted strict comparison, and
Bernstein/Taylor dependency closure. Those analytic theorems already quantify
over arbitrary finite dimension. The only import change is in
`EulerUnitProfiles.lean`: the unnecessary `LowDimensionMixtureEndpoint` import
is replaced by `PositiveCosineRepresentation` and
`BernsteinPositiveCoefficients`, which are the actual definitions used there.
The dimension-one-through-ten endpoint and its finite scalar tables are not
imported by this extension. `BecknerOnofri/GenericCosineRepresentation.lean`
assembles mixed-partial positivity and the normalized countable mixture from
these proved inputs together with the generalized rough estimate and selection.
