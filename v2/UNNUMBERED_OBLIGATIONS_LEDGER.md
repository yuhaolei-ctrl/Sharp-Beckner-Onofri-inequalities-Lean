# Unnumbered obligations ledger (U01-U24)

Generated 2026-10-10 01:01 UTC by the v2 ledger worker (G16 part 1). Source checklist: `catalogue/UNNUMBERED_OBLIGATIONS.md` of the handoff. Every entry below corresponds to the row of the same id in `IMPLEMENTATION_STATUS.csv`, where the full evidence and the resolved declaration names are kept.

Reading guide: statement and route use the four independent audit columns (statement, proof route, compilation, axioms). An alternative proof route is always recorded as route-difference. Nothing here was checked by running lean, lake or `#print axioms` in this pass; compilation is read from olean timestamps and axioms from preserved logs and worker notes (see COVERAGE_SUMMARY.md, section 8).

## Status table

| id | catalogue title | owner | statement | proof route | compilation | axioms |
|---|---|---|---|---|---|---|
| U01 | Homogeneous entropy, zero mass, normalization, extended values | G01 | matches | route-difference | compiled | standard-3-axioms |
| U02 | Fourier and coupling normalization | G01 | matches | route-difference | compiled | standard-3-axioms |
| U03 | Critical exponential moments and Gibbs integrability | G02 | conditional | route-difference | compiled | standard-3-axioms |
| U04 | Density coordinate rearrangement, smoothness recovery, entropy preservation | G02 | matches-with-difference | partial | compiled | standard-3-axioms |
| U05 | Heat resolvent positivity and the induction for mixed derivatives | G03 | matches | route-difference | compiled | standard-3-axioms |
| U06 | Mixture expectation identities and strictness | G04 | matches-with-difference | route-difference | compiled | standard-3-axioms |
| U07 | Early non-strict d11 lower bound and later strictness | G05 | matches | route-difference | compiled | standard-3-axioms |
| U08 | Cube energy and spin-count moments | G06 | matches | written-route | compiled | standard-3-axioms |
| U09 | Twelve-square theta identity and analytic derivation | G07 | conditional | route-difference | compiled | standard-3-axioms |
| U10 | Gaussian/Mellin estimates and scalar Bernstein comparison | G07 | matches | written-route | compiled | standard-3-axioms |
| U11 | C3 extension of the Poisson remainder | G08 | matches | written-route | compiled | standard-3-axioms |
| U12 | Rational lower bounds for circle weights | G09 | matches | written-route | compiled | standard-3-axioms |
| U13 | Scalar circle positivity and degree-seventeen polynomial | G09 | matches | written-route | compiled | standard-3-axioms |
| U14 | Continuity and convexity of the explicit correction | G09 | matches | written-route | compiled | standard-3-axioms |
| U15 | Boundary conditional densities and spin disintegration | G10 | matches-with-difference | route-difference | compiled | standard-3-axioms |
| U16 | Affine feature residuals and rational bounds | G11 | matches | written-route | compiled | standard-3-axioms |
| U17 | Finite Gibbs formula and one-sided exponential remainder | G11 | matches | route-difference | compiled | standard-3-axioms |
| U18 | Positive reference variance and centered regression identities | G12 | matches | written-route | compiled | standard-3-axioms |
| U19 | Rational extension and origin jets | G12 | matches-with-difference | route-difference | compiled | standard-3-axioms |
| U20 | Interval arithmetic and expression interpreter soundness | G13 | matches | route-difference | compiled | standard-3-axioms |
| U21 | Cell coverage and integration from zero | G13 | matches | route-difference | compiled | standard-3-axioms |
| U22 | Large means including the endpoint point mass | G14 | matches | route-difference | compiled | standard-3-axioms |
| U23 | All branches, Sobolev compactness, and pressure derivatives | G15 | conditional | partial | compiled | standard-3-axioms |
| U24 | Prior cited results and all implicit assumptions | G16 | conditional | partial | compiled | standard-3-axioms |

## Entries

### U01. Homogeneous entropy, zero mass, normalization, extended values

- Owner: G01. Source locator: `eq:section2-relative-entropy`.
- Catalogue obligation: Prove the new domain-correct extension and bridge it to old real/EReal density entropies; preserve singular-measure infinity separately.
- Statement alignment: matches (homogeneous extension: zero mass gives 0, mass 1 reduces to the ordinary density entropy, extended value in EReal/ENNReal; bridges to the old real/EReal entropies; singular measures keep value top, measureEntropy_of_not_ac and measureEntropy_torus_not_ac)
- Proof-route alignment: route-difference (V2.Vocab.homEntropy is defined through the pointwise nonnegative integrand r log(r/m) - r + m with a bridge to the integral of f log f - m log m; the written Jensen argument is not used)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Vocab.homEntropy`, `V2.Vocab.homEntropy_of_mass_zero`, `V2.Vocab.homEntropy_of_mass_ne_zero`, `V2.Vocab.homEntropy_of_mass_one`, `V2.Vocab.homEntropy_congr_ae`, `V2.Vocab.homEntropy_const_mul`, `V2.Vocab.measureEntropy`, `V2.Vocab.measureEntropy_of_not_ac`, `V2.Vocab.measureEntropy_withDensity`, `V2.Vocab.measureEntropy_eq_klDiv`, `V2.Vocab.measureEntropy_density_eq`, `V2.Vocab.measureEntropy_density_eq_top_iff`, `V2.Vocab.measureEntropy_torus_not_ac`
- Open gap: Written-route proof not formalized: the Jensen-based computation of the homogeneous entropy.
- Evidence: Source: Vocab/SECTION2_RESOLUTION.md (eq:section2-relative-entropy row); name resolution against the repository index.

### U02. Fourier and coupling normalization

- Owner: G01. Source locator: `eq:intro-dual-energy-def`.
- Catalogue obligation: Prove the exact c_d, beta_s, spectralEnergy, and potential-energy conversion identities.
- Statement alignment: matches (c_d, beta_s and the spectral-energy / negative-Sobolev-energy / potential-energy conversions are stated as exact identities; A -> beta = (2 A c_d)^-1 bridge in coefficient_pressure_duality)
- Proof-route alignment: route-difference (the algebraic normalizations are direct; the physical Green double-integral identity is delivered by the legacy physicalGreen_eq_spectral (rough-bound summability), not by Parseval and Lemma 2.1)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Vocab.kernelConstant`, `V2.Vocab.kernelConstant_pos`, `V2.Vocab.kernelConstant_mul_spectralThreshold`, `V2.Vocab.kernelConstant_mul_negSobolevEnergy`, `V2.Vocab.kernelConstant_mul_negSobolevEnergy_toReal`, `V2.Vocab.green_interaction_eq_kernelConstant_mul`, `V2.Vocab.interaction_eq_kernelConstant_mul`, `V2.Vocab.spectralEnergy_eq_mul_negSobolevEnergy`, `V2.Vocab.coefficient_pressure_duality`, `V2.Vocab.gapCoefficient_eq`
- Open gap: Written-route proof not formalized: the Parseval / Lemma 2.1 derivation of the physical-space identity.
- Evidence: Source: Vocab/SECTION2_RESOLUTION.md (eq:intro-dual-energy-def and Prop 2.2 rows).

### U03. Critical exponential moments and Gibbs integrability

- Owner: G02. Source locator: `eq:section2-all-exponential-moments`.
- Catalogue obligation: Cover the finite weighted integrals used by duality; no totalized divergent Bochner integral.
- Statement alignment: conditional (eq:section2-all-exponential-moments has no declaration of its own: it is a corollary of the critical Adams bound via e^{p|u|} <= e^{pu} + e^{-pu}; the v2 clean form of the critical Adams input is only the named Prop CriticalAdamsInput, which no declaration consumes; the available theorem HD.critical_adams_bound is unconditional but sits on the old endpoint chain; Gibbs densities have finite partition function under the rough-exponential bound of GenericAttainment)
- Proof-route alignment: route-difference (Gibbs integrability is obtained by replaying the first half of Gap.primal_gap and the rough exponential bound of the legacy GenericAttainment instead of the written exponential-moment corollary; the critical exponential moment goes through legacy AdamsEndpoint.critical_entropy_energy -> circle_heatInteraction_entropy -> physical_green_endpoint -> endpoint_through_ten rather than a d = 1 Lebedev-Milin proof)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Vocab.CriticalAdamsInput`, `V2.Vocab.criticalAdamsInput_iff`, `V2.Vocab.exists_gibbs_density`, `V2.Vocab.partition_pos`, `V2.Vocab.normalizedGibbsDensity`, `V2.Vocab.normalizedGibbsDensity_finiteEntropy`, `HighDim.critical_adams_bound`
- Open gap: Replace circle_heatInteraction_entropy by a d = 1 proof independent of endpoint_through_ten, or consume CriticalAdamsInput as a hypothesis; state eq:section2-all-exponential-moments as a declaration if it is required downstream.
- Evidence: Sources: Vocab/SECTION2_RESOLUTION.md (row eq:section2-all-exponential-moments 'not located as a single declaration', sections C, E4, F.2). HD.critical_adams_bound reaches the endpoint-tainted legacy chain (LowDimensionPhysicalEndpoint, endpoint_through_ten, LowDimensionMixtureEndpoint).

### U04. Density coordinate rearrangement, smoothness recovery, entropy preservation

- Owner: G02. Source locator: `lem:coordinate-rearrangement`.
- Catalogue obligation: Track the canonical rearranged density, not just existence of an equimeasurable optimizer.
- Statement alignment: matches-with-difference (the canonical rearranged density is tracked, but through MeasSuccessive (measure-level successive Steiner chain, O1) rather than the repository's AESuccessiveSteiner (a.e. version); marginals are taken on the ambient torus)
- Proof-route alignment: partial (existence of the rearranged chain and entropy / energy preservation are proved along the written route; smoothness recovery is delivered through the MeasSuccessive formulation, and the module docstring of Rearrangement/Comparison.lean refers to a declaration coordinate_minimizer_gap that does not exist)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Rearrangement.coordinate_rearranged_minimizer`, `V2.Rearrangement.exists_meas_chain`
- Open gap: Reconcile the dangling coordinate_minimizer_gap docstring reference; confirm that MeasSuccessive implies the statement used by Section3 (O1).
- Evidence: Source: Rearrangement package notes and worker report; name resolution. Rearrangement/Comparison.lean has an olean older than its source (stale by mtime only; downstream Rearrangement oleans were rebuilt afterwards).

### U05. Heat resolvent positivity and the induction for mixed derivatives

- Owner: G03. Source locator: `prop:cosine-all`.
- Catalogue obligation: P011 is assigned manually; cover the nonscalar fractional operator and positivity of the comparison kernel.
- Statement alignment: matches (heat kernel on the torus is the product of circle heat kernels; positivity, evenness, continuity and radial monotonicity of the comparison kernel; cosine representation of the mixed derivatives from the legacy GeneralEulerBridge)
- Proof-route alignment: route-difference (same as S015: the induction for mixed derivatives and the nonscalar fractional operator use the Chebyshev profile, the Jacobi-tensor Mellin kernel with Schur normalization and tensor Bernstein polynomials; the listed circleHeat_* declarations belong to S012 and are not on the cosine_representation path)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Rearrangement.circleHeat_eq_tsum`, `V2.Rearrangement.circleHeat_pos`, `V2.Rearrangement.circleHeat_nonneg`, `V2.Rearrangement.circleHeat_even`, `V2.Rearrangement.circleHeat_continuous`, `V2.Rearrangement.circleHeat_radial_antitone`, `V2.Rearrangement.heatKernel_eq_prod_circleHeat`, `HighDim.GeneralEulerBridge.cosine_representation`
- Open gap: Written-route proof not formalized: see S015.
- Evidence: Source: Rearrangement package; name resolution only. prop:cosine-all itself is S-row territory (G03).

### U06. Mixture expectation identities and strictness

- Owner: G04. Source locator: `eq:mixture-strict-entropy-gap`.
- Catalogue obligation: Handle countable correlated mixture laws, conditional independence, Tonelli, and positive probability of an active hypergeometric coordinate.
- Statement alignment: matches-with-difference (positivity of the strict entropy gap is proved; the displayed quantitative form 3/(2200 d) * sum P(L_i >= 1) of eq:mixture-strict-entropy-gap is not what the legacy countable_mixture_gap supplies: it gives w_a^2 * latentWeight * gap(d) / 2 for a component a with N a != 0, with the repository's gap d; only positivity is used downstream)
- Proof-route alignment: route-difference (strictness is taken from the legacy countable_mixture_gap / ElevenMixture.finite_mixture_gap chain instead of the written Tonelli computation over correlated latent mixture laws; the V2.Mixture tail-average identities are written-route)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Section3.finite_mixture_gap`, `V2.Section3.mixture_energy_gap`, `V2.Section3.posMass`, `V2.Section3.posMass_lower`, `V2.Section3.mixtureStrictness_written`, `V2.Section3.mixtureInequality_written`, `V2.Section3.MixtureStrictness`, `V2.Mixture.finite_mixture_singular_tail`, `V2.Mixture.countable_mixture_singular_tail`, `V2.Mixture.latentAverage_tsum`, `Legacy.ElevenMixture.finite_mixture_gap`
- Open gap: The (3/(2200 d)) * sum P(L_i >= 1) form is not formalized; module-level taint through LowDimensionMixtureEndpoint remains.
- Evidence: Sources: Section3/RESOLUTION.md (Strict gap row, catalogue item U06). Section 3 taint: declaration-level free of forbidden endpoint modules (Section3 trace2/trace4: 0 forbidden-module hits), but the module-level import closure still reaches Legacy LowDimensionMixtureEndpoint via MixtureEnergyStatementBridge -> EntropyShearer.PaperStatement -> ... -> FiniteEntropyPhysical -> Legacy.FiniteEnergyGreenIdentification -> ... -> StrictCountableMixture -> LowDimensionMixtureEndpoint (Section3/RESOLUTION.md)

### U07. Early non-strict d11 lower bound and later strictness

- Owner: G05. Source locator: `d11:thm:interval`.
- Catalogue obligation: Audit the surrounding proof order; front-loaded printed location is not a premise.
- Statement alignment: matches (non-strict early lower bound beta0 <= globalTransition = transition_lower is stated and used only as non-strict; the strict inequality is a later consequence, strict_lower_of_coexistence, with beta0 = 3543/200)
- Proof-route alignment: route-difference (the early non-strict bound is conditional on the named Prop SmoothMixtureGap11, discharged by the legacy ElevenMixture chain (countable_mixture_gap); manuscript order is kept in Eleven/Assembly.lean, but strict_lower_of_coexistence reaches the old HighDim.Eleven.coexistence). Eleven coexistence taint: this item reaches the old HighDim.Eleven chain (coexistence / local_unique_convolution, module ElevenCoexistence, plus HighDim.Eleven.transition_pos) in place of the written Sobolev-IFT / compactness proofs; route difference
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Eleven.beta0`, `V2.Eleven.beta0_le_globalTransition`, `V2.Eleven.transition_lower`, `V2.Eleven.strict_lower_of_coexistence`, `V2.Eleven.transition_upper`, `V2.Eleven.globalTransition_eq_eleven`, `V2.Eleven.prop41`, `V2.Eleven.SmoothMixtureGap11`
- Open gap: Replace legacy coexistence and ElevenMixture gap chain by V2 proofs to remove the old chain from the v2 closure.
- Evidence: Sources: Eleven/RESOLUTION.md (Prop 4.1 row and ordering note: Assembly.lean keeps estimates -> scalar estimate -> uniqueness through 3543/200 (non-strict) -> coexistence -> strict bound).

### U08. Cube energy and spin-count moments

- Owner: G06. Source locator: `eq:section5-global-cube-energy`.
- Catalogue obligation: Count every Fourier sign and support multiplicity; preserve nonnegative mixture coefficients.
- Statement alignment: matches (cube energy and spin-count moment identities in the printed form, with every Fourier sign and support multiplicity and nonnegative mixture coefficients)
- Proof-route alignment: written-route (cube moments, exchangeable symmetry, shell counting 2^r C(12,r), cube_half_energy_eq_quadratic, printed_energy_eq_quadratic and relativeEntropy_eq_count)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `HighDim.Spin.cube_half_energy_eq_quadratic`, `V2.Channel.printed_energy_eq_quadratic`, `V2.Channel.relativeEntropy_eq_count`
- Open gap: None recorded.
- Evidence: Sources: Channel/RESOLUTION.md (printed energy rows); name resolution.

### U09. Twelve-square theta identity and analytic derivation

- Owner: G07. Source locator: `subsec:appendix-scalar-tail`.
- Catalogue obligation: Include convergence, nome normalization, Weierstrass/Eisenstein and theta identities, and the finite final elimination.
- Statement alignment: conditional (downstream consumers of the identity take the named Prop TwelveSquareIdentity; twelve_square_routeM proves it, so the identity itself is unconditional in the repository, but the manuscript's route is replaced)
- Proof-route alignment: route-difference (A.1 twelve-square identity is proved by modular-form uniqueness (RouteM; Matt's decision 2026-10-09: route difference); the written Weierstrass / Jacobi-triple-product steps (DLMF 23.8.1, 23.3.7, 23.6.2-4, 20.4.2/20.4.6) stay open)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.ThetaTail.TwelveSquareIdentity`, `V2.ThetaTail.RouteM.twelve_square_routeM`, `V2.ThetaTail.RouteM.lambert_conversion`, `V2.ThetaTail.RouteM.E6_theta`, `V2.ThetaTail.RouteM.theta_eta_product`, `V2.ThetaTail.RouteM.jt3_sq_duplication`, `V2.ThetaTail.RouteM.jt4_sq_duplication`, `V2.ThetaTail.RouteM.jt2_sq_duplication`, `V2.ThetaTail.theta12_elimination`, `V2.ThetaTail.lambert_coefficients`, `V2.ThetaTail.G_le_lambert_of_twelveSquare`
- Open gap: Written Weierstrass / Eisenstein / Jacobi-triple-product derivation (W2, W5, W6, W9 in the infrastructure note) not formalized; the finite final elimination is present as theta12_elimination.
- Evidence: Sources: ThetaTail/THETA_INFRASTRUCTURE.md; Matt's decision 2026-10-09; axioms_*.log in ThetaTail (standard three axioms).

### U10. Gaussian/Mellin estimates and scalar Bernstein comparison

- Owner: G07. Source locator: `lem:section5-global-scalar-tail`.
- Catalogue obligation: Treat n=0,1,2,3 and n>=4; prove positive denominator and degree-seven normalized Bernstein identity.
- Statement alignment: matches (n = 0,1,2,3 treated as explicit cases and n >= 4 via the Tn tail lemmas; denominator positivity tailBernsteinSum_pos; degree-seven normalized Bernstein identity tailP_eq_bernstein)
- Proof-route alignment: written-route (Gaussian/Mellin representation G_eq_mellin, termwise Tn estimates, exact Bernstein coefficient comparison)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.ThetaTail.Tn`, `V2.ThetaTail.Hn`, `V2.ThetaTail.Rn`, `V2.ThetaTail.tailP_eq_bernstein`, `V2.ThetaTail.tailBernsteinSum_pos`, `V2.ThetaTail.G_eq_mellin`, `V2.ThetaTail.mellinTerm_sum`, `V2.ThetaTail.polynomial_part`
- Open gap: None recorded.
- Evidence: Sources: ThetaTail/THETA_INFRASTRUCTURE.md; ThetaTail axioms logs.

### U11. C3 extension of the Poisson remainder

- Owner: G08. Source locator: `lem:section5-global-circle-remainder`.
- Catalogue obligation: Pass via smoothing and finite nonnegative partial sums; do not claim smooth Fourier decay for C3 inputs.
- Statement alignment: matches (C^3 extension of the Poisson remainder through smoothing and finite nonnegative partial sums; no smooth Fourier decay is claimed for C^3 inputs)
- Proof-route alignment: written-route (smoothing then finite nonnegative partial sums)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Circle.poisson_c3_remainder`
- Open gap: None recorded.
- Evidence: Sources: Circle/DECLARATIONS.md; Circle/axioms.out (standard three axioms).

### U12. Rational lower bounds for circle weights

- Owner: G09. Source locator: `d12-circle-eq:Wlower`.
- Catalogue obligation: P052; cubic orthogonality, exact square remainder, positive denominators, and u=0.
- Statement alignment: matches (rational lower bounds for the circle weights, cubic orthogonality, exact square remainder, positive denominators, and the u = 0 case)
- Proof-route alignment: written-route (P052: orthogonality, exact remainder identity, rational lower bounds)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Circle.weight_one_ge`, `V2.Circle.weight_two_ge`, `V2.Circle.weight_remainder_identity`, `V2.Circle.pi1_orth`, `V2.Circle.pi2_orth`
- Open gap: None recorded.
- Evidence: Sources: Circle/DECLARATIONS.md; Circle/axioms.out.

### U13. Scalar circle positivity and degree-seventeen polynomial

- Owner: G09. Source locator: `d12-circle-eq:scalarcircle`.
- Catalogue obligation: P053; keep signed initial series coefficients; unnormalized Bernstein representation.
- Statement alignment: matches (scalar circle positivity with the signed initial series coefficients kept; degree-seventeen polynomial; unnormalized Bernstein representation)
- Proof-route alignment: written-route (P053: signed initial terms retained, eighteen positive integer Bernstein coefficients)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Circle.scalar_circle_ineq`, `V2.Circle.scalar_positivity`, `V2.Circle.bernstein17_pos`, `V2.Circle.P17_eq_bernstein17`, `V2.Circle.baseexpand_hasSum`
- Open gap: None recorded.
- Evidence: Sources: Circle/DECLARATIONS.md; Circle/LEMMA516_PLAN.md; Circle/axioms.out.

### U14. Continuity and convexity of the explicit correction

- Owner: G09. Source locator: `prop:section5-spin-entropy`.
- Catalogue obligation: Export the properties of psi on the closed interval needed in conditional Jensen.
- Statement alignment: matches (continuity, nonnegativity and convexity of the explicit correction psi on the closed interval, exported for conditional Jensen; monotonicity of the V2 version)
- Proof-route alignment: written-route (properties of psi exported as in the written proof)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Circle.psi_continuousOn`, `V2.Circle.psi_nonneg`, `V2.Circle.psi_convexOn`, `V2.Assembly.psiV2_mono`
- Open gap: None recorded.
- Evidence: Sources: Circle/DECLARATIONS.md; Assembly deptrace; Circle/axioms.out.

### U15. Boundary conditional densities and spin disintegration

- Owner: G10. Source locator: `prop:section5-spin-entropy`.
- Catalogue obligation: Check conditional C3/positivity and integrability, posterior laws, entropy chain rule, Jensen, and feasibility cap.
- Statement alignment: matches-with-difference (boundary conditional densities, posterior laws, entropy chain rule, Jensen and the feasibility cap are stated at the level of the V2 Channel package; conditional C^3 and positivity assumptions are as in the written statement, with the cap, first-moment and log-profile proofs organized differently)
- Proof-route alignment: route-difference (the Channel cap, first-moment bounds and log-profile monotonicity are proved by different arguments than the written ones; the entropy chain rule goes through the repository ConditionalEntropy development)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Channel.channel_entropy_core`, `V2.Channel.conditional_explicit`, `V2.Channel.conditional_log_profile_mono`, `V2.Channel.allMinus_le`, `V2.Channel.integrate_budget`
- Open gap: No literal formalization of the written disintegration of the boundary conditional densities.
- Evidence: Sources: Channel/RESOLUTION.md; Channel axiom reports; Assembly deptrace.

### U16. Affine feature residuals and rational bounds

- Owner: G11. Source locator: `lem:section5-global-curvature`.
- Catalogue obligation: Bridge the exact rational matrix certificate to real weighted Cauchy--Schwarz.
- Statement alignment: matches (exact rational matrix certificate bridged to real weighted Cauchy-Schwarz)
- Proof-route alignment: written-route (exact rational certificate with the repository weightQ / momentQ / meanCoordinateQ, 179/200 + 6/4096 = 45899/51200 < 9/10 by norm_num, then real weighted Cauchy-Schwarz; notes say decide +kernel is used for the rational checks)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.FiniteState.alphaQ`, `V2.FiniteState.betaQ`, `V2.FiniteState.upperQ`, `V2.FiniteState.residualQ_lt_upperQ`, `V2.FiniteState.upperQ_le_cap`, `V2.FiniteState.curvature_coefficient_lt`, `V2.FiniteState.fixed_mean_curvature_affine`, `V2.FiniteState.weighted_cauchy_schwarz`
- Open gap: None recorded.
- Evidence: Sources: FiniteState/COMPARISON_G11.md and COMPARISON_G12.md; FiniteState/axioms_report.txt. The note cites 251 or 302 declarations in the package; the code index gives a different count.

### U17. Finite Gibbs formula and one-sided exponential remainder

- Owner: G11. Source locator: `d12-spin-eq:mgflower`.
- Catalogue obligation: Boundary target probabilities allowed; only a one-sided bound on -5e is required.
- Statement alignment: matches (finite Gibbs formula; boundary target probabilities allowed; one-sided bound on -5e)
- Proof-route alignment: route-difference (exponential remainder by Lagrange form instead of the integral Taylor remainder; Young's pointwise inequality replaced by relative-entropy nonnegativity)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.FiniteState.gibbs_variational`, `V2.FiniteState.exp_le_one_sided`, `V2.FiniteState.scaled_log_mgf_le`
- Open gap: None recorded.
- Evidence: Sources: FiniteState/COMPARISON_G11.md; FiniteState/axioms_report.txt.

### U18. Positive reference variance and centered regression identities

- Owner: G12. Source locator: `d12-spin-eq:variance-x`.
- Catalogue obligation: Prove positivity including t=0, and both mass/mean-centered residual equalities.
- Statement alignment: matches (positive reference variance including t = 0; both mass- and mean-centered residual equalities)
- Proof-route alignment: written-route (positivity and centered regression identities as in the written proof)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.FiniteState.famSpinVar_pos_of_nonneg_beta`, `V2.FiniteState.regResid_center`, `V2.FiniteState.regResid_center_x`
- Open gap: None recorded.
- Evidence: Sources: FiniteState/COMPARISON_G12.md; FiniteState/axioms_report.txt.

### U19. Rational extension and origin jets

- Owner: G12. Source locator: `eq:section5-origin-summary`.
- Catalogue obligation: P055; prove analyticity, cancellations, and zero derivatives through order three, independently of a quartic coefficient certificate.
- Statement alignment: matches-with-difference (zero derivatives through order three at the origin with analyticity of the rational extension; proved independently of a quartic coefficient certificate; vanishing order O(t^3) is the statement, versus O(t^4) in the surrounding certificate)
- Proof-route alignment: route-difference (orthogonality and jet cancellations are checked by decide +kernel computation rather than by the written hand cancellation)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.FiniteState.famF_origin_vanishing`, `V2.FiniteState.famResidVar_origin_vanishing`, `V2.Interval.family_zero_jets`
- Open gap: None recorded.
- Evidence: Sources: FiniteState/COMPARISON_G12.md; Interval/ZeroJets.lean; axiom reports.

### U20. Interval arithmetic and expression interpreter soundness

- Owner: G13. Source locator: `subsec:d12-spin-verification`.
- Catalogue obligation: Bind exact expressions to Lean definitions, prove all dyadic rounding/recurrence/log remainder rules, and reject invalid operations.
- Statement alignment: matches (soundness of dyadic rounding, reciprocal, log and Taylor-enclosure rules; interpreter soundness; invalid operations rejected, with tests recip_zero_* and log_nonpos_lo; exact expressions bound to Lean definitions by familyProg_eq and the P1/P2 register theorems)
- Proof-route alignment: route-difference (coherent-family enclosure construction in place of the written interval-arithmetic recurrence presentation)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Interval.Iv.mem_add`, `V2.Interval.Iv.mem_mul`, `V2.Interval.Iv.mem_recip`, `V2.Interval.Iv.log_mem`, `V2.Interval.step_sound`, `V2.Interval.runRS_sound`, `V2.Interval.build_mem`, `V2.Interval.taylorEnclosure_sound`, `V2.Interval.okAt_sound`, `V2.Interval.familyProg_eq`, `V2.Interval.P1_registers`, `V2.Interval.P2_registers`, `V2.Interval.recip_zero_mid`, `V2.Interval.log_nonpos_lo`
- Open gap: Glue IntervalKernel into the Interval/Final import graph.
- Evidence: Sources: Interval/CERTIFICATE_SPEC.md. The spec still says the certificate is 'not checked by the kernel', while IntervalKernel now checks it.

### U21. Cell coverage and integration from zero

- Owner: G13. Source locator: `d12-spin-eq:three`.
- Catalogue obligation: Prove all 160 cells cover the interval; no division by t^4 at zero; quantify over all real parameters and all states.
- Statement alignment: matches (scalar_certificate takes hc1 hc2 hc3; discharged by IntervalKernel.hc1-hc3; hc1, hc2, hc3 (the 160 cell checks) are now proved by the kernel in V2.IntervalKernel.Cells1-3 (axioms propext, Classical.choice, Quot.sound; logs/11_v2_axiom_scan.txt); V2.Final.Unconditional.* states the Challenge-shaped theorems with no extra hypotheses)
- Proof-route alignment: route-difference (cells are checked by decide +kernel in chunks of 8 cells (Cells{r}_{c}) rather than the written verification table; coverage by Row.cover; no division by t^4 at zero because of family_zero_jets and chain_taylor_*)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Interval.Row.cover`, `V2.Interval.checkCell_big`, `V2.Interval.checkCell_small`, `V2.Interval.chain_taylor_lower`, `V2.Interval.chain_taylor_upper`, `V2.Interval.family_zero_jets`, `V2.Interval.scalar_certificate`, `V2.IntervalKernel.hc1`, `V2.IntervalKernel.hc2`, `V2.IntervalKernel.hc3`
- Open gap: none beyond S053
- Evidence: Sources: Interval/CERTIFICATE_SPEC.md; IntervalKernel/NOTES.md (about 24.5 s kernel per cell; IntervalKernel is untracked in git and imported by no other module; build of Cells3 chunks was still running when this ledger was generated).

### U22. Large means including the endpoint point mass

- Owner: G14. Source locator: `prop:section5-spin-entropy`.
- Catalogue obligation: Cover 99/100<=t<=1 without evaluating the singular reference parameter at t=1.
- Statement alignment: matches (large means 99/100 <= t <= 1 including the endpoint point mass; the singular reference parameter is never evaluated at t = 1)
- Proof-route alignment: route-difference (elementary route: direct bound at a = 99/100, Mathlib log bounds, exact rational weight sum)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Assembly.large_mean_bound`, `V2.Assembly.binaryCost_ninety_nine_gt`, `V2.Assembly.psiV2_ninety_nine_gt`
- Open gap: None recorded.
- Evidence: Sources: Assembly deptrace; Assembly worker notes.

### U23. All branches, Sobolev compactness, and pressure derivatives

- Owner: G15. Source locator: `prop:section5-global-onset`.
- Catalogue obligation: Preserve the written global route and all local saddle/Morse--Bott assertions; derivatives come from analyticity, not big-O alone.
- Statement alignment: conditional (every conclusion takes OnsetEndpointInputs d and 12 <= d; derivatives are obtained from analyticity)
- Proof-route alignment: partial (global route G3-G7 and G13 formalized; branch construction by the C^0 IFT rather than the fixed-exponent H^s IFT N0, which is absent; the Morse-Bott manifold clause and the explicit cos formula remain open)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Onset.full_branch_onset_of_inputs`, `V2.Onset.optimizers_eventually_branch_orbit_v2`, `V2.Onset.sobolev_subsequence_limit`, `V2.Onset.pressure_second_derivative_right_v2`, `V2.Onset.pressure_second_derivative_left_v2`, `V2.Onset.OnsetEndpointInputs`
- Open gap: N0; Morse-Bott manifold clause of P8; explicit cos formula (5.full-branch-w2).
- Evidence: Sources: Onset/PROOF_STEPS.md; Final/deptrace_final.tsv.

### U24. Prior cited results and all implicit assumptions

- Owner: G16. Source locator: `sec:common-reduction`.
- Catalogue obligation: The full source and bibliography remain controlling. Resolve cited prerequisites in Lean or expose the exact missing theorem; this finite ledger is a minimum audit checklist, not a claim that all proof steps fit 24 entries.
- Statement alignment: conditional (cited prerequisites exist only as the named Props PositiveThresholdInput, CriticalAdamsInput and CircleLebedevMilinInput, which no declaration consumes; the Shearer-type entropy inequality is proved in the repository)
- Proof-route alignment: partial (positivity of beta_gm and the critical Adams bound are available only through endpoint-tainted legacy theorems or as hypotheses)
- Lean compilation: compiled (full library build `lake build BecknerOnofri` exit 0, logs/10_full_library_build.log; includes all V2 and IntervalKernel modules)
- Axiom / kernel check: standard-3-axioms (propext, Classical.choice, Quot.sound; every V2 declaration, 5406 in 219 modules, scanned with Lean.collectAxioms over the transitive closure, 0 violations, logs/11_v2_axiom_scan.txt; legacy declarations listed in resolved_lean_declarations (95) checked separately, all standard, logs/14_nonv2_listed_axioms.tsv)
- Lean declarations: `V2.Vocab.PositiveThresholdInput`, `V2.Vocab.CriticalAdamsInput`, `V2.Vocab.CircleLebedevMilinInput`, `V2.Vocab.globalTransition_pos_of_input`, `PaperResult.entropy_shearer`
- Open gap: Prove the three named Props independently or expose them as explicit hypotheses of the final theorems; the finite ledger is a minimum checklist, not a proof-step inventory.
- Evidence: Sources: Vocab/SECTION2_RESOLUTION.md section E4; Final/NOTES.md.
