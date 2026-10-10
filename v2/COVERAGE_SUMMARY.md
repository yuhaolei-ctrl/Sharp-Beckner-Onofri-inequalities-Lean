# Coverage summary

Generated 2026-10-10 01:01 UTC by the v2 ledger worker (G16 part 1) from `IMPLEMENTATION_STATUS.csv` (82 rows: S001-S058 and U01-U24) and the worker notes under `thread_state/workers/`. The numbered ids S001-S058 are the rows of the CSV (not S001-S082).

## 1. Counts per column

Counts are by the leading value of each cell; the parenthetical text of the cell says how and on what.

### statement_alignment

| value | all 82 | S rows (58) | U rows (24) |
|---|---|---|---|
| matches | 50 | 35 | 15 |
| matches-with-difference | 19 | 15 | 4 |
| conditional | 13 | 8 | 5 |
| not-formalized | 0 | 0 | 0 |
| unknown - not audited | 0 | 0 | 0 |

### proof_route_alignment

| value | all 82 | S rows (58) | U rows (24) |
|---|---|---|---|
| written-route | 26 | 18 | 8 |
| route-difference | 51 | 38 | 13 |
| partial | 5 | 2 | 3 |
| not-formalized | 0 | 0 | 0 |
| unknown - not audited | 0 | 0 | 0 |

### lean_compilation

| value | all 82 | S rows (58) | U rows (24) |
|---|---|---|---|
| compiled | 80 | 57 | 23 |
| not-compiled | 2 | 1 | 1 |

### axiom_kernel_check

| value | all 82 | S rows (58) | U rows (24) |
|---|---|---|---|
| standard-3-axioms | 41 | 28 | 13 |
| not-checked | 41 | 30 | 11 |

Module-level compilation state recomputed when this file was generated (V2 sources versus `.lake` oleans): 214 V2 modules built, 4 stale by mtime, 5 without olean.

- Without olean: `IntervalKernel.Cells3`, `IntervalKernel.Cells3_4`, `IntervalKernel.Cells3_5`, `IntervalKernel.Cells3_6`, `IntervalKernel.Cells3_7`
- Olean older than source (stale by mtime only): `Rearrangement.Comparison`, `Section3.Defs`, `Section3.Discharge`, `Section3.Lemma31`

## 2. Facts fixed by the owner

a. **Conditional on hc1/hc2/hc3.** The d>=12 endpoint, Theorem 1.3, and every declaration consuming Interval's scalar certificate take `hc1 hc2 hc3 : forall k < row_i.count, row_i.checkCell k = true` (row1/row2/row3) as hypotheses; they are conditional on hc1/hc2/hc3 (Lemma 5.21 `ScalarBounds`), discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in. Rows marked so: S003, S033, S040, S042, S044, S053, S056, S057, U21.
b. **Section 3 module-level taint.** `theorem_1_1_written` is declaration-level clean, but the module-level import closure still reaches Legacy `LowDimensionMixtureEndpoint` via `MixtureEnergyStatementBridge -> ...` (Section3/RESOLUTION.md). This is stated on every Section 3 row: S001, S017, S018, S019, S020, S021, S022, S023.
c. **Eleven coexistence.** Lemma 4.8 (S031), Prop 4.9 (S032), the strict part of Prop 4.1 (S024) and Theorem 1.2 (S002) reach the old `HighDim.Eleven.coexistence` (route difference); the same chain feeds U07.
d. **A.1 twelve-square identity** is proved by modular-form uniqueness (Matt's decision 2026-10-09: route difference); the written Weierstrass / Jacobi-triple-product steps stay open (rows S045, U09).
e. **Eleven competitor bound.** The Challenge `eleven_competitor` bound is 14.4088 (= 18011/1250) and differs from the manuscript's 8653/600 (rows S002, S025); both statements are proved (`eleven_competitor_written` carries the manuscript bound).

## 3. Rows that are not-formalized, partial or conditional

A row appears when its statement is not-formalized or conditional, its proof route is not-formalized or partial, or its module is not compiled. No row has the value not-formalized in a leading position; the set is therefore conditional / partial / not-compiled.

| id | source label | owner | flags |
|---|---|---|---|
| S003 | thm:intro-high-dimensional | G15 | statement=conditional |
| S012 | lem:coordinate-rearranged-minimizer | G02 | route=partial |
| S026 | lem:section4-periodization-entropy-identity | G05 | route=partial |
| S033 | prop:spectral-d12-base | G14 | statement=conditional |
| S040 | cor:section5-high-endpoint | G14 | statement=conditional |
| S042 | prop:section5-global-entropy-gap | G14 | statement=conditional |
| S044 | prop:section5-spin-entropy | G14 | statement=conditional |
| S053 | d12-spin-lem:scalar | G13 | statement=conditional, compilation=not-compiled |
| S056 | prop:section5-global-onset | G15 | statement=conditional |
| S057 | cor:section5-defect-onset | G15 | statement=conditional |
| U03 | eq:section2-all-exponential-moments | G02 | statement=conditional |
| U04 | lem:coordinate-rearrangement | G02 | route=partial |
| U09 | subsec:appendix-scalar-tail | G07 | statement=conditional |
| U21 | d12-spin-eq:three | G13 | statement=conditional, compilation=not-compiled |
| U23 | prop:section5-global-onset | G15 | statement=conditional, route=partial |
| U24 | sec:common-reduction | G16 | statement=conditional, route=partial |

- **S003** (`thm:intro-high-dimensional`): Glue IntervalKernel.hc1/hc2/hc3 into Final (no unconditional scalarBounds exists); decide whether Assembly/Final should consume spectral_dimension_transfer_written; N0 (H^s analytic IFT), explicit cos formula (5.full-branch-w2), Morse-Bott manifold clause.
- **S012** (`lem:coordinate-rearranged-minimizer`): O1 (AESuccessiveSteiner cannot replace MeasSuccessive in general; exists_meas_chain supplies it for Lipschitz starts); eq:coordinate-minimizer-gap not reproved; docstring reference to coordinate_minimizer_gap dangling.
- **S026** (`lem:section4-periodization-entropy-identity`): Random-variable-level chain rule / subadditivity; identification of JointLaw.shannonEntropy with the old labelEntropy (optional).
- **S033** (`prop:spectral-d12-base`): Supply ScalarBounds unconditionally (IntervalKernel gluing).
- **S040** (`cor:section5-high-endpoint`): IntervalKernel gluing; written-route transfer.
- **S042** (`prop:section5-global-entropy-gap`): IntervalKernel gluing; cube-energy identity taken from the legacy Spin module.
- **S044** (`prop:section5-spin-entropy`): Chain 5.12(i) + 5.12(ii) into t^4/250 <= ... is assembled in Assembly.global_entropy_gap (S042); IntervalKernel gluing.
- **S053** (`d12-spin-lem:scalar`): Glue IntervalKernel.hc1/hc2/hc3 into Final (an unconditional ScalarBounds does not exist yet); axiom check of IntervalKernel declarations; Cells3 chunks must finish building.
- **S056** (`prop:section5-global-onset`): N0; continuity of the pressure on (0,2d) (not needed in the formalized route); IntervalKernel gluing for the inputs.
- **S057** (`cor:section5-defect-onset`): IntervalKernel gluing; identification of the 11- and 12-version amplitudes (not needed).
- **U03** (`eq:section2-all-exponential-moments`): Replace circle_heatInteraction_entropy by a d = 1 proof independent of endpoint_through_ten, or consume CriticalAdamsInput as a hypothesis; state eq:section2-all-exponential-moments as a declaration if it is required downstream.
- **U04** (`lem:coordinate-rearrangement`): Reconcile the dangling coordinate_minimizer_gap docstring reference; confirm that MeasSuccessive implies the statement used by Section3 (O1).
- **U09** (`subsec:appendix-scalar-tail`): Written Weierstrass / Eisenstein / Jacobi-triple-product derivation (W2, W5, W6, W9 in the infrastructure note) not formalized; the finite final elimination is present as theta12_elimination.
- **U21** (`d12-spin-eq:three`): Finish the IntervalKernel build and glue Cells{1,2,3} into Final.
- **U23** (`prop:section5-global-onset`): N0; Morse-Bott manifold clause of P8; explicit cos formula (5.full-branch-w2).
- **U24** (`sec:common-reduction`): Prove the three named Props independently or expose them as explicit hypotheses of the final theorems; the finite ledger is a minimum checklist, not a proof-step inventory.

## 4. Rows that could not be determined

None. The 22 rows whose proof_route_alignment was `unknown - not audited` (S001, S005, S008, S009, S010, S011, S013, S014, S015, S018, S019, S020, S021, S022, S027, S030, S035, S037, U01, U02, U05, U08) were audited on 2026-10-10 by comparing the written proofs (handoff `catalogue/proofs/`, `source_slices/`) with the Lean proof structure of the resolved declarations, including the legacy lemmas they invoke (reading only; no lean or lake run). Result: 16 route-difference (S001, S005, S009, S010, S011, S014, S015, S018, S020, S021, S022, S030, S037, U01, U02, U05) and 6 written-route (S008, S013, S019, S027, S035, U08). S018 is a judgment call: the manuscript only cites Prop 2.2 of Mun-Rosenzweig, so no written proof exists to match.

## 5. Consolidated route differences

Thematic list (each theme with the rows that record it); the per-row text is in section 6.

- A.1 twelve-square identity by modular-form uniqueness (RouteM) instead of Weierstrass / triple-product steps: S045, U09
- Minimizer selection by polarization closure (`canonical_selection`) instead of the fibrewise heat-Mellin argument: S012, S016
- Local uniqueness / branch construction by the C^0 implicit-function theorem instead of the fixed-exponent H^s IFT (N0 absent): S002, S003, S031, S054, S055, S056, U23
- Lagrange remainder instead of integral Taylor remainder (Interval on [0,1/8]; FiniteState exponential bound): S052, S053, U17
- Young pointwise inequality replaced by relative-entropy nonnegativity: S052, U17
- Legacy ElevenMixture single-component gap and the repository 1/625 label bound instead of the (1/44000) sum P form and 1/600: S002, S024, S025, S028, U06, U07
- Repository d -> d+1 transfer `spectral_dimension_transfer` consumed in place of `spectral_dimension_transfer_written`: S003, S040
- Lemma 5.9 generated by swaps and reflections: S041
- Mixture / Scalar harmonic identity and discrete layer-cake: S043
- Channel cap, first-moment and log-profile proofs: U15
- Eleven profile Fourier transform by Gamma-Gaussian subordination instead of the Bessel K formula; certified finite shell sum: S029
- Old HighDim.Eleven.coexistence chain used for Lemma 4.8 / Prop 4.9 / strict part of Prop 4.1 / Theorem 1.2: S002, S024, S031, S032, U07
- Duality and extremizer correspondence of Section 2 through legacy weak-duality theorems, the rough exponential bound, Gibbs-limit construction and radial Wiener summability instead of the written sup-interchange, equality cases and Banach-algebra bootstrap: S005, S009, S010, U02
- Circle rearrangement by Lipschitz polarization closure and L^1 limit instead of Burchard-Hajaiej and nested-arc layer-cake: S011
- Positive Taylor coefficients by tensor Bernstein polynomials / Jacobi-tensor Mellin kernel with Schur normalization and Chebyshev profile instead of Widder's theorem and the written smoothness argument: S014, S015, U05
- Section 3 scalar certificates (168-case radius-64 truncated shells, degree-40 polynomial theta majorant, rational subadditivity in the Gaussian-binomial lemma, legacy coefficient-cap entropy bound) instead of the written 189-pair recurrence, shell counts / grid enclosure, artanh monotonicity and cited Prop 2.2: S018, S020, S021, S022, and by inheritance S001
- Section 4 finite scalar check by the radius-64 truncated-shell certificate instead of the full q-range recurrence with B = 2^96: S030
- Random-rectangle transfer through the hypergeometric latent L and finite truncation plus monotone limit instead of direct Fubini-Tonelli on (N, M): S037
- Homogeneous entropy via the pointwise nonnegative integrand instead of Jensen: U01

## 6. Per-row route differences (proof_route_alignment = route-difference)

| id | source label | difference |
|---|---|---|
| S001 | thm:intro-low-dimensional | (assembly follows the written proof: Final.low_dim_* derive from Section3.theorem_1_1_written, which composes Lemma 3.1, Prop 3.7 and the Section 2 inputs along the written route R1/R2/R4; it inherits the route differences of S016 (selection by polarization closure), S020 and S022 (scalar-gap and theta certificates), S023 (countable passage) and S006/S007 (endpoint-tainted obstruction and curve geometry); the d=1 equality classification is not derived in the manuscript proof (only recalled) and is the legacy Legacy.CircleEqualityComplete / CircleEquality.*paper_family result) |
| S002 | thm:intro-d11 | (Lemma 4.8 local uniqueness via the legacy C^0 implicit-function route, Prop 4.9 coexistence repackaged from legacy HighDim.Eleven.coexistence, Prop 4.5 label-entropy bound via the repository 1/625, uniqueness step through legacy ElevenMixture) |
| S003 | thm:intro-high-dimensional | (spectral part consumes the repository d -> d+1 transfer Transfer.spectral_dimension_transfer, not spectral_dimension_transfer_written; onset part uses the C^0 implicit-function construction LocalEleven instead of the fixed-exponent H^s IFT, L^2-Rellich plus tail splitting for compactness, 12-version branch for pressure derivatives) |
| S004 | lem:section2-finite-entropy-energy | (the energy bound follows the written Donsker-Varadhan route in physical space; the entropy limit uses the repository HeatEntropyConvergence argument instead of the written weak lower semicontinuity plus contraction under P_t, N4 'not examined line by line') |
| S005 | prop:section2-coefficient-pressure-duality | (the smooth-density restriction of the pressure follows the written heat-flow argument; the duality itself is not proved by the written interchange of the suprema with an attained potential u_rho: the two inequalities go through the legacy weak-duality theorems SubcriticalPrimalDual.dual_le_gibbs (Gibbs density of an admissible potential, integrability from the rough exponential bound GenericAttainment.rough_bound) and density_le_dual (dual potential of an L^2 density), with a heat-flow reduction of finite-entropy densities to L^2 densities in PressureDuality.pressure_le_coefficientDefect) |
| S006 | lem:section2-universal-obstructions | (clauses (i)-top and (ii) follow clean repository proofs; the finiteness at A_crit goes through legacy AdamsEndpoint.critical_entropy_energy -> circle_heatInteraction_entropy -> Legacy.physical_green_endpoint -> endpoint_through_ten, i.e. the old endpoint chain, instead of the manuscript's critical Adams inequality eq:section2-critical-adams (Lebedev-Milin / Okikiolu); the v2 clean form exists only as the named Props CriticalAdamsInput / CircleLebedevMilinInput, which no declaration consumes) |
| S007 | prop:section2-basic-curve-geometry | (curve properties follow clean repository proofs; transition_positive, coefficient_zero_iff and coefficient_lower_bounds are endpoint-tainted: d<=10 via LowDimension.pressure_formula -> endpoint_through_ten, d=11 via HighDim.Eleven.transition_pos, d>=12 via Target.pressure_threshold, whereas the manuscript proves beta_gm > 0 independently from CdCRS2025 Theorem 3 / Lebedev-Milin) |
| S009 | cor:section2-extremizer-correspondence | (the extremizer correspondence is obtained by the Gibbs-limit construction OptimizerGibbsLimit / ContinuousOptimizerFromL2 and regularity from radial Wiener summability and Euler-Lagrange identification (OptimizerEulerPaper), not by the written zero-gap equality cases and the H^{jd} Banach-algebra bootstrap) |
| S010 | prop:section2-subcritical-attainment | (coercivity of the dual functional comes from the Green-kernel RoughExponentialBound of the legacy SubcriticalRoughBound, not from the critical Adams inequality; compactness is by upper semicontinuity of the log-partition function on a weak ball in SubcriticalAttainment / RawAttainment, not by Vitali convergence) |
| S011 | lem:circle-rearrangement | (the Riesz-type inequality is proved from the Lipschitz polarization closure and an L^1 limit (CircleRearrangementL1Limit / CircleLayerCake), not from Burchard-Hajaiej; the contraction is obtained by passing to the limit, not by the written nested-arc layer-cake argument) |
| S014 | lem:positive-bernstein | (positivity of the Taylor coefficients comes from the finite-difference coefficients of tensor Bernstein polynomials (Legacy BernsteinPositiveCoefficients, ClosedCubeTaylor), not from Widder's absolutely monotone theorem) |
| S015 | prop:cosine-all | (same induction and Neumann-series architecture as the written proof, but cosine-variable smoothness is obtained through the Chebyshev profile, the comparison kernel is the Jacobi-tensor Mellin kernel with Schur normalization, and positivity of the Taylor coefficients uses tensor Bernstein polynomials) |
| S016 | lem:selection-full-entropy-domain | (the repository selection is built by the closure of finite polarizations, CoordinateRearrangement.exists_canonical_chain / exists_canonical_coordinate_limit, with global optimality passed through closure, not the written fibrewise heat-Mellin argument; v2 adds the written-route energy comparison separately in V2.Rearrangement) |
| S018 | lem:circle-entropy | (the manuscript only cites Prop 2.2 of Mun-Rosenzweig for the entropy bound and gives no proof; Lean folds the legacy two-sided Legacy.D10.CircleEntropy.entropy_bound (Euler-recurrence coefficient cap) by conjugate symmetry; there is no written proof to match, so this is not a verified written route) |
| S020 | prop:scalar | (tail n >= 22, d = 3..10, as written; the case d = 2 is split n >= 4 / n <= 3 through GaussianHeatTwo, the finite certificate is a 168-case check with radius-64 truncated shells rather than the written 189-pair p_q recurrence, and the theta-integral certificate differs (see S022)) |
| S021 | lem:gaussian-binomial | (ratio-product skeleton as written, but the key step uses subadditivity of the rational function (1-x)/(1+x) in place of monotonicity of artanh and logarithms) |
| S022 | lem:theta-integral-certificate | (degree-40 polynomial majorant (1+2x+3x^4)^10 - 1 with closed-form integrals and kernel-checked rational roundings (ThetaPolynomialMajorant / ThetaPolynomialCertificate), not the written shell counts r_10(q), grid enclosure and eta bound) |
| S023 | prop:equality | (written route R1/R2/R4 formalized, but the countable passage is by monotone convergence in ENNReal on Fourier energies instead of density truncation, only the inequality half of the entropy chain rule is proved via Shearer r=1, the mixed-index average reuses MixedBinomialComparison, and Prop 3.4 / Lemma 3.5 enter through their legacy proofs) |
| S024 | d11:thm:interval | (strict lower bound derived from prop49, i.e. legacy HighDim.Eleven.coexistence; non-strict lower bound uses the legacy single-component gap ElevenMixture.countable_mixture_gap instead of the written (1/44000) sum P(L_i >= 1) form) |
| S025 | prop:section4-entropy-bound | (the 1/600 label-entropy bound is derived from the repository's stronger 1/625 via single-coordinate moment and subadditivity, not the written (1/44000) sum P(L_i >= 1) argument) |
| S028 | lem:section4-lattice-label-entropy | (repository single-coordinate moment bound coordinateLabelMoment_lt plus subadditivity, versus the written (1/44000) sum P(L_i >= 1) gap form with rounded sums) |
| S029 | lem:section4-profile-fourier-transform | (Fourier transform by Gamma-Gaussian subordination instead of the Bessel K formula; the manuscript's shell expansion eq:section4-shell-expansion and rounded sums replaced by the old certified finite sum Shell.certified_finite_energy and the old theta estimate) |
| S030 | d11:prop:scalar | (tail estimate follows the written proof; the finite part 1 <= n <= 21 uses the legacy radius-64 truncated-shell certificate (ElevenScalarFinite / Certificates) rather than the written full q-range recurrence with B = 2^96) |
| S031 | lem:section4-local-uniqueness | (wrapper of the legacy local_unique_convolution: H^11 embeds in C^0 and uniqueness is proved by the continuous-function implicit-function theorem, uniqueness in a C^0 neighbourhood, not the written Banach-algebra IFT in H^11 with Plancherel inverse bound) |
| S032 | prop:section4-first-order-coexistence | (V2.Eleven.prop49 only repackages the old HighDim.Eleven.coexistence / uniform_hessian / corner theorems; the written Rellich-Adams-Vitali compactness is replaced by exists_nonzero_limit_optimizer) |
| S037 | prop:spectral-marginal-energy | (same random-rectangle / Lemma 5.4 / induction chain, but the latent variable is introduced through the hypergeometric latent L first, and the countable passage is by finite truncation plus monotone limit instead of the written direct Fubini-Tonelli on (N, M)) |
| S040 | cor:section5-high-endpoint | (Prop 5.7 is consumed through the repository d -> d+1 transfer spectral_dimension_transfer, not the written spectral_dimension_transfer_written; the threshold identification uses the legacy pressure_threshold_from_twelve) |
| S041 | lem:common-cubic | (symmetry proved for transpositions and coordinate reflections separately, generated by swap induction and separately_even_all_signs, instead of the written one-step argument for an arbitrary R in B_d; same ingredients Ginibre / Euler support / strict covariance) |
| S043 | prop:section5-singular-fourier-tail | (harmonic identity from the repository scalarHarmonic_tsum rather than the written telescoping recurrence; arbitrary-index tail from the repository discrete layer-cake mixedTail_le_diagonal rather than the written continuous layer-cake comparison; scalar bound T_n <= R_n from S045) |
| S044 | prop:section5-spin-entropy | (cap nu(all minus) <= 2^-12 proved in circle coordinates for cosine-monotone functions rather than on the pushforward arcsine measure; conditional first moment 0 <= t_i < 1 by antipodal pairing, no arcsine formula; monotonicity of the conditional log profile by differentiation under the integral sign instead of the old log_integral_exp_monotone; large-mean bound from the Gibbs variational inequality at a = 99/100 with Mathlib log 2 bounds) |
| S045 | lem:section5-global-scalar-tail | (A.1 twelve-square identity is proved by modular-form uniqueness (RouteM; Matt's decision 2026-10-09: route difference); the written Weierstrass / Jacobi-triple-product steps (DLMF 23.8.1, 23.3.7, 23.6.2-4, 20.4.2/20.4.6) stay open; the remaining steps n = 0,1,2,3 and n >= 4, Gaussian/Mellin and Bernstein, follow the written derivation per the ThetaTail note) |
| S051 | d12-spin-lem:feasible | (Euler beta integral, Jensen and log(1+u) <= u steps follow the written route; minor local differences: t^9(1-t) <= 1/10 and t chi >= 11 by exact algebraic factorizations instead of the maximum / derivative, concavity of (y-c)/(chi+y) from convexity of 1/x instead of the second derivative, DLMF 5.12.1 via Mathlib's complex betaIntegral; D4/D7/D9 in the note) |
| S052 | d12-spin-lem:perturb | (for y <= 0 the Lagrange form of the Taylor remainder is used instead of the integral remainder; the Gibbs inequality is proved by the pointwise Young inequality r u <= r log r - r + e^u instead of nonnegativity of relative entropy; otherwise Cor 5.18, Gibbs with H = -5e and the scaled MGF bound as written) |
| S053 | d12-spin-lem:scalar | (the manuscript's Taylor integral formula on [0,1/8] is replaced by the Lagrange (mean-value) form for a coherent chain, Coh.taylor / chain_taylor_lower / chain_taylor_upper; jet soundness is proved through coherent families, not iterated derivatives of the closed form; the 160 cells are checked by IntervalKernel.fastCheck with decide +kernel in 8-cell chunks instead of the interpreter run; row-3 cell endpoints are not dyadic and only the enclosures are) |
| S054 | lem:section5-quartic-reduction | (the implicit-function theorem is done in C(Torus,R) and Sobolev information is recovered afterwards for every s by rescaled analytic maps; the manuscript's fixed-exponent analytic IFT in H^s_0, s > d/2 (obligation N0) is not formalized) |
| S055 | prop:section5-local-branches | (equal active amplitudes proved directly on Fourier coefficients, not by the written divisibility argument; branch construction by the C^0 IFT as in S054) |
| S056 | prop:section5-global-onset | (steps G3-G7, G13: uniform bounds, Euler bootstrap, tail-splitting compactness and the exclusion of proper-support branches are new; but the branch construction and the O(delta) H^s profile bound are the existing C^0 LocalEleven constructions, classification uses the legacy SupportedFamily.raw_sobolev_classification, the compactness step uses the legacy L^2 Rellich ball and RoughExponentialBound, and the fixed-exponent H^s IFT N0 is not done) |
| S057 | cor:section5-defect-onset | (one-sided derivatives are re-derived in a clean module from the 12-version DiagonalScalarBranch.supercriticalEnergy_hasDerivAt and pressure = 0 below beta_s; pressure identification uses the legacy GlobalOptimizerClassification.branch_eventually_optimizer; the 11- and 12-version branch amplitudes are not proved equal) |
| U01 | eq:section2-relative-entropy | (V2.Vocab.homEntropy is defined through the pointwise nonnegative integrand r log(r/m) - r + m with a bridge to the integral of f log f - m log m; the written Jensen argument is not used) |
| U02 | eq:intro-dual-energy-def | (the algebraic normalizations are direct; the physical Green double-integral identity is delivered by the legacy physicalGreen_eq_spectral (rough-bound summability), not by Parseval and Lemma 2.1) |
| U03 | eq:section2-all-exponential-moments | (Gibbs integrability is obtained by replaying the first half of Gap.primal_gap and the rough exponential bound of the legacy GenericAttainment instead of the written exponential-moment corollary; the critical exponential moment goes through legacy AdamsEndpoint.critical_entropy_energy -> circle_heatInteraction_entropy -> physical_green_endpoint -> endpoint_through_ten rather than a d = 1 Lebedev-Milin proof) |
| U05 | prop:cosine-all | (same as S015: the induction for mixed derivatives and the nonscalar fractional operator use the Chebyshev profile, the Jacobi-tensor Mellin kernel with Schur normalization and tensor Bernstein polynomials; the listed circleHeat_* declarations belong to S012 and are not on the cosine_representation path) |
| U06 | eq:mixture-strict-entropy-gap | (strictness is taken from the legacy countable_mixture_gap / ElevenMixture.finite_mixture_gap chain instead of the written Tonelli computation over correlated latent mixture laws; the V2.Mixture tail-average identities are written-route) |
| U07 | d11:thm:interval | (the early non-strict bound is conditional on the named Prop SmoothMixtureGap11, discharged by the legacy ElevenMixture chain (countable_mixture_gap); manuscript order is kept in Eleven/Assembly.lean, but strict_lower_of_coexistence reaches the old HighDim.Eleven.coexistence). Eleven coexistence taint: this item reaches the old HighDim.Eleven chain (coexistence / local_unique_convolution, module ElevenCoexistence, plus HighDim.Eleven.transition_pos) in place of the written Sobolev-IFT / compactness proofs; route difference |
| U09 | subsec:appendix-scalar-tail | (A.1 twelve-square identity is proved by modular-form uniqueness (RouteM; Matt's decision 2026-10-09: route difference); the written Weierstrass / Jacobi-triple-product steps (DLMF 23.8.1, 23.3.7, 23.6.2-4, 20.4.2/20.4.6) stay open) |
| U15 | prop:section5-spin-entropy | (the Channel cap, first-moment bounds and log-profile monotonicity are proved by different arguments than the written ones; the entropy chain rule goes through the repository ConditionalEntropy development) |
| U17 | d12-spin-eq:mgflower | (exponential remainder by Lagrange form instead of the integral Taylor remainder; Young's pointwise inequality replaced by relative-entropy nonnegativity) |
| U19 | eq:section5-origin-summary | (orthogonality and jet cancellations are checked by decide +kernel computation rather than by the written hand cancellation) |
| U20 | subsec:d12-spin-verification | (coherent-family enclosure construction in place of the written interval-arithmetic recurrence presentation) |
| U21 | d12-spin-eq:three | (cells are checked by decide +kernel in chunks of 8 cells (Cells{r}_{c}) rather than the written verification table; coverage by Row.cover; no division by t^4 at zero because of family_zero_jets and chain_taylor_*) |
| U22 | prop:section5-spin-entropy | (elementary route: direct bound at a = 99/100, Mathlib log bounds, exact rational weight sum) |

### Partial routes

- S012 (`lem:coordinate-rearranged-minimizer`): (written route formalized for the bounded-density fibrewise heat-Mellin energy comparison: Lemma 2.8 per fibre, Tonelli, Plancherel on the finite heat integral, entropy invariance, induction over coordinates; the relative-entropy computation eq:coordinate-minimizer-gap is NOT reproved, the smooth/Gibbs form of the minimizer comes from the repository regularity route)
- S026 (`lem:section4-periodization-entropy-identity`): (smoothness follows the written M-test; the chain rule and subadditivity of Shannon entropy are NOT reproved at random-variable level, the explicit-sum versions labelEntropy_subadditive / conditionalLabelEntropy_le_labelEntropy are used and transported by condShannon_eq)
- U04 (`lem:coordinate-rearrangement`): (existence of the rearranged chain and entropy / energy preservation are proved along the written route; smoothness recovery is delivered through the MeasSuccessive formulation, and the module docstring of Rearrangement/Comparison.lean refers to a declaration coordinate_minimizer_gap that does not exist)
- U23 (`prop:section5-global-onset`): (global route G3-G7 and G13 formalized; branch construction by the C^0 IFT rather than the fixed-exponent H^s IFT N0, which is absent; the Morse-Bott manifold clause and the explicit cos formula remain open)
- U24 (`sec:common-reduction`): (positivity of beta_gm and the critical Adams bound are available only through endpoint-tainted legacy theorems or as hypotheses)

## 7. Statement differences (statement_alignment = matches-with-difference)

| id | source label | difference |
|---|---|---|
| S002 | thm:intro-d11 | (Challenge-vocabulary eleven_competitor asserts Ent(rho_*) < 14.4088 = 18011/1250, the repository bound, which differs from the manuscript's 8653/600; eleven_competitor_written states the manuscript bound 8653/600; all other conjuncts of Theorem 1.2 match, including 3543/200 < beta_gm < 2063/100 < beta_s < 22 and energy > 14475384292906/10^12) |
| S007 | prop:section2-basic-curve-geometry | (stated on all real beta / all real A, stronger domain than [0,2d] and (0,inf); beta_gm defined as sSup of the zero set with the quotient formula proved afterwards; defect-zero-set and lower bounds depend on beta_gm > 0) |
| S010 | prop:section2-subcritical-attainment | (the statement is delivered by composing separate declarations; smoothness of the potential u itself is not a standalone raw statement, it appears inside PrescribedSelection.canonical_selection; extra conjunct 0 <= dualFunctional; endpoint clause beta = 2d via the beta-free regularity theorems) |
| S011 | lem:circle-rearrangement | (kernel q bounded, nonnegative, radially nonincreasing in the geodesic norm; monotonicity stated pointwise in Circle.circle_rearrangement and almost everywhere in PolarizationL1.layerRearrangement_mono) |
| S012 | lem:coordinate-rearranged-minimizer | (successive_rearrangement_energy_le / rearranged_pressureValue_ge use MeasSuccessive (AESuccessiveSteiner plus a.e. strong measurability of the intermediate stages) instead of AESuccessiveSteiner, obligation O1; coordinate_rearranged_minimizer takes a given smooth global minimizer and returns the Steiner-rearranged minimizer, valid for every beta > 0) |
| S015 | prop:cosine-all | (holds for every d > 0, the manuscript states d >= 2; all beta > 0, smooth Euler pair, mean zero, separately even, coordinatewise nonincreasing) |
| S016 | lem:selection-full-entropy-domain | (all d > 0 instead of d >= 2; (i) existence and smooth positive Gibbs form from the repository, (ii)/(iii) selection and mixture representation obtained by composing coordinate_rearranged_minimizer with cosine_representation; the relative-entropy computation eq:coordinate-minimizer-gap is replaced by repository regularity; MeasSuccessive versus AESuccessiveSteiner, O1) |
| S017 | lem:collapse-conditional-reduction | (MixtureInequality / MixtureStrictness are the lemma's own premises as Prop-valued hypotheses; the dimension restriction d <= 10 is not assumed, only 2 <= d (lemma_3_1) or 0 < d (lemma_3_1_smooth, strictness false at d = 1); conclusion adds pressure d (2d) = 0) |
| S022 | lem:theta-integral-certificate | (proved strictly, thetaIntegral 10 < 41/25, slightly stronger than the printed <=; J_d < (d/10)(41/25) packaged) |
| S023 | prop:equality | (stronger: iff, with both reverse directions; hypotheses 2 <= d <= 10; mixture class is the literal finite-entropy countable cosine-power mixtures) |
| S036 | lem:spectral-rectangle | (the repository states S_{d-1}(R_-i) on the ambient lattice Z^d with the i-th radius 0; the literal reduced form is proved as spectral_rectangle via latticeSum_update_zero_eq_succAbove) |
| S037 | prop:spectral-marginal-energy | (arbitrary correlated countable weights, extended-real energies, d >= 12 and 12 <= r <= d, both displays; marginals are functions on the ambient torus with inversePowerEnergy r) |
| S041 | lem:common-cubic | (stated for every d > 0 instead of d >= 12; Phi is the repository's dualFunctional beta_s via Phi_eq_dualFunctional, comparison class H_0^{d/2} versus all H^{d/2} bridged; common_cubic_symmetry_translate adds a translation-allowed form) |
| S054 | lem:section5-quartic-reduction | (existing repository statements for d >= 11 in the vocabulary Space d: reduced expansion Psi = delta S + Q_4 + O(S^3 + \|delta\| S^2) with the C^0 neighbourhood; the explicit cosine formula eq:full-branch-w2 and a stand-alone log Z Taylor lemma are absent; V2.Onset adds the H^s Banach-algebra and exponential bounds) |
| S055 | prop:section5-local-branches | (d >= 11; neighbourhoods are C^0 neighbourhoods in Space d with the H^s version as the last clause of StableSupportedClassification; the Morse-Bott 'critical set is a smooth manifold' part is not a separate field (tangent independence plus Hessian kernel only); active Hessian eigenvalue list not re-read) |
| U04 | lem:coordinate-rearrangement | (the canonical rearranged density is tracked, but through MeasSuccessive (measure-level successive Steiner chain, O1) rather than the repository's AESuccessiveSteiner (a.e. version); marginals are taken on the ambient torus) |
| U06 | eq:mixture-strict-entropy-gap | (positivity of the strict entropy gap is proved; the displayed quantitative form 3/(2200 d) * sum P(L_i >= 1) of eq:mixture-strict-entropy-gap is not what the legacy countable_mixture_gap supplies: it gives w_a^2 * latentWeight * gap(d) / 2 for a component a with N a != 0, with the repository's gap d; only positivity is used downstream) |
| U15 | prop:section5-spin-entropy | (boundary conditional densities, posterior laws, entropy chain rule, Jensen and the feasibility cap are stated at the level of the V2 Channel package; conditional C^3 and positivity assumptions are as in the written statement, with the cap, first-moment and log-profile proofs organized differently) |
| U19 | eq:section5-origin-summary | (zero derivatives through order three at the origin with analyticity of the rational extension; proved independently of a quartic coefficient certificate; vanishing order O(t^3) is the statement, versus O(t^4) in the surrounding certificate) |

### Conditional statements

- S003 (`thm:intro-high-dimensional`): (conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; the Onset.*_of_inputs theorems are additionally conditional on OnsetEndpointInputs d and 12 <= d; Final.* types equal the Challenge types with hc1 hc2 hc3 added as hypotheses)
- S033 (`prop:spectral-d12-base`): (all Assembly.* theorems take the hypothesis ScalarBounds = Lemma 5.21; conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in)
- S040 (`cor:section5-high-endpoint`): (conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; statement: inequality with equality only for rho = 1, dual potential inequality with A_s(d) and equality only for constants, beta_gm = beta_s, IsGreatest zero-pressure set, IsLeast zero-defect coefficient)
- S042 (`prop:section5-global-entropy-gap`): (takes ScalarBounds, conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; statement: smooth strictly positive permutation-invariant mixture density with log rho = V(cos), d_i V >= 0, d_i^2 V >= 0 gives Ent - E/2 >= rho^(e_1)^4/250, rho^(e_1) >= 0 and rho^(e_1) = 0 implies rho = 1, all included; internal 1/70 version also proved)
- S044 (`prop:section5-spin-entropy`): (part (ii) in count form and in measure form needs ScalarBounds = Lemma 5.21 through count_form_public / count_form_internal, conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; part (i) Channel.spin_entropy_comparison_i is unconditional with the printed hypotheses (hmix and the second-derivative hypothesis are unused, as the manuscript remarks), conclusion written with \|\|rho^(n e_i)\|\|^2 and t = Re rho^(e_1); 0 <= t is not part of the (i) statement; large_mean_bound for 99/100 <= t <= 1 including the point mass is unconditional)
- S053 (`d12-spin-lem:scalar`): (family_scalar_bounds, scalar_certificate and Final.scalarBounds_of_checks take hc1 hc2 hc3: forall k < row_i.count, row_i.checkCell k = true; conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; the statement proved is f >= t^4/10 (strict for t > 0), V <= t^4/50, e_j >= -1/4 for 0 <= t <= 99/100 for the FiniteState family famF / famResidVar / famResid; IntervalKernel.hc1/hc2/hc3 prove the three checks by kernel evaluation but are imported by no Final / Assembly module)
- S056 (`prop:section5-global-onset`): (every conclusion takes OnsetEndpointInputs d = spectral inequality + forward density rigidity (Cor 5.8) and 12 <= d; Final.onsetEndpointInputs_of_checks derives these inputs from hc1/hc2/hc3, conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in)
- S057 (`cor:section5-defect-onset`): (takes OnsetEndpointInputs d and 12 <= d; Final.high_dim_defect_onset is conditional on hc1/hc2/hc3, conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in)
- U03 (`eq:section2-all-exponential-moments`): (eq:section2-all-exponential-moments has no declaration of its own: it is a corollary of the critical Adams bound via e^{p\|u\|} <= e^{pu} + e^{-pu}; the v2 clean form of the critical Adams input is only the named Prop CriticalAdamsInput, which no declaration consumes; the available theorem HD.critical_adams_bound is unconditional but sits on the old endpoint chain; Gibbs densities have finite partition function under the rough-exponential bound of GenericAttainment)
- U09 (`subsec:appendix-scalar-tail`): (downstream consumers of the identity take the named Prop TwelveSquareIdentity; twelve_square_routeM proves it, so the identity itself is unconditional in the repository, but the manuscript's route is replaced)
- U21 (`d12-spin-eq:three`): (conditional on hc1/hc2/hc3 (row1/row2/row3 checkCell, i.e. Lemma 5.21 ScalarBounds); discharged only when V2.IntervalKernel.Cells{1,2,3} are glued in; scalar_certificate takes hc1 hc2 hc3 : forall k < row_i.count, row_i.checkCell k = true as hypotheses)
- U23 (`prop:section5-global-onset`): (every conclusion takes OnsetEndpointInputs d and 12 <= d; derivatives are obtained from analyticity)
- U24 (`sec:common-reduction`): (cited prerequisites exist only as the named Props PositiveThresholdInput, CriticalAdamsInput and CircleLebedevMilinInput, which no declaration consumes; the Shearer-type entropy inequality is proved in the repository)

## 8. How the columns were filled, and inconsistencies found

Method. This pass did not run lean, lake or `#print axioms` (a long kernel build was running) and committed nothing. lean_compilation = the olean of every module that holds a listed declaration exists and is not older than its source (legacy modules count as baseline-built). axiom_kernel_check = standard-3-axioms only when every listed declaration appears in a preserved axiom report (per-declaration logs and traces, the FiniteState package-wide `axioms_report.txt`, the Vocab/Rearrangement `axall2` check, or the Section3 / Transfer notes); otherwise not-checked with the count. No `sorry` occurs in `BecknerOnofri/V2` (a word-level grep finds only "sorry-free" in docstrings) and no `axiom` declaration exists there.

Inconsistencies and loose ends:

- IntervalKernel is untracked in git and imported by no other module, so Final/Assembly do not consume it; hc1/hc2/hc3 are proved there by `decide +kernel` in 8-cell chunks. At generation time Cells3 has no olean yet. The build was still moving, so rerun the ledger build for the final compile column.
- Interval/CERTIFICATE_SPEC.md still says the 160-cell check is "not checked by the kernel" (cells cannot be checked by the kernel in that session); IntervalKernel now does exactly that.
- The v2 ids are S001-S058 and U01-U24 (82 rows), not S001-S082.
- Rearrangement/Comparison.lean (line 320) refers to `coordinate_minimizer_gap`, which is not a declaration (only the label `eq:coordinate-minimizer-gap`).
- Olean older than source by mtime: `Rearrangement.Comparison`, `Section3.Defs`, `Section3.Discharge`, `Section3.Lemma31`. The downstream oleans were rebuilt later, so these are treated as compiled; a fresh `lake build` would confirm.
- Assembly and Final consume the repository d -> d+1 transfer `spectral_dimension_transfer`; the statement-equal `spectral_dimension_transfer_written` exists but is not consumed (Final/NOTES.md, Transfer/RESOLUTION.md).
- The named Props `PositiveThresholdInput`, `CriticalAdamsInput` and `CircleLebedevMilinInput` are stated but consumed by no declaration; the corresponding cited facts reach the old endpoint chain through legacy theorems.
- Section3: declaration-level traces are clean (0 forbidden-module hits) but the legacy theorems that the V2 declarations wrap reach `LowDimensionMixtureEndpoint` at module level (S3 taint, every Section 3 row).
- Final deptrace: no forbidden primary hits, but the strict list is hit by `SelectedCubicSymmetry`, `SpinMixtureMoments`, `CircleGammaDefinitions`, `SpinMixtureCap` (Final/deptrace_final.tsv).
- Declaration counts differ between notes and code: FiniteState `COMPARISON_G12.md` says 251 declarations, `axioms_report.txt` says 302, and the source index finds 287 theorem/def/structure-level declarations.
- Vocab/Rearrangement `axall2` (217 declarations) predates the later edit of Rearrangement/Comparison.lean, whose declarations therefore count as not covered by that check.

## 9. Evidence legend

- Worker notes: `thread_state/workers/<Package>/` (Vocab/SECTION2_RESOLUTION.md, Circle/DECLARATIONS.md and LEMMA516_PLAN.md, Section3/RESOLUTION.md, Eleven/RESOLUTION.md, Transfer/RESOLUTION.md, Channel/RESOLUTION.md, FiniteState/COMPARISON_G11.md and COMPARISON_G12.md, ThetaTail/THETA_INFRASTRUCTURE.md, Onset/PROOF_STEPS.md, Interval/CERTIFICATE_SPEC.md, IntervalKernel/NOTES.md, Final/NOTES.md).
- Traces: `deptrace*.tsv` (declaration-level forbidden-module / forbidden-name tracer) in Final, Assembly, Eleven, Transfer, Section3, G00.
- Axiom logs: Circle/axioms.out, ThetaTail/axioms_*.log, Transfer/final_axioms.log, FiniteState/axioms_report.txt, G00/baseline_axioms_28.txt and the TSV traces carrying an axioms column.
- Route audit of 2026-10-10: the 22 formerly unknown proof_route_alignment cells were filled by reading the written proofs and the Lean declarations (including the legacy lemmas they invoke); no lean, lake or `#print axioms` was run. No cell is `unknown - not audited` any longer.
