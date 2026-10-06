# Correspondence: manuscript ↔ Lean

This file maps the manuscript *Sharp Beckner–Onofri inequalities on the flat torus:
coefficients, defects, and phase transitions* (Y. Lei and M. Rosenzweig, manuscript dated
1 October 2026) to the Lean development, so that a reader of the paper can locate where
each result is proved.

* **Comparator surface.** `Challenge.lean` restates Theorems 1.1, 1.2 and 1.3 with
  Mathlib-only definitions; `Solution.lean` proves each of its 27 declarations from the
  library. Only this surface is compared by Comparator (`comparator.json`).
* **Library.** Every numbered lemma, proposition, corollary and theorem of the manuscript
  (51 results) has formal counterparts in the library, listed below. Declarations
  `BecknerOnofri.Target.*` are in `BecknerOnofri/Targets.lean` and
  `BecknerOnofri.Paper2.*` in `BecknerOnofri/Paper2/Proofs.lean`; each is proved from
  the development in `BecknerOnofri/` and `Legacy/` (a historical namespace of the same
  development, not an external assumption). The library counterparts are not part of
  the Comparator surface, so they should be read in their source files.
* **Status.** All declarations below are proved, with no `sorry` and no axioms beyond
  `propext`, `Classical.choice` and `Quot.sound`.

## The Comparator surface

| Manuscript | `Challenge.lean` declaration | Proved from |
|---|---|---|
| Theorem 1.1, (1.23) for all densities | `BecknerOnofri.low_dim_entropy_inequality` | `BecknerOnofri.Paper2.low_density_extended` |
| Theorem 1.1, (1.22) | `BecknerOnofri.low_dim_beckner_onofri` | `BecknerOnofri.Target.low_potential_endpoint` |
| Theorem 1.1, sharpness of (1.22) | `BecknerOnofri.low_dim_coefficient_sharp` | `BecknerOnofri.Target.low_coefficient_sharp` |
| Theorem 1.1, equality for d = 1, family (1.19) | `BecknerOnofri.circle_beckner_onofri_eq_iff` | `BecknerOnofri.Target.low_circle_potential` |
| Theorem 1.1, equality for d = 1, family (1.20) | `BecknerOnofri.circle_entropy_eq_iff` | `BecknerOnofri.Target.low_circle_density` |
| Theorem 1.1, equality for 2 ≤ d ≤ 10 (densities) | `BecknerOnofri.low_dim_entropy_eq_iff` | `BecknerOnofri.Target.low_density_rigidity` |
| Theorem 1.1, equality for 2 ≤ d ≤ 10 (potentials) | `BecknerOnofri.low_dim_beckner_onofri_eq_iff` | `BecknerOnofri.Target.low_potential_rigidity` |
| (1.24), pressure | `BecknerOnofri.low_dim_pressure_eq` | `BecknerOnofri.Target.low_pressure_formula` |
| (1.24), defect | `BecknerOnofri.low_dim_defect_eq` | `BecknerOnofri.Target.low_coefficient_formula` |
| (1.24), β_gm(d) = 2d | `BecknerOnofri.low_dim_globalTransition` | `BecknerOnofri.Target.low_pressure_formula`, `general_pressure_zero_set`, `general_threshold_bounds` |
| Theorem 1.2, (1.26)–(1.27) | `BecknerOnofri.eleven_competitor` | `BecknerOnofri.Target.eleven_profile_regular`, `eleven_competitor_entropy`, `eleven_competitor_energy` |
| Theorem 1.2, (1.28), first part | `BecknerOnofri.eleven_spectral_pressure` | `BecknerOnofri.Target.eleven_spectral_pressure` |
| Theorem 1.2, (1.28), second part | `BecknerOnofri.eleven_globalTransition_bounds` | `BecknerOnofri.Target.eleven_transition_interval` |
| Theorem 1.2, coexistence | `BecknerOnofri.eleven_coexistence` | `BecknerOnofri.Target.eleven_coexistence` |
| Theorem 1.2, positive Hessian at the uniform density | `BecknerOnofri.eleven_uniform_hessian_pos` | `BecknerOnofri.Target.eleven_uniform_hessian` |
| Theorem 1.2, corner of P₁₁ | `BecknerOnofri.eleven_pressure_corner` | `BecknerOnofri.Target.eleven_pressure_corner` |
| Theorem 1.2 and the following discussion, P'₋ = 0 < P'₊ | `BecknerOnofri.eleven_pressure_derivative_jump` | `BecknerOnofri.Target.eleven_pressure_derivative_jump` |
| Theorem 1.2, corner of C₁₁ | `BecknerOnofri.eleven_defect_corner` | `BecknerOnofri.Target.eleven_defect_corner` |
| Theorem 1.3, (1.30) for all densities | `BecknerOnofri.high_dim_entropy_inequality` | `BecknerOnofri.Paper2.high_density_extended` |
| Theorem 1.3, equality in (1.30) | `BecknerOnofri.high_dim_entropy_eq_iff` | `BecknerOnofri.Target.density_rigidity` |
| Theorem 1.3, (1.31) | `BecknerOnofri.high_dim_beckner_onofri` | `BecknerOnofri.Target.potential_endpoint` |
| Theorem 1.3, equality in (1.31) | `BecknerOnofri.high_dim_beckner_onofri_eq_iff` | `BecknerOnofri.Target.potential_rigidity` |
| Theorem 1.3, (1.32) | `BecknerOnofri.high_dim_thresholds` | `BecknerOnofri.Target.pressure_threshold`, `coefficient_threshold` |
| (1.29), κ_d > 0 | `BecknerOnofri.kappa_pos` | `BecknerOnofri.Target.kappa_positive` |
| Theorem 1.3, (1.33)–(1.35) | `BecknerOnofri.high_dim_onset_branch` | `BecknerOnofri.Target.full_branch_onset` |
| Theorem 1.3, (1.36) | `BecknerOnofri.high_dim_pressure_onset` | `BecknerOnofri.Target.pressure_onset` |
| Theorem 1.3, (1.37) | `BecknerOnofri.high_dim_defect_onset` | `BecknerOnofri.Target.coefficient_onset` |

Equation numbers refer to the manuscript.

# All numbered results

## Introduction: main results

| Result | Label | Lean declarations |
|–-|–-|–-|
| Theorem 1.1 (Dimensions 1 ≤ d ≤ 10) | `thm:intro-low-dimensional` | `BecknerOnofri.Target.low_density_endpoint`, `BecknerOnofri.Target.low_potential_endpoint`, `BecknerOnofri.Target.low_density_rigidity`, `BecknerOnofri.Target.low_potential_rigidity`, `BecknerOnofri.Target.low_circle_potential`, `BecknerOnofri.Target.low_circle_density`, `BecknerOnofri.Target.low_coefficient_sharp`, `BecknerOnofri.Target.low_pressure_formula`, `BecknerOnofri.Target.low_coefficient_formula`, `BecknerOnofri.Target.low_physical_density_endpoint`, `BecknerOnofri.Paper2.low_density_extended` |
| Theorem 1.2 (Dimension d = 11) | `thm:intro-d11` | `BecknerOnofri.Target.eleven_profile_regular`, `BecknerOnofri.Target.eleven_competitor_entropy`, `BecknerOnofri.Target.eleven_competitor_energy`, `BecknerOnofri.Target.eleven_spectral_pressure`, `BecknerOnofri.Target.eleven_transition_interval`, `BecknerOnofri.Target.eleven_uniform_unique`, `BecknerOnofri.Target.eleven_coexistence`, `BecknerOnofri.Target.eleven_uniform_hessian`, `BecknerOnofri.Target.eleven_pressure_corner`, `BecknerOnofri.Target.eleven_defect_corner` |
| Theorem 1.3 (Dimensions d ≥ 12) | `thm:intro-high-dimensional` | `BecknerOnofri.Target.density_endpoint`, `BecknerOnofri.Target.density_rigidity`, `BecknerOnofri.Target.potential_endpoint`, `BecknerOnofri.Target.potential_rigidity`, `BecknerOnofri.Target.pressure_threshold`, `BecknerOnofri.Target.coefficient_threshold`, `BecknerOnofri.Target.kappa_positive`, `BecknerOnofri.Target.full_branch_onset`, `BecknerOnofri.Target.pressure_onset`, `BecknerOnofri.Target.coefficient_onset`, `BecknerOnofri.Paper2.high_density_extended` |

## Section 2: common variational and structural reduction

| Result | Label | Lean declarations |
|–-|–-|–-|
| Lemma 2.1 (Finite entropy controls the logarithmic interaction) | `lem:section2-finite-entropy-energy` | `BecknerOnofri.Target.finite_entropy_energy`, `BecknerOnofri.Target.finite_entropy_physical_bound`, `BecknerOnofri.Target.heat_regularization_smooth`, `BecknerOnofri.Target.heat_interaction_limit`, `BecknerOnofri.Target.heat_entropy_limit`, `BecknerOnofri.Target.heat_l1_limit` |
| Proposition 2.2 (Exact coefficient–pressure duality) | `prop:section2-coefficient-pressure-duality` | `BecknerOnofri.Target.pressure_duality`, `BecknerOnofri.Target.pressure_smooth_sup` |
| Lemma 2.3 (Concentration and first-shell tests) | `lem:section2-universal-obstructions` | `BecknerOnofri.Target.pressure_concentration_divergence`, `BecknerOnofri.Target.coefficient_concentration_divergence`, `BecknerOnofri.Target.critical_adams_bound`, `BecknerOnofri.Target.pressure_at_collapse_finite`, `BecknerOnofri.Target.coefficient_at_collapse_finite`, `BecknerOnofri.Target.pressure_sharpness`, `BecknerOnofri.Target.coefficient_sharpness` |
| Proposition 2.4 (Basic geometry of the pressure and defect) | `prop:section2-basic-curve-geometry` | `BecknerOnofri.Target.general_pressure_geometry`, `BecknerOnofri.Target.general_coefficient_geometry`, `BecknerOnofri.Target.interaction_physical_positive`, `BecknerOnofri.Target.general_transition_quotient`, `BecknerOnofri.Target.general_pressure_zero_set`, `BecknerOnofri.Target.general_coefficient_zero_set`, `BecknerOnofri.Target.general_threshold_bounds` |
| Lemma 2.5 (Primal–dual gap identities) | `prop:section2-gap-identities` | `BecknerOnofri.Target.finite_entropy_green_potential`, `BecknerOnofri.Target.primal_gap_identity`, `BecknerOnofri.Target.dual_gap_identity` |
| Corollary 2.6 (Extremizer correspondence and Euler–Lagrange equation) | `cor:section2-extremizer-correspondence` | `BecknerOnofri.Target.primal_extremizer_correspondence`, `BecknerOnofri.Target.dual_extremizer_correspondence`, `BecknerOnofri.Target.optimizer_euler_equation`, `BecknerOnofri.Target.optimizer_smooth_kirkwood` |
| Proposition 2.7 (Subcritical attainment and regularity) | `prop:section2-subcritical-attainment` | `BecknerOnofri.Target.subcritical_dual_attainment`, `BecknerOnofri.Target.primal_extremizer_correspondence`, `BecknerOnofri.Target.dual_extremizer_correspondence`, `BecknerOnofri.Target.optimizer_smooth_kirkwood` |
| Lemma 2.8 (Circle rearrangement) | `lem:circle-rearrangement` | `BecknerOnofri.Target.circle_rearrangement` |
| Lemma 2.9 | `lem:fractional` | `BecknerOnofri.Target.fractional_intertwining`, `BecknerOnofri.Paper2.physical_fractional_intertwining`, `BecknerOnofri.Paper2.physical_operatorGraph_transport`, `BecknerOnofri.Paper2.physical_spectralPower_domain`, `BecknerOnofri.Paper2.physical_measure_transport`, `BecknerOnofri.Paper2.physical_form_transport`, `BecknerOnofri.Paper2.physical_potential` |
| Lemma 2.10 (Positive Taylor expansion) | `lem:positive-bernstein` | `BecknerOnofri.Target.closed_cube_positive_taylor` |
| Proposition 2.11 | `prop:cosine-all` | `BecknerOnofri.Target.smooth_monotone_euler_cosine` |
| Lemma 2.12 (Entropy-preserving selection of subcritical minimizers) | `lem:selection-full-entropy-domain` | `BecknerOnofri.Target.prescribed_equimeasurable_selection`, `BecknerOnofri.Target.prescribed_canonical_selection`, `BecknerOnofri.Target.subcritical_dual_attainment`, `BecknerOnofri.Target.optimizer_smooth_kirkwood` |

## Section 3: dimensions two through ten

| Result | Label | Lean declarations |
|–-|–-|–-|
| Proposition 3.1 | `prop:scalar` | `BecknerOnofri.Target.low_scalar_gap` |
| Lemma 3.2 | `lem:theta-integral-certificate` | `BecknerOnofri.Target.low_theta_integral`, `BecknerOnofri.Target.low_theta_dimension_bound` |
| Lemma 3.3 | `lem:hypergeometric` | `BecknerOnofri.Target.low_hypergeometric_identity`, `BecknerOnofri.Target.low_harmonic_identity` |
| Lemma 3.4 | `lem:circle-entropy` | `BecknerOnofri.Target.low_density_endpoint`, `BecknerOnofri.Target.low_circle_density`, `BecknerOnofri.Target.circle_entropy_full_domain` |
| Proposition 3.5 | `prop:equality` | `BecknerOnofri.Target.low_density_rigidity`, `BecknerOnofri.Target.low_potential_rigidity` |

## Section 4: dimension eleven

| Result | Label | Lean declarations |
|–-|–-|–-|
| Proposition 4.1 | `prop:section4-entropy-bound` | `BecknerOnofri.Target.eleven_competitor_entropy`, `BecknerOnofri.Target.eleven_competitor_entropy_fine` |
| Lemma 4.2 (Periodization and conditional entropy) | `lem:section4-periodization-entropy-identity` | `BecknerOnofri.Target.eleven_profile_mass`, `BecknerOnofri.Target.eleven_entropy_chain`, `BecknerOnofri.Target.eleven_profile_regular`, `BecknerOnofri.Paper2.periodization_derivatives_locally_uniform` |
| Lemma 4.3 (Euclidean entropy) | `lem:section4-euclidean-entropy` | `BecknerOnofri.Target.student_beta_integral`, `BecknerOnofri.Target.eleven_euclidean_entropy` |
| Lemma 4.4 (Entropy of the integer shift) | `lem:section4-lattice-label-entropy` | `BecknerOnofri.Target.eleven_coordinate_marginal`, `BecknerOnofri.Target.eleven_label_moment`, `BecknerOnofri.Target.eleven_coordinate_label_entropy`, `BecknerOnofri.Target.eleven_label_entropy_chain` |
| Lemma 4.5 (Fourier transform of the Euclidean profile) | `lem:section4-profile-fourier-transform` | `BecknerOnofri.Target.eleven_half_integer_laplace`, `BecknerOnofri.Target.eleven_euclidean_fourier`, `BecknerOnofri.Target.eleven_periodized_fourier`, `BecknerOnofri.Target.eleven_unscaled_fourier` |
| Proposition 4.6 | `d11:prop:scalar` | `BecknerOnofri.Target.eleven_scalar_finite`, `BecknerOnofri.Target.eleven_scalar_all`, `BecknerOnofri.Target.eleven_theta_integral` |
| Lemma 4.7 (Local uniqueness of the uniform critical point) | `lem:section4-local-uniqueness` | `BecknerOnofri.Target.eleven_local_uniqueness` |
| Proposition 4.8 (First-order coexistence at the global transition) | `prop:section4-first-order-coexistence` | `BecknerOnofri.Target.eleven_uniform_hessian`, `BecknerOnofri.Target.eleven_coexistence`, `BecknerOnofri.Target.eleven_pressure_corner`, `BecknerOnofri.Target.eleven_defect_corner` |
| Proposition 4.9 | `d11:thm:interval` | `BecknerOnofri.Target.eleven_transition_interval`, `BecknerOnofri.Target.eleven_competitor_energy`, `BecknerOnofri.Target.eleven_uniform_unique` |

## Section 5: dimensions at least twelve

| Result | Label | Lean declarations |
|–-|–-|–-|
| Proposition 5.1 | `prop:spectral-d12-base` | `BecknerOnofri.Target.density_endpoint`, `BecknerOnofri.Target.density_rigidity` |
| Lemma 5.2 | `lem:spectral-subset-entropy` | `BecknerOnofri.Target.coordinate_marginal_entropy`, `BecknerOnofri.Target.entropy_shearer_all_subsets` |
| Lemma 5.3 (One-dimensional summation) | `lem:spectral-slice` | `BecknerOnofri.Target.spectral_slice` |
| Lemma 5.4 (Rectangular lattice sums) | `lem:spectral-rectangle` | `BecknerOnofri.Target.rectangular_lattice` |
| Proposition 5.5 (Energy comparison for cosine-power mixtures) | `prop:spectral-marginal-energy` | `BecknerOnofri.Target.cosine_mixture_deletion_energy`, `BecknerOnofri.Target.cosine_mixture_subset_energy` |
| Proposition 5.7 (Transfer from dimension twelve) | `prop:spectral-dimension-transfer` | `BecknerOnofri.Target.density_endpoint`, `BecknerOnofri.Target.density_rigidity` |
| Corollary 5.8 (Spectral inequality and equality) | `cor:section5-high-endpoint` | `BecknerOnofri.Target.density_endpoint`, `BecknerOnofri.Target.density_rigidity`, `BecknerOnofri.Target.potential_endpoint`, `BecknerOnofri.Target.potential_rigidity`, `BecknerOnofri.Target.pressure_threshold` |
| Lemma 5.9 (Symmetry of maximizers) | `lem:common-cubic` | `BecknerOnofri.Target.all_optimizer_cubic_symmetry` |
| Proposition 5.10 (Global entropy estimate) | `prop:section5-global-entropy-gap` | `BecknerOnofri.Target.global_shape_entropy` |
| Proposition 5.11 (The singular Fourier tail) | `prop:section5-singular-fourier-tail` | `BecknerOnofri.Target.smooth_mixture_singular_tail` |
| Proposition 5.12 (Entropy comparison and the finite-state inequality) | `prop:section5-spin-entropy` | `BecknerOnofri.Target.spin_channel_gamma_entropy`, `BecknerOnofri.Target.spin_mixture_feasible`, `BecknerOnofri.Target.spin_channel_symmetry`, `BecknerOnofri.Target.spin_exchangeable_entropy`, `BecknerOnofri.Target.spin_exchangeable_energy`, `BecknerOnofri.Target.global_spin_entropy` |
| Lemma 5.13 (Scalar tail bound) | `lem:section5-global-scalar-tail` | `BecknerOnofri.Target.scalar_tail_all` |
| Lemma 5.14 | `lem:section5-global-circle-remainder` | `BecknerOnofri.Target.circle_entropy_remainder` |
| Lemma 5.15 | `lem:section5-global-convex-order` | `BecknerOnofri.Target.circle_logconvex_comparison`, `BecknerOnofri.Target.circle_entropy_rate_lower` |
| Lemma 5.16 | `lem:section5-global-gamma-entropy` | `BecknerOnofri.Target.circle_gamma_actual_density` |
| Lemma 5.17 | `lem:section5-global-small-gamma` | `BecknerOnofri.Target.circle_gamma_small` |
| Lemma 5.18 (Finite rational curvature check) | `lem:section5-global-curvature` | `BecknerOnofri.Target.spin_fixed_mean_curvature`, `BecknerOnofri.Target.spin_all_mean_curvature` |
| Corollary 5.19 (Global supporting parabolas) | `cor:section5-global-parabola` | `BecknerOnofri.Target.spin_supporting_parabola`, `BecknerOnofri.Target.spin_fixed_mean_entropy_convexity` |
| Lemma 5.20 (Quartic reduced functional) | `lem:section5-quartic-reduction` | `BecknerOnofri.Target.first_shell_moments`, `BecknerOnofri.Target.local_continuous_quartic_reduction`, `BecknerOnofri.Target.local_sobolev_quadratic_slaving`, `BecknerOnofri.Target.local_sobolev_analytic_graph` |
| Proposition 5.21 (Local critical branches) | `prop:section5-local-branches` | `BecknerOnofri.Target.local_quartic_signs`, `BecknerOnofri.Target.local_quartic_pressure_order`, `BecknerOnofri.Target.local_fullmode_stationary_hessian`, `BecknerOnofri.Target.local_supported_stationary_branch`, `BecknerOnofri.Target.local_supported_energy_family`, `BecknerOnofri.Target.local_equal_active_fourier_modes`, `BecknerOnofri.Target.local_supported_classification`, `BecknerOnofri.Target.local_proper_support_saddle`, `BecknerOnofri.Target.local_fullmode_morse_bott`, `BecknerOnofri.Target.local_stable_supported_classification`, `BecknerOnofri.Target.local_active_squared_hessian` |
| Proposition 5.22 (Global minimizers and pressure onset) | `prop:section5-global-onset` | `BecknerOnofri.Target.first_shell_order_parameter`, `BecknerOnofri.Target.order_parameter_onset`, `BecknerOnofri.Target.full_branch_onset`, `BecknerOnofri.Target.pressure_onset` |
| Corollary 5.23 (Quadratic vanishing of the coefficient defect) | `cor:section5-defect-onset` | `BecknerOnofri.Target.coefficient_onset`, `BecknerOnofri.Target.pressure_derivative_at_threshold`, `BecknerOnofri.Target.pressure_first_derivative_limits`, `BecknerOnofri.Target.pressure_second_derivative_limits`, `BecknerOnofri.Target.pressure_first_derivative_expansion`, `BecknerOnofri.Target.pressure_second_derivative_expansion` |

Remark 5.6 (a counterexample for arbitrary densities) is a remark, not a numbered result,
and is not formalized.

## Differences between printed and formal statements

| Where | Manuscript | Lean |
|---|---|---|
| Theorems 1.1–1.3 | `‖ρ‖²_{Ḣ^{-d/2}}` with the constant `c_d` | `spectralEnergy ρ = (2π)^d ‖ρ‖²_{Ḣ^{-d/2}}` and `β_s(d) = (2π)^d/c_d`, so `c_d ‖ρ‖² = spectralEnergy ρ / β_s(d)` |
| (1.23), (1.30) | all `ρ ∈ P_ac(𝕋ᵈ)` | `extendedEntropy ρ ∈ (-∞, ∞]`, equal to `Ent ρ` for finite entropy and `∞` otherwise |
| Theorems 1.1–1.3, equality | finite-entropy densities, constant potentials | the same, with equality of functions almost everywhere |
| Theorem 1.2, corners | corners of `P₁₁` at `β_gm(11)` and of `C₁₁` at `A_gm(11)` | finiteness near the point and non-differentiability of the real-valued function; for `P₁₁` also the one-sided derivatives `0 < p` |
| Theorem 1.2, Hessian | strictly positive at the uniform density | `d²/dt² 𝓔_β(1 + t h)|₀ ≥ (1 - β_gm/β_s) ∫ h²` for smooth mean-zero `h`, with `1 - β_gm/β_s > 0` |
| Theorem 1.3, onset | `O_{H^s}(δ)` for every fixed `s`, uniformly in `x₀` | explicit constants `η, C` for each `s ≥ 0`, uniformly in `x₀`; the branch is also a Morse–Bott local maximum of the potential functional |
| Lemma 3.2 | `J_10 ≤ 41/25` for a convergent integral | `J_10 < 41/25` for the Bochner integral; integrability is proved in `Legacy.BecknerOnofri.ThetaIntegrability` but not restated |
| Proposition 2.7 | the attaining potential is smooth | the smooth representative is proved in `BecknerOnofri.RawOptimizerCorrespondence` but not restated in the target |
| Proposition 2.11 | pointwise cosine mixture | almost-everywhere identity; the pointwise form is proved in `BecknerOnofri.GenericCosineRepresentation` |
| Lemma 2.9, proof | displayed cutoff rate `O(δ^{2m-1})` | closure proved by form-norm convergence instead |

## Proof routes

The finite computations follow a different but complete route in places: in dimension 2
the finite scalar comparisons cover `n = 1, 2, 3` and an analytic Gaussian estimate covers
`n ≥ 4`; several low-dimensional certificates use the scale `2^40` instead of `2^80`; and
the theta integral `J_10` is bounded with a rational Laplace majorant. All finite
arithmetic is checked by the Lean kernel (`decide +kernel`) and connected to the real
statements by proved lemmas; no external computation is assumed.
