# Correspondence: manuscript ↔ Lean

This file maps the manuscript *Sharp Beckner–Onofri inequalities on the flat torus:
coefficients, defects, and phase transitions* (Y. Lei and M. Rosenzweig, version of
6 October 2026) to the Lean development, so that a reader of the paper can locate where each
result is proved. Result numbers follow that version; labels are the LaTeX labels.

* **Comparator surface.** `Challenge.lean` restates Theorems 1.1, 1.2 and 1.3 with
  Mathlib-only definitions; `Solution.lean` proves each of its 28 declarations from the
  library. Only this surface is compared by Comparator (`comparator.json`).
* **Library.** The numbered results have formal counterparts listed below. Declarations
  `BecknerOnofri.PaperResult.*` are in `BecknerOnofri/PaperResults.lean`,
  `BecknerOnofri.Target.*` in `BecknerOnofri/Targets.lean` and `BecknerOnofri.Paper2.*` in
  `BecknerOnofri/Paper2/Proofs.lean`; each is proved from the development in
  `BecknerOnofri/` and `Legacy/` (a historical namespace of the same development, not an
  external assumption). These counterparts are not on the Comparator path.
* **Status.** All declarations below are proved, with no `sorry` and no axioms beyond
  `propext`, `Classical.choice` and `Quot.sound`.

## The Comparator surface

| Manuscript | `Challenge.lean` declaration | Proved from |
|---|---|---|
| Theorem 1.1, eq:intro-low-dual for all densities | `BecknerOnofri.low_dim_entropy_inequality` | `BecknerOnofri.Paper2.low_density_extended` |
| Theorem 1.1, eq:intro-low-primal | `BecknerOnofri.low_dim_beckner_onofri` | `BecknerOnofri.Target.low_potential_endpoint` |
| Theorem 1.1, sharpness of eq:intro-low-primal | `BecknerOnofri.low_dim_coefficient_sharp` | `BecknerOnofri.Target.low_coefficient_sharp` |
| Theorem 1.1, equality for d = 1, family eq:intro-circle-extremizers | `BecknerOnofri.circle_beckner_onofri_eq_iff` | `BecknerOnofri.Target.low_circle_potential` |
| Theorem 1.1, equality for d = 1, family eq:intro-circle-poisson | `BecknerOnofri.circle_entropy_eq_iff` | `BecknerOnofri.Target.low_circle_density` |
| Theorem 1.1, equality for 2 ≤ d ≤ 10 (densities) | `BecknerOnofri.low_dim_entropy_eq_iff` | `BecknerOnofri.Target.low_density_rigidity` |
| Theorem 1.1, equality for 2 ≤ d ≤ 10 (potentials) | `BecknerOnofri.low_dim_beckner_onofri_eq_iff` | `BecknerOnofri.Target.low_potential_rigidity` |
| eq:intro-low-coefficient-consequence, pressure | `BecknerOnofri.low_dim_pressure_eq` | `BecknerOnofri.Target.low_pressure_formula` |
| eq:intro-low-coefficient-consequence, defect | `BecknerOnofri.low_dim_defect_eq` | `BecknerOnofri.Target.low_coefficient_formula` |
| eq:intro-low-coefficient-consequence, β_gm(d) = 2d | `BecknerOnofri.low_dim_globalTransition` | `BecknerOnofri.Target.low_pressure_formula`, `general_pressure_zero_set`, `general_threshold_bounds` |
| Theorem 1.2, the constant C₁₁ of eq:intro-rho-star | `BecknerOnofri.eleven_profile_constant` | proved directly (Γ(11) = 10!, Γ(11/2) = 945√π/32) |
| Theorem 1.2, eq:intro-rho-star and eq:intro-d11-certificate | `BecknerOnofri.eleven_competitor` | `BecknerOnofri.Target.eleven_profile_regular`, `eleven_competitor_entropy`, `eleven_competitor_energy` |
| Theorem 1.2, eq:intro-d11-threshold, first part | `BecknerOnofri.eleven_spectral_pressure` | `BecknerOnofri.Target.eleven_spectral_pressure` |
| Theorem 1.2, eq:intro-d11-threshold, second part | `BecknerOnofri.eleven_globalTransition_bounds` | `BecknerOnofri.Target.eleven_transition_interval` |
| Theorem 1.2, coexistence | `BecknerOnofri.eleven_coexistence` | `BecknerOnofri.Target.eleven_coexistence` |
| Theorem 1.2, positive Hessian at the uniform density | `BecknerOnofri.eleven_uniform_hessian_pos` | `BecknerOnofri.Target.eleven_uniform_hessian` |
| Theorem 1.2, corner of P₁₁ | `BecknerOnofri.eleven_pressure_corner` | `BecknerOnofri.Target.eleven_pressure_corner` |
| Theorem 1.2 and the following discussion, P′₋ = 0 < P′₊ | `BecknerOnofri.eleven_pressure_derivative_jump` | `BecknerOnofri.Target.eleven_pressure_derivative_jump` |
| Theorem 1.2, corner of C₁₁ | `BecknerOnofri.eleven_defect_corner` | `BecknerOnofri.Target.eleven_defect_corner` |
| Theorem 1.3, eq:intro-high-dual for all densities | `BecknerOnofri.high_dim_entropy_inequality` | `BecknerOnofri.Paper2.high_density_extended` |
| Theorem 1.3, equality in eq:intro-high-dual | `BecknerOnofri.high_dim_entropy_eq_iff` | `BecknerOnofri.Target.density_rigidity` |
| Theorem 1.3, eq:intro-high-primal | `BecknerOnofri.high_dim_beckner_onofri` | `BecknerOnofri.Target.potential_endpoint` |
| Theorem 1.3, equality in eq:intro-high-primal | `BecknerOnofri.high_dim_beckner_onofri_eq_iff` | `BecknerOnofri.Target.potential_rigidity` |
| Theorem 1.3, eq:intro-high-threshold | `BecknerOnofri.high_dim_thresholds` | `BecknerOnofri.Target.pressure_threshold`, `coefficient_threshold` |
| eq:intro-kappa, κ_d > 0 | `BecknerOnofri.kappa_pos` | `BecknerOnofri.Target.kappa_positive` |
| Theorem 1.3, eq:intro-onset-range–eq:intro-onset-branch | `BecknerOnofri.high_dim_onset_branch` | `BecknerOnofri.Target.full_branch_onset` |
| Theorem 1.3, eq:intro-pressure-onset | `BecknerOnofri.high_dim_pressure_onset` | `BecknerOnofri.Target.pressure_onset` |
| Theorem 1.3, eq:intro-C-onset | `BecknerOnofri.high_dim_defect_onset` | `BecknerOnofri.Target.coefficient_onset` |

# All numbered results

## Section 2: common variational and structural reduction

| Result | Label | Lean declarations |
|---|---|---|
| Lemma 2.1 (Finite entropy controls the logarithmic interaction) | `lem:section2-finite-entropy-energy` | `BecknerOnofri.PaperResult.finite_entropy_energy`, `BecknerOnofri.PaperResult.finite_entropy_physical_bound`, `BecknerOnofri.PaperResult.heat_regularization_smooth`, `BecknerOnofri.PaperResult.heat_interaction_limit`, `BecknerOnofri.PaperResult.heat_entropy_limit`, `BecknerOnofri.PaperResult.heat_l1_limit` |
| Proposition 2.2 (Exact coefficient–pressure duality) | `prop:section2-coefficient-pressure-duality` | `BecknerOnofri.PaperResult.pressure_duality`, `BecknerOnofri.PaperResult.pressure_smooth_sup` |
| Lemma 2.3 (Concentration and first-shell tests) | `lem:section2-universal-obstructions` | `BecknerOnofri.PaperResult.pressure_concentration_divergence`, `BecknerOnofri.PaperResult.coefficient_concentration_divergence`, `BecknerOnofri.PaperResult.critical_adams_bound`, `BecknerOnofri.PaperResult.pressure_at_collapse_finite`, `BecknerOnofri.PaperResult.coefficient_at_collapse_finite`, `BecknerOnofri.PaperResult.pressure_sharpness`, `BecknerOnofri.PaperResult.coefficient_sharpness` |
| Proposition 2.4 (Basic geometry of the pressure and defect) | `prop:section2-basic-curve-geometry` | `BecknerOnofri.PaperResult.general_pressure_geometry`, `BecknerOnofri.PaperResult.general_coefficient_geometry`, `BecknerOnofri.PaperResult.interaction_physical_positive`, `BecknerOnofri.PaperResult.general_transition_quotient`, `BecknerOnofri.Target.general_pressure_zero_set`, `BecknerOnofri.PaperResult.general_coefficient_zero_set`, `BecknerOnofri.Target.general_threshold_bounds` |
| Lemma 2.5 (Primal–dual gap identities) | `prop:section2-gap-identities` | `BecknerOnofri.PaperResult.finite_entropy_green_potential`, `BecknerOnofri.PaperResult.primal_gap_identity`, `BecknerOnofri.PaperResult.dual_gap_identity` |
| Corollary 2.6 (Extremizer correspondence and Euler–Lagrange equation) | `cor:section2-extremizer-correspondence` | `BecknerOnofri.PaperResult.primal_extremizer_correspondence`, `BecknerOnofri.PaperResult.dual_extremizer_correspondence`, `BecknerOnofri.PaperResult.optimizer_euler_equation`, `BecknerOnofri.PaperResult.optimizer_smooth_kirkwood` |
| Proposition 2.7 (Subcritical attainment and regularity) | `prop:section2-subcritical-attainment` | `BecknerOnofri.PaperResult.subcritical_dual_attainment`, `BecknerOnofri.PaperResult.primal_extremizer_correspondence`, `BecknerOnofri.PaperResult.dual_extremizer_correspondence`, `BecknerOnofri.PaperResult.optimizer_smooth_kirkwood` |
| Lemma 2.8 (Circle rearrangement) | `lem:circle-rearrangement` | `BecknerOnofri.PaperResult.circle_rearrangement` |
| Lemma 2.9 | `lem:fractional` | `BecknerOnofri.PaperResult.fractional_intertwining`, `BecknerOnofri.Paper2.physical_fractional_intertwining`, `BecknerOnofri.Paper2.physical_operatorGraph_transport`, `BecknerOnofri.Paper2.physical_spectralPower_domain`, `BecknerOnofri.Paper2.physical_measure_transport`, `BecknerOnofri.Paper2.physical_form_transport`, `BecknerOnofri.Paper2.physical_potential` |
| Lemma 2.10 (Positive Taylor expansion) | `lem:positive-bernstein` | `BecknerOnofri.PaperResult.closed_cube_positive_taylor` |
| Proposition 2.11 | `prop:cosine-all` | `BecknerOnofri.PaperResult.smooth_monotone_euler_cosine` |
| Lemma 2.12 (Entropy-preserving selection of subcritical minimizers) | `lem:selection-full-entropy-domain` | `BecknerOnofri.PaperResult.prescribed_equimeasurable_selection`, `BecknerOnofri.PaperResult.prescribed_canonical_selection`, `BecknerOnofri.PaperResult.subcritical_dual_attainment`, `BecknerOnofri.PaperResult.optimizer_smooth_kirkwood` |

## Section 3: dimensions two through ten

| Result | Label | Lean declarations |
|---|---|---|
| Proposition 3.1 | `prop:scalar` | `BecknerOnofri.PaperResult.low_scalar_gap` |
| Lemma 3.2 | `lem:E1-bound` | `BecknerOnofri.PaperResult.e1_bound` |
| Lemma 3.3 | `lem:theta-integral-certificate` | `BecknerOnofri.PaperResult.low_theta_integral`, `BecknerOnofri.PaperResult.low_theta_dimension_bound`, `BecknerOnofri.PaperResult.eleven_theta_integral`, `BecknerOnofri.PaperResult.twelve_theta_integral` |
| Lemma 3.4 | `lem:hypergeometric` | `BecknerOnofri.PaperResult.low_hypergeometric_identity`, `BecknerOnofri.PaperResult.low_harmonic_identity` |
| Lemma 3.5 | `lem:circle-entropy` | `BecknerOnofri.PaperResult.low_density_endpoint`, `BecknerOnofri.Target.low_circle_density`, `BecknerOnofri.PaperResult.circle_entropy_full_domain` |
| Lemma 3.6 (Free energy of mixtures) | `lem:mixture-transfer` | `BecknerOnofri.PaperResult.mixture_transfer` (at β = 2d) |
| Proposition 3.7 | `prop:equality` | `BecknerOnofri.Target.low_density_rigidity`, `BecknerOnofri.Target.low_potential_rigidity` |

## Section 4: dimension eleven

| Result | Label | Lean declarations |
|---|---|---|
| Proposition 4.1 | `prop:section4-entropy-bound` | `BecknerOnofri.Target.eleven_competitor_entropy`, `BecknerOnofri.PaperResult.eleven_competitor_entropy_fine` |
| Lemma 4.2 (Periodization and conditional entropy) | `lem:section4-periodization-entropy-identity` | `BecknerOnofri.PaperResult.eleven_profile_mass`, `BecknerOnofri.PaperResult.eleven_entropy_chain`, `BecknerOnofri.Target.eleven_profile_regular`, `BecknerOnofri.Paper2.periodization_derivatives_locally_uniform` |
| Lemma 4.3 (Euclidean entropy) | `lem:section4-euclidean-entropy` | `BecknerOnofri.PaperResult.student_beta_integral`, `BecknerOnofri.PaperResult.eleven_euclidean_entropy` |
| Lemma 4.4 (Entropy of the integer shift) | `lem:section4-lattice-label-entropy` | `BecknerOnofri.PaperResult.eleven_coordinate_marginal`, `BecknerOnofri.PaperResult.eleven_label_moment`, `BecknerOnofri.PaperResult.eleven_coordinate_label_entropy`, `BecknerOnofri.PaperResult.eleven_label_entropy_chain` |
| Lemma 4.5 (Fourier transform of the Euclidean profile) | `lem:section4-profile-fourier-transform` | `BecknerOnofri.PaperResult.eleven_half_integer_laplace`, `BecknerOnofri.PaperResult.eleven_euclidean_fourier`, `BecknerOnofri.PaperResult.eleven_periodized_fourier`, `BecknerOnofri.PaperResult.eleven_unscaled_fourier` |
| Proposition 4.6 | `d11:prop:scalar` | `BecknerOnofri.PaperResult.eleven_scalar_finite`, `BecknerOnofri.PaperResult.eleven_scalar_all`, `BecknerOnofri.PaperResult.eleven_theta_integral` |
| Lemma 4.7 (Local uniqueness of the uniform critical point) | `lem:section4-local-uniqueness` | `BecknerOnofri.PaperResult.eleven_local_uniqueness` |
| Proposition 4.8 (First-order coexistence at the global transition) | `prop:section4-first-order-coexistence` | `BecknerOnofri.Target.eleven_uniform_hessian`, `BecknerOnofri.Target.eleven_coexistence`, `BecknerOnofri.Target.eleven_pressure_corner`, `BecknerOnofri.Target.eleven_defect_corner` |
| Proposition 4.9 | `d11:thm:interval` | `BecknerOnofri.Target.eleven_transition_interval`, `BecknerOnofri.Target.eleven_competitor_energy`, `BecknerOnofri.PaperResult.eleven_uniform_unique` |

## Section 5: dimensions at least twelve

| Result | Label | Lean declarations |
|---|---|---|
| Proposition 5.1 | `prop:spectral-d12-base` | `BecknerOnofri.PaperResult.density_endpoint`, `BecknerOnofri.PaperResult.density_rigidity` |
| Lemma 5.2 | `lem:spectral-subset-entropy` | `BecknerOnofri.PaperResult.coordinate_marginal_entropy`, `BecknerOnofri.PaperResult.entropy_shearer_all_subsets` |
| Lemma 5.3 (One-dimensional summation) | `lem:spectral-slice` | `BecknerOnofri.PaperResult.spectral_slice` |
| Lemma 5.4 (Rectangular lattice sums) | `lem:spectral-rectangle` | `BecknerOnofri.PaperResult.rectangular_lattice` |
| Proposition 5.5 (Energy comparison for cosine-power mixtures) | `prop:spectral-marginal-energy` | `BecknerOnofri.PaperResult.cosine_mixture_deletion_energy`, `BecknerOnofri.PaperResult.cosine_mixture_subset_energy` |
| Proposition 5.7 (Transfer from dimension twelve) | `prop:spectral-dimension-transfer` | `BecknerOnofri.PaperResult.density_endpoint`, `BecknerOnofri.PaperResult.density_rigidity` |
| Corollary 5.8 (Spectral inequality and equality) | `cor:section5-high-endpoint` | `BecknerOnofri.PaperResult.density_endpoint`, `BecknerOnofri.PaperResult.density_rigidity`, `BecknerOnofri.PaperResult.potential_endpoint`, `BecknerOnofri.PaperResult.potential_rigidity`, `BecknerOnofri.PaperResult.pressure_threshold` |
| Lemma 5.9 (Symmetry of maximizers) | `lem:common-cubic` | `BecknerOnofri.PaperResult.all_optimizer_cubic_symmetry` |
| Proposition 5.10 (Global entropy estimate) | `prop:section5-global-entropy-gap` | `BecknerOnofri.PaperResult.global_entropy_gap` |
| Proposition 5.11 (The singular Fourier tail) | `prop:section5-singular-fourier-tail` | `BecknerOnofri.PaperResult.smooth_mixture_singular_tail` |
| Proposition 5.12 (Entropy comparison and the finite-state inequality) | `prop:section5-spin-entropy` | `BecknerOnofri.PaperResult.channel_entropy`, `BecknerOnofri.PaperResult.finite_state_inequality`, `BecknerOnofri.PaperResult.spin_mixture_feasible`, `BecknerOnofri.PaperResult.spin_channel_symmetry`, `BecknerOnofri.PaperResult.spin_exchangeable_entropy`, `BecknerOnofri.PaperResult.spin_exchangeable_energy` |
| Lemma 5.13 (Scalar tail bound) | `lem:section5-global-scalar-tail` | `BecknerOnofri.PaperResult.scalar_tail_bound` |
| Lemma 5.14 | `lem:section5-global-circle-remainder` | `BecknerOnofri.PaperResult.circle_entropy_remainder` |
| Lemma 5.15 | `lem:section5-global-convex-order` | `BecknerOnofri.PaperResult.circle_logconvex_comparison`, `BecknerOnofri.PaperResult.circle_entropy_rate_lower` |
| Lemma 5.16 | `lem:section5-global-gamma-entropy` | `BecknerOnofri.PaperResult.circle_gamma_actual_density` |
| Lemma 5.17 | `lem:section5-global-small-gamma` | `BecknerOnofri.PaperResult.small_gamma` |
| Lemma 5.18 (A Jensen remainder) | `lem:section5-jensen-remainder` | `BecknerOnofri.PaperResult.jensen_remainder` |
| Lemma 5.19 (Curvature on slices of fixed mean) | `lem:section5-global-curvature` | `BecknerOnofri.PaperResult.fixed_mean_curvature` |
| Lemma 5.20 | `lem:section5-scalar-pressure` | `BecknerOnofri.PaperResult.scalar_pressure`, `BecknerOnofri.PaperResult.pressure_reduction` |
| Lemma 5.21 (Quartic reduced functional) | `lem:section5-quartic-reduction` | `BecknerOnofri.PaperResult.first_shell_moments`, `BecknerOnofri.PaperResult.local_continuous_quartic_reduction`, `BecknerOnofri.PaperResult.local_sobolev_quadratic_slaving`, `BecknerOnofri.PaperResult.local_sobolev_analytic_graph` |
| Proposition 5.22 (Local critical branches) | `prop:section5-local-branches` | `BecknerOnofri.PaperResult.local_quartic_signs`, `BecknerOnofri.PaperResult.local_quartic_pressure_order`, `BecknerOnofri.PaperResult.local_fullmode_stationary_hessian`, `BecknerOnofri.PaperResult.local_supported_stationary_branch`, `BecknerOnofri.PaperResult.local_supported_energy_family`, `BecknerOnofri.PaperResult.local_equal_active_fourier_modes`, `BecknerOnofri.PaperResult.local_supported_classification`, `BecknerOnofri.PaperResult.local_proper_support_saddle`, `BecknerOnofri.PaperResult.local_fullmode_morse_bott`, `BecknerOnofri.PaperResult.local_stable_supported_classification`, `BecknerOnofri.PaperResult.local_active_squared_hessian` |
| Proposition 5.23 (Global minimizers and pressure onset) | `prop:section5-global-onset` | `BecknerOnofri.PaperResult.first_shell_order_parameter`, `BecknerOnofri.PaperResult.order_parameter_onset`, `BecknerOnofri.PaperResult.full_branch_onset`, `BecknerOnofri.PaperResult.pressure_onset` |
| Corollary 5.24 (Quadratic vanishing of the coefficient defect) | `cor:section5-defect-onset` | `BecknerOnofri.PaperResult.coefficient_onset`, `BecknerOnofri.PaperResult.pressure_derivative_at_threshold`, `BecknerOnofri.PaperResult.pressure_first_derivative_limits`, `BecknerOnofri.PaperResult.pressure_second_derivative_limits`, `BecknerOnofri.PaperResult.pressure_first_derivative_expansion`, `BecknerOnofri.PaperResult.pressure_second_derivative_expansion` |

Remark 5.6 (a counterexample for arbitrary densities) is not formalized.

## Differences between printed and formal statements

| Where | Manuscript | Lean |
|---|---|---|
| Theorems 1.1–1.3 | `‖ρ‖²_{Ḣ^{-d/2}}` with the constant `c_d` | `spectralEnergy ρ = (2π)^d ‖ρ‖²_{Ḣ^{-d/2}}` and `β_s(d) = (2π)^d/c_d`, so `c_d ‖ρ‖² = spectralEnergy ρ / β_s(d)` |
| eq:intro-low-dual, eq:intro-high-dual | all `ρ ∈ P_ac(𝕋ᵈ)` | `extendedEntropy ρ ∈ (-∞, ∞]`, equal to `Ent ρ` for finite entropy and `∞` otherwise |
| Theorems 1.1–1.3, equality | finite-entropy densities, constant potentials | the same, with equality of functions almost everywhere |
| Theorem 1.2, eq:intro-rho-star | `C₁₁ = Γ(11)/(π^{11/2}Γ(11/2))` | the profile uses `122880/π⁶`; `eleven_profile_constant` proves the two agree |
| Theorem 1.2, corners | corners of `P₁₁` at `β_gm(11)` and of `C₁₁` at `A_gm(11)` | finiteness near the point and non-differentiability of the real-valued function; for `P₁₁` also the one-sided derivatives `0 < p` |
| Theorem 1.2, Hessian | strictly positive at the uniform density | `d²/dt² 𝓔_β(1 + t h)|₀ ≥ (1 - β_gm/β_s) ∫ h²` for smooth mean-zero `h`, with `1 - β_gm/β_s > 0` |
| Theorem 1.3, onset | `O_{H^s}(δ)` for every fixed `s`, uniformly in `x₀` | explicit constants for each `s ≥ 0`, uniformly in `x₀`; the branch is also a Morse–Bott local maximum of the potential functional |
| Lemma 3.3 | `J_d ≤ …` for convergent integrals | strict bounds `J_10 < 1.64`, `J_11 < 5/2`, `J_12 < 3.29` for Bochner integrals; integrability is proved separately |
| Lemma 3.6 | every `β > 0` | the case `β = 2d`, as used in Proposition 3.7 |
| Proposition 2.7 | the attaining potential is smooth | the smooth representative is proved in `BecknerOnofri.RawOptimizerCorrespondence` but not restated |
| Proposition 2.11 | pointwise cosine mixture | almost-everywhere identity; the pointwise form is proved in `BecknerOnofri.GenericCosineRepresentation` |
| Proposition 5.12(i) | Fourier sums over `n ≥ 3` | the same, as `tsum`s together with their summability |
| Lemma 5.18 | `E ψ(S) - ψ(t) ≥ η(t)(E I_B(S) - I_B(t))` | the pointwise Bregman inequality `D_ψ(s,t) ≥ η(t) D_{I_B}(s,t)`, integrated in `ConditionalEntropy.conditional_jensen_remainder` |
| Lemma 5.20 | `0 < t ≤ 0.99` | `1/16 ≤ t ≤ 0.99`; the range `t ≤ 1/16` of Proposition 5.12(ii) is covered by the analytic small-mean estimate `Spin.small_mean_spin_inequality` |
| Lemma 2.9, proof | displayed cutoff rate `O(δ^{2m-1})` | closure proved by form-norm convergence instead |

## Proof routes

Where the formal proof differs from the printed one, the route is complete and checked:

* **Lemma 5.13.** For `3 ≤ n ≤ 50` the shell coefficients `p_q` are computed exactly for
  `q < 3n + 10` and the remaining mass `(Σ_j C(2n,n+|j|))^{12} - Σ_{q<Q} p_q` is charged the
  weight `Q^{-6}`; the manuscript computes all `p_q`. The bound for `n = 2` is the exact
  rational value. For `n > 50` the proof is the manuscript's.
* **Lemma 3.3 (d = 12).** The decay rate `π` is replaced by `3.1415 ≤ π` and `e^{-π}` by
  `0.04322`; the resulting rational bound is `3.2859 < 3.29`.
* **Proposition 5.12(ii), small means.** For `0 ≤ t ≤ 1/16` the formal proof uses an
  analytic estimate `F(p) + 12·(3/40)t⁴ ≥ t⁴/50` (with `ψ(t) ≥ 3t⁴/40` and the η-term `≥ 0`)
  instead of the origin jet and the Taylor-model cells below `1/16`.
* **Lemma 5.20.** `𝓑(t) - t⁴/200` is enclosed on 127 consecutive cells of `[1/16, 0.99]` by
  first-order Taylor models in fixed point (`2^{-100}`, outward rounding) with verified
  exponential and logarithm; the manuscript uses order-4 Taylor models on 78 cells of
  `[1/500, 0.99]` and the origin jet below `1/500`.
* **Lemma 5.17.** The barrier comparison is carried out in the Bessel variable `h`
  (`h̲(R(h)) ≤ h` by a first-contact argument) rather than for the inverse function; the
  weight and entropy-tail bounds are compared with truncated series by Bernstein checks; the
  `g₁` numerator is used in an unreduced form of degree 62.
* **Joint spin moments on count classes** (used for eq:section5-global-cube-energy and
  eq:section5-spin-count-identities). `∑_{|σ|=j} ∏_{i∈S} σ_i` is read off from the generating
  function `∏_i (x + c_i) = (x-1)^{|S|}(x+1)^{12-|S|}`; only the binomial coefficients are
  checked numerically, not the `2^{12}` configurations.
* **Proposition 5.10.** Both the selected-maximizer form used for Theorem 1.3
  (`SelectedNumericalModel.selected_entropy_gap`) and the general form for every density
  satisfying the shape hypotheses (`ShapeEntropy.global_shape_entropy`) are proved.
* **Propositions 3.1 and 4.6, finite indices.** The bound eq:finite-scalar-truncation is
  used with `Q = 64` instead of `Q = 80`. The coefficients `p_q`, `q ≤ 64`, are computed in
  the kernel by truncated convolution of coefficient lists, and the remaining mass is
  charged the weight `65^{-d/2}`.
* **Lower dimensions.** In dimension 2 the finite scalar comparisons cover `n = 1, 2, 3`
  and an analytic Gaussian estimate covers `n ≥ 4`; several low-dimensional certificates use
  the scale `2^40` instead of `2^80`; `J_10` and `J_11` are bounded with rational Laplace
  majorants (with the weight `r^{-1} ≤ 1`).

All finite arithmetic is checked by the Lean kernel (`decide +kernel`) and connected to the
real statements by proved lemmas; no external computation is assumed.
