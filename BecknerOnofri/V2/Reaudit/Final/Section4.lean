module

public import BecknerOnofri.V2.Final.Eleven
public import BecknerOnofri.V2.Reaudit.Compactness.All
public import BecknerOnofri.V2.Reaudit.ElevenBounds.All

@[expose] public section

/-! # Section 4 and Theorem 1.2 along the route of the manuscript

This module re-assembles Proposition 4.1, Proposition 4.9 and Theorem 1.2 from the route-aligned
pieces of the second pass, in the order of the printed proof, without using `V2.Eleven.Assembly`'s
`prop49`, `strict_lower_of_coexistence` or `theorem_1_2`, nor `HighDim.Eleven.coexistence`:

1. the quantitative gap `E_{β₀}(ρ) ≥ (1/44000) Σ_i P(L_i ≥ 1)` (`ElevenBounds.mixture_gap_eleven`), hence
   uniqueness of the uniform minimizer on `[0, 3543/200]` and the non-strict bound
   `3543/200 ≤ β_gm(11)` (`ElevenBounds.uniform_unique_quantitative`,
   `ElevenBounds.beta0_le_globalTransition_quantitative`);
2. the entropy bound for `ρ_*` through the lattice-label random variables
   (`ElevenBounds.entropy_bound_printed`) and the energy bound through the full shell expansion
   (`ElevenBounds.energy_bound_via_shells`), hence the upper bound `β_gm(11) < 2063/100`;
3. coexistence at `β_gm(11)` with strong `H^{11/2}` convergence (`Compactness.coexistence`), the Hessian,
   the corners and the derivative jumps (`Compactness.prop49_manuscript`);
4. only then, the strict lower bound `3543/200 < β_gm(11)`.

Each statement is the statement of the corresponding declaration of `V2.Eleven` / `V2.Final`
(`type_of%`), so that the final theorems keep their Challenge-vocabulary types. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.Final
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- The entropy bound `Ent(ρ_*) < 7305164/10⁶ + 17897/2520 + 1/600` of `d11:eq:entropy-upper`, where
the term `1/600` is the lattice-label entropy bound of `lem:section4-lattice-label-entropy`
(`ElevenBounds.condShannon_lt_printed`, random-variable form with the chain rule). -/
theorem periodized_entropy_fine_route (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    (torusEntropy ρ.value).toReal < 7305164 / 10 ^ 6 + 17897 / 2520 + 1 / 600 := by
  have hρ := V2.Eleven.finiteEntropy_of_value_eq ρ h
  rw [← entropy_eq_toReal_torusEntropy ρ hρ]
  obtain ⟨hid, -⟩ := ElevenBounds.entropy_bound_via_rv
    (P := V2.Eleven.JointLaw.lawEta) (X := (id : (Fin 11 → ℝ) → Fin 11 → ℝ)) ρ h
    measurable_id (V2.Eleven.JointLaw.canonical_space.1)
  have h2 := ElevenBounds.condShannon_lt_printed
    (P := V2.Eleven.JointLaw.lawEta) (X := (id : (Fin 11 → ℝ) → Fin 11 → ℝ))
    measurable_id (V2.Eleven.JointLaw.canonical_space.1)
  rw [hid]
  linarith [V2.Eleven.euclidean_entropy_fine]

/-- `β_gm(11) < 2063/100`, from the printed competitor bounds (entropy through the label random
variables, energy through the full shell expansion). -/
theorem transition_upper_route (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    VariationalCurves.globalTransition 11 < 2063 / 100 :=
  V2.Eleven.globalTransition_lt_of_competitor ρ (V2.Eleven.finiteEntropy_of_value_eq ρ h)
    (periodized_entropy_fine_route ρ h) (ElevenBounds.energy_bound_via_shells ρ h)

/-- **Proposition 4.9** (`prop:section4-first-order-coexistence`): coexistence with strong
convergence, Hessian, corners and derivative jumps, along the compactness argument of the print. -/
theorem prop49_route : type_of% V2.Eleven.prop49 := Compactness.prop49_manuscript

/-- **The strict lower bound** `3543/200 < β_gm(11)`: the non-strict bound and uniqueness of the uniform
minimizer on `[0, 3543/200]` (quantitative gap, no coexistence), then the nonuniform global minimizer at
`β_gm` of `Compactness.coexistence` excludes `β_gm = 3543/200`. -/
theorem strict_lower_route : V2.Eleven.beta0 < VariationalCurves.globalTransition 11 := by
  refine lt_of_le_of_ne ElevenBounds.beta0_le_globalTransition_quantitative fun heq => ?_
  obtain ⟨-, ρ, hmin, -, -, hnon⟩ := prop49_route.1
  have hβ0 : (0 : ℝ) ≤ VariationalCurves.globalTransition 11 := by
    rw [← heq]; unfold V2.Eleven.beta0; norm_num
  exact hnon ((ElevenBounds.uniform_unique_quantitative _ hβ0 heq.ge ρ hmin.1).1 hmin)

/-- **Proposition 4.1** (`d11:thm:interval`), in the printed order. -/
theorem prop41_route : type_of% V2.Eleven.prop41 := by
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile :=
    ⟨HighDim.Eleven.competitorDensity, rfl⟩
  exact ⟨⟨strict_lower_route, transition_upper_route ρ₀ hρ₀⟩,
    fun β hβ hβ0 ρ hρ => ElevenBounds.uniform_unique_quantitative β hβ hβ0 ρ hρ,
    fun ρ h => ElevenBounds.energy_bound_via_shells ρ h⟩

/-- **Theorem 1.2** (`thm:intro-d11`). -/
theorem theorem_1_2_route : type_of% V2.Eleven.theorem_1_2 := by
  have hv := prop41_route
  have h49 := prop49_route
  have hsm : SmoothOnTorus V2.Eleven.rhoStar.value := V2.Eleven.periodizedProfile_smooth_of_M_test
  refine ⟨⟨V2.Eleven.rhoStar_value, V2.Eleven.finiteEntropy_of_value_eq _ V2.Eleven.rhoStar_value, hsm,
      fun x => HighDim.Eleven.periodizedProfile_pos x,
      ElevenBounds.torusEntropy_bound_printed _ V2.Eleven.rhoStar_value,
      ElevenBounds.energy_bound_via_shells _ V2.Eleven.rhoStar_value⟩,
    ⟨V2.Eleven.defect_spectral_eq_pressure,
      V2.Eleven.spectral_pressure_gt_thirtieth _ V2.Eleven.rhoStar_value⟩,
    ⟨hv.1.1, hv.1.2, V2.Eleven.upper_lt_spectral.1, V2.Eleven.upper_lt_spectral.2⟩, h49.1, h49.2.1,
    h49.2.2.1.2, h49.2.2.2.1.2⟩

/-! ## Theorem 1.2 in the vocabulary of `Challenge.lean` -/

/-- The energy bound in `spectralEnergy` form, from the shell expansion. -/
theorem eleven_energy_gt_route (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ := by
  have hb := ElevenBounds.energy_bound_via_shells ρ h
  have hN : negSobolevEnergy ρ.value ≠ ⊤ := by
    intro htop
    rw [htop] at hb
    norm_num at hb
  rw [spectralEnergy_eq_mul_negSobolevEnergy, ← ENNReal.ofReal_toReal hN,
    ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by
    have : (0 : ℝ) < 14475384292906 / 10 ^ 12 := by norm_num
    nlinarith)).2 ?_
  have : (2 : ℝ) * (144753 / 10000) < 2 * (14475384292906 / 10 ^ 12) := by norm_num
  linarith

/-- **Theorem 1.2, (eq:intro-d11-certificate)**, manuscript bound `Ent(ρ_*) < 8653/600`. -/
theorem eleven_competitor_written_route : type_of% V2.Final.eleven_competitor_written := by
  have hv := V2.Eleven.rhoStar_value
  have h := theorem_1_2_route.1
  refine ⟨V2.Eleven.rhoStar, hv, h.2.2.1, h.2.2.2.1, h.2.1, ?_, eleven_energy_gt_route _ hv⟩
  rw [entropy_eq_toReal_torusEntropy _ h.2.1]
  exact h.2.2.2.2.1

/-- **Theorem 1.2, (eq:intro-d11-certificate)**, `Challenge.eleven_competitor` (repository entropy bound
`18011/1250`, stronger than the printed `8653/600`). -/
theorem eleven_competitor_route : type_of% V2.Final.eleven_competitor := by
  have hv := V2.Eleven.rhoStar_value
  have h := theorem_1_2_route.1
  refine ⟨V2.Eleven.rhoStar, hv, h.2.2.1, h.2.2.2.1, h.2.1, ?_, eleven_energy_gt_route _ hv⟩
  rw [entropy_eq_toReal_torusEntropy _ h.2.1]
  have := V2.Eleven.periodized_entropy_bound_of_repository _ hv
  norm_num at this ⊢
  exact this

theorem eleven_spectral_pressure_route : type_of% V2.Final.eleven_spectral_pressure :=
  theorem_1_2_route.2.1

theorem eleven_globalTransition_bounds_route : type_of% V2.Final.eleven_globalTransition_bounds :=
  theorem_1_2_route.2.2.1

theorem eleven_coexistence_route : type_of% V2.Final.eleven_coexistence :=
  theorem_1_2_route.2.2.2.1

theorem eleven_uniform_hessian_pos_route : type_of% V2.Final.eleven_uniform_hessian_pos :=
  theorem_1_2_route.2.2.2.2.1

theorem eleven_pressure_corner_route : type_of% V2.Final.eleven_pressure_corner :=
  ⟨prop49_route.2.2.1.1, theorem_1_2_route.2.2.2.2.2.1⟩

theorem eleven_pressure_derivative_jump_route : type_of% V2.Final.eleven_pressure_derivative_jump :=
  prop49_route.2.2.2.2.1

theorem eleven_defect_corner_route : type_of% V2.Final.eleven_defect_corner :=
  ⟨prop49_route.2.2.2.1.1, theorem_1_2_route.2.2.2.2.2.2⟩

#print axioms theorem_1_2_route
#print axioms prop41_route
#print axioms prop49_route
#print axioms strict_lower_route
#print axioms eleven_competitor_written_route
#print axioms eleven_competitor_route
#print axioms eleven_pressure_corner_route
#print axioms eleven_defect_corner_route

end BecknerOnofri.V2.Reaudit.Final
