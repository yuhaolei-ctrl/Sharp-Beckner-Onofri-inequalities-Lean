module

public import BecknerOnofri.V2.Eleven.All
public import BecknerOnofri.V2.Final.Low

@[expose] public section

/-! # Theorem 1.2 (dimension eleven) in the vocabulary of `Challenge.lean` (Final package)

Everything is derived from `V2.Eleven.theorem_1_2`, `V2.Eleven.prop41`, `V2.Eleven.prop49` and the
estimates of `V2.Eleven.Estimates`, except `eleven_profile_constant` (a Gamma-function computation).

Statement difference (`eleven_competitor`): `Challenge.eleven_competitor` asserts
`Ent(ρ_*) < 14.4088 = 18011/1250`, which is the *repository's* bound
(`HighDim.Eleven.competitor_entropy`, via `V2.Eleven.periodized_entropy_bound_of_repository`), strictly
stronger than the manuscript's Proposition 4.2 bound `8653/600 ≈ 14.4217`
(`eleven_competitor_written`, proved along the manuscript's chain `721/50 + 1/600`).  Both are stated. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Final
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- **Theorem 1.2, (eq:intro-rho-star).**  Statement as in `Challenge.eleven_profile_constant`. -/
theorem eleven_profile_constant :
    Real.Gamma 11 / (Real.pi ^ ((11 : ℝ) / 2) * Real.Gamma (11 / 2)) = 122880 / Real.pi ^ 6 := by
  have h11 : Real.Gamma 11 = 3628800 := by
    rw [show (11 : ℝ) = (10 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hhalf : Real.Gamma (11 / 2) = 945 / 32 * Real.sqrt Real.pi := by
    have h (x : ℝ) (hx : 0 < x) := Real.Gamma_add_one hx.ne'
    rw [show (11 / 2 : ℝ) = 9 / 2 + 1 by norm_num, h _ (by norm_num),
      show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, h _ (by norm_num),
      show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, h _ (by norm_num),
      show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, h _ (by norm_num),
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, h _ (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hpow : Real.pi ^ ((11 : ℝ) / 2) = Real.pi ^ 5 * Real.sqrt Real.pi := by
    rw [show (11 : ℝ) / 2 = (5 : ℕ) + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hs : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [h11, hhalf, hpow]
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le]
  ring

/-- The energy bound in `spectralEnergy` form. -/
theorem eleven_energy_gt (ρ : ProbabilityDensity 11)
    (h : ρ.value = HighDim.Eleven.periodizedProfile) :
    ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ := by
  have hb := Eleven.periodized_energy_bound ρ h
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

/-- **Theorem 1.2, (eq:intro-d11-certificate).**  Statement as in `Challenge.eleven_competitor`
(entropy bound `14.4088 = 18011/1250` of the repository, see the module docstring). -/
theorem eleven_competitor :
    ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      entropy ρ < (144088 : ℝ) / 10000 ∧
      ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ := by
  have hv := Eleven.rhoStar_value
  have h := Eleven.theorem_1_2.1
  refine ⟨Eleven.rhoStar, hv, h.2.2.1, h.2.2.2.1, h.2.1, ?_, eleven_energy_gt _ hv⟩
  rw [entropy_eq_toReal_torusEntropy _ h.2.1]
  have := Eleven.periodized_entropy_bound_of_repository _ hv
  norm_num at this ⊢
  exact this

/-- **Theorem 1.2, (eq:intro-d11-certificate), manuscript bound.**  The same certificate with the
manuscript's entropy bound `Ent(ρ_*) < 8653/600` (Proposition 4.2), proved along the manuscript's chain. -/
theorem eleven_competitor_written :
    ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      entropy ρ < (8653 : ℝ) / 600 ∧
      ENNReal.ofReal (2 * ((144753 : ℝ) / 10000)) < spectralEnergy ρ := by
  have hv := Eleven.rhoStar_value
  have h := Eleven.theorem_1_2.1
  refine ⟨Eleven.rhoStar, hv, h.2.2.1, h.2.2.2.1, h.2.1, ?_, eleven_energy_gt _ hv⟩
  rw [entropy_eq_toReal_torusEntropy _ h.2.1]
  exact h.2.2.2.2.1

/-- **Theorem 1.2, (eq:intro-d11-threshold).**  Statement as in `Challenge.eleven_spectral_pressure`
(`(1/30 : EReal)` is definitionally the cast of `(1/30 : ℝ)`). -/
theorem eleven_spectral_pressure :
    coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) ∧
      (1 / 30 : EReal) < pressure 11 (spectralThreshold 11) :=
  Eleven.theorem_1_2.2.1

/-- **Theorem 1.2, (eq:intro-d11-threshold).**  Statement as in `Challenge.eleven_globalTransition_bounds`. -/
theorem eleven_globalTransition_bounds :
    (3543 : ℝ) / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100 ∧
      (2063 : ℝ) / 100 < spectralThreshold 11 ∧ spectralThreshold 11 < 22 :=
  Eleven.theorem_1_2.2.2.1

/-- **Theorem 1.2, coexistence.**  Statement as in `Challenge.eleven_coexistence`. -/
theorem eleven_coexistence :
    IsGlobalMinimizer (VariationalCurves.globalTransition 11) (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11,
        IsGlobalMinimizer (VariationalCurves.globalTransition 11) ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ (ρ.value =ᵐ[torusMeasure 11] fun _ => 1) :=
  Eleven.theorem_1_2.2.2.2.1

/-- **Theorem 1.2, local stability.**  Statement as in `Challenge.eleven_uniform_hessian_pos`. -/
theorem eleven_uniform_hessian_pos :
    0 < 1 - VariationalCurves.globalTransition 11 / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - VariationalCurves.globalTransition 11 / spectralThreshold 11) *
            (∫ x, h x ^ 2 ∂torusMeasure 11) ≤
          HighDim.Eleven.uniformHessian (VariationalCurves.globalTransition 11) h :=
  Eleven.theorem_1_2.2.2.2.2.1

/-- **Theorem 1.2, pressure corner.**  Statement as in `Challenge.eleven_pressure_corner`
(`Eleven.pressureReal β` is by definition `(pressure 11 β).toReal`). -/
theorem eleven_pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = ((pressure 11 β).toReal : EReal)) ∧
      ¬ DifferentiableAt ℝ (fun β => (pressure 11 β).toReal)
        (VariationalCurves.globalTransition 11) :=
  ⟨Eleven.prop49.2.2.1.1, Eleven.theorem_1_2.2.2.2.2.2.1⟩

/-- **Theorem 1.2, first-order transition.**  Statement as in
`Challenge.eleven_pressure_derivative_jump` (component (d) of `V2.Eleven.prop49`). -/
theorem eleven_pressure_derivative_jump :
    ∃ p : ℝ, 0 < p ∧
      HasDerivWithinAt (fun β => (pressure 11 β).toReal) 0
        (Set.Iio (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11) ∧
      HasDerivWithinAt (fun β => (pressure 11 β).toReal) p
        (Set.Ioi (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11) :=
  Eleven.prop49.2.2.2.2.1

/-- **Theorem 1.2, defect corner.**  Statement as in `Challenge.eleven_defect_corner`. -/
theorem eleven_defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < VariationalCurves.zeroDefectCoefficient 11 ∧
      ∀ A : ℝ, |A - VariationalCurves.zeroDefectCoefficient 11| < ε →
        coefficientDefect 11 A = ((coefficientDefect 11 A).toReal : EReal)) ∧
      ¬ DifferentiableAt ℝ (fun A => (coefficientDefect 11 A).toReal)
        (VariationalCurves.zeroDefectCoefficient 11) :=
  ⟨Eleven.prop49.2.2.2.1.1, Eleven.theorem_1_2.2.2.2.2.2.2⟩

#print axioms eleven_profile_constant
#print axioms eleven_competitor
#print axioms eleven_competitor_written
#print axioms eleven_spectral_pressure
#print axioms eleven_globalTransition_bounds
#print axioms eleven_coexistence
#print axioms eleven_uniform_hessian_pos
#print axioms eleven_pressure_corner
#print axioms eleven_pressure_derivative_jump
#print axioms eleven_defect_corner

end BecknerOnofri.V2.Final
