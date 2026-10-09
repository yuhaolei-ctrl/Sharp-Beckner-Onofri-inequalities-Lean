module

public import BecknerOnofri.V2.Final.Endpoint
public import BecknerOnofri.V2.Section3.FinalWritten
public import BecknerOnofri.ThresholdReduction
public import BecknerOnofri.ConcentrationDivergence

@[expose] public section

/-! # Theorem 1.1 (`1 ≤ d ≤ 10`) in the vocabulary of `Challenge.lean` (Final package)

All statements are derived from `Section3.theorem_1_1_written`, whose conclusion is stated with the
manuscript normalization (`c_d`, `‖ρ‖_{Ḣ^{-d/2}}`, `Vocab.torusEntropy`).  The translation to the
`Challenge` normalization (`spectralThreshold`, `spectralEnergy`, `entropy`, `extendedEntropy`) uses
only `Vocab.kernelConstant_mul_negSobolevEnergy_toReal` (`c_d ‖ρ‖² = spectralEnergy ρ / β_s(d)`). -/

noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace BecknerOnofri.V2.Final
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab BecknerOnofri.V2.Section3

/-- Equality in `eq:collapse-entropy-full` (manuscript normalization) is equality in the
`Challenge` normalization `(d/β_s(d)) · spectralEnergy ρ = Ent ρ`. -/
theorem entropyEquality_iff_challenge {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    EntropyEquality d ρ ↔
      (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) := by
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
  have key := kernelConstant_mul_negSobolevEnergy_toReal hd ρ
  have h1 : (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      (d : ℝ) / spectralThreshold d * (spectralEnergy ρ).toReal := by
    rw [mul_assoc, key]; ring
  unfold EntropyEquality
  rw [← EReal.coe_ennreal_toReal hfin, ← EReal.coe_mul, EReal.coe_eq_coe_iff, h1,
    ← entropy_eq_toReal_torusEntropy ρ hρ]

section Low
variable (d : ℕ)

/-- **Theorem 1.1, (eq:intro-low-dual).**  Statement as in `Challenge.low_dim_entropy_inequality`. -/
theorem low_dim_entropy_inequality (hd : 1 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤
      extendedEntropy ρ := by
  have hd0 : 0 < d := hd
  refine ereal_le_extendedEntropy hd0 ρ _ fun hρ => ?_
  have hext := (theorem_1_1_written hd hd10).2.1 ρ
  unfold ExtendedBound at hext
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd0 ρ hρ
  have hN : negSobolevEnergy ρ.value ≠ ⊤ := (negSobolevEnergy_ne_top_iff ρ).2 hfin
  have hc : 0 < kernelConstant d := kernelConstant_pos hd0
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [torusEntropy_density_eq_ofReal_entropy ρ hρ, ← ENNReal.ofReal_toReal hN,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (entropy_nonneg ρ hρ)] at hext
  have key := kernelConstant_mul_negSobolevEnergy_toReal hd0 ρ
  have h1 : (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
      (d : ℝ) / spectralThreshold d * (spectralEnergy ρ).toReal := by
    rw [mul_assoc, key]; ring
  rw [← h1]
  exact hext

/-- **Theorem 1.1, (eq:intro-low-primal).**  Statement as in `Challenge.low_dim_beckner_onofri`. -/
theorem low_dim_beckner_onofri (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  (theorem_1_1_written hd hd10).1 u hu

/-- **Theorem 1.1, sharpness.**  Statement as in `Challenge.low_dim_coefficient_sharp`. -/
theorem low_dim_coefficient_sharp (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) :=
  (theorem_1_1_written hd hd10).2.2.1

/-- **Theorem 1.1, equality for `d = 1` (potentials).**  Statement as in
`Challenge.circle_beckner_onofri_eq_iff`. -/
theorem circle_beckner_onofri_eq_iff (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c :=
  ((theorem_1_1_written (le_refl 1) (by norm_num)).2.2.2.1 rfl).2 u hu

/-- **Theorem 1.1, equality for `d = 1` (densities).**  Statement as in
`Challenge.circle_entropy_eq_iff`. -/
theorem circle_entropy_eq_iff (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    (((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧
        ρ.value =ᵐ[torusMeasure 1] fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2 := by
  have h := entropyEquality_iff_challenge (by norm_num : 0 < 1) ρ hρ
  rw [Nat.cast_one] at h
  rw [← h]
  exact ((theorem_1_1_written (le_refl 1) (by norm_num)).2.2.2.1 rfl).1 ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (densities).**  Statement as in
`Challenge.low_dim_entropy_eq_iff`. -/
theorem low_dim_entropy_eq_iff (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 := by
  rw [← entropyEquality_iff_challenge (by omega) ρ hρ]
  exact ((theorem_1_1_written (by omega) hd10).2.2.2.2.1 hd).1 ρ hρ

/-- **Theorem 1.1, equality for `2 ≤ d ≤ 10` (potentials).**  Statement as in
`Challenge.low_dim_beckner_onofri_eq_iff`. -/
theorem low_dim_beckner_onofri_eq_iff (hd : 2 ≤ d) (hd10 : d ≤ 10)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  ((theorem_1_1_written (by omega) hd10).2.2.2.2.1 hd).2 u hu

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_pressure_eq`. -/
theorem low_dim_pressure_eq (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ :=
  (theorem_1_1_written hd hd10).2.2.2.2.2.2.1 β

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_defect_eq`.
`theorem_1_1_written` only gives `C_d(A_c(d)) = 0`; the formula for all `A` follows by antitonicity of
`C_d` and `0 ≤ C_d` (above `A_c`) and `HighDim.coefficientDefect_below_collapse` (below `A_c`),
the latter being the concentration lemma (Lemma 2.3), also used in `Section3.collapse_isLeast`. -/
theorem low_dim_defect_eq (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  have hd0 : 0 < d := hd
  split_ifs with h
  · refine le_antisymm ?_ (coefficientDefect_nonneg d A)
    calc coefficientDefect d A ≤ coefficientDefect d (collapseCoefficient d) :=
          coefficientDefect_antitone hd0 h
      _ = 0 := (theorem_1_1_written hd hd10).2.2.2.2.2.1
  · exact coefficientDefect_below_collapse hd0 (not_le.mp h)

/-- **(eq:intro-low-coefficient-consequence).**  Statement as in `Challenge.low_dim_globalTransition`. -/
theorem low_dim_globalTransition (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    VariationalCurves.globalTransition d = 2 * (d : ℝ) :=
  (theorem_1_1_written hd hd10).2.2.2.2.2.2.2

end Low

#print axioms entropyEquality_iff_challenge
#print axioms low_dim_entropy_inequality
#print axioms low_dim_beckner_onofri
#print axioms low_dim_coefficient_sharp
#print axioms circle_beckner_onofri_eq_iff
#print axioms circle_entropy_eq_iff
#print axioms low_dim_entropy_eq_iff
#print axioms low_dim_beckner_onofri_eq_iff
#print axioms low_dim_pressure_eq
#print axioms low_dim_defect_eq
#print axioms low_dim_globalTransition

end BecknerOnofri.V2.Final
