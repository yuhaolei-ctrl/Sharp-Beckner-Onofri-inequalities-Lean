module

public import BecknerOnofri.V2.Reaudit.Obstruction.ConcentrationDensity

@[expose] public section

/-! # Row S006 (concentration test): the entropy of the scaled mollifier

Printed (`eq:section2-concentration-entropy`): `Ent(ρ_ε) = d log(1/ε) + ∫ η log η`.
Proof: `ρ_ε log ρ_ε = log(ε^{-d}) ρ_ε + ε^{-d} (η log η)(ε⁻¹ ·)`, both pieces are bounded and
measurable, and the change of variables `integral_mollified_scaling` applies to `η` and to
`η log η`. -/

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-- The hypotheses on the profile `η` of the concentrating family: bounded, measurable,
nonnegative, of integral `1`, supported in the cube `{|y_j| ≤ 1/4}`. -/
structure AdmissibleProfile (η : (Fin d → ℝ) → ℝ) (M : ℝ) : Prop where
  measurable : Measurable η
  nonneg : ∀ y, 0 ≤ η y
  le : ∀ y, η y ≤ M
  support : ∀ y, η y ≠ 0 → ∀ j, |y j| ≤ 1 / 4
  mass : ∫ y, η y = 1

/-- Elementary bound: `|t log t| ≤ 1 + M²` for `0 ≤ t ≤ M`. -/
lemma abs_mul_log_le {t M : ℝ} (h0 : 0 ≤ t) (hM : t ≤ M) : |t * Real.log t| ≤ 1 + M ^ 2 := by
  rcases h0.eq_or_lt with rfl | hpos
  · simp; positivity
  by_cases h1 : 1 ≤ t
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1
    have hle : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos hpos
    rw [abs_of_nonneg (mul_nonneg h0 hl)]
    nlinarith [sq_nonneg M]
  · rw [not_le] at h1
    have hl : Real.log t ≤ 0 := Real.log_nonpos h0 h1.le
    have hle : Real.log (t⁻¹) ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hle
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 hl)]
    have : -(t * Real.log t) ≤ t * (t⁻¹ - 1) := by nlinarith
    have h2 : t * (t⁻¹ - 1) = 1 - t := by field_simp
    nlinarith [sq_nonneg M]

variable {η : (Fin d → ℝ) → ℝ} {M ε : ℝ}

lemma AdmissibleProfile.measurable_mul_log (h : AdmissibleProfile η M) :
    Measurable (fun y => η y * Real.log (η y)) :=
  h.measurable.mul (Real.measurable_log.comp h.measurable)

lemma AdmissibleProfile.mul_log_support (h : AdmissibleProfile η M) :
    ∀ y, η y * Real.log (η y) ≠ 0 → ∀ j, |y j| ≤ 1 / 4 :=
  fun y hy => h.support y (fun h0 => hy (by rw [h0, zero_mul]))

lemma AdmissibleProfile.integrable_mollified (h : AdmissibleProfile η M) (hε : 0 < ε) :
    Integrable (mollified η ε : Torus d → ℝ) (torusMeasure d) :=
  (integrable_const ((ε ^ d)⁻¹ * M)).mono' (measurable_mollified h.measurable ε).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mollified_nonneg h.nonneg hε x)]
      exact mollified_le h.le hε x)

lemma AdmissibleProfile.integral_mollified (h : AdmissibleProfile η M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : ∫ x, mollified η ε x ∂torusMeasure d = 1 :=
  BecknerOnofri.V2.Reaudit.Obstruction.integral_mollified h.measurable h.support h.mass hε hε1

/-- The finite-entropy condition for the mollified family. -/
lemma AdmissibleProfile.integrable_mollified_mul_log (h : AdmissibleProfile η M) (hε : 0 < ε) :
    Integrable (fun x : Torus d => mollified η ε x * Real.log (mollified η ε x)) (torusMeasure d) := by
  refine (integrable_const (1 + ((ε ^ d)⁻¹ * M) ^ 2)).mono'
    ((measurable_mollified h.measurable ε).mul
      (Real.measurable_log.comp (measurable_mollified h.measurable ε))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_mul_log_le (mollified_nonneg h.nonneg hε x) (mollified_le h.le hε x)

/-- **Printed `eq:section2-concentration-entropy`**: `Ent(ρ_ε) = d log(1/ε) + ∫ η log η`. -/
theorem AdmissibleProfile.entropy_mollified (h : AdmissibleProfile η M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ x, mollified η ε x * Real.log (mollified η ε x) ∂torusMeasure d =
      d * Real.log (1 / ε) + ∫ y, η y * Real.log (η y) := by
  set c : ℝ := (ε ^ d)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (pow_pos hε d)
  have hpt : ∀ x : Torus d, mollified η ε x * Real.log (mollified η ε x) =
      Real.log c * mollified η ε x +
        c * (η (ε⁻¹ • torusRep x) * Real.log (η (ε⁻¹ • torusRep x))) := by
    intro x
    by_cases h0 : η (ε⁻¹ • torusRep x) = 0
    · simp [mollified, h0]
    · have hpos : 0 < η (ε⁻¹ • torusRep x) := lt_of_le_of_ne (h.nonneg _) (Ne.symm h0)
      simp only [mollified, ← hc]
      rw [Real.log_mul hcpos.ne' h0]
      ring
  have hi1 := h.integrable_mollified hε
  have hm2 : Measurable (fun x : Torus d =>
      c * (η (ε⁻¹ • torusRep x) * Real.log (η (ε⁻¹ • torusRep x)))) :=
    measurable_const.mul (h.measurable_mul_log.comp (measurable_scaledRep _))
  have hi2 : Integrable (fun x : Torus d =>
      c * (η (ε⁻¹ • torusRep x) * Real.log (η (ε⁻¹ • torusRep x)))) (torusMeasure d) := by
    refine (integrable_const (c * (1 + M ^ 2))).mono' hm2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hcpos]
    exact mul_le_mul_of_nonneg_left (abs_mul_log_le (h.nonneg _) (h.le _)) hcpos.le
  simp_rw [hpt]
  rw [integral_add (hi1.const_mul _) hi2, integral_const_mul, h.integral_mollified hε hε1,
    integral_mollified_scaling (fun y => η y * Real.log (η y)) h.measurable_mul_log
      h.mul_log_support hε hε1]
  rw [hc, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  ring

end BecknerOnofri.V2.Reaudit.Obstruction
