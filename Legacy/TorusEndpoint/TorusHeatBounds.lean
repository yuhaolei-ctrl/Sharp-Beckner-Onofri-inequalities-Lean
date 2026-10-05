module

public import Legacy.TorusEndpoint.TorusHeatPositivity
public import Legacy.TorusEndpoint.PositiveFourierAnalytic
public import Legacy.TorusEndpoint.GreenMultiplierSummability

@[expose] public section

/-!
# Actual heat Fourier coefficients, mass, and large-time decay

All Gaussian lattice summability is proved. The large-time constant is the
finite nonzero Gaussian mass at time one half. No Green or Mellin identity
is asserted in this module.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint.TorusHeatBounds

open TorusHeatPositivity GreenMultiplierSummability

noncomputable def heatWeight {d : ℕ} (t : ℝ) (k : Frequency d) : ℝ :=
  Real.exp (-Real.pi * t * radiusSq k)

theorem heatWeight_pos {d : ℕ} (t : ℝ) (k : Frequency d) : 0 < heatWeight t k :=
  Real.exp_pos _

@[simp] theorem heatWeight_zero (d : ℕ) (t : ℝ) : heatWeight t (0 : Frequency d) = 1 := by
  simp [heatWeight, radiusSq]

theorem heatWeight_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (heatWeight t : Frequency d → ℝ) := by
  have hs := (Complex.hasSum_re (torusTheta_summable ht (0 : Torus d)).hasSum).summable
  change Summable (fun k : Frequency d => Real.exp (-Real.pi * t * ∑ j, (k j : ℝ)^2))
  simpa only [heatWeight, radiusSq, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one, mul_one, Complex.ofReal_re] using hs

theorem heatWeight_norm_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun k : Frequency d => ‖(heatWeight t k : ℂ)‖) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (heatWeight_pos t _)] using
    (heatWeight_summable ht : Summable (heatWeight t : Frequency d → ℝ))

theorem torusTheta_eq_absoluteFourierSeries {d : ℕ} (t : ℝ) :
    torusTheta (d := d) t = absoluteFourierSeries (fun k => (heatWeight t k : ℂ)) := rfl

theorem torusTheta_continuous {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (torusTheta (d := d) t) := by
  rw [torusTheta_eq_absoluteFourierSeries]
  exact absoluteFourierSeries_continuous _ (heatWeight_norm_summable ht)

theorem torusTheta_actual_fourierCoefficient {d : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (torusTheta t) k = (heatWeight t k : ℂ) := by
  rw [torusTheta_eq_absoluteFourierSeries]
  exact absoluteFourierSeries_coefficient _ (heatWeight_norm_summable ht) k

theorem torusTheta_integral {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ x, torusTheta t x ∂torusMeasure d) = 1 := by
  rw [torusTheta_eq_absoluteFourierSeries,
    absoluteFourierSeries_integral _ (heatWeight_norm_summable ht), heatWeight_zero]
  exact Complex.ofReal_one

theorem torusTheta_re_integral {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ x, (torusTheta t x).re ∂torusMeasure d) = 1 := by
  have hi : Integrable (torusTheta (d := d) t) (torusMeasure d) :=
    (torusTheta_continuous ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, torusTheta t x ∂torusMeasure d).re := integral_re hi
    _ = 1 := by rw [torusTheta_integral ht]; rfl

noncomputable def nonzeroHeatWeight {d : ℕ} (t : ℝ) (k : Frequency d) : ℝ :=
  if k = 0 then 0 else heatWeight t k

theorem nonzeroHeatWeight_nonneg {d : ℕ} (t : ℝ) (k : Frequency d) :
    0 ≤ nonzeroHeatWeight t k := by
  unfold nonzeroHeatWeight
  split_ifs
  · exact le_rfl
  · exact (heatWeight_pos t k).le

theorem nonzeroHeatWeight_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (nonzeroHeatWeight t : Frequency d → ℝ) := by
  apply Summable.of_nonneg_of_le (nonzeroHeatWeight_nonneg t) _ (heatWeight_summable ht)
  intro k
  unfold nonzeroHeatWeight
  split_ifs
  · exact (heatWeight_pos t k).le
  · exact le_rfl

noncomputable def heatTailMass (d : ℕ) : ℝ :=
  ∑' k : Frequency d, nonzeroHeatWeight (1 / 2) k

theorem heatTailMass_nonneg (d : ℕ) : 0 ≤ heatTailMass d :=
  tsum_nonneg (nonzeroHeatWeight_nonneg (1 / 2))

theorem torusTheta_sub_one {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    torusTheta t x - 1 =
      ∑' k : Frequency d, (nonzeroHeatWeight t k : ℂ) * UnitAddTorus.mFourier k x := by
  classical
  have hs := (torusTheta_summable ht x).tsum_eq_add_tsum_ite (0 : Frequency d)
  have hzero : (Real.exp (-Real.pi * t * (∑ j : Fin d, ((0 : Frequency d) j : ℝ)^2)) : ℂ) *
      UnitAddTorus.mFourier (0 : Frequency d) x = 1 := by
    simp [UnitAddTorus.mFourier_zero]
  rw [hzero] at hs
  apply sub_eq_iff_eq_add.mpr
  rw [add_comm]
  simpa only [torusTheta, nonzeroHeatWeight, heatWeight, radiusSq, apply_ite,
    Complex.ofReal_zero, ite_mul, zero_mul] using hs

theorem heatWeight_large_time {d : ℕ} {t : ℝ} (ht : 1 ≤ t)
    {k : Frequency d} (hk : k ≠ 0) :
    heatWeight t k ≤ heatWeight (1 / 2) k * Real.exp (-Real.pi * t / 2) := by
  have hr := radiusSq_one_le hk
  have hprod := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hr)
  have htr : t / 2 + radiusSq k / 2 ≤ t * radiusSq k := by nlinarith
  have hp := mul_le_mul_of_nonneg_left htr Real.pi_pos.le
  unfold heatWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem nonzeroHeatWeight_large_time {d : ℕ} {t : ℝ} (ht : 1 ≤ t)
    (k : Frequency d) :
    nonzeroHeatWeight t k ≤ nonzeroHeatWeight (1 / 2) k * Real.exp (-Real.pi * t / 2) := by
  by_cases hk : k = 0
  · simp [nonzeroHeatWeight, hk]
  · simpa only [nonzeroHeatWeight, if_neg hk] using heatWeight_large_time ht hk

/-- Uniform exponential decay with an explicit, proved-finite Gaussian lattice constant. -/
theorem torusTheta_sub_one_norm_le {d : ℕ} {t : ℝ} (ht : 1 ≤ t) (x : Torus d) :
    ‖torusTheta t x - 1‖ ≤ heatTailMass d * Real.exp (-Real.pi * t / 2) := by
  rw [torusTheta_sub_one (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht)]
  apply tsum_of_norm_bounded
    ((nonzeroHeatWeight_summable (show (0 : ℝ) < 1 / 2 by norm_num)).hasSum.mul_right
      (Real.exp (-Real.pi * t / 2)))
  intro k
  simp only [norm_mul, mFourier_norm_apply, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (nonzeroHeatWeight_nonneg t k)]
  exact nonzeroHeatWeight_large_time ht k

end Legacy.TorusEndpoint.TorusHeatBounds
