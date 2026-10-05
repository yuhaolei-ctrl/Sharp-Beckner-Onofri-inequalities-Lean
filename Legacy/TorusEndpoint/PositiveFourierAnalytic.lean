module

public import Legacy.TorusEndpoint.PositiveFourierExponential
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Actual Fourier coefficients and positive quadrature for absolutely convergent series

This module identifies the constructed coefficients with Haar integrals and
therefore connects the convolution/exponential construction to grid aliasing.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint

theorem absoluteFourierSeries_continuous {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) : Continuous (absoluteFourierSeries a) := by
  apply continuous_tsum (fun k => continuous_const.mul (UnitAddTorus.mFourier k).continuous) ha
  intro k x
  change ‖a k * UnitAddTorus.mFourier k x‖ ≤ ‖a k‖
  rw [norm_mul, mFourier_norm_apply, mul_one]

theorem integral_shifted_character {d : ℕ} (k r : Frequency d) :
    (∫ x, UnitAddTorus.mFourier (-r) x * UnitAddTorus.mFourier k x ∂torusMeasure d) =
      if r = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d)) r k
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    ← UnitAddTorus.mFourier_neg, torusMeasure, mul_comm] using h

theorem absoluteFourierSeries_coefficient {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (r : Frequency d) :
    UnitAddTorus.mFourierCoeff (absoluteFourierSeries a) r = a r := by
  classical
  let F : Frequency d → Torus d → ℂ := fun k x =>
    a k * (UnitAddTorus.mFourier (-r) x * UnitAddTorus.mFourier k x)
  have hF (k) : Integrable (F k) (torusMeasure d) := by
    apply Continuous.integrable_of_hasCompactSupport
      (continuous_const.mul ((UnitAddTorus.mFourier (-r)).continuous.mul
        (UnitAddTorus.mFourier k).continuous))
    exact HasCompactSupport.of_compactSpace _
  have hn (k) (x : Torus d) : ‖F k x‖ = ‖a k‖ := by
    simp only [F, norm_mul, mFourier_norm_apply, one_mul, mul_one]
  have hs : Summable (fun k => ∫ x, ‖F k x‖ ∂torusMeasure d) := by
    simpa only [hn, integral_const, probReal_univ, one_smul] using ha
  have hterm (k) : (∫ x, F k x ∂torusMeasure d) = if r = k then a k else 0 := by
    change (∫ x, a k * (UnitAddTorus.mFourier (-r) x * UnitAddTorus.mFourier k x)
      ∂torusMeasure d) = _
    rw [integral_const_mul, integral_shifted_character]
    split_ifs <;> simp
  calc
    _ = ∫ x, ∑' k, F k x ∂torusMeasure d := by
      unfold UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [absoluteFourierSeries, smul_eq_mul, F]
        rw [← tsum_mul_left]
        apply tsum_congr
        intro k
        ring
    _ = ∑' k, ∫ x, F k x ∂torusMeasure d :=
      (integral_tsum_of_summable_integral_norm hF hs).symm
    _ = a r := by simp only [hterm]; simp

theorem absoluteFourierSeries_integral {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    (∫ x, absoluteFourierSeries a x ∂torusMeasure d) = a 0 := by
  simpa only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul, torusMeasure] using
    absoluteFourierSeries_coefficient a ha 0

theorem nonnegative_series_integral_le_grid_average {d N : ℕ} [NeZero N]
    (a : Frequency d → ℝ) (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) :
    (∫ x, absoluteFourierSeries (fun k => (a k : ℂ)) x ∂torusMeasure d).re ≤
      (gridAverage (N := N) (absoluteFourierSeries (fun k => (a k : ℂ)))).re := by
  have hn : Summable (fun k => ‖(a k : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _)] using ha
  rw [absoluteFourierSeries_integral _ hn, Complex.ofReal_re]
  simpa only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one] using
    nonnegative_coefficient_le_grid_average (N := N) a ha hpos 0

theorem exponential_series_integral_le_grid_average {d N : ℕ} [NeZero N]
    (a : Frequency d → ℝ) (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) :
    (∫ x, Complex.exp (absoluteFourierSeries (fun k => (a k : ℂ)) x)
      ∂torusMeasure d).re ≤
      (gridAverage (N := N) (fun x =>
        Complex.exp (absoluteFourierSeries (fun k => (a k : ℂ)) x))).re := by
  have heq : absoluteFourierSeries (fun k => (fourierExponential a k : ℂ)) =
      fun x => Complex.exp (absoluteFourierSeries (fun k => (a k : ℂ)) x) :=
    funext (fourierExponential_series a ha hpos)
  simpa only [heq] using
    nonnegative_series_integral_le_grid_average (N := N) (fourierExponential a)
      (fourierExponential_hasSum a ha hpos).summable (fourierExponential_nonneg a hpos)

end Legacy.TorusEndpoint
