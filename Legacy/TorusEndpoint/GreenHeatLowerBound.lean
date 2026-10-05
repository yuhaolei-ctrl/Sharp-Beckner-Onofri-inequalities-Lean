import Legacy.TorusEndpoint.GreenLowerBound
import Legacy.TorusEndpoint.GreenHeatRegularization

/-!
# Shifted heat tests for the actual heat-regularized Green function

The test functions below are genuine positive continuous functions of mass
one. Their Fourier coefficients are proved from the actual absolutely
convergent heat series, with the sign of the translation explicit.
-/

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint.GreenHeatLowerBound

open TorusHeatPositivity TorusHeatBounds GreenMultiplierSummability GreenKernelReal
  GreenPairing GreenLowerBound GreenHeatRegularization

theorem heatWeight_neg {d : ℕ} (t : ℝ) (k : Frequency d) :
    heatWeight t (-k) = heatWeight t k := by
  simp only [heatWeight, radiusSq, Pi.neg_apply, Int.cast_neg, neg_sq]

noncomputable def shiftedHeatTest {d : ℕ} (t : ℝ) (x y : Torus d) : ℝ :=
  (torusTheta t (x - y)).re

theorem shiftedHeatTest_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (x y : Torus d) :
    0 < shiftedHeatTest t x y := torusTheta_re_pos ht (x - y)

theorem shiftedHeatTest_continuous {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Continuous (shiftedHeatTest t x) :=
  Complex.continuous_re.comp
    ((torusTheta_continuous ht).comp (continuous_const.sub continuous_id))

theorem shiftedHeatTest_memLp {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    MemLp (shiftedHeatTest t x) 2 (torusMeasure d) :=
  (shiftedHeatTest_continuous ht x).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem shiftedHeat_coeff_summable {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Summable (fun k : Frequency d =>
      ‖(heatWeight t k : ℂ) * UnitAddTorus.mFourier (-k) x‖) := by
  simpa only [norm_mul, mFourier_norm_apply, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (heatWeight_pos t _)] using
    (heatWeight_summable ht : Summable (heatWeight t : Frequency d → ℝ))

theorem shifted_heat_series {d : ℕ} (t : ℝ) (x y : Torus d) :
    torusTheta t (x - y) =
      absoluteFourierSeries
        (fun k => (heatWeight t k : ℂ) * UnitAddTorus.mFourier (-k) x) y := by
  rw [torusTheta_eq_absoluteFourierSeries]
  unfold absoluteFourierSeries
  calc
    _ = ∑' k : Frequency d, (heatWeight t (-k) : ℂ) *
        UnitAddTorus.mFourier (-k) (x - y) :=
      ((Equiv.neg (Frequency d)).tsum_eq (fun k =>
        (heatWeight t k : ℂ) * UnitAddTorus.mFourier k (x - y))).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [heatWeight_neg, PhysicalFiniteFourier.character_sub, neg_neg]
      ring

theorem shiftedHeatTest_coe {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (fun y => (shiftedHeatTest t x y : ℂ)) =
      absoluteFourierSeries
        (fun k => (heatWeight t k : ℂ) * UnitAddTorus.mFourier (-k) x) := by
  funext y
  calc
    _ = torusTheta t (x - y) := by
      apply Complex.ext
      · rfl
      · exact (torusTheta_im_zero ht (x - y)).symm
    _ = _ := shifted_heat_series t x y

theorem shiftedHeatTest_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Torus d) (k : Frequency d) :
    densityFourier (shiftedHeatTest t x) k =
      (heatWeight t k : ℂ) * UnitAddTorus.mFourier (-k) x := by
  change UnitAddTorus.mFourierCoeff (fun y => (shiftedHeatTest t x y : ℂ)) k = _
  rw [shiftedHeatTest_coe ht x]
  exact absoluteFourierSeries_coefficient _ (shiftedHeat_coeff_summable ht x) k

theorem shiftedHeatTest_integral {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    (∫ y, shiftedHeatTest t x y ∂torusMeasure d) = 1 := by
  have h := shiftedHeatTest_fourierCoeff ht x 0
  simp only [densityFourier, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul, heatWeight_zero, Complex.ofReal_one, mul_one,
    integral_complex_ofReal] at h
  exact_mod_cast h

theorem hasSum_heatGreenKernel_re {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    HasSum (fun k : Frequency d =>
      heatGreenWeight d t k * (UnitAddTorus.mFourier k x).re)
      (heatGreenKernel d t x).re := by
  have h := Complex.hasSum_re
    (summable_fourierSeries_apply (fun k => (heatGreenWeight d t k : ℂ))
      (heatGreenWeight_complex_norm_summable ht) x).hasSum
  simpa only [heatGreenKernel, absoluteFourierSeries, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The actual integral against a shifted positive heat test equals the actual
regularized Green Fourier series. The sign of the shifted coefficient is
reconciled by the equality of the real parts of opposite characters. -/
theorem realGreen_shiftedHeatTest_integral {d : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Torus d) :
    (∫ y, realGreen d y * shiftedHeatTest t x y ∂torusMeasure d) =
      (heatGreenKernel d t x).re := by
  have hp : HasSum (fun k : Frequency d =>
      heatGreenWeight d t k * (UnitAddTorus.mFourier k x).re)
      (∫ y, realGreen d y * shiftedHeatTest t x y ∂torusMeasure d) := by
    simpa only [shiftedHeatTest_fourierCoeff ht x, UnitAddTorus.mFourier_neg,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.conj_re, heatGreenWeight, mul_assoc] using
      hasSum_realGreen_pairing (shiftedHeatTest_memLp ht x)
  exact hp.unique (hasSum_heatGreenKernel_re ht x)

/-- All positive-time regularizations share the actual Green lower constant,
pointwise on the torus. No lower bound for raw finite Fourier sums is used. -/
theorem heatGreenKernel_re_lower_bound {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : 0 < t) (x : Torus d) :
    -greenLowerConstant d ≤ (heatGreenKernel d t x).re := by
  have h := realGreen_test_lower_bound hd (shiftedHeatTest_memLp ht x)
    (Eventually.of_forall (fun y => (shiftedHeatTest_pos ht x y).le))
  rwa [shiftedHeatTest_integral ht x, mul_one, realGreen_shiftedHeatTest_integral ht x] at h

end Legacy.TorusEndpoint.GreenHeatLowerBound
