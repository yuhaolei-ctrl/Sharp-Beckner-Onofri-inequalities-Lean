import Legacy.TorusEndpoint.TorusHeatBounds
import Legacy.TorusEndpoint.GreenPairing

/-!
# Actual L2 heat pairings and nonnegative-test lower bounds

The Fourier convention agrees with GreenPairing: the kernel, not the test,
is conjugated. Every spatial integral is proved integrable. There is no time
integration, Mellin identity, or conclusion about a Green lower bound here.
-/

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint.TorusHeatPairing

open TorusHeatPositivity TorusHeatBounds GreenPairing

theorem heatFluctuation_memLp {d : ℕ} {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : Torus d => torusTheta t x - 1) 2 (torusMeasure d) :=
  ((torusTheta_continuous ht).sub continuous_const).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def heatFluctuationLp {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Lp ℂ 2 (torusMeasure d) :=
  (heatFluctuation_memLp ht).toLp (fun x => torusTheta t x - 1)

theorem heatFluctuationLp_coe_ae {d : ℕ} {t : ℝ} (ht : 0 < t) :
    heatFluctuationLp (d := d) ht =ᵐ[torusMeasure d] (fun x => torusTheta t x - 1) :=
  (heatFluctuation_memLp ht).coeFn_toLp

theorem heatFluctuation_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (fun x => torusTheta t x - 1) k =
      (nonzeroHeatWeight t k : ℂ) := by
  have he : (fun x : Torus d => torusTheta t x - 1) =
      absoluteFourierSeries (fun j => (nonzeroHeatWeight t j : ℂ)) :=
    funext (torusTheta_sub_one ht)
  rw [he]
  apply absoluteFourierSeries_coefficient
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (nonzeroHeatWeight_nonneg t _)] using
    (nonzeroHeatWeight_summable ht : Summable (nonzeroHeatWeight t : Frequency d → ℝ))

theorem heatFluctuationLp_fourierCoeff {d : ℕ} {t : ℝ} (ht : 0 < t)
    (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (heatFluctuationLp ht) k =
      (nonzeroHeatWeight t k : ℂ) := by
  rw [← heatFluctuation_fourierCoeff ht k]
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [heatFluctuationLp_coe_ae ht] with x hx
  rw [hx]

theorem complex_heat_pairing_integrable {d : ℕ} {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (torusMeasure d)) :
    Integrable (fun x => conj (torusTheta t x - 1) * f x) (torusMeasure d) :=
  (heatFluctuation_memLp ht).star.integrable_mul (Lp.memLp f)

/-- Parseval for the genuine heat fluctuation and an arbitrary actual L2 test. -/
theorem hasSum_heat_pairing {d : ℕ} {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d =>
      (nonzeroHeatWeight t k : ℂ) * UnitAddTorus.mFourierCoeff f k)
      (∫ x, conj (torusTheta t x - 1) * f x ∂torusMeasure d) := by
  have h : HasSum (fun k : Frequency d =>
      conj (UnitAddTorus.mFourierCoeff (heatFluctuationLp ht) k) *
        UnitAddTorus.mFourierCoeff f k)
      (∫ x, conj (heatFluctuationLp ht x) * f x ∂torusMeasure d) :=
    UnitAddTorus.hasSum_prod_mFourierCoeff (heatFluctuationLp (d := d) ht) f
  have he : (∫ x, conj (heatFluctuationLp ht x) * f x ∂torusMeasure d) =
      ∫ x, conj (torusTheta t x - 1) * f x ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [heatFluctuationLp_coe_ae ht] with x hx
    rw [hx]
  rw [he] at h
  simpa only [heatFluctuationLp_fourierCoeff ht, Complex.conj_ofReal] using h

theorem summable_heat_pairing_norm {d : ℕ} {t : ℝ} (ht : 0 < t)
    (f : Lp ℂ 2 (torusMeasure d)) :
    Summable (fun k : Frequency d =>
      ‖(nonzeroHeatWeight t k : ℂ) * UnitAddTorus.mFourierCoeff f k‖) :=
  summable_norm_iff.mpr (hasSum_heat_pairing ht f).summable

theorem real_heat_pairing_integrable {d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    Integrable (fun x => ((torusTheta t x).re - 1) * f x) (torusMeasure d) := by
  have hi := (heatFluctuation_memLp ht).re.integrable_mul hf
  change Integrable (fun x => (torusTheta t x - 1).re * f x) (torusMeasure d) at hi
  simpa only [Complex.sub_re, Complex.one_re] using hi

/-- The real tested heat fluctuation uses the same Fourier sign as the real Green pairing. -/
theorem hasSum_real_heat_pairing {d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d => nonzeroHeatWeight t k * (densityFourier f k).re)
      (∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d) := by
  let F : Lp ℂ 2 (torusMeasure d) := hf.ofReal.toLp (fun x => (f x : ℂ))
  have h := Complex.hasSum_re (hasSum_heat_pairing ht F)
  have he : (∫ x, conj (torusTheta t x - 1) * F x ∂torusMeasure d).re =
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d := by
    calc
      _ = ∫ x, (conj (torusTheta t x - 1) * F x).re ∂torusMeasure d :=
        (integral_re (complex_heat_pairing_integrable ht F)).symm
      _ = _ := by
        apply integral_congr_ae
        have hF : F =ᵐ[torusMeasure d] (fun x => (f x : ℂ)) := hf.ofReal.coeFn_toLp
        filter_upwards [hF] with x hx
        rw [hx]
        simp only [Complex.mul_re, Complex.conj_re, Complex.sub_re, Complex.one_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [he] at h
  simpa only [F, fourierCoeff_real_toLp hf, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The positivity estimate is valid for every t>0, hence in particular at small times. -/
theorem real_heat_pairing_lower_bound {d : ℕ} {t : ℝ} (ht : 0 < t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d))
    (hpos : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) :
    -(∫ x, f x ∂torusMeasure d) ≤
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d := by
  have hfi := hf.integrable (by norm_num)
  have h := integral_mono_ae hfi.neg (real_heat_pairing_integrable ht hf) ?_
  · simpa only [Pi.neg_apply, integral_neg] using h
  filter_upwards [hpos] with x hx
  change -f x ≤ ((torusTheta t x).re - 1) * f x
  have hp := mul_nonneg (torusTheta_re_pos ht x).le hx
  nlinarith

/-- Large-time tested lower bound, with the proved-finite Gaussian lattice constant. -/
theorem real_heat_pairing_large_time_lower_bound {d : ℕ} {t : ℝ} (ht : 1 ≤ t)
    {f : Torus d → ℝ} (hf : MemLp f 2 (torusMeasure d))
    (hpos : ∀ᵐ x ∂torusMeasure d, 0 ≤ f x) :
    -(heatTailMass d * Real.exp (-Real.pi * t / 2) * ∫ x, f x ∂torusMeasure d) ≤
      ∫ x, ((torusTheta t x).re - 1) * f x ∂torusMeasure d := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ht
  have hfi := hf.integrable (by norm_num)
  have hlow : Integrable (fun x => -(heatTailMass d * Real.exp (-Real.pi * t / 2)) * f x)
      (torusMeasure d) := hfi.const_mul _
  have h := integral_mono_ae hlow (real_heat_pairing_integrable ht0 hf) ?_
  · simpa only [neg_mul, integral_neg, integral_const_mul] using h
  filter_upwards [hpos] with x hx
  have hn := torusTheta_sub_one_norm_le ht x
  have hr := (abs_le.mp (Complex.abs_re_le_norm (torusTheta t x - 1))).1
  simp only [Complex.sub_re, Complex.one_re] at hr
  have hp : -(heatTailMass d * Real.exp (-Real.pi * t / 2)) ≤ (torusTheta t x).re - 1 := by
    linarith
  exact mul_le_mul_of_nonneg_right hp hx

end Legacy.TorusEndpoint.TorusHeatPairing
