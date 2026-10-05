module

public import Legacy.TorusEndpoint.GreenMellinMultiplier
public import Legacy.TorusEndpoint.GreenPairing

@[expose] public section

/-!
# Absolute convergence of the Green Mellin pairing

The exchange between the time integral and the full frequency series is
justified by the sum of the integrals of the absolute values. The last
identity uses the actual real L² Green function and actual density Fourier
coefficients, not an assumed representation of a kernel.
-/

open MeasureTheory Set Filter

namespace Legacy.TorusEndpoint.GreenMellinSeries

open GreenMultiplierSummability TorusHeatBounds GreenMellinMultiplier GreenPairing

theorem greenMultiplier_nonneg {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    0 ≤ greenMultiplier d k := by
  unfold greenMultiplier
  split_ifs
  · exact le_rfl
  · exact one_div_nonneg.mpr (mul_nonneg (endpointSigma_pos hd).le
      (pow_nonneg (frequencyRadius_nonneg k) _))

noncomputable def mellinTerm {d : ℕ} (a : Frequency d → ℝ) (k : Frequency d) (t : ℝ) : ℝ :=
  (t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k) * a k

theorem mellinTerm_integrable {d : ℕ} (hd : 0 < d) (a : Frequency d → ℝ)
    (k : Frequency d) : IntegrableOn (mellinTerm a k) (Ioi 0) :=
  (nonzeroHeatWeight_mellin_integrable hd k).mul_const (a k)

theorem integral_mellinTerm {d : ℕ} (hd : 0 < d) (a : Frequency d → ℝ)
    (k : Frequency d) :
    (∫ t in Ioi 0, mellinTerm a k t) = 2 * (greenMultiplier d k * a k) := by
  unfold mellinTerm
  rw [integral_mul_const, nonzeroHeatWeight_mellin_integral hd k]
  ring

theorem integral_norm_mellinTerm {d : ℕ} (hd : 0 < d) (a : Frequency d → ℝ)
    (k : Frequency d) :
    (∫ t in Ioi 0, ‖mellinTerm a k t‖) = 2 * ‖greenMultiplier d k * a k‖ := by
  have he : (∫ t in Ioi 0, ‖mellinTerm a k t‖) =
      ∫ t in Ioi 0, (t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k) * ‖a k‖ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hp : 0 ≤ t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k :=
      mul_nonneg (Real.rpow_nonneg ht.le _) (nonzeroHeatWeight_nonneg t k)
    change ‖(t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k) * a k‖ = _
    rw [norm_mul, Real.norm_of_nonneg hp]
  rw [he, integral_mul_const, nonzeroHeatWeight_mellin_integral hd k, norm_mul,
    Real.norm_of_nonneg (greenMultiplier_nonneg hd k)]
  ring

theorem summable_integral_norm_mellinTerm {d : ℕ} (hd : 0 < d)
    (a : Frequency d → ℝ) (ha : Summable (fun k => ‖greenMultiplier d k * a k‖)) :
    Summable (fun k => ∫ t in Ioi 0, ‖mellinTerm a k t‖) := by
  simpa only [integral_norm_mellinTerm hd a] using ha.mul_left 2

theorem integral_mellinSeries {d : ℕ} (hd : 0 < d)
    (a : Frequency d → ℝ) (ha : Summable (fun k => ‖greenMultiplier d k * a k‖)) :
    (∫ t in Ioi 0, ∑' k, mellinTerm a k t) =
      2 * ∑' k, greenMultiplier d k * a k := by
  rw [← integral_tsum_of_summable_integral_norm
    (mellinTerm_integrable hd a) (summable_integral_norm_mellinTerm hd a ha)]
  simp only [integral_mellinTerm hd a, tsum_mul_left]

theorem summable_realGreen_pairing_abs {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    Summable (fun k => ‖greenMultiplier d k * (densityFourier f k).re‖) := by
  apply (summable_realGreen_pairing_norm hf).of_nonneg_of_le (fun k => norm_nonneg _)
  intro k
  have h := Complex.abs_re_le_norm ((greenMultiplier d k : ℂ) * densityFourier f k)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Real.norm_eq_abs] using h

theorem realGreen_mellinSeries {d : ℕ} (hd : 0 < d) {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    (∫ t in Ioi 0, ∑' k, mellinTerm (fun k => (densityFourier f k).re) k t) =
      2 * ∫ x, GreenKernelReal.realGreen d x * f x ∂torusMeasure d := by
  rw [integral_mellinSeries hd _ (summable_realGreen_pairing_abs hf),
    (hasSum_realGreen_pairing hf).tsum_eq]

end Legacy.TorusEndpoint.GreenMellinSeries
