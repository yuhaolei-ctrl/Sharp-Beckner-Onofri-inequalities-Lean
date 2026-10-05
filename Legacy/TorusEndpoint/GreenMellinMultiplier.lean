module

public import Legacy.TorusEndpoint.GreenMultiplierSummability
public import Legacy.TorusEndpoint.TorusHeatBounds

@[expose] public section

/-!
# The exact Mellin integral of the Green multiplier

The nonzero heat weights below are the actual Gaussian Fourier multipliers.
Both integrability and the normalization of their Mellin integral are proved.
No interchange of an infinite frequency sum with the time integral is assumed.
-/

open MeasureTheory Set

namespace Legacy.TorusEndpoint.GreenMellinMultiplier

open GreenMultiplierSummability TorusHeatBounds

theorem gamma_integrand_integrable {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hr) _)
    (Real.Gamma_pos_of_pos ha))

theorem radial_mellin_normalization {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    (1 / 2 : ℝ) * ((1 / (Real.pi * r ^ 2)) ^ ((d : ℝ) / 2) *
      Real.Gamma ((d : ℝ) / 2)) = 1 / (endpointSigma d * r ^ d) := by
  have hp : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hg : 0 < Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))
  have hrp : 0 < r ^ d := pow_pos hr _
  have he : (r ^ 2 : ℝ) ^ ((d : ℝ) / 2) = r ^ d := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * ((d : ℝ) / 2) = d by ring, Real.rpow_natCast]
  have hi : (1 / (Real.pi * r ^ 2)) ^ ((d : ℝ) / 2) =
      (Real.pi ^ ((d : ℝ) / 2) * r ^ d)⁻¹ := by
    rw [one_div, Real.inv_rpow (mul_nonneg Real.pi_pos.le (sq_nonneg r)),
      Real.mul_rpow Real.pi_pos.le (sq_nonneg r), he]
  rw [hi]
  unfold endpointSigma
  field_simp [hp.ne', hg.ne', hrp.ne']

theorem heatWeight_mellin_integrable {d : ℕ} (hd : 0 < d)
    {k : Frequency d} (hk : k ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * heatWeight t k) (Ioi 0) := by
  have hr : 0 < Real.pi * radiusSq k :=
    mul_pos Real.pi_pos (lt_of_lt_of_le (by norm_num) (radiusSq_one_le hk))
  have h := gamma_integrand_integrable
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num : (0 : ℝ) < 2)) hr
  convert h using 1
  ext t
  congr 1
  unfold heatWeight
  congr 1
  ring

theorem heatWeight_mellin_integral {d : ℕ} (hd : 0 < d)
    {k : Frequency d} (hk : k ≠ 0) :
    (1 / 2 : ℝ) * (∫ t in Ioi 0, t ^ ((d : ℝ) / 2 - 1) * heatWeight t k) =
      greenMultiplier d k := by
  have hr : 0 < Real.pi * radiusSq k :=
    mul_pos Real.pi_pos (lt_of_lt_of_le (by norm_num) (radiusSq_one_le hk))
  have he : (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * heatWeight t k) =
      (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * Real.exp (-(Real.pi * radiusSq k * t))) := by
    funext t
    unfold heatWeight
    congr 2
    ring
  rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi
    (div_pos (Nat.cast_pos.mpr hd) (by norm_num)) hr, ← frequencyRadius_sq k]
  rw [radial_mellin_normalization hd (frequencyRadius_pos hk)]
  simp only [greenMultiplier, if_neg hk]

theorem nonzeroHeatWeight_mellin_integrable {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k) (Ioi 0) := by
  by_cases hk : k = 0
  · simp [nonzeroHeatWeight, hk]
  · simpa only [nonzeroHeatWeight, if_neg hk] using heatWeight_mellin_integrable hd hk

theorem nonzeroHeatWeight_mellin_integral {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    (∫ t in Ioi 0, t ^ ((d : ℝ) / 2 - 1) * nonzeroHeatWeight t k) =
      2 * greenMultiplier d k := by
  by_cases hk : k = 0
  · simp [nonzeroHeatWeight, hk, greenMultiplier]
  · have h := heatWeight_mellin_integral hd hk
    simp only [nonzeroHeatWeight, if_neg hk]
    linarith

end Legacy.TorusEndpoint.GreenMellinMultiplier
