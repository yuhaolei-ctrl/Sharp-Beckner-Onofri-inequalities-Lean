import Legacy.BecknerOnofri.GaussianTheta
import Legacy.BecknerOnofri.GaussianMellinTerm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Mellin inversion for the actual nonzero Gaussian lattice sum.
The exchange of the infinite sum and the improper integral is justified by
summability of the integrals of the norms. Odd dimensions use real powers. -/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.GaussianLattice
open Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability ThetaDomination

noncomputable def mellinTerm {d : ℕ} (a : ℝ) (k : Frequency d) (t : ℝ) : ℝ :=
  ((t-a)^((d : ℝ)/2-1) * nonzeroGaussian t k) / Real.Gamma ((d : ℝ)/2)

noncomputable def mellinIntegrand (d : ℕ) (a t : ℝ) : ℝ :=
  (t-a)^((d : ℝ)/2-1) * (realTheta t^d-1)

theorem mellinTerm_integrable {d : ℕ} (hd : 0 < d) (a : ℝ) (k : Frequency d) :
    IntegrableOn (mellinTerm a k) (Ioi a) := by
  change IntegrableOn (fun t => mellinTerm a k t) (Ioi a)
  by_cases hk : k = 0
  · simp [mellinTerm, nonzeroGaussian, hk]
  · have h := GaussianMellinTerm.normalized_dimension_integrable hd (radiusSq_one_le hk) a
    simpa only [mellinTerm, nonzeroGaussian, if_neg hk, gaussian, mul_comm] using h

theorem mellinTerm_integral {d : ℕ} (hd : 0 < d) (a : ℝ) (k : Frequency d) :
    (∫ t in Ioi a, mellinTerm a k t) = gaussianTerm a k := by
  by_cases hk : k = 0
  · simp [mellinTerm, nonzeroGaussian, gaussianTerm, spectralWeight, hk]
  · have h := GaussianMellinTerm.normalized_dimension_integral hd (radiusSq_one_le hk) a
    simpa only [mellinTerm, nonzeroGaussian, if_neg hk, gaussianTerm, spectralWeight,
      gaussian, mul_comm, one_div, div_eq_mul_inv, one_mul] using h

theorem mellinTerm_nonneg {d : ℕ} (hd : 0 < d) {a t : ℝ} (ht : a < t)
    (k : Frequency d) : 0 ≤ mellinTerm a k t := by
  unfold mellinTerm
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (sub_pos.mpr ht).le _) (nonzeroGaussian_nonneg t k))
    (Real.Gamma_pos_of_pos (div_pos (Nat.cast_pos.mpr hd) (by norm_num))).le

theorem summable_integral_norm_mellinTerm {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : Frequency d => ∫ t in Ioi a, ‖mellinTerm a k t‖) := by
  have he (k : Frequency d) :
      (∫ t in Ioi a, ‖mellinTerm a k t‖) = gaussianTerm a k := by
    rw [← mellinTerm_integral hd a k]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.norm_of_nonneg (mellinTerm_nonneg hd ht k)
  simp_rw [he]
  exact summable_gaussianTerm ha

/-- Sum the normalized, nonzero Gaussian Mellin integrands on the actual
integer lattice; summability of each theta series is proved separately. -/
theorem tsum_mellinTerm {d : ℕ} (a : ℝ) {t : ℝ} (ht : 0 < t) :
    (∑' k : Frequency d, mellinTerm a k t) =
      mellinIntegrand d a t / Real.Gamma ((d : ℝ)/2) := by
  simp only [mellinTerm, mellinIntegrand, tsum_div_const, tsum_mul_left,
    tsum_nonzeroGaussian_eq_theta_pow_sub_one d ht]

/-- The full shifted Mellin identity, with all interchange hypotheses proved. -/
theorem gaussianEnergy_mellin {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    gaussianEnergy d a =
      (1 / Real.Gamma ((d : ℝ)/2)) * ∫ t in Ioi a, mellinIntegrand d a t := by
  have h := integral_tsum_of_summable_integral_norm
    (mellinTerm_integrable hd a) (summable_integral_norm_mellinTerm hd ha)
  simp only [mellinTerm_integral hd a] at h
  change gaussianEnergy d a = _ at h
  calc
    _ = ∫ t in Ioi a, ∑' k : Frequency d, mellinTerm a k t := h
    _ = ∫ t in Ioi a, mellinIntegrand d a t / Real.Gamma ((d : ℝ)/2) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact tsum_mellinTerm a (lt_trans ha ht)
    _ = _ := by rw [integral_div]; ring

theorem gaussianEnergy_pos {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    0 < gaussianEnergy d a := by
  let k : Frequency d := fun _ => 1
  have hk : k ≠ 0 := by
    intro h
    have he := congrFun h ⟨0, hd⟩
    norm_num [k] at he
  have hr : 0 < radiusSq k := lt_of_lt_of_le zero_lt_one (radiusSq_one_le hk)
  apply (summable_gaussianTerm ha).tsum_pos
    (fun l => mul_nonneg (spectralWeight_nonneg l) (Real.exp_pos _).le) k
  unfold gaussianTerm spectralWeight gaussian
  rw [if_neg hk]
  exact mul_pos (one_div_pos.mpr (Real.sqrt_pos.mpr (pow_pos hr d))) (Real.exp_pos _)

/-- The actual theta integrand in the Mellin identity is integrable. -/
theorem integrable_mellinIntegrand {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (mellinIntegrand d a) (Ioi a) := by
  apply Integrable.of_integral_ne_zero
  intro hz
  have h := gaussianEnergy_mellin hd ha
  rw [hz, mul_zero] at h
  exact (gaussianEnergy_pos hd ha).ne' h

#print axioms gaussianEnergy_mellin
#print axioms integrable_mellinIntegrand
end Legacy.BecknerOnofri.GaussianLattice
