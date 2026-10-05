import BecknerOnofri.ElevenThetaBound

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Legacy.BecknerOnofri.ThetaDomination
open Legacy.BecknerOnofri.ThetaExponentialIntegral
namespace BecknerOnofri.HighDim.Eleven.ThetaBound

theorem shifted_moment_integral (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ici 1, r^m * Real.exp (-a*(r-1))) = laplacePolynomial m a := by
  rw [integral_Ici_eq_integral_Ioi]
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) 1).setIntegral_preimage_emb
    (MeasurableEquiv.addRight (1 : ℝ)).measurableEmbedding
      (fun r : ℝ => r^m * Real.exp (-a*(r-1))) (Ioi 1)
  rw [preimage_add_const_Ioi, sub_self] at hshift
  rw [← hshift]
  have he (v : ℝ) : (v+1)^m * Real.exp (-a*((v+1)-1)) =
      ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * (v^j * Real.exp (-a*v)) := by
    rw [add_sub_cancel_right, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow, mul_one]
    ring
  simp_rw [he]
  rw [integral_finsetSum (Finset.range (m+1))
    (fun j _ => (scaled_moment_integrable j ha).const_mul _)]
  simp only [integral_const_mul, scaled_moment_integral _ ha]
  unfold laplacePolynomial
  apply Finset.sum_congr rfl
  intro j _
  rw [one_div_pow]
  ring

theorem laplacePolynomial_pos (m : ℕ) {a : ℝ} (ha : 0 < a) : 0 < laplacePolynomial m a := by
  unfold laplacePolynomial
  apply Finset.sum_pos' (fun j _ => by positivity)
  refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  simpa using one_div_pos.mpr ha

theorem shifted_moment_integrable (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r^m * Real.exp (-a*(r-1))) (Ici 1) := by
  apply Integrable.of_integral_ne_zero
  rw [shifted_moment_integral m ha]
  exact (laplacePolynomial_pos m ha).ne'

def weightPolynomial (r : ℝ) : ℝ := (r^4+r^5)/2+1
def weightIntegralValue (a : ℝ) : ℝ :=
  (laplacePolynomial 4 a+laplacePolynomial 5 a)/2+laplacePolynomial 0 a

theorem shifted_weight_integral {a : ℝ} (ha : 0 < a) :
    (∫ r : ℝ in Ici 1, weightPolynomial r * Real.exp (-a*(r-1))) = weightIntegralValue a := by
  have he (r : ℝ) : weightPolynomial r * Real.exp (-a*(r-1)) =
      (r^4 * Real.exp (-a*(r-1)) + r^5 * Real.exp (-a*(r-1)))/2 +
        r^0 * Real.exp (-a*(r-1)) := by unfold weightPolynomial; ring
  simp_rw [he]
  have hdiv : Integrable (fun r : ℝ =>
      (r^4 * Real.exp (-a*(r-1)) + r^5 * Real.exp (-a*(r-1)))/2)
      (volume.restrict (Ici 1)) :=
    ((shifted_moment_integrable 4 ha).add (shifted_moment_integrable 5 ha)).div_const 2
  rw [integral_add hdiv (shifted_moment_integrable 0 ha),
    integral_div, integral_add (shifted_moment_integrable 4 ha) (shifted_moment_integrable 5 ha)]
  simp only [shifted_moment_integral _ ha, weightIntegralValue]

theorem shifted_weight_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => weightPolynomial r * Real.exp (-a*(r-1))) (Ici 1) := by
  apply Integrable.of_integral_ne_zero
  rw [shifted_weight_integral ha]
  exact (show 0 < weightIntegralValue a from by
    unfold weightIntegralValue
    have := laplacePolynomial_pos 4 ha
    have := laplacePolynomial_pos 5 ha
    have := laplacePolynomial_pos 0 ha
    positivity).ne'

theorem half_power_le {r : ℝ} (hr : 1 ≤ r) :
    r^(9/2 : ℝ)+r⁻¹ ≤ weightPolynomial r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hpow : r^(9/2 : ℝ) = r^4 * Real.sqrt r := by
    rw [show (9/2 : ℝ) = (4 : ℕ)+(1/2 : ℝ) by norm_num,
      Real.rpow_add hr0, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : Real.sqrt r ≤ (r+1)/2 := by
    nlinarith [sq_nonneg (Real.sqrt r-1), Real.sq_sqrt hr0.le]
  have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg hr0.le 4)
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  rw [hpow]
  unfold weightPolynomial
  nlinarith

#print axioms shifted_weight_integral
end BecknerOnofri.HighDim.Eleven.ThetaBound
