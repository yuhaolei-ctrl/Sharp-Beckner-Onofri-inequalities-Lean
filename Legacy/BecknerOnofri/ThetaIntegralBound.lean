module

public import Legacy.BecknerOnofri.ThetaConstants
public import Legacy.BecknerOnofri.ThetaIntegrability
public import Legacy.BecknerOnofri.ThetaPolynomialMajorant
public import Legacy.BecknerOnofri.ThetaPolynomialCertificate
public import Legacy.BecknerOnofri.ThetaExponentialIntegral

@[expose] public section

/-! A numerical bound for the actual theta integral.  The proof uses a
finite polynomial majorant of the complete one-dimensional theta series. -/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.ThetaBound
open ThetaCertificate ThetaDomination
open ThetaPolynomialCertificate

theorem exp_neg_a_le_r : Real.exp (-(a : ℝ)) ≤ (r : ℝ) := by
  have h := (div_lt_iff₀ r_pos).mp inverse_r_lt_exp_a
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  exact le_of_lt (by simpa [mul_comm] using h)

theorem exponential_rate_le {u : ℝ} (hu : 0 ≤ u) (q : ℕ) :
    Real.exp (-Real.pi * u) ^ q ≤ Real.exp (-((a : ℝ) * q) * u) := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right a_lt_pi.le (Nat.cast_nonneg q)) hu
  nlinarith

theorem exponential_coefficient_le (q : ℕ) :
    Real.exp (-((a : ℝ) * q)) ≤ (r : ℝ) ^ q := by
  calc
    _ = Real.exp (-(a : ℝ)) ^ q := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_a_le_r q

/-- All forty terms majorize the original theta integrand, including its
entire infinite series. -/
theorem integrand_le_finite_sum {u : ℝ} (hu : 1 ≤ u) :
    thetaIntegrand realTheta 10 u ≤
      ∑ q ∈ Finset.range 40, (coeff (q+1) : ℝ) *
        ThetaExponentialIntegral.weight ((a : ℝ)*(q+1)) u := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have ht : Real.pi ≤ Real.pi * u := by nlinarith [Real.pi_pos]
  have htpos : 0 < Real.pi * u := lt_of_lt_of_le Real.pi_pos ht
  have hpow := pow_le_pow_left₀ (le_trans zero_le_one (one_le_realTheta htpos))
    (realTheta_le_polynomial ht) 10
  have hw : 0 ≤ u^4 + u⁻¹ := by positivity
  have he : thetaIntegrand realTheta 10 u =
      (u^4+u⁻¹) * (realTheta (Real.pi*u)^10-1) := by
    unfold thetaIntegrand
    norm_num [Real.rpow_natCast]
  rw [he]
  calc
    _ ≤ (u^4+u⁻¹) * ((1+2*Real.exp (-Real.pi*u)+3*Real.exp (-Real.pi*u)^4)^10-1) := by
      apply mul_le_mul_of_nonneg_left _ hw
      simpa only [neg_mul] using sub_le_sub_right hpow 1
    _ = ∑ q ∈ Finset.range 40,
        (coeff (q+1) : ℝ) * ((u^4+u⁻¹)*Real.exp (-Real.pi*u)^(q+1)) := by
      rw [polynomial_identity, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      unfold ThetaExponentialIntegral.weight
      simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (exponential_rate_le hu0 (q+1)) hw)
        (Nat.cast_nonneg (coeff (q+1)) : (0 : ℝ) ≤ coeff (q+1))

theorem factorReal_nonneg {A : ℝ} (hA : 0 < A) : 0 ≤ factorReal A := by
  unfold factorReal
  positivity

/-- Integrate the finite majorant and use the certified rational constants. -/
theorem integral_le_certificate : thetaIntegral realTheta 10 ≤ upperReal := by
  have hi (q : ℕ) : IntegrableOn
      (fun u => (coeff (q+1) : ℝ) *
        ThetaExponentialIntegral.weight ((a : ℝ)*(q+1)) u) (Ici (1 : ℝ)) :=
    (ThetaExponentialIntegral.integrable_weight
      (mul_pos a_pos (by positivity) : 0 < (a : ℝ)*(q+1))).const_mul _
  have hs := integrable_finsetSum (Finset.range 40) (fun q _ => hi q)
  calc
    _ ≤ ∫ u in Ici (1 : ℝ), ∑ q ∈ Finset.range 40,
        (coeff (q+1) : ℝ) * ThetaExponentialIntegral.weight ((a : ℝ)*(q+1)) u := by
      apply setIntegral_mono_on integrableOn_realThetaIntegrand_ten hs measurableSet_Ici
      intro u hu
      exact integrand_le_finite_sum hu
    _ = ∑ q ∈ Finset.range 40, (coeff (q+1) : ℝ) *
        ThetaExponentialIntegral.weightIntegral ((a : ℝ)*(q+1)) := by
      rw [integral_finsetSum (Finset.range 40) (fun q _ => hi q)]
      simp only [integral_const_mul, ThetaExponentialIntegral.weightIntegral]
    _ ≤ upperReal := by
      unfold upperReal
      apply Finset.sum_le_sum
      intro q hq
      have hA : 0 < (a : ℝ)*(q+1) := mul_pos a_pos (by positivity)
      have hI := ThetaExponentialIntegral.integral_upper hA
      change ThetaExponentialIntegral.weightIntegral ((a : ℝ)*(q+1)) ≤
        Real.exp (-((a : ℝ)*(q+1))) * factorReal ((a : ℝ)*(q+1)) at hI
      calc
        _ ≤ (coeff (q+1) : ℝ) *
            (Real.exp (-((a : ℝ)*(q+1))) * factorReal ((a : ℝ)*(q+1))) :=
          mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)
        _ ≤ (coeff (q+1) : ℝ) *
            ((r : ℝ)^(q+1) * factorReal ((a : ℝ)*(q+1))) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (by simpa only [Nat.cast_add, Nat.cast_one] using exponential_coefficient_le (q+1))
            (factorReal_nonneg hA)
        _ = _ := by ring

/-- The manuscript's actual improper integral satisfies `J₁₀ < 41/25`.
There are no analytic hypotheses in this statement. -/
theorem realThetaIntegral_ten_lt : thetaIntegral realTheta 10 < (41/25 : ℝ) :=
  integral_le_certificate.trans_lt sum_real_lt

/-- The resulting numerical bound in every positive dimension at most ten. -/
theorem realThetaIntegral_lt {d : ℕ} (hd : 0 < d) (hd10 : d ≤ 10) :
    thetaIntegral realTheta d < (d : ℝ)/10 * (41/25 : ℝ) :=
  (realThetaIntegral_le_tenth_unconditional hd10).trans_lt
    (mul_lt_mul_of_pos_left realThetaIntegral_ten_lt (by positivity))

#print axioms realThetaIntegral_ten_lt

end Legacy.BecknerOnofri.ThetaBound
