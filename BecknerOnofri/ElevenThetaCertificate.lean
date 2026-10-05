module

public import BecknerOnofri.ElevenThetaIntegral

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Legacy.BecknerOnofri.ThetaDomination
namespace BecknerOnofri.HighDim.Eleven.ThetaBound

def base : ℝ := 2*((433 : ℝ)/10000)/(1-((433 : ℝ)/10000)^3)
def rate : ℝ := (157 : ℝ)/50

theorem theta_shifted {r : ℝ} (hr : 1 ≤ r) :
    realTheta (Real.pi*r) ≤ 1+base*Real.exp (-rate*(r-1)) := by
  have he : Real.exp (-Real.pi*r) ≤ (433/10000)*Real.exp (-rate*(r-1)) := by
    rw [show -Real.pi*r = -Real.pi + (-Real.pi*(r-1)) by ring, Real.exp_add]
    apply mul_le_mul exp_neg_pi_lt.le ?_ (Real.exp_pos _).le (by norm_num)
    apply Real.exp_le_exp.mpr
    have hp : rate ≤ Real.pi := by unfold rate; linarith [Real.pi_gt_d2]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left he
    (by norm_num : (0 : ℝ) ≤ 2/(1-((433 : ℝ)/10000)^3))
  have h := theta_uniform hr
  unfold base
  linarith

theorem exp_scaled (j : ℕ) (r : ℝ) :
    Real.exp (-(((j+1 : ℕ) : ℝ)*rate)*(r-1)) = (Real.exp (-rate*(r-1)))^(j+1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem polynomial_identity (b e : ℝ) :
    (1+b*e)^11-1 = ∑ j ∈ Finset.range 11,
      ((11 : ℕ).choose (j+1) : ℝ)*b^(j+1)*e^(j+1) := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

def row (j : ℕ) (r : ℝ) : ℝ :=
  ((11 : ℕ).choose (j+1) : ℝ)*base^(j+1)*
    (weightPolynomial r * Real.exp (-(((j+1 : ℕ) : ℝ)*rate)*(r-1)))

theorem integrand_le_rows {r : ℝ} (hr : 1 ≤ r) :
    thetaIntegrand realTheta 11 r ≤ ∑ j ∈ Finset.range 11, row j r := by
  have ht := one_le_realTheta (mul_pos Real.pi_pos (zero_lt_one.trans_le hr))
  have hz : 0 ≤ realTheta (Real.pi*r)^11-1 := sub_nonneg.mpr (one_le_pow₀ ht)
  have hp := pow_le_pow_left₀ (zero_le_one.trans ht) (theta_shifted hr) 11
  have hw : 0 ≤ weightPolynomial r := by unfold weightPolynomial; positivity
  unfold thetaIntegrand
  norm_num only [Nat.cast_ofNat, show (11 : ℝ)/2-1 = 9/2 by norm_num]
  calc
    _ ≤ weightPolynomial r * (realTheta (Real.pi*r)^11-1) :=
      mul_le_mul_of_nonneg_right (half_power_le hr) hz
    _ ≤ weightPolynomial r * ((1+base*Real.exp (-rate*(r-1)))^11-1) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hp 1) hw
    _ = ∑ j ∈ Finset.range 11, row j r := by
      rw [polynomial_identity, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [row, exp_scaled]
      ring

theorem row_integrable (j : ℕ) : IntegrableOn (row j) (Ici (1 : ℝ)) := by
  exact (shifted_weight_integrable
    (by unfold rate; positivity : 0 < ((j+1 : ℕ) : ℝ)*rate)).const_mul _

theorem row_integral (j : ℕ) :
    (∫ r : ℝ in Ici 1, row j r) =
      ((11 : ℕ).choose (j+1) : ℝ)*base^(j+1)*weightIntegralValue (((j+1 : ℕ) : ℝ)*rate) := by
  unfold row
  rw [integral_const_mul, shifted_weight_integral (by unfold rate; positivity)]

/-- The full dimension-eleven improper theta integral, with its rational
certificate completely discharged. -/
theorem thetaIntegral_lt : thetaIntegral realTheta 11 < (5 : ℝ)/2 := by
  have hi : IntegrableOn (fun r => ∑ j ∈ Finset.range 11, row j r) (Ici (1 : ℝ)) :=
    integrable_finsetSum _ (fun j _ => row_integrable j)
  have hb := setIntegral_mono_on theta_integrable hi measurableSet_Ici
    (fun r hr => integrand_le_rows hr)
  have he : (∫ r : ℝ in Ici 1, ∑ j ∈ Finset.range 11, row j r) = rationalUpper := by
    rw [integral_finsetSum _ (fun j _ => row_integrable j)]
    simp_rw [row_integral]
    simp only [rationalUpper, base, rate, weightIntegralValue, Nat.cast_add, Nat.cast_one]
  rw [he] at hb
  exact hb.trans_lt rationalUpper_lt

#print axioms thetaIntegral_lt
end BecknerOnofri.HighDim.Eleven.ThetaBound
