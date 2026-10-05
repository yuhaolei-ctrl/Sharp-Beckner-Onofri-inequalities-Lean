import Legacy.BecknerOnofri.Endpoint
import Legacy.BecknerOnofri.FiniteScalarCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.IntervalCases

/-!
# Matching the actual endpoint coefficient to the rational finite certificates

The lambda coefficient is twice the endpoint coefficient. In odd dimensions
the half-integer Gamma value cancels the square root in pi^(d/2), so only
integer powers of the rational lower bound for pi are needed.
-/

namespace Legacy.BecknerOnofri

open scoped Nat

theorem twice_endpointConstant_eq_gamma (d : ℕ) :
    2 * endpointConstant d = (d : ℝ) * Real.Gamma ((d : ℝ) / 2) /
      Real.pi ^ ((d : ℝ) / 2) := by
  unfold endpointConstant Legacy.TorusEndpoint.endpointSigma
  rw [div_div_eq_mul_div]
  ring

theorem twice_endpointConstant_even (m : ℕ) (hm : 1 ≤ m) :
    2 * endpointConstant (2 * m) =
      (2 * m : ℝ) * ((m - 1).factorial : ℝ) / Real.pi ^ m := by
  rw [twice_endpointConstant_eq_gamma]
  have he : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast]
  have hG := Real.Gamma_nat_eq_factorial (m - 1)
  rw [← Nat.cast_add_one, Nat.sub_add_cancel hm] at hG
  rw [hG]
  push_cast
  rfl

theorem twice_endpointConstant_odd (m : ℕ) :
    2 * endpointConstant (2 * m + 1) =
      (2 * m + 1 : ℝ) * ((2 * m - 1 : ℕ)‼ : ℝ) /
        (2 ^ m * Real.pi ^ m) := by
  rw [twice_endpointConstant_eq_gamma]
  have he : ((2 * m + 1 : ℕ) : ℝ) / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
  rw [he, Real.Gamma_nat_add_half, Real.rpow_add Real.pi_pos,
    Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hp := Real.pi_ne_zero
  push_cast
  field_simp

/-- The rational numerator after the half-integer Gamma simplification. -/
def scalarFactorQ (d : ℕ) : ℚ :=
  let m := d / 2
  if d % 2 = 0 then (d * Nat.factorial (m - 1) : ℕ)
  else (d * Nat.factorial (2 * m) : ℕ) / (4 ^ m * Nat.factorial m : ℕ)

theorem scalarFactorQ_nonneg (d : ℕ) : 0 ≤ scalarFactorQ d := by
  unfold scalarFactorQ
  split_ifs <;> positivity

theorem lambdaUpper_cast (d : ℕ) :
    (FiniteScalar.lambdaUpper d : ℝ) =
      (scalarFactorQ d : ℝ) / ((314159 / 100000 : ℝ) ^ (d / 2)) := by
  unfold FiniteScalar.lambdaUpper scalarFactorQ
  split_ifs <;> push_cast <;> ring

/-- Finite Gamma evaluations for exactly the dimensions used by the certificate. -/
theorem twice_endpointConstant_formula (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10) :
    2 * endpointConstant d = (scalarFactorQ d : ℝ) / Real.pi ^ (d / 2) := by
  interval_cases d
  · have h := twice_endpointConstant_odd 1
    norm_num [scalarFactorQ, Nat.doubleFactorial] at h ⊢
    convert h using 1 <;> ring
  · have h := twice_endpointConstant_even 2 (by decide)
    norm_num [scalarFactorQ] at h ⊢
    exact h
  · have h := twice_endpointConstant_odd 2
    norm_num [scalarFactorQ, Nat.doubleFactorial] at h ⊢
    convert h using 1 <;> ring
  · have h := twice_endpointConstant_even 3 (by decide)
    norm_num [scalarFactorQ] at h ⊢
    exact h
  · have h := twice_endpointConstant_odd 3
    norm_num [scalarFactorQ, Nat.doubleFactorial] at h ⊢
    convert h using 1 <;> ring
  · have h := twice_endpointConstant_even 4 (by decide)
    norm_num [scalarFactorQ] at h ⊢
    exact h
  · have h := twice_endpointConstant_odd 4
    norm_num [scalarFactorQ, Nat.doubleFactorial] at h ⊢
    convert h using 1 <;> ring
  · have h := twice_endpointConstant_even 5 (by decide)
    norm_num [scalarFactorQ] at h ⊢
    exact h

/-- The finite-certificate rational upper coefficient bounds the actual one. -/
theorem twice_endpointConstant_le_lambdaUpper (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10) :
    2 * endpointConstant d ≤ (FiniteScalar.lambdaUpper d : ℝ) := by
  rw [twice_endpointConstant_formula d hd3 hd10, lambdaUpper_cast]
  have hbase : (0 : ℝ) < 314159 / 100000 := by norm_num
  have hpi : (314159 / 100000 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d6]
  exact div_le_div_of_nonneg_left (by exact_mod_cast scalarFactorQ_nonneg d)
    (pow_pos hbase _) (pow_le_pow_left₀ hbase.le hpi _)

end Legacy.BecknerOnofri

#print axioms Legacy.BecknerOnofri.twice_endpointConstant_le_lambdaUpper
