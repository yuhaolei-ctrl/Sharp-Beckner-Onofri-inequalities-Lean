module

public import BecknerOnofri.Constants
public import Mathlib.Tactic

@[expose] public section

/-! Exact algebraic positivity of the quartic coefficient in dimensions at least twelve. -/

namespace BecknerOnofri.HighDim

theorem five_mul_dimension_le_half_power (d : ℕ) (hd : 12 ≤ d) :
    5 * (d : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by
  have hroot : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  induction d, hd using Nat.le_induction with
  | base =>
      rw [show ((12 : ℕ) : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
  | succ d hd ih =>
      have hdreal : (12 : ℝ) ≤ d := by exact_mod_cast hd
      have hnonneg : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      have hmul := mul_le_mul_of_nonneg_left hroot hnonneg
      have hexp : ((d + 1 : ℕ) : ℝ) / 2 = (d : ℝ) / 2 + 1 / 2 := by
        push_cast
        ring
      rw [hexp, Real.rpow_add (by norm_num)]
      push_cast
      nlinarith

theorem kappa_pos (d : ℕ) (hd : 12 ≤ d) : 0 < kappa d := by
  have hdreal : (12 : ℝ) ≤ d := by exact_mod_cast hd
  have hhalf := five_mul_dimension_le_half_power d hd
  have hfull : (6 : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      (6 : ℝ) ≤ (2 : ℝ) ^ (12 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hhalfpos : 0 < (2 : ℝ) ^ ((d : ℝ) / 2) - 1 := by linarith
  have hfullpos : 0 < 2 * ((2 : ℝ) ^ d - 1) := by linarith
  have hself : 1 / (2 * ((2 : ℝ) ^ d - 1)) ≤ (1 / 10 : ℝ) := by
    apply (div_le_iff₀ hfullpos).2
    linarith
  have hcross : 2 * ((d : ℝ) - 1) /
      ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) < (2 / 5 : ℝ) := by
    apply (div_lt_iff₀ hhalfpos).2
    linarith
  have hfullne : (2 : ℝ) ^ d - 1 ≠ 0 := by linarith
  have hformula : kappa d = (1 / 2 : ℝ) - 1 / (2 * ((2 : ℝ) ^ d - 1)) -
      2 * ((d : ℝ) - 1) / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) := by
    unfold kappa quarticA quarticB
    field_simp
    ring
  rw [hformula]
  linarith

end BecknerOnofri.HighDim
