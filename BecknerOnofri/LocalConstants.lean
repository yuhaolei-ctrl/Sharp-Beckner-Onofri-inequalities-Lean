import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
The two actual real-exponential estimates used in the manuscript's dimension-twelve
local strict-negativity criterion, including the final denominator and ratio bounds.
The finite Taylor bounds below are Mathlib theorems with kernel-checked rational
arithmetic; no floating-point oracle or numerical execution is trusted.
-/

namespace BecknerOnofri.HighDim

theorem exp_six_over_fortynine_lt : Real.exp (6 / 49 : ℝ) < 8 / 7 := by
  calc
    Real.exp (6 / 49 : ℝ) < 1 / (1 - 6 / 49 : ℝ) :=
      Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)
    _ < 8 / 7 := by norm_num

theorem exp_187_over_105_lt : Real.exp (187 / 105 : ℝ) < 6 := by
  have hhalf : Real.exp (187 / 210 : ℝ) < 61 / 25 := by
    calc
      Real.exp (187 / 210 : ℝ) ≤
          (∑ m ∈ Finset.range 4, (187 / 210 : ℝ) ^ m / m.factorial) +
            (187 / 210 : ℝ) ^ 4 * (4 + 1) / ((4 : ℕ).factorial * 4) :=
        Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
      _ < 61 / 25 := by norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [show (187 / 105 : ℝ) = 187 / 210 + 187 / 210 by norm_num, Real.exp_add]
  calc
    Real.exp (187 / 210 : ℝ) * Real.exp (187 / 210 : ℝ) <
        (61 / 25 : ℝ) * (61 / 25 : ℝ) :=
      mul_self_lt_mul_self (Real.exp_nonneg _) hhalf
    _ < 6 := by norm_num

theorem local_exit_denominator_pos :
    0 < 1 - Real.exp (187 / 105 : ℝ) / 64 := by
  linarith [exp_187_over_105_lt]

theorem local_exit_ratio_bound :
    (12 / 64 : ℝ) * Real.exp (6 / 49 : ℝ) /
      (1 - Real.exp (187 / 105 : ℝ) / 64) < 48 / 203 := by
  apply (div_lt_iff₀ local_exit_denominator_pos).2
  linarith [exp_six_over_fortynine_lt, exp_187_over_105_lt]

theorem local_exit_ratio_lt :
    (12 / 64 : ℝ) * Real.exp (6 / 49 : ℝ) /
      (1 - Real.exp (187 / 105 : ℝ) / 64) < 6 / 25 :=
  lt_trans local_exit_ratio_bound (by norm_num)

end BecknerOnofri.HighDim
