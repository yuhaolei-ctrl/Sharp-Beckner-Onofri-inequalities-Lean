module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem pi_six_upper : Real.pi^6 < 1000 := by
  have h := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num : 6 ≠ 0)
  norm_num at h
  linarith

theorem pi_six_scale_bounds : (8 : ℝ) < Real.pi^6/120 ∧ Real.pi^6/120 < 81/10 := by
  have hl := pow_lt_pow_left₀ Real.pi_gt_d4 (by norm_num : (0 : ℝ) ≤ 3.1415) (by norm_num : 6 ≠ 0)
  have hu := pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by norm_num : 6 ≠ 0)
  norm_num at hl hu
  constructor <;> linarith

theorem exp_pi_square_lower : (19000 : ℝ) < Real.exp (Real.pi^2) := by
  have harg : (24649/2500 : ℝ) < Real.pi^2 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  apply lt_trans _ (Real.exp_lt_exp.mpr harg)
  apply lt_of_lt_of_le _ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 24649/2500) 40)
  norm_num [Finset.sum_range_succ, Nat.factorial_succ]

#print axioms exp_pi_square_lower
#print axioms pi_six_scale_bounds
end BecknerOnofri.HighDim.EntropyTail
