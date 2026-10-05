module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact arithmetic used in the high-dimensional Beckner--Onofri argument

These lemmas establish the rational and polynomial comparisons in Section 5
of `sharp_beckner_onofri_flat_torus.tex`.  They do not assert the analytic
endpoint inequality or validate the separate finite-grid computation.
All arithmetic proofs are checked by Lean's kernel.
-/

namespace BecknerOnofri.Arithmetic

/-- The explicit majorant in the one-dimensional slice estimate. -/
theorem slice_majorant_eq :
    (3 : ℚ) / 4 * (1 + 128 / 729 +
      128 * ((2 : ℚ)⁻¹ ^ 12 + (2 : ℚ)⁻¹ ^ 11 / 11)) =
      311141 / 342144 := by
  norm_num

theorem slice_majorant_lt_one : (311141 : ℚ) / 342144 < 1 := by
  norm_num

theorem inverse_sqrt_two_lt_three_quarters :
    (1 : ℝ) / Real.sqrt 2 < 3 / 4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
  apply (div_lt_iff₀ hp).2
  nlinarith

theorem sqrt_two_gt_twenty_four_seventeenths :
    (24 : ℝ) / 17 < Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

/-- The first positive boundary value in the rectangular-lattice argument. -/
theorem pair_polynomial_identity (d : ℝ) :
    2 * (d - 2) ^ 2 - (d - 1) ^ 2 = (d - 3) ^ 2 - 2 := by
  ring

theorem pair_polynomial_pos {d : ℝ} (hd : 13 ≤ d) :
    0 < 2 * (d - 2) ^ 2 - (d - 1) ^ 2 := by
  rw [pair_polynomial_identity]
  have hh : 0 ≤ (d - 13) ^ 2 := sq_nonneg _
  nlinarith

/-- The second boundary value, expanded at the first transferred dimension. -/
theorem endpoint_polynomial_identity (d : ℝ) :
    2 * d ^ 3 - 27 * (d - 1) ^ 2 =
      2 * (d - 13) ^ 3 + 51 * (d - 13) ^ 2 + 366 * (d - 13) + 506 := by
  ring

theorem endpoint_polynomial_pos {d : ℝ} (hd : 13 ≤ d) :
    0 < 2 * d ^ 3 - 27 * (d - 1) ^ 2 := by
  rw [endpoint_polynomial_identity]
  have h2 : 0 ≤ (d - 13) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (d - 13) ^ 3 := pow_nonneg (by linarith) _
  linarith

theorem projected_dimension_ratio {d : ℝ} (hd : 13 ≤ d) :
    (11 : ℝ) / 12 ≤ (d - 2) / (d - 1) := by
  apply (le_div_iff₀ (by linarith : 0 < d - 1)).2
  linarith

/-- The logarithmic derivative majorant in the tail/reserve comparison. -/
theorem tail_ratio_derivative_majorant_neg {d : ℝ} (hd : 13 ≤ d) :
    25 / (2 * d) - 1 - 1 / (d - 1) < 0 := by
  have hp : 0 < 2 * d := by linarith
  have hq : 0 < d - 1 := by linarith
  have hfirst : 25 / (2 * d) < (1 : ℝ) := by
    apply (div_lt_one hp).2
    linarith
  have hlast : 0 < (1 : ℝ) / (d - 1) := div_pos (by norm_num) hq
  linarith

theorem tail_ratio_at_thirteen :
    ((17 : ℚ) / 15) ^ 2 * 2 ^ 14 / (13 * 12) ^ 2 = 295936 / 342225 := by
  norm_num

theorem tail_ratio_at_thirteen_lt_one : (295936 : ℚ) / 342225 < 1 := by
  norm_num

/-- The exact integer comparison converting the radial partition bound to
the initial density-norm bound. -/
theorem partition_to_initial_norm : (24000 : ℕ) ^ 5 < 300000 ^ 4 := by
  norm_num

theorem partition_to_initial_norm_real : (24000 : ℝ) ^ 5 < 300000 ^ 4 := by
  norm_num

theorem restart_norm : (67394 : ℚ) / 1000 < 100 := by norm_num

theorem restart_coefficient : (620979 : ℚ) / 1000000 < 7 / 10 := by norm_num

/-- The rational conclusion of the local-negativity exponential estimates. -/
theorem local_exit_ratio_eq :
    ((12 : ℚ) * (8 / 7)) / (64 * (1 - 6 / 64)) = 48 / 203 := by
  norm_num

theorem local_exit_ratio_lt : (48 : ℚ) / 203 < 6 / 25 := by norm_num

theorem local_exit_gap : (6 : ℚ) / 25 - 48 / 203 = 18 / 5075 := by norm_num

theorem local_exit_exponents :
    (12 : ℚ) / 98 = 6 / 49 ∧ (12 : ℚ) / 7 + 1 / 15 = 187 / 105 := by
  norm_num

/-- Geometric growth needed for negativity of every quartic branch coefficient. -/
theorem sqrt_two_pow_gt_four_dimension {d : ℕ} (hd : 12 ≤ d) :
    4 * (d : ℝ) < (Real.sqrt 2) ^ d := by
  induction d, hd using Nat.le_induction with
  | base =>
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have he : (Real.sqrt 2) ^ 12 = 64 := by
        calc
          (Real.sqrt 2) ^ 12 = ((Real.sqrt 2) ^ 2) ^ 6 := by ring
          _ = 64 := by rw [hs]; norm_num
      norm_num [he]
  | succ d hd ih =>
      have hs : (7 : ℝ) / 5 < Real.sqrt 2 := by
        have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_nonneg (2 : ℝ)
        nlinarith
      have hd' : (12 : ℝ) ≤ d := by exact_mod_cast hd
      have hp : 0 < (Real.sqrt 2) ^ d := by positivity
      have hh := mul_lt_mul_of_pos_left hs hp
      rw [pow_succ]
      push_cast
      nlinarith

/-- Reconcile the integer power used in the growth induction with the
paper's real exponent, including odd dimensions. -/
theorem half_dimension_power (d : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) / 2) = (Real.sqrt 2) ^ d := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

theorem spectral_power_gt_four_dimension {d : ℕ} (hd : 12 ≤ d) :
    4 * (d : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2) := by
  rw [half_dimension_power]
  exact sqrt_two_pow_gt_four_dimension hd

/-- The algebraic sign criterion for the full-branch quartic coefficient. -/
theorem kappa_positive_of_growth {d t : ℝ} (hd : 1 ≤ d) (ht : 4 * d < t) :
    0 < -(2 * (-(1 / 4 : ℝ) + 1 / (4 * (t ^ 2 - 1))) +
      (d - 1) * (2 / (t - 1))) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have ht2 : 0 < t ^ 2 - 1 := by nlinarith
  have hg : 0 < (t - 4 * d) * t := mul_pos (by linarith) ht0
  have hn : 0 < t ^ 2 - 4 * (d - 1) * t - 4 * d + 2 := by nlinarith
  have he : -(2 * (-(1 / 4 : ℝ) + 1 / (4 * (t ^ 2 - 1))) +
      (d - 1) * (2 / (t - 1))) =
      (t ^ 2 - 4 * (d - 1) * t - 4 * d + 2) / (2 * (t ^ 2 - 1)) := by
    field_simp
    ring
  rw [he]
  exact div_pos hn (mul_pos (by norm_num) ht2)

/-- Positivity of the exact coefficient in the high-dimensional main theorem.
The half-dimensional exponent is a real power, so odd dimensions are included. -/
theorem kappa_positive {d : ℕ} (hd : 12 ≤ d) :
    0 < -(2 * (-(1 / 4 : ℝ) + 1 / (4 * ((2 : ℝ) ^ d - 1))) +
      ((d : ℝ) - 1) * (2 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1))) := by
  have hs : ((2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ d := by
    rw [half_dimension_power, ← pow_mul, Nat.mul_comm d 2, pow_mul,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  simpa only [hs] using kappa_positive_of_growth hd' (spectral_power_gt_four_dimension hd)

end BecknerOnofri.Arithmetic
