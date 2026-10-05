import Legacy.BecknerOnofri.ThetaDomination
import Mathlib.Analysis.Real.Pi.Bounds

/-!
A sparse polynomial majorant for the actual integer theta series on `t ≥ π`.
The geometric-series tail is proved with explicit summability; it does not
redefine theta or assume a finite-shell interpretation.
-/

open scoped BigOperators

namespace Legacy.BecknerOnofri.ThetaDomination

/-- The real theta function is its zero mode plus twice its positive modes. -/
theorem realTheta_eq_one_add_two_mul_tsum {t : ℝ} (ht : 0 < t) :
    realTheta t = 1 + 2 * ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have heven : Function.Even (fun j : ℤ ↦ Real.exp (-t * (j : ℝ) ^ 2)) := by
    intro j
    simp only [Int.cast_neg, neg_sq]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat heven (summable_realTheta ht)
  simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Real.exp_zero,
    Int.cast_natCast, two_nsmul] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ Real.exp (-t * (n : ℝ) ^ 2))] at h
  change realTheta t = 1 + _ at h
  linarith

/-- A convenient geometric-series ratio bound throughout the integration range. -/
theorem exp_neg_le_one_third {t : ℝ} (ht : Real.pi ≤ t) :
    Real.exp (-t) ≤ (1 / 3 : ℝ) := by
  have hE : (3 : ℝ) ≤ Real.exp t := by
    have hp := Real.pi_gt_three
    have he := Real.add_one_le_exp t
    linarith
  calc
    Real.exp (-t) = 1 / Real.exp t := by rw [Real.exp_neg, one_div]
    _ ≤ (1 / 3 : ℝ) := one_div_le_one_div_of_le (by norm_num) hE

/-- Each mode after the first positive one is bounded by a geometric term. -/
theorem exp_square_shift_two_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Real.exp (-t * ((n + 2 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-t) ^ 4 * Real.exp (-t) ^ n := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : (n : ℝ) + 4 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
  have hp := mul_le_mul_of_nonneg_left hs ht
  push_cast
  nlinarith only [hp]

/-- A geometric majorant controls the complete infinite positive-mode tail. -/
theorem realTheta_positive_tail_le {t : ℝ} (ht : Real.pi ≤ t) :
    (∑' n : ℕ, Real.exp (-t * ((n + 2 : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (-t) ^ 4 * (1 - Real.exp (-t))⁻¹ := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := lt_of_le_of_lt (exp_neg_le_one_third ht) (by norm_num)
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-t * (n : ℝ) ^ 2)) := by
    simpa only [Int.cast_natCast] using
      (summable_int_iff_summable_nat_and_neg.mp (summable_realTheta htpos)).1
  have htail : Summable (fun n : ℕ ↦ Real.exp (-t * ((n + 2 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 2).mpr hnat
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-t) ^ 4 * Real.exp (-t) ^ n :=
      htail.tsum_le_tsum (exp_square_shift_two_le htpos.le)
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

/-- The sparse polynomial majorant for the manuscript's actual theta function. -/
theorem realTheta_le_polynomial {t : ℝ} (ht : Real.pi ≤ t) :
    realTheta t ≤ 1 + 2 * Real.exp (-t) + 3 * (Real.exp (-t)) ^ 4 := by
  have htpos : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have hq := exp_neg_le_one_third ht
  have hden : 0 < 1 - Real.exp (-t) := by linarith
  have hfac : 2 * (1 - Real.exp (-t))⁻¹ ≤ (3 : ℝ) := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hden).mpr (by linarith)
  have htail := realTheta_positive_tail_le ht
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-t * (n : ℝ) ^ 2)) := by
    simpa only [Int.cast_natCast] using
      (summable_int_iff_summable_nat_and_neg.mp (summable_realTheta htpos)).1
  have hone : Summable (fun n : ℕ ↦ Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hnat
  have he := hone.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.cast_one, one_pow, mul_one,
    show ∀ n : ℕ, n + 1 + 1 = n + 2 from fun n ↦ by omega] at he
  rw [realTheta_eq_one_add_two_mul_tsum htpos, he]
  have hmul := mul_le_mul_of_nonneg_right hfac
    (show 0 ≤ Real.exp (-t) ^ 4 by positivity)
  nlinarith only [htail, hmul]

end Legacy.BecknerOnofri.ThetaDomination
