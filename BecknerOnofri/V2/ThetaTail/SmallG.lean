module

public import BecknerOnofri.V2.ThetaTail.GaussianU
public import BecknerOnofri.V2.ThetaTail.ExpBridge

@[expose] public section

/-! # `G(2/5) < 23/200`, `G(2/7) < 33/100` (`d12-tail-eq:smallG`) and `e^{8/5} < 5`

The real-analytic bridges to the kernel-checked rational certificates of Appendix B.1 are
unconditional; the final inequalities `G(2/5) < 23/200`, `G(2/7) < 33/100` are HONESTLY
CONDITIONAL on `TwelveSquareIdentity` (they go through `G_lt_U_of_twelveSquare`). -/
noncomputable section
open Finset Filter Topology
namespace BecknerOnofri.V2.ThetaTail

lemma dCoeffR_pos {t : ℕ} (ht : t ∈ Finset.Icc 1 12) : 0 < dCoeffR t := by
  have := dCoeff_pos t ht
  unfold dCoeffR
  exact_mod_cast this

/-- `∑ d_s E_M(c s) ≤ ∑ d_s e^{-c s}` for odd `M`, `c ≥ 0` -/
theorem dExpSum_le (M : ℕ) (hM : Odd M) (c : ℚ) (hc : 0 ≤ c) :
    ((dExpSum M c : ℚ) : ℝ) ≤ ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-(c : ℝ) * t) := by
  unfold dExpSum
  push_cast
  refine sum_le_sum fun t ht => ?_
  have h := expAlt_le_exp_neg M hM (c * t) (by positivity)
  push_cast at h
  have e : -(c : ℝ) * t = -((c : ℝ) * t) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (dCoeffR_pos ht).le

theorem Ufun_two_fifths_lt : Ufun (2 / 5) < 23 / 200 := by
  have hlog : Real.log (5 / 2) < 9163 / 10000 := by
    have h1 := log_le_logUpper 16 (5 / 2) (by norm_num)
    have h2 := ratCast_lt log52_upper
    push_cast at h1 h2 ⊢
    linarith
  have hS := dExpSum_le 13 (by decide) (2 / 5) (by norm_num)
  have hq := ratCast_lt smallG_52
  push_cast at hS hq
  unfold Ufun
  have e : -Real.log (2 / 5) = Real.log (5 / 2) := by
    rw [← Real.log_inv]; norm_num
  rw [e]
  have hS' : (8817 : ℝ) / 1000 < ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-(2 / 5) * t) := by
    have hh : ((dExpSum 13 (2 / 5) : ℚ) : ℝ) = _ := rfl
    linarith
  have e2 : (-(2 / 5 : ℝ)) = -(2 / 5 : ℝ) := rfl
  norm_num at hS' ⊢
  nlinarith [hlog, hS']

theorem Ufun_two_sevenths_lt : Ufun (2 / 7) < 33 / 100 := by
  have hlog : Real.log (7 / 2) < 1566 / 1250 := by
    have h1 := log_le_logUpper 16 (7 / 2) (by norm_num)
    have h2 := ratCast_lt log72_upper
    push_cast at h1 h2 ⊢
    linarith
  have hS := dExpSum_le 11 (by decide) (2 / 7) (by norm_num)
  have hq := ratCast_lt smallG_72
  push_cast at hS hq
  unfold Ufun
  have e : -Real.log (2 / 7) = Real.log (7 / 2) := by
    rw [← Real.log_inv]; norm_num
  rw [e]
  have hS' : (272 : ℝ) / 25 < ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-(2 / 7) * t) := by
    linarith
  norm_num at hS' ⊢
  nlinarith [hlog, hS']

/-- `G(2/5) < 23/200` (conditional) -/
theorem G_two_fifths_lt_of_twelveSquare (hT : TwelveSquareIdentity) : G (2 / 5) < 23 / 200 :=
  (G_lt_U_of_twelveSquare hT (by norm_num) (by norm_num)).trans Ufun_two_fifths_lt

/-- `G(2/7) < 33/100` (conditional) -/
theorem G_two_sevenths_lt_of_twelveSquare (hT : TwelveSquareIdentity) : G (2 / 7) < 33 / 100 :=
  (G_lt_U_of_twelveSquare hT (by norm_num) (by norm_num)).trans Ufun_two_sevenths_lt

end BecknerOnofri.V2.ThetaTail
