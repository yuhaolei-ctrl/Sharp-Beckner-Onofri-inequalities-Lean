module

public import BecknerOnofri.V2.ThetaTail.GaussianZeta
public import BecknerOnofri.V2.ThetaTail.LogBridge

@[expose] public section

/-! # The explicit majorant `U(η)` (`d12-tail-eq:U`) and the rational comparisons

`U(η) = 2003/250 · log(1/η) + 77/1000 + 3111/800 η − 27/100 η² + η⁴/216 − ∑_{s=1}^{12} d_s e^{-sη}`.

* unconditional: `63/8 ζ(6) < 2003/250`, `ζ(5) < 1037/1000`, `ζ(4) > 27/25`, `ζ(2) < 5/3`,
  `c₀ < 77/1000` (real-analytic bridges to the kernel-checked rational certificates);
* HONESTLY CONDITIONAL on `TwelveSquareIdentity`: `G(η) < U(η)` for `0 < η < 1`. -/
noncomputable section
open Finset Filter Topology
namespace BecknerOnofri.V2.ThetaTail

/-- `U(η)` -/
def Ufun (η : ℝ) : ℝ :=
  2003 / 250 * (-Real.log η) + 77 / 1000 + 3111 / 800 * η - 27 / 100 * η ^ 2 + η ^ 4 / 216
    - ∑ t ∈ Finset.Icc 1 12, dCoeffR t * Real.exp (-η * t)

theorem log_two_gt : (693 : ℝ) / 1000 < Real.log 2 := by
  have h1 := logLower_le_log 16 2 (by norm_num)
  have h2 := ratCast_lt log2_lower
  push_cast at h1 h2 ⊢
  linarith

theorem log_three_gt : (1098 : ℝ) / 1000 < Real.log 3 := by
  have h1 := logLower_le_log 16 3 (by norm_num)
  have h2 := ratCast_lt log3_lower
  push_cast at h1 h2 ⊢
  linarith

theorem two_log_two_lt : 2 * Real.log 2 < (1387 : ℝ) / 2000 * 2 := by
  have h1 := log_le_logUpper 16 2 (by norm_num)
  have h2 := ratCast_lt log2_upper2
  push_cast at h1 h2 ⊢
  linarith

theorem log_four_lt : Real.log 4 < (1387 : ℝ) / 1000 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]
  have := two_log_two_lt
  linarith

theorem log_four_gt : (1386 : ℝ) / 1000 < Real.log 4 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]
  have := log_two_gt
  linarith

theorem zetaLog_ge : (693 : ℝ) / 64000 + 1098 / 729000 + 1386 / 4096000 < zetaLog := by
  have h := (summable_zetaLog).sum_le_tsum (range 4) (fun n _ => by
    exact div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
      (by positivity))
  have e : ∑ n ∈ range 4, Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ 6
      = Real.log 2 / 64 + Real.log 3 / 729 + Real.log 4 / 4096 := by
    simp [Finset.sum_range_succ]
    norm_num
  rw [e] at h
  have := log_two_gt
  have := log_three_gt
  have := log_four_gt
  unfold zetaLog
  linarith

theorem c0_lt : Real.log 4 / 8 * zetaR 6 - 63 / 8 * zetaLog < 77 / 1000 := by
  have h6 := zetaR_six_lt
  have hl := log_four_lt
  have hz := zetaLog_ge
  have hz0 : 0 < zetaR 6 := by
    unfold zetaR
    exact (summable_zetaTerm (p := 6) (by norm_num)).tsum_pos (fun n => by positivity) 0 (by positivity)
  have hl0 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hprod : Real.log 4 * zetaR 6 < (1387 / 1000) * (101737 / 100000) := by
    nlinarith
  have hc := ratCast_lt c0_upper
  push_cast at hc
  nlinarith

/-- `G(η) < U(η)` for `0 < η < 1`, conditional on the twelve-square identity. -/
theorem G_lt_U_of_twelveSquare (hT : TwelveSquareIdentity) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    G η < Ufun η := by
  have h := G_le_Phi_of_twelveSquare hT hη
  have hL : 0 < -Real.log η := by
    have := Real.log_neg hη hη1; linarith
  have z6 := zetaR_six_coeff_lt
  have z5 := zetaR_five_lt
  have z4 := zetaR_four_gt
  have z2 := zetaR_two_lt
  have c0 := c0_lt
  have z2nn : 0 ≤ zetaR 2 := by
    unfold zetaR
    exact tsum_nonneg fun n => by positivity
  have hη2 : 0 < η ^ 2 := by positivity
  have hη4 : 0 < η ^ 4 := by positivity
  unfold Ufun
  nlinarith [mul_lt_mul_of_pos_right z5 hη, mul_lt_mul_of_pos_right z4 hη2,
    mul_lt_mul_of_pos_right z2 hη4, mul_le_mul_of_nonneg_right z6.le hL.le]

end BecknerOnofri.V2.ThetaTail
