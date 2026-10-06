module

public import BecknerOnofri.SpinPressureReduction
public import BecknerOnofri.SpinLargeMean
public import BecknerOnofri.SpinSmallMean
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The finite-state inequality (Proposition 5.12(ii))

For every exchangeable spin law with count vector `p ∈ 𝓟_t`, `G_t(p) ≥ t⁴/200`.

* For `1/16 ≤ t ≤ 0.99` we use `G_t(p) ≥ 𝓑(t)` and Lemma 5.19, `𝓑(t) > t⁴/200`.
* For `0.99 ≤ t ≤ 1` we use the high-mean bound (eq:section5-spin-large-mean-bound).
* For `0 ≤ t ≤ 1/16` we use the analytic small-mean estimate `SpinSmallMean`, which gives
  `F(p) + 12 · (3/40) t⁴ ≥ t⁴/50`. This replaces the manuscript's origin-jet argument for
  `(0, 1/500]` and the Taylor-model cells of `[1/500, 1/16]`; the case `t = 0` is included.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Set

namespace BecknerOnofri.HighDim.Spin

/-- The η-term of `G_t` is nonnegative: `H(p|b) ≥ 12 I_B(t)` on `𝓟_t`. -/
theorem eta_term_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {p : Count → ℝ}
    (hp : FeasibleAt t p) : 0 ≤ eta t * (relativeEntropy p reference - 12 * binaryCost t) := by
  rcases eq_or_lt_of_le ht1 with rfl | hlt
  · simp [eta]
  · exact mul_nonneg (eta_nonneg ht0 ht1)
      (sub_nonneg.mpr (entropy_lower_at_smaller_mean t t p ht0 hlt le_rfl hp))

theorem psi_mono {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) : psi a ≤ psi t := by
  unfold psi
  have h4 := pow_le_pow_left₀ ha hat 4
  have h10 := pow_le_pow_left₀ ha hat 10
  linarith

/-- Proposition 5.12(ii) for small means. -/
theorem penalized_small_mean {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 16) {p : Count → ℝ}
    (hp : FeasibleAt t p) : t ^ 4 / 200 ≤ penalized t p := by
  have hs := small_mean_spin_inequality t p ht0 ht hp
  have he := eta_term_nonneg ht0 (by linarith) hp
  have hψ : 3 / 40 * t ^ 4 ≤ psi t := by
    unfold psi; nlinarith [pow_nonneg ht0 10]
  have h4 : 0 ≤ t ^ 4 := by positivity
  unfold penalized
  nlinarith

theorem log_one_point_nine_nine_lower : (6881346 / 10000000 : ℝ) < Real.log (199 / 100) := by
  have h2 := Real.log_two_gt_d9
  have hq := log_le_half_sub_inv (x := 200 / 199) (by norm_num)
  have hsplit : Real.log (199 / 100) = Real.log 2 - Real.log (200 / 199) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hsplit]
  norm_num at hq h2 ⊢
  linarith

theorem log_hundred_upper : Real.log 100 < 46052 / 10000 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 46052 / 10000) 30
  have hs : (100 : ℝ) < ∑ j ∈ Finset.range 30, (46052 / 10000 : ℝ) ^ j / j.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- The high-mean constant: `24 I_B(0.99) - Σ w_s + 12 ψ(0.99) > 0.034`. -/
theorem large_mean_constant :
    (34 / 1000 : ℝ) < 24 * binaryCost (99 / 100) - (∑ s : Order, weight s) + 12 * psi (99 / 100) := by
  have h1 := log_one_point_nine_nine_lower
  have h2 := log_hundred_upper
  have hb : binaryCost (99 / 100) =
      ((199 / 100) * Real.log (199 / 100) - (1 / 100) * Real.log 100) / 2 := by
    unfold binaryCost
    rw [show (1 : ℝ) - 99 / 100 = (100 : ℝ)⁻¹ by norm_num, show (1 : ℝ) + 99 / 100 = 199 / 100 by
      norm_num, Real.log_inv]
    ring
  have hw : (∑ s : Order, weight s) = ((∑ s : Order, weightQ s : ℚ) : ℝ) := by
    simp [weight]
  have hwq : (∑ s : Order, weightQ s) = 2623054016093528283908531 / 141778173564004158720000 := by
    decide +kernel
  rw [hb, hw, hwq]
  unfold psi
  norm_num
  nlinarith [h1, h2]

/-- Proposition 5.12(ii) for large means. -/
theorem penalized_large_mean {t : ℝ} (ht : 99 / 100 ≤ t) (ht1 : t ≤ 1) {p : Count → ℝ}
    (hp : FeasibleAt t p) : t ^ 4 / 200 ≤ penalized t p := by
  have hl := large_mean_spin_lower (99 / 100) t p psi (by norm_num) (by norm_num) ht hp
    (psi_mono (by norm_num) ht)
  have hc := large_mean_constant
  have he := eta_term_nonneg (by linarith) ht1 hp
  have h4 : t ^ 4 ≤ 1 := pow_le_one₀ (by linarith) ht1
  unfold penalized
  linarith

/-- **Proposition 5.12(ii)** (prop:section5-spin-entropy (ii)), given Lemma 5.19 on
`[1/16, 0.99]`: every `p ∈ 𝓟_t`, `0 ≤ t ≤ 1`, satisfies `G_t(p) ≥ t⁴/200`. -/
theorem finite_state_inequality_of_pressure
    (hB : ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < pressureScalar t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {p : Count → ℝ} (hp : FeasibleAt t p) :
    t ^ 4 / 200 ≤ penalized t p := by
  by_cases h1 : t ≤ 1 / 16
  · exact penalized_small_mean ht.1 h1 hp
  by_cases h2 : t ≤ 99 / 100
  · push Not at h1
    exact (hB t ⟨h1.le, h2⟩).le.trans
      (pressureScalar_le_penalized (by linarith) (by linarith) hp)
  · push Not at h2
    exact penalized_large_mean h2.le ht.2 hp

end BecknerOnofri.HighDim.Spin
