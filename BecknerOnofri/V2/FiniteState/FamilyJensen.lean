module

public import BecknerOnofri.V2.FiniteState.FamilyFeasible
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-!
# State-zero cap by the written argument: `log(1+u) ≤ u` and Jensen (Lemma 5.19)

The manuscript (Appendix A.3, proof of `d12-spin-lem:feasible`) writes
`ν_0/b_0 = ∏_{k=0}^{11} (χ(1-a)+2k)/(χ+k)`, uses `log(1+u) ≤ u`, and applies Jensen's inequality
for the twelve integers `0,…,11` to the concave map `y ↦ (y-χa)/(χ+y)`, with mean `11/2`.

This file follows that route.  One small difference: concavity is obtained from the convexity of
`y ↦ (χ+y)⁻¹` on `[0,∞)` (`convexOn_zpow (-1)` translated by `χ`), writing
`(y-c)/(χ+y) = 1 - (χ+c)(χ+y)⁻¹`, instead of computing the second derivative
`-2χ(1+a)/(χ+y)³`.  The earlier tangent-line proof (`FamilyBounds`) is kept as an independent
cross-check; the theorems here have distinct names.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- `y ↦ (y - c)/(χ + y)` is concave on `[0, ∞)` when `χ > 0` and `χ + c > 0`
(second derivative `-2(χ+c)/(χ+y)³ < 0`). -/
theorem concaveOn_ratio {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun y => (y - c) / (χ + y)) := by
  have h1 : ConvexOn ℝ (Ici (0 : ℝ)) (fun y : ℝ => (χ + y) ^ (-1 : ℤ)) := by
    have := (convexOn_zpow (𝕜 := ℝ) (-1)).translate_right χ
    refine this.subset ?_ (convex_Ici 0)
    intro y hy
    show 0 < χ + y
    have : (0 : ℝ) ≤ y := hy
    linarith
  have h2 := ((h1.smul hc.le).neg)
  have h3 := h2.add (concaveOn_const (1 : ℝ) (convex_Ici (0 : ℝ)))
  refine h3.congr (fun y hy => ?_)
  have hy' : (0 : ℝ) ≤ y := hy
  have : 0 < χ + y := by linarith
  simp only [Pi.add_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- Jensen's inequality for the twelve integers `0,…,11` (mean `11/2`). -/
theorem sum_jensen {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ∑ k ∈ Finset.range 12, ((k : ℝ) - c) / (χ + k) ≤ 12 * ((11 / 2 - c) / (χ + 11 / 2)) := by
  have h := (concaveOn_ratio hχ hc).le_map_sum (t := Finset.range 12)
    (w := fun _ => (1 / 12 : ℝ)) (p := fun k => (k : ℝ))
    (fun _ _ => by norm_num) (by simp)
    (fun k _ => show (0 : ℝ) ≤ k from Nat.cast_nonneg k)
  have hm : ∑ k ∈ Finset.range 12, (1 / 12 : ℝ) • (k : ℝ) = 11 / 2 := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    norm_num [Finset.sum_range_succ]
  simp only [smul_eq_mul, ← Finset.mul_sum] at h hm ⊢
  rw [hm] at h
  linarith

/-- State-zero cap, written route: `log(ν_0/b_0) ≤ ∑ (k-χa)/(χ+k) ≤ 12 (11/2-χa)/(χ+11/2) < 0`. -/
theorem state_zero_ratio_lt_one_jensen {χ a : ℝ} (hχ : 0 < χ) (ha1 : a < 1)
    (hca : 11 / 2 < χ * a) :
    ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) < 1 := by
  have hapos : 0 < a := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hχ.le h]
  have hpos : ∀ k ∈ Finset.range 12, 0 < (χ * (1 - a) + 2 * k) / (χ + k) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 < 1 - a := by linarith
    positivity
  have hP : 0 < ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) :=
    Finset.prod_pos hpos
  rw [← Real.log_neg_iff hP, Real.log_prod (fun k hk => (hpos k hk).ne')]
  have hlog : ∀ k ∈ Finset.range 12,
      Real.log ((χ * (1 - a) + 2 * k) / (χ + k)) ≤ ((k : ℝ) - χ * a) / (χ + k) := by
    intro k hk
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : (χ * (1 - a) + 2 * k) / (χ + k) = ((k : ℝ) - χ * a) / (χ + k) + 1 := by
      field_simp; ring
    have := Real.log_le_sub_one_of_pos (hpos k hk)
    rw [e] at this ⊢
    linarith
  calc ∑ k ∈ Finset.range 12, Real.log ((χ * (1 - a) + 2 * k) / (χ + k))
      ≤ ∑ k ∈ Finset.range 12, ((k : ℝ) - χ * a) / (χ + k) := Finset.sum_le_sum hlog
    _ ≤ 12 * ((11 / 2 - χ * a) / (χ + 11 / 2)) := sum_jensen hχ (by nlinarith)
    _ < 0 := by
      have hm : 0 < χ + 11 / 2 := by linarith
      have : (11 / 2 - χ * a) / (χ + 11 / 2) < 0 := div_neg_of_neg_of_pos (by linarith) hm
      linarith

/-- `ν_0 < b_0` by the written (Jensen) route. -/
theorem famNu_zero_state_lt_jensen {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famNu t 0 < reference 0 := by
  have hχ := famChi_pos ht0 ht1
  have hca : 11 / 2 < famChi t * famBias t := by
    have := famChi_mul_bias_ge ht0 ht1; linarith
  exact famNu_zero_state_lt_of_ratio ht0 ht1
    (state_zero_ratio_lt_one_jensen hχ (famBias_lt_one ht0 ht1) hca)

theorem famLaw_zero_state_lt_jensen {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famLaw t 0 < reference 0 :=
  famLaw_zero_state_lt_of_nu ht0 ht1 (famNu_zero_state_lt_jensen ht0 ht1)

end BecknerOnofri.V2.FiniteState
