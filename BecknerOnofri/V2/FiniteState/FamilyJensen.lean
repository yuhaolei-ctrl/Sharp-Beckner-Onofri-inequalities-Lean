module

public import BecknerOnofri.V2.FiniteState.FamilyFeasible
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# State-zero cap by the written argument: `log(1+u) ≤ u` and Jensen (Lemma 5.19)

The manuscript (Appendix A.3, proof of `d12-spin-lem:feasible`) writes
`ν_0/b_0 = ∏_{k=0}^{11} (χ(1-a)+2k)/(χ+k)`, uses `log(1+u) ≤ u`, and applies Jensen's inequality
for the twelve integers `0,…,11` to the concave map `y ↦ (y-χa)/(χ+y)`, with mean `11/2`.

This file follows that route: concavity of `y ↦ (y-c)/(χ+y)` on `[0,∞)` is obtained from the
second derivative `-2(χ+c)/(χ+y)³ < 0` (`concaveOn_of_deriv2_nonpos`), with `c = χa`.  The earlier
tangent-line proof (`FamilyBounds.sum_tangent`) is kept as an independent cross-check; the theorems
here have distinct names.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Set
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- `y ↦ (y - c)/(χ + y)` is concave on `[0, ∞)` when `χ > 0` and `χ + c > 0`
(second derivative `-2(χ+c)/(χ+y)³ < 0`). -/
theorem concaveOn_ratio {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun y => (y - c) / (χ + y)) := by
  set f : ℝ → ℝ := fun y => (y - c) / (χ + y) with hf
  have hd1 : ∀ y : ℝ, 0 < χ + y → HasDerivAt f ((χ + c) / (χ + y) ^ 2) y := by
    intro y hy
    have hu : HasDerivAt (fun y : ℝ => χ + y) 1 y := (hasDerivAt_id y).const_add χ
    have hn : HasDerivAt (fun y : ℝ => y - c) 1 y := (hasDerivAt_id y).sub_const c
    have := hn.div hu hy.ne'
    convert this using 1
    field_simp
    ring
  have hd2 : ∀ y : ℝ, 0 < χ + y →
      HasDerivAt (fun y : ℝ => (χ + c) / (χ + y) ^ 2) (-2 * (χ + c) / (χ + y) ^ 3) y := by
    intro y hy
    have hu : HasDerivAt (fun y : ℝ => χ + y) 1 y := (hasDerivAt_id y).const_add χ
    have hu2 : HasDerivAt (fun y : ℝ => (χ + y) ^ 2) (((2 : ℕ) : ℝ) * (χ + y) ^ (2 - 1) * 1) y :=
      hu.pow 2
    have hne : (χ + y) ^ 2 ≠ 0 := pow_ne_zero 2 hy.ne'
    have := (hasDerivAt_const y (χ + c)).div hu2 hne
    convert this using 1
    field_simp
    ring
  have hev : ∀ x : ℝ, 0 < χ + x →
      deriv f =ᶠ[𝓝 x] fun y => (χ + c) / (χ + y) ^ 2 := by
    intro x hx
    have hopen : IsOpen {y : ℝ | 0 < χ + y} :=
      isOpen_lt continuous_const (continuous_const.add continuous_id)
    filter_upwards [hopen.mem_nhds (show x ∈ {y : ℝ | 0 < χ + y} from hx)] with y hy
    exact (hd1 y hy).deriv
  have hpos : ∀ x ∈ Ici (0 : ℝ), 0 < χ + x := fun x hx => by
    have : (0 : ℝ) ≤ x := hx
    linarith
  apply concaveOn_of_deriv2_nonpos (convex_Ici 0)
  · intro x hx
    exact (hd1 x (hpos x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hd1 x (hpos x (le_of_lt hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact ((hd2 x (hpos x (le_of_lt hx))).differentiableAt.congr_of_eventuallyEq
      (hev x (hpos x (le_of_lt hx)))).differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' := hpos x (le_of_lt hx)
    show deriv (deriv f) x ≤ 0
    rw [(hev x hx').deriv_eq, (hd2 x hx').deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · positivity

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
