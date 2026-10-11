module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# Scalar feasibility facts for the explicit reference family (Lemma 5.19, Appendix A.3)

Compiled (sorry-free).  Pure real-analysis facts about the parameters
`L, λ, a, χ, ω` and the state-zero product; no dependence on the thirteen-state vocabulary.
-/

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

def famL (t : ℝ) : ℝ := 9 / 2 * t ^ 10
def famLam (t : ℝ) : ℝ := famL t / (1 + famL t)
def famBias (t : ℝ) : ℝ := t - famL t * (1 - t)
def famChi (t : ℝ) : ℝ := 31 / t ^ 2 - 32 + 12 * t ^ 4 + t ^ 2 / (10 * (1 - t))
def famP (u : ℝ) : ℝ := 31 - 32 * u + 12 * u ^ 3
def famOmega (t : ℝ) : ℝ := t ^ 2 * (1 - t) / (famP (t ^ 2) * (1 - t) + t ^ 4 / 10)

/-- Maximum of `t^9 (1-t)` is `9^9/10^10` (at `t = 9/10`), by calculus as printed: on `[0,1]` the
derivative of `φ(t) = t^9 (1-t)` is `t^8 (9 - 10 t)`, so `φ` increases on `[0,9/10]` and decreases on
`[9/10,1]`; for `t > 1` the left-hand side is negative. -/
theorem pow9_mul_one_sub_le {t : ℝ} (ht : 0 ≤ t) : t ^ 9 * (1 - t) ≤ 9 ^ 9 / 10 ^ 10 := by
  set φ : ℝ → ℝ := fun t => t ^ 9 * (1 - t) with hφ
  have hd : ∀ x : ℝ, HasDerivAt φ (x ^ 8 * (9 - 10 * x)) x := by
    intro x
    have h : HasDerivAt (fun t : ℝ => t ^ 9 * (1 - t))
        (((9 : ℕ) : ℝ) * x ^ (9 - 1) * (1 - id x) + x ^ 9 * -1) x :=
      (hasDerivAt_pow 9 x).mul ((hasDerivAt_id x).const_sub 1)
    refine h.congr_deriv ?_
    simp
    ring
  have hcont : Continuous φ := by fun_prop
  have hdiff : Differentiable ℝ φ := fun x => (hd x).differentiableAt
  have hmono : MonotoneOn φ (Set.Icc 0 (9 / 10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have : 0 ≤ x ^ 8 := by positivity
    have : 0 ≤ 9 - 10 * x := by linarith [hx.2]
    positivity
  have hanti : AntitoneOn φ (Set.Icc (9 / 10) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have : 0 ≤ x ^ 8 := by positivity
    have : 9 - 10 * x ≤ 0 := by linarith [hx.1]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have hval : φ (9 / 10) = 9 ^ 9 / 10 ^ 10 := by simp only [hφ]; norm_num
  by_cases h1 : t ≤ 1
  · by_cases h : t ≤ 9 / 10
    · calc φ t ≤ φ (9 / 10) := hmono ⟨ht, h⟩ ⟨by norm_num, le_refl _⟩ h
        _ = _ := hval
    · push Not at h
      calc φ t ≤ φ (9 / 10) := hanti ⟨le_refl _, by norm_num⟩ ⟨h.le, h1⟩ h.le
        _ = _ := hval
  · push Not at h1
    have h2 : t ^ 9 * (1 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h3 : (0 : ℝ) ≤ 9 ^ 9 / 10 ^ 10 := by positivity
    linarith

theorem famL_mul_one_sub_le {t : ℝ} (ht : 0 ≤ t) : famL t * (1 - t) ≤ t / 5 := by
  have h := pow9_mul_one_sub_le ht
  have hc : (9 / 2 : ℝ) * (9 ^ 9 / 10 ^ 10) < 1 / 5 := by norm_num
  have e : famL t * (1 - t) = 9 / 2 * t * (t ^ 9 * (1 - t)) := by unfold famL; ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 9 / 2 * t)
  nlinarith [mul_le_mul_of_nonneg_left hc.le ht]

/-- `4t/5 ≤ a(t) ≤ t` for `0 ≤ t ≤ 1`. -/
theorem famBias_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * t / 5 ≤ famBias t ∧ famBias t ≤ t := by
  have h := famL_mul_one_sub_le ht0
  have hL : 0 ≤ famL t * (1 - t) :=
    mul_nonneg (by unfold famL; positivity) (by linarith)
  unfold famBias
  constructor <;> linarith

/-- The middle expression `31/t - 32t + 12t⁵` of the printed chain. -/
def midExpr (t : ℝ) : ℝ := 31 / t - 32 * t + 12 * t ^ 5

/-- Its derivative `-31/t² - 32 + 60t⁴` is at most `-3` on `(0,1]`. -/
theorem midExpr_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt midExpr (-31 / t ^ 2 - 32 + 60 * t ^ 4) t := by
  have h1 : HasDerivAt (fun t : ℝ => 31 / t) (-31 / t ^ 2) t := by
    have := (hasDerivAt_inv ht).const_mul 31
    convert this using 1
    · ext x; simp [div_eq_mul_inv]
    · field_simp
  have h2 : HasDerivAt (fun t : ℝ => 32 * t) 32 t := by
    simpa using (hasDerivAt_id t).const_mul 32
  have h3 : HasDerivAt (fun t : ℝ => 12 * t ^ 5) (60 * t ^ 4) t := by
    have := (hasDerivAt_pow 5 t).const_mul 12
    convert this using 1
    ring
  have := (h1.sub h2).add h3
  unfold midExpr
  convert this using 1

theorem midExpr_deriv_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    -31 / t ^ 2 - 32 + 60 * t ^ 4 ≤ -3 := by
  have h2 : t ^ 2 ≤ 1 := by nlinarith
  have h4 : t ^ 4 ≤ 1 := by
    have : t ^ 4 = (t ^ 2) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg t]
  have h31 : -31 / t ^ 2 ≤ -31 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `31/t - 32t + 12t⁵ ≥ 11` on `(0,1]`: the expression is nonincreasing (derivative `≤ -3`) with
value `11` at `t = 1`. -/
theorem midExpr_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : 11 ≤ midExpr t := by
  have hanti : AntitoneOn midExpr (Set.Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
    · intro x hx
      exact (midExpr_hasDerivAt hx.1.ne').continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact (midExpr_hasDerivAt hx.1.ne').differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(midExpr_hasDerivAt hx.1.ne').deriv]
      have := midExpr_deriv_le hx.1 hx.2.le
      linarith
  have h := hanti ⟨ht0, ht1⟩ ⟨by norm_num, le_refl _⟩ ht1
  have h1 : midExpr 1 = 11 := by unfold midExpr; norm_num
  linarith

/-- `t χ(t) ≥ 11` on `(0,1)`, by the printed calculus argument: `t χ(t) = 31/t - 32t + 12t⁵ +
t³/(10(1-t)) ≥ 31/t - 32t + 12t⁵ ≥ 11`. -/
theorem t_mul_famChi_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 11 ≤ t * famChi t := by
  have h1t : 0 < 1 - t := by linarith
  have e : t * famChi t = midExpr t + t ^ 3 / (10 * (1 - t)) := by
    unfold famChi midExpr
    field_simp
  have hnn : 0 ≤ t ^ 3 / (10 * (1 - t)) := by positivity
  have h11 := midExpr_ge ht0 ht1.le
  linarith

theorem famChi_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famChi t := by
  have h := t_mul_famChi_ge ht0 ht1
  by_contra hc
  push Not at hc
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0.le hc]

/-- `χ a ≥ 44/5` (> 11/2). -/
theorem famChi_mul_bias_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 44 / 5 ≤ famChi t * famBias t := by
  have h1 := t_mul_famChi_ge ht0 ht1
  have h2 := (famBias_bounds ht0.le ht1.le).1
  have hχ := famChi_pos ht0 ht1
  -- χ a ≥ χ · 4t/5 = (4/5)(tχ) ≥ 44/5
  nlinarith [mul_le_mul_of_nonneg_left h2 hχ.le]

/-- `P(u) = 31 - 32u + 12u³ = 31(1-u)³ + 61u(1-u)² + 29u²(1-u) + 11u³`: the positive form
(eq `d12-spin-eq:positiveP`) printed in the proof of Lemma `d12-spin-lem:feasible`. -/
theorem positiveP_identity (u : ℝ) :
    famP u = 31 * (1 - u) ^ 3 + 61 * u * (1 - u) ^ 2 + 29 * u ^ 2 * (1 - u) + 11 * u ^ 3 := by
  unfold famP; ring

/-- `P(u) > 0` for `0 ≤ u ≤ 1`, read off from the positive form. -/
theorem famP_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 < famP u := by
  rw [positiveP_identity]
  have h : 0 ≤ 1 - u := by linarith
  rcases hu0.eq_or_lt with h0 | h0
  · subst h0; norm_num
  · have : 0 < 11 * u ^ 3 := by positivity
    have : 0 ≤ 31 * (1 - u) ^ 3 := by positivity
    have : 0 ≤ 61 * u * (1 - u) ^ 2 := by positivity
    have : 0 ≤ 29 * u ^ 2 * (1 - u) := by positivity
    linarith

/-- `ω(t) = 1/χ(t)` (`d12-spin-eq:h`): the stable rational form agrees with the reciprocal. -/
theorem famOmega_mul_famChi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : famOmega t * famChi t = 1 := by
  have h1t : 0 < 1 - t := by linarith
  have hP : 0 < famP (t ^ 2) * (1 - t) + t ^ 4 / 10 := by
    have hu1 : t ^ 2 ≤ 1 := by nlinarith
    have := famP_pos (sq_nonneg t) hu1
    positivity
  have hchi : famChi t = (famP (t ^ 2) * (1 - t) + t ^ 4 / 10) / (t ^ 2 * (1 - t)) := by
    unfold famChi famP
    field_simp
  rw [hchi]
  unfold famOmega
  have hne : famP (t ^ 2) * (1 - t) + t ^ 4 / 10 ≠ 0 := hP.ne'
  have h2 : t ^ 2 * (1 - t) ≠ 0 := by positivity
  rw [div_mul_div_comm, mul_comm (t ^ 2 * (1 - t)) (famP (t ^ 2) * (1 - t) + t ^ 4 / 10)]
  exact div_self (mul_ne_zero hne h2)

/-- Tangent-line bound at the mean `11/2` for the concave map `y ↦ (y - c)/(χ + y)`.
This is the independent cross-check of the Jensen step; the written Jensen route is in
`FamilyJensen`. -/
theorem tangent_term {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) {k : ℝ} (hk : 0 ≤ k) :
    (k - c) / (χ + k) ≤
      (11 / 2 - c) / (χ + 11 / 2) + (χ + c) / (χ + 11 / 2) ^ 2 * (k - 11 / 2) := by
  have hk' : 0 < χ + k := by linarith
  have hm : 0 < χ + 11 / 2 := by linarith
  have key : (11 / 2 - c) / (χ + 11 / 2) + (χ + c) / (χ + 11 / 2) ^ 2 * (k - 11 / 2) -
      (k - c) / (χ + k) = (χ + c) * (k - 11 / 2) ^ 2 / ((χ + k) * (χ + 11 / 2) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (χ + c) * (k - 11 / 2) ^ 2 / ((χ + k) * (χ + 11 / 2) ^ 2) := by positivity
  linarith

/-- Sum over the twelve integers `0..11`; the linear terms cancel because the mean is `11/2`. -/
theorem sum_tangent {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ∑ k ∈ Finset.range 12, ((k : ℝ) - c) / (χ + k) ≤ 12 * ((11 / 2 - c) / (χ + 11 / 2)) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range 12) =>
    tangent_term hχ hc (Nat.cast_nonneg k))
  have hlin : ∑ k ∈ Finset.range 12, ((k : ℝ) - 11 / 2) = 0 := by
    norm_num [Finset.sum_range_succ]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hlin, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_zero, add_zero] at h
  push_cast at h
  exact h

/-- State-zero cap: with `χ > 0`, `a < 1`, `χ a > 11/2`, the product `ν_0 / b_0 < 1`. -/
theorem state_zero_ratio_lt_one {χ a : ℝ} (hχ : 0 < χ) (ha1 : a < 1) (hca : 11 / 2 < χ * a) :
    ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) < 1 := by
  have hapos : 0 < a := by
    by_contra h; push Not at h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hχ.le h]
  have hfac : ∀ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k) ≤
      Real.exp ((k - χ * a) / (χ + k)) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (χ * (1 - a) + 2 * k) / (χ + k) = (k - χ * a) / (χ + k) + 1 := by
      field_simp; ring
    rw [this]
    exact Real.add_one_le_exp _
  have hnn : ∀ k ∈ Finset.range 12, 0 ≤ (χ * (1 - a) + 2 * k) / (χ + k) := by
    intro k _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    apply div_nonneg
    · have : 0 < 1 - a := by linarith
      positivity
    · linarith
  calc ∏ k ∈ Finset.range 12, (χ * (1 - a) + 2 * k) / (χ + k)
      ≤ ∏ k ∈ Finset.range 12, Real.exp ((k - χ * a) / (χ + k)) := Finset.prod_le_prod₀ hnn hfac
    _ = Real.exp (∑ k ∈ Finset.range 12, ((k : ℝ) - χ * a) / (χ + k)) := (Real.exp_sum _ _).symm
    _ < 1 := by
      rw [Real.exp_lt_one_iff]
      have hcpos : 0 < χ + χ * a := by nlinarith
      have h := sum_tangent hχ hcpos (c := χ * a)
      have hm : 0 < χ + 11 / 2 := by linarith
      have : (11 / 2 - χ * a) / (χ + 11 / 2) < 0 := div_neg_of_neg_of_pos (by linarith) hm
      linarith

end BecknerOnofri.V2.FiniteState
