module

public import BecknerOnofri.V2.FiniteState.OriginVanishing
public import BecknerOnofri.V2.FiniteState.FamilyJensen
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! # `d12-spin-lem:feasible` (S051) along the printed calculus / beta-mixture argument

Printed proof (V2 TeX 4687-4745, appendix proof of `d12-spin-lem:feasible`):

* (a) the maximum of `t⁹(1-t)` on `[0,1]` occurs at `9/10`; hence `L(1-t)/t ≤ (9/2)(9⁹/10¹⁰) < 1/5`
  and `4t/5 ≤ a(t) ≤ t < 1`.                        (`pow9_mul_one_sub_le_calculus`, `L_bound_calculus`,
  `famBias_bounds_calculus`)
* (b) `tχ ≥ 31/t - 32t + 12t⁵ ≥ 11`, since the derivative of the middle expression is
  `-31/t² - 32 + 60t⁴ ≤ -3` on `(0,1]` and its value at `1` is `11`; thus `χ > 0` and `χ a ≥ 44/5`.
                                                     (`tchi_ge_calculus`, `famChi_mul_bias_ge_calculus`)
* (c) Euler's beta integral: `ν_j` is the `Beta(α,β)`-mixture of binomials; summing the binomial
  probabilities under the integral gives mass one, the conditional mean `2θ-1` gives mean `a`;
  `(1-λ)a + λ = t`.   (reused: `famNu_eq_integral`, `famNu_sum_beta`, `famNu_mean_beta`,
  `famLaw_sum_beta`, `famLaw_mean_beta` of `V2.FiniteState.FamilyBeta`.)
* (d) the cap at state zero: `ν_0/b_0 = ∏ (χ(1-a)+2k)/(χ+k)`, `log(1+u) ≤ u`, and Jensen for the
  concave map `y ↦ (y - χa)/(χ+y)` whose **second derivative** is `-2χ(1+a)/(χ+y)³ < 0`.
                                       (`concaveOn_ratio_deriv2`, `state_zero_ratio_lt_one_printed`)
* (e) regularity at zero: `ω = 1/χ = u(1-t)/(P(u)(1-t)+u²/10)` with `P` in the positive form,
  analytic near `0` with `ω(0) = 0`, the rational form of `ν_j` in `ω`, `p(0) = b`.
                                       (`positiveP_identity`, `famOmega_analyticAt`, reused `famLaw_analyticAt`)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open scoped BigOperators Topology ContDiff
open Set BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-! ### (a) maximum of `t⁹(1-t)` by calculus -/

/-- The maximum of `t⁹(1-t)` on `[0,1]` occurs at `9/10`: it is increasing on `[0,9/10]`
(derivative `t⁸(9-10t) ≥ 0`) and decreasing on `[9/10,1]`. -/
theorem pow9_mul_one_sub_le_calculus {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ 9 * (1 - t) ≤ 9 ^ 9 / 10 ^ 10 := by
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
  have hmono : MonotoneOn φ (Icc 0 (9 / 10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have : 0 ≤ x ^ 8 := by positivity
    have : 0 ≤ 9 - 10 * x := by linarith [hx.2]
    positivity
  have hanti : AntitoneOn φ (Icc (9 / 10) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have : 0 ≤ x ^ 8 := by positivity
    have : 9 - 10 * x ≤ 0 := by linarith [hx.1]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have hval : φ (9 / 10) = 9 ^ 9 / 10 ^ 10 := by simp only [hφ]; norm_num
  by_cases h : t ≤ 9 / 10
  · calc φ t ≤ φ (9 / 10) := hmono ⟨ht0, h⟩ ⟨by norm_num, le_refl _⟩ h
      _ = _ := hval
  · push Not at h
    calc φ t ≤ φ (9 / 10) := hanti ⟨le_refl _, by norm_num⟩ ⟨h.le, ht1⟩ h.le
      _ = _ := hval

/-- `L(t)(1-t)/t ≤ (9/2)(9⁹/10¹⁰) < 1/5` for `0 < t ≤ 1`. -/
theorem L_bound_calculus {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    famL t * (1 - t) / t ≤ 9 / 2 * (9 ^ 9 / 10 ^ 10) ∧ 9 / 2 * ((9 : ℝ) ^ 9 / 10 ^ 10) < 1 / 5 := by
  refine ⟨?_, by norm_num⟩
  have h := pow9_mul_one_sub_le_calculus ht0.le ht1
  have e : famL t * (1 - t) / t = 9 / 2 * (t ^ 9 * (1 - t)) := by
    unfold famL; field_simp
  rw [e]
  linarith

/-- `4t/5 ≤ a(t) ≤ t` for `0 ≤ t ≤ 1` (printed form of `famBias_bounds`, proved from the
calculus maximum). -/
theorem famBias_bounds_calculus {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * t / 5 ≤ famBias t ∧ famBias t ≤ t := by
  have hL : famL t * (1 - t) ≤ t / 5 := by
    rcases ht0.eq_or_lt with h | h
    · subst h; simp [famL]
    · have := (L_bound_calculus h ht1)
      have h1 := this.1
      have h2 := this.2
      rw [div_le_iff₀ h] at h1
      nlinarith
  have hL0 : 0 ≤ famL t * (1 - t) :=
    mul_nonneg (by unfold famL; positivity) (by linarith)
  unfold famBias
  constructor <;> linarith

/-! ### (b) `t χ(t) ≥ 11` by calculus -/

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
  have hanti : AntitoneOn midExpr (Ioc 0 1) := by
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

/-- `t χ(t) ≥ 31/t - 32t + 12t⁵ ≥ 11` on `(0,1)`. -/
theorem tchi_ge_calculus {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    midExpr t ≤ t * famChi t ∧ 11 ≤ t * famChi t := by
  have h1t : 0 < 1 - t := by linarith
  have e : t * famChi t = midExpr t + t ^ 3 / (10 * (1 - t)) := by
    unfold famChi midExpr
    field_simp
  have hnn : 0 ≤ t ^ 3 / (10 * (1 - t)) := by positivity
  have h11 := midExpr_ge ht0 ht1.le
  constructor <;> linarith

theorem famChi_pos_calculus {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : 0 < famChi t := by
  have h := (tchi_ge_calculus ht0 ht1).2
  by_contra hc
  push Not at hc
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0.le hc]

/-- `χ a ≥ 44/5 > 11/2` (eq `d12-spin-eq:ca`). -/
theorem famChi_mul_bias_ge_calculus {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    44 / 5 ≤ famChi t * famBias t := by
  have h1 := (tchi_ge_calculus ht0 ht1).2
  have h2 := (famBias_bounds_calculus ht0.le ht1.le).1
  have hχ := famChi_pos_calculus ht0 ht1
  nlinarith [mul_le_mul_of_nonneg_left h2 hχ.le]

/-! ### (d) concavity from the second derivative, Jensen, and the state-zero cap -/

/-- `y ↦ (y - c)/(χ + y)` has first derivative `(χ+c)/(χ+y)²` and **second derivative**
`-2(χ+c)/(χ+y)³ < 0` (with `c = χ a`, `χ + c = χ(1+a)`), hence is concave on `[0,∞)`. -/
theorem concaveOn_ratio_deriv2 {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
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

/-- Jensen's inequality for the twelve integers `0, …, 11` (mean `11/2`) and the concave map
`y ↦ (y - c)/(χ + y)`. -/
theorem sum_jensen_printed {χ c : ℝ} (hχ : 0 < χ) (hc : 0 < χ + c) :
    ∑ k ∈ Finset.range 12, ((k : ℝ) - c) / (χ + k) ≤ 12 * ((11 / 2 - c) / (χ + 11 / 2)) := by
  have h := (concaveOn_ratio_deriv2 hχ hc).le_map_sum (t := Finset.range 12)
    (w := fun _ => (1 / 12 : ℝ)) (p := fun k => (k : ℝ))
    (fun _ _ => by norm_num) (by simp)
    (fun k _ => show (0 : ℝ) ≤ k from Nat.cast_nonneg k)
  have hm : ∑ k ∈ Finset.range 12, (1 / 12 : ℝ) • (k : ℝ) = 11 / 2 := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    norm_num [Finset.sum_range_succ]
  simp only [smul_eq_mul, ← Finset.mul_sum] at h hm ⊢
  rw [hm] at h
  linarith

/-- State-zero cap, printed: with `χ > 0`, `a < 1`, `χ a > 11/2`,
`ν_0/b_0 = ∏_{k<12} (χ(1-a)+2k)/(χ+k) < 1`, via `log(1+u) ≤ u` and Jensen. -/
theorem state_zero_ratio_lt_one_printed {χ a : ℝ} (hχ : 0 < χ) (ha1 : a < 1)
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
    _ ≤ 12 * ((11 / 2 - χ * a) / (χ + 11 / 2)) := sum_jensen_printed hχ (by nlinarith)
    _ < 0 := by
      have hm : 0 < χ + 11 / 2 := by linarith
      have : (11 / 2 - χ * a) / (χ + 11 / 2) < 0 := div_neg_of_neg_of_pos (by linarith) hm
      linarith

/-- `ν_0 < b_0`, printed route. -/
theorem famNu_zero_state_lt_printed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famNu t 0 < reference 0 := by
  have hχ := famChi_pos_calculus ht0 ht1
  have hca : 11 / 2 < famChi t * famBias t := by
    have := famChi_mul_bias_ge_calculus ht0 ht1; linarith
  have ha1 : famBias t < 1 := lt_of_le_of_lt (famBias_bounds_calculus ht0.le ht1.le).2 ht1
  exact famNu_zero_state_lt_of_ratio ht0 ht1 (state_zero_ratio_lt_one_printed hχ ha1 hca)

/-- `p_0 < b_0`. -/
theorem famLaw_zero_state_lt_printed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    famLaw t 0 < reference 0 :=
  famLaw_zero_state_lt_of_nu ht0 ht1 (famNu_zero_state_lt_printed ht0 ht1)

/-! ### (e) regularity at zero -/

/-- `P(u) = 31 - 32u + 12u³ = 31(1-u)³ + 61u(1-u)² + 29u²(1-u) + 11u³`
(eq `d12-spin-eq:positiveP`). -/
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

/-- `ω(0) = 0` and `ω` is real analytic at `0` (it is a quotient of polynomials whose
denominator is `31 ≠ 0` at `0`): the final expression in `d12-spin-eq:h` "extends analytically
near zero". -/
theorem famOmega_analyticAt : AnalyticAt ℝ famOmega 0 := (famOmega_contDiffAt ω).analyticAt

theorem famOmega_zero' : famOmega 0 = 0 := famOmega_zero

/-- `ω = 1/χ` on `(0,1)` (eq `d12-spin-eq:h`): the analytic extension agrees with the
reciprocal of `χ` where `p(t)` is defined by the rising-factorial formulas. -/
theorem famOmega_eq_inv_famChi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : famOmega t = 1 / famChi t := by
  have h := famOmega_mul_famChi ht0 ht1
  have hχ := famChi_pos_calculus ht0 ht1
  field_simp
  linarith

/-- On `(0,1)` the coordinates of the analytic family are those of the printed
rising-factorial formula `p_j = (1-λ) ν_j + λ 1_{j=12}` (eq `d12-spin-eq:beta`, with
`ν_j` the beta-binomial law with parameters `χ(1±a)/2`). -/
theorem famLaw_eq_rising {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (j : Count) :
    famLaw t j = (1 - famLam t) * famNuRising t j +
      famLam t * (if j.val = 12 then 1 else 0) := by
  unfold famLaw
  rw [famNu_eq_betaBinom ht0 ht1, famNuRising_eq_betaBinom]

/-- Analytic extension of the coordinates, agreement with the printed formulas on `(0,1)`, and
`p(0) = b`. -/
theorem famLaw_analytic_zero_printed :
    (∀ j : Count, AnalyticAt ℝ (fun t => famLaw t j) 0) ∧ famLaw 0 = reference ∧
      (∀ t : ℝ, 0 < t → t < 1 → ∀ j : Count, famLaw t j = (1 - famLam t) * famNuRising t j +
        famLam t * (if j.val = 12 then 1 else 0)) :=
  ⟨famLaw_analyticAt, famLaw_zero, fun _ ht0 ht1 j => famLaw_eq_rising ht0 ht1 j⟩

/-- The beta mixture: with `α = χ(1+a)/2`, `β = χ(1-a)/2` (both positive), Euler's beta integral
represents `ν_j` as the `Beta(α,β)`-mixture of binomials; summing the binomial probabilities under
the integral gives `∑ ν_j = 1`, the conditional mean `2θ - 1` gives `∑ x_j ν_j = 2α/(α+β) - 1 = a`;
and `(1-λ)a + λ = t`. -/
theorem beta_mixture_printed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 < famAlpha t ∧ 0 < famBeta t ∧
      (∀ j : Count, famNu t j =
        (∫ θ in Ioo (0 : ℝ) 1, ((12).choose j.val : ℝ) *
          (θ ^ j.val * (1 - θ) ^ (12 - j.val) * eulerW (famAlpha t) (famBeta t) θ)) /
          ProbabilityTheory.beta (famAlpha t) (famBeta t)) ∧
      ∑ j : Count, famNu t j = 1 ∧ ∑ j : Count, meanCoordinate j * famNu t j = famBias t ∧
      (1 - famLam t) * famBias t + famLam t = t :=
  ⟨famAlpha_pos ht0 ht1, famBeta_pos ht0 ht1, famNu_eq_integral ht0 ht1, famNu_sum_beta ht0 ht1,
    famNu_mean_beta ht0 ht1, famLam_bias_all t⟩

/-! ### The lemma as printed -/

/-- **Lemma `d12-spin-lem:feasible`.**  For `0 < t < 1`, the vector `p(t)` is positive, belongs to
`𝒫_t`, and satisfies `p_0(t) < 2^{-12}`; its coordinates extend analytically to a neighborhood of
zero, with `p(0) = b`.  The cap at state zero and the bounds on `a`, `χ` are obtained from the
calculus steps (a), (b), (d) above; mass and mean are the beta-mixture identities of
`FamilyBeta` (reused). -/
theorem feasible_printed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((∀ j : Count, 0 < famLaw t j) ∧ FeasibleAt t (famLaw t) ∧ famLaw t 0 < 1 / 2 ^ 12) ∧
      ((∀ j : Count, AnalyticAt ℝ (fun s => famLaw s j) 0) ∧ famLaw 0 = reference ∧
        (∀ t : ℝ, 0 < t → t < 1 → ∀ j : Count, famLaw t j = (1 - famLam t) * famNuRising t j +
          famLam t * (if j.val = 12 then 1 else 0))) := by
  have hcap := famLaw_zero_state_lt_printed ht0 ht1
  have hb : reference 0 = 1 / 4096 := by
    unfold reference referenceQ; push_cast; norm_num
  have hfeas : FeasibleAt t (famLaw t) :=
    famLaw_feasibleAt_of_parts ht0 ht1 (famLaw_sum_beta ht0 ht1) (famLaw_mean_beta ht0 ht1) hcap
  refine ⟨⟨fun j => famLaw_pos ht0 ht1 j, hfeas, ?_⟩, famLaw_analytic_zero_printed⟩
  have : (1 : ℝ) / 2 ^ 12 = 1 / 4096 := by norm_num
  rw [this]; linarith


end BecknerOnofri.V2.Reaudit.ScalarBridges
