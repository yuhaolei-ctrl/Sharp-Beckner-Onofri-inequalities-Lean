module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

/-! # The function `psi(t) = t^4/(14-10 t^2)` of Lemma 5.16

Source: `eq:section5-circle-explicit-bound` (statement of Lemma 5.16) and G09 ("Export continuity,
nonnegativity, and convexity of `psi` on `[0,1]`").  Here `14 - 10 t^2 >= 4 > 0` on `[-1,1]`.
Derivatives: `psi' = (56 t^3 - 20 t^5)/(14-10t^2)^2`,
`psi'' = t^2 (2352 - 840 t^2 + 200 t^4)/(14-10t^2)^3`, the quadratic factor in `t^2` being positive. -/
noncomputable section
open Set
namespace BecknerOnofri.V2.Circle


/-- `ψ(t) = t⁴/(14-10t²)` (Lemma 5.16). -/
noncomputable def psi (t : ℝ) : ℝ := t ^ 4 / (14 - 10 * t ^ 2)

theorem den_hasDerivAt (t : ℝ) : HasDerivAt (fun t : ℝ => 14 - 10 * t ^ 2) (-(20 * t)) t := by
  have := ((hasDerivAt_pow 2 t).const_mul 10).const_sub 14
  convert this using 1
  simp; ring

theorem psi_hasDerivAt {t : ℝ} (h : 14 - 10 * t ^ 2 ≠ 0) :
    HasDerivAt psi ((56 * t ^ 3 - 20 * t ^ 5) / (14 - 10 * t ^ 2) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 4) (4 * t ^ 3) t := by
    simpa using hasDerivAt_pow 4 t
  refine (h1.div (den_hasDerivAt t) h).congr_deriv ?_
  field_simp
  ring

theorem psi_hasDerivAt' {t : ℝ} (h : 14 - 10 * t ^ 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => (56 * t ^ 3 - 20 * t ^ 5) / (14 - 10 * t ^ 2) ^ 2)
      (t ^ 2 * (2352 - 840 * t ^ 2 + 200 * t ^ 4) / (14 - 10 * t ^ 2) ^ 3) t := by
  have h1 : HasDerivAt (fun t : ℝ => 56 * t ^ 3 - 20 * t ^ 5) (56 * (3 * t ^ 2) - 20 * (5 * t ^ 4)) t := by
    exact (((hasDerivAt_pow 3 t).const_mul 56).sub ((hasDerivAt_pow 5 t).const_mul 20)).congr_deriv (by simp)
  have h2 : HasDerivAt (fun t : ℝ => (14 - 10 * t ^ 2) ^ 2) (2 * (14 - 10 * t ^ 2) * (-(20 * t))) t := by
    exact ((den_hasDerivAt t).pow 2).congr_deriv (by simp)
  refine (h1.div h2 (pow_ne_zero 2 h)).congr_deriv ?_
  field_simp
  ring


theorem psi_den_ne {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 14 - 10 * t ^ 2 ≠ 0 := by
  have : t ^ 2 ≤ 1 := by nlinarith
  intro h; linarith

theorem psi_den_pos {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 < 14 - 10 * t ^ 2 := by
  have : t ^ 2 ≤ 1 := by nlinarith
  linarith

theorem psi_continuousOn : ContinuousOn psi (Icc 0 1) := fun _ ht =>
  (psi_hasDerivAt (psi_den_ne ht.1 ht.2)).continuousAt.continuousWithinAt

theorem psi_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ psi t :=
  div_nonneg (by positivity) (psi_den_pos h0 h1).le

theorem psi_convexOn : ConvexOn ℝ (Icc 0 1) psi := by
  have hI : interior (Icc (0:ℝ) 1) = Ioo 0 1 := interior_Icc
  have hd : ∀ x ∈ Ioo (0:ℝ) 1, deriv psi x = (56 * x ^ 3 - 20 * x ^ 5) / (14 - 10 * x ^ 2) ^ 2 :=
    fun x hx => (psi_hasDerivAt (psi_den_ne hx.1.le hx.2.le)).deriv
  have hev : ∀ x ∈ Ioo (0:ℝ) 1, deriv psi =ᶠ[nhds x]
      fun t => (56 * t ^ 3 - 20 * t ^ 5) / (14 - 10 * t ^ 2) ^ 2 := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy using hd y hy
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 1) psi_continuousOn
  · rw [hI]
    exact fun x hx => (psi_hasDerivAt (psi_den_ne hx.1.le hx.2.le)).differentiableAt.differentiableWithinAt
  · rw [hI]
    intro x hx
    exact (((psi_hasDerivAt' (psi_den_ne hx.1.le hx.2.le)).differentiableAt).congr_of_eventuallyEq
      (hev x hx)).differentiableWithinAt
  · rw [hI]
    intro x hx
    have h2 : deriv (deriv psi) x = x ^ 2 * (2352 - 840 * x ^ 2 + 200 * x ^ 4) / (14 - 10 * x ^ 2) ^ 3 := by
      rw [(hev x hx).deriv_eq]
      exact (psi_hasDerivAt' (psi_den_ne hx.1.le hx.2.le)).deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [h2]
    have hp := psi_den_pos hx.1.le hx.2.le
    apply div_nonneg _ (pow_nonneg hp.le 3)
    apply mul_nonneg (sq_nonneg _)
    nlinarith [sq_nonneg (x ^ 2 - 21/10), sq_nonneg x]

end BecknerOnofri.V2.Circle
