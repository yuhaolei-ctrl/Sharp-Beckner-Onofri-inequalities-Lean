module

public import BecknerOnofri.V2.FiniteState.OriginVanishing
public import BecknerOnofri.V2.FiniteState.FamilyJensen
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! # `d12-spin-lem:feasible` (S051) along the printed calculus / beta-mixture argument

Printed proof (V2 TeX 4687-4745, appendix proof of `d12-spin-lem:feasible`).  Its steps are proved,
in the modules below the finite-state vocabulary, as follows; these are the declarations the final
theorems consume (`FamilyBounds`, `FamilyJensen`, `FamilyBeta`):

* (a) the maximum of `t⁹(1-t)` on `[0,1]` occurs at `9/10` (derivative `t⁸(9-10t)`): `pow9_mul_one_sub_le`,
  hence `L(1-t)/t ≤ (9/2)(9⁹/10¹⁰) < 1/5` and `4t/5 ≤ a(t) ≤ t < 1` (`famL_mul_one_sub_le`, `famBias_bounds`).
* (b) `tχ ≥ 31/t - 32t + 12t⁵ ≥ 11`, the derivative of the middle expression being
  `-31/t² - 32 + 60t⁴ ≤ -3` on `(0,1]` with value `11` at `1`: `midExpr_deriv_le`, `midExpr_ge`,
  `t_mul_famChi_ge`, `famChi_pos`, `famChi_mul_bias_ge`.
* (c) Euler's beta integral: `famNu_eq_integral`, `famNu_sum_beta`, `famNu_mean_beta`,
  `famLaw_sum_beta`, `famLaw_mean_beta` of `FamilyBeta`.
* (d) the cap at state zero: `log(1+u) ≤ u` and Jensen for the concave map `y ↦ (y - χa)/(χ+y)`
  whose **second derivative** is `-2(χ+c)/(χ+y)³ < 0`: `concaveOn_ratio` (via
  `concaveOn_of_deriv2_nonpos`), `sum_jensen`, `state_zero_ratio_lt_one_jensen`,
  `famLaw_zero_state_lt_jensen`.
* (e) regularity at zero: `ω = 1/χ = u(1-t)/(P(u)(1-t)+u²/10)` with `P` in the positive form
  (`positiveP_identity`, `famP_pos`, `famOmega_mul_famChi`), analytic near `0` with `ω(0) = 0`.

This file only restates the lemma as printed, from those declarations.  (Earlier versions of this file
re-proved (a), (b), (d) under `*_calculus` names that could not be wired because of an import cycle with
`FamilyBounds`/`FamilyJensen`; the calculus proofs now live in those modules themselves.) -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open scoped BigOperators Topology ContDiff
open Set BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-! ### (e) regularity at zero, and the lemma as printed -/

/-- `ω(0) = 0` and `ω` is real analytic at `0` (it is a quotient of polynomials whose
denominator is `31 ≠ 0` at `0`): the final expression in `d12-spin-eq:h` "extends analytically
near zero". -/
theorem famOmega_analyticAt : AnalyticAt ℝ famOmega 0 := (famOmega_contDiffAt ω).analyticAt

theorem famOmega_zero' : famOmega 0 = 0 := famOmega_zero

/-- `ω = 1/χ` on `(0,1)` (eq `d12-spin-eq:h`): the analytic extension agrees with the
reciprocal of `χ` where `p(t)` is defined by the rising-factorial formulas. -/
theorem famOmega_eq_inv_famChi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : famOmega t = 1 / famChi t := by
  have h := famOmega_mul_famChi ht0 ht1
  have hχ := famChi_pos ht0 ht1
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
calculus steps (a), (b), (d) listed above (proved in `FamilyBounds`, `FamilyJensen`); mass and mean are the beta-mixture identities of
`FamilyBeta` (reused). -/
theorem feasible_printed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((∀ j : Count, 0 < famLaw t j) ∧ FeasibleAt t (famLaw t) ∧ famLaw t 0 < 1 / 2 ^ 12) ∧
      ((∀ j : Count, AnalyticAt ℝ (fun s => famLaw s j) 0) ∧ famLaw 0 = reference ∧
        (∀ t : ℝ, 0 < t → t < 1 → ∀ j : Count, famLaw t j = (1 - famLam t) * famNuRising t j +
          famLam t * (if j.val = 12 then 1 else 0))) := by
  have hcap := famLaw_zero_state_lt_jensen ht0 ht1
  have hb : reference 0 = 1 / 4096 := by
    unfold reference referenceQ; push_cast; norm_num
  have hfeas : FeasibleAt t (famLaw t) :=
    famLaw_feasibleAt_of_parts ht0 ht1 (famLaw_sum_beta ht0 ht1) (famLaw_mean_beta ht0 ht1) hcap
  refine ⟨⟨fun j => famLaw_pos ht0 ht1 j, hfeas, ?_⟩, famLaw_analytic_zero_printed⟩
  have : (1 : ℝ) / 2 ^ 12 = 1 / 4096 := by norm_num
  rw [this]; linarith


end BecknerOnofri.V2.Reaudit.ScalarBridges
