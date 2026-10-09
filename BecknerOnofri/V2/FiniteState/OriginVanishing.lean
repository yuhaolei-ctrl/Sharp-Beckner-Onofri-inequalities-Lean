module

public import BecknerOnofri.V2.FiniteState.OriginSmooth
public import BecknerOnofri.V2.FiniteState.TaylorCoefficients
public import BecknerOnofri.V2.FiniteState.JetCalculus

@[expose] public section

/-!
# Origin vanishings: `f^{(k)}(0) = 𝒱^{(k)}(0) = 0` for `0 ≤ k ≤ 3`  (P055, `eq:section5-origin-summary`)

Assembled from `famF_isBigO`, `famResidVar_isBigO` (origin orders), `famF_contDiffAt`,
`famResidVar_contDiffAt` (regularity) and the finite Taylor-coefficient lemma.  These statements are
proved before and independently of the interval certificate and do not use the quartic coefficient.
The analytic regularity claimed in the manuscript is proved as `AnalyticAt` (Mathlib's
`ContDiffAt ℝ ω`), so there is no statement difference there.
-/

noncomputable section
open Filter Topology
open scoped ContDiff
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

theorem famF_origin_vanishing :
    iteratedDeriv 0 famF 0 = 0 ∧ iteratedDeriv 1 famF 0 = 0 ∧ iteratedDeriv 2 famF 0 = 0 ∧
      iteratedDeriv 3 famF 0 = 0 :=
  iteratedDeriv_zero_eq_zero_of_isBigO (famF_contDiffAt 3) famF_isBigO

theorem famResidVar_origin_vanishing :
    iteratedDeriv 0 famResidVar 0 = 0 ∧ iteratedDeriv 1 famResidVar 0 = 0 ∧
      iteratedDeriv 2 famResidVar 0 = 0 ∧ iteratedDeriv 3 famResidVar 0 = 0 :=
  iteratedDeriv_zero_eq_zero_of_isBigO (famResidVar_contDiffAt 3)
    (famResidVar_isBigO.trans (isBigO_pow_pow (by norm_num : 4 ≤ 6)))

/-- Analyticity at `0` of the coordinates of the family (Lemma 5.19, last sentence). -/
theorem famLaw_analyticAt (j : Count) : AnalyticAt ℝ (fun t => famLaw t j) 0 :=
  (famLaw_contDiffAt ω j).analyticAt

theorem famSpinVar_analyticAt : AnalyticAt ℝ famSpinVar 0 := (famSpinVar_contDiffAt ω).analyticAt

theorem famResid_analyticAt (j : Count) : AnalyticAt ℝ (fun t => famResid t j) 0 :=
  (famResid_contDiffAt ω j).analyticAt

theorem famResidVar_analyticAt : AnalyticAt ℝ famResidVar 0 := (famResidVar_contDiffAt ω).analyticAt

theorem famF_analyticAt : AnalyticAt ℝ famF 0 := (famF_contDiffAt ω).analyticAt

/-- `e_j(0) = 0` (used for the third scalar bound at zero). -/
theorem famResid_zero (j : Count) : famResid 0 j = 0 := by
  obtain ⟨C, hC⟩ := (famResid_isBigO j).bound
  have := hC.self_of_nhds
  simpa using this

end BecknerOnofri.V2.FiniteState
