module

public import BecknerOnofri.V2.FiniteState.OriginVanishing
public import BecknerOnofri.V2.Reaudit.ScalarBridges.KrawtchoukOrthogonality
public import BecknerOnofri.V2.Reaudit.ScalarBridges.OriginReflection

@[expose] public section

/-! # `eq:section5-origin-summary` (U19): the printed origin expansions and the two
finite-evaluation steps replaced by their printed arguments

Printed proof (Appendix A.3, "Behavior at zero"):

* `a(t) = t + O(t¹⁰)`, `λ(t) = O(t¹⁰)`, `ω(t) = t²/31 + O(t⁴)`
  (`famBias_sub_isBigO_ten`, `famLam_isBigO_ten`, `famOmega_sub_isBigO_four`);
* orthogonality of the symmetric products of fair independent spins and `A_1 = x`,
  `A_2 = (12x²-1)/11` (`KrawtchoukOrthogonality`);
* `E_b ℓ² = 144 E_b x² = 12` since `E_b x² = 1/12` (`sum_reference_ell_sq_spins`, from the
  orthogonality relation with `s = r = 1`);
* reflection `j ↦ 12 - j` preserves `b`, makes `ℓ` odd and `d` even, hence the cubic coefficient
  vanishes (`sum_reference_cubic_reflection`);
* `e_j = O(t³)`, `𝒱 = O(t⁶)`, `f = O(t⁴)`; analyticity of all the functions in
  `d12-spin-eq:residual` near `0` (from the rational extension, not from smoothness); hence
  `f^{(k)}(0) = 𝒱^{(k)}(0) = 0` for `0 ≤ k ≤ 3` (`origin_summary_printed`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace BecknerOnofri.V2.Reaudit.ScalarBridges

open Filter Topology Asymptotics
open scoped BigOperators ContDiff
open BecknerOnofri.HighDim.Spin BecknerOnofri.V2.FiniteState

/-- `a(t) = t + O(t¹⁰)` (exact: `a(t) - t = -(9/2) t¹⁰ (1 - t)`).  The proof lives in the base
module `FiniteState.FamilyJets`, where the second-order jet `famBias_jet` is derived from it. -/
theorem famBias_sub_isBigO_ten : (fun t => famBias t - t) =O[𝓝 0] fun t : ℝ => t ^ 10 :=
  BecknerOnofri.V2.FiniteState.famBias_sub_isBigO_ten

/-- `λ(t) = O(t¹⁰)` (proof in `FiniteState.FamilyJets`; `famLam_isBigO` is derived from it). -/
theorem famLam_isBigO_ten : famLam =O[𝓝 0] fun t : ℝ => t ^ 10 :=
  BecknerOnofri.V2.FiniteState.famLam_isBigO_ten

/-- `ω(t) = t²/31 + O(t⁴)`, as printed (proof in `FiniteState.FamilyJets`; the second-order jet
`famOmega_jet`, with remainder `O(t³)`, is derived from it). -/
theorem famOmega_sub_isBigO_four :
    (fun t => famOmega t - t ^ 2 / 31) =O[𝓝 0] fun t : ℝ => t ^ 4 :=
  BecknerOnofri.V2.FiniteState.famOmega_sub_isBigO_four

/-- **`eq:section5-origin-summary`** and the derivative vanishings, with analyticity: every function
in `d12-spin-eq:residual` is real analytic at `0` (it is obtained from the rational extension of the
reference probabilities, positive near `0`, with `σ_x²(0) = 1/12`), `e_j(t) = O(t³)`,
`𝒱(t) = O(t⁶)`, `f(t) = O(t⁴)`, and `f^{(k)}(0) = 𝒱^{(k)}(0) = 0` for `0 ≤ k ≤ 3`. -/
theorem origin_summary_printed :
    ((∀ j : Count, AnalyticAt ℝ (fun t => famLaw t j) 0) ∧ AnalyticAt ℝ famSpinVar 0 ∧
        (∀ j : Count, AnalyticAt ℝ (fun t => famResid t j) 0) ∧ AnalyticAt ℝ famResidVar 0 ∧
        AnalyticAt ℝ famF 0) ∧
      ((∀ j : Count, (fun t => famResid t j) =O[𝓝 0] fun t : ℝ => t ^ 3) ∧
        famResidVar =O[𝓝 0] (fun t : ℝ => t ^ 6) ∧ famF =O[𝓝 0] (fun t : ℝ => t ^ 4)) ∧
      ((∀ k, k ≤ 3 → iteratedDeriv k famF 0 = 0) ∧ (∀ k, k ≤ 3 → iteratedDeriv k famResidVar 0 = 0)) := by
  refine ⟨⟨famLaw_analyticAt, famSpinVar_analyticAt, famResid_analyticAt, famResidVar_analyticAt,
    famF_analyticAt⟩, ⟨famResid_isBigO, famResidVar_isBigO, famF_isBigO⟩, ?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3⟩ := famF_origin_vanishing
    intro k hk
    interval_cases k <;> assumption
  · obtain ⟨h0, h1, h2, h3⟩ := famResidVar_origin_vanishing
    intro k hk
    interval_cases k <;> assumption


end BecknerOnofri.V2.Reaudit.ScalarBridges
