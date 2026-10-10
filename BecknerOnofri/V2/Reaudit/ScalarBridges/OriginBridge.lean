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

/-- `a(t) = t + O(t¹⁰)` (exact: `a(t) - t = -(9/2) t¹⁰ (1 - t)`). -/
theorem famBias_sub_isBigO_ten : (fun t => famBias t - t) =O[𝓝 0] fun t : ℝ => t ^ 10 := by
  have h : (fun t : ℝ => famBias t - t) = fun t : ℝ => -(9 / 2) * (t ^ 10 * (1 - t)) := by
    funext t; unfold famBias famL; ring
  rw [h]
  have h1 : (fun t : ℝ => t ^ 10 * (1 - t)) =O[𝓝 0] fun t : ℝ => t ^ 10 := by
    have hb : (fun t : ℝ => 1 - t) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
      Filter.Tendsto.isBigO_one ℝ (c := 1 - 0) ((by fun_prop : Continuous fun t : ℝ => 1 - t).tendsto 0)
    simpa using (isBigO_refl (fun t : ℝ => t ^ 10) (𝓝 0)).mul hb
  exact h1.const_mul_left _

/-- `λ(t) = O(t¹⁰)`. -/
theorem famLam_isBigO_ten : famLam =O[𝓝 0] fun t : ℝ => t ^ 10 := by
  have hc : ContinuousAt (fun t : ℝ => (1 + famL t)⁻¹) 0 := by
    apply ContinuousAt.inv₀
    · unfold famL; fun_prop
    · simp [famL]
  have hb : (fun t : ℝ => (1 + famL t)⁻¹) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    Filter.Tendsto.isBigO_one ℝ (c := (1 + famL 0)⁻¹) hc.tendsto
  have h1 : famL =O[𝓝 0] fun t : ℝ => t ^ 10 := by
    have : famL = fun t : ℝ => (9 / 2) * t ^ 10 := by funext t; rfl
    rw [this]
    exact (isBigO_refl (fun t : ℝ => t ^ 10) (𝓝 0)).const_mul_left _
  have := h1.mul hb
  refine this.congr' ?_ ?_
  · exact Filter.Eventually.of_forall fun t => by simp [famLam, div_eq_mul_inv]
  · exact Filter.Eventually.of_forall fun t => by simp

/-- `ω(t) = t²/31 + O(t⁴)`, as printed.  (The repository's `famOmega_jet` records the weaker
remainder `O(t³)`, which is all the second-order jets use; the exact identity
`ω(t) - t²/31 = t⁴ Q(t)` with `Q` continuous at `0` that underlies both is used here.) -/
theorem famOmega_sub_isBigO_four :
    (fun t => famOmega t - t ^ 2 / 31) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
  have hcont : Continuous famOmegaDen := by unfold famOmegaDen famP; fun_prop
  set Q : ℝ → ℝ := fun t => ((1 - t) * (32 - 12 * t ^ 4) - t ^ 2 / 10) / (31 * famOmegaDen t)
    with hQ
  have hQc : ContinuousAt Q 0 := by
    apply ContinuousAt.div
    · fun_prop
    · exact (continuous_const.mul hcont).continuousAt
    · rw [famOmegaDen_zero]; norm_num
  have hQb : Q =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := Filter.Tendsto.isBigO_one ℝ (c := Q 0) hQc.tendsto
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), famOmegaDen t ≠ 0 := by
    have : Tendsto famOmegaDen (𝓝 0) (𝓝 31) := by
      simpa [famOmegaDen_zero] using hcont.tendsto 0
    exact this.eventually_ne (by norm_num)
  have h4 : (fun t : ℝ => t ^ 4 * Q t) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
    simpa using (isBigO_refl (fun t : ℝ => t ^ 4) (𝓝 0)).mul hQb
  refine h4.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hne] with t ht
  have e : famOmega t = t ^ 2 * (1 - t) / famOmegaDen t := rfl
  simp only [hQ, e]
  field_simp
  simp only [famOmegaDen, famP]
  ring

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
