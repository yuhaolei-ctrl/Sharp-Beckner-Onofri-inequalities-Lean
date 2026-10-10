module

public import BecknerOnofri.V2.Reaudit.MorseBott.BranchRemainder
public import BecknerOnofri.GlobalOptimizerClassification
public import BecknerOnofri.GlobalPressureOnset

@[expose] public section

/-! # Common-branch interface for `prop:section5-global-onset` / `cor:section5-defect-onset`

One branch, one remainder.  Write `δ = 1 - 1/μ` and `U_δ := SupportedFamily.branch univ δ` (the
profile-family potential of `(5.full-branch-profile)`).

* `common_branch_interface` (unconditional): for `μ ↓ 1`, the derivative-family potential
  `DiagonalScalarBranch.branchPotential hd (amplitude hd μ)` *equals* `U_δ`, and the dual value of
  `U_δ` at coupling `μ β_s` is `(d/(2κ_d)) δ² + δ³ R(δ)` with `R` real analytic at `0`.
* `pressure_common_branch_form` (conditional on the two existing endpoint hypotheses, exactly those
  already used by `GlobalOptimizerClassification.branch_eventually_optimizer`): the pressure of the
  global problem is that same value, in the coupling variable `β` as well.

The analytic remainder (not an unspecified `O(δ³)`) is what the manuscript differentiates; see
`PressureDifferentiation.lean`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.DiagonalScalarBranch

/-- The supercritical energy of the derivative family has the analytic cubic-remainder form in the
onset variable. -/
theorem supercriticalEnergy_remainder_form {d : ℕ} (hd : 12 ≤ d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      supercriticalEnergy hd μ = (d : ℝ) / (2 * kappa d) * onset μ ^ 2 + onset μ ^ 3 * R (onset μ) := by
  obtain ⟨R, hR, hform⟩ := exists_branch_remainder hd
  refine ⟨R, hR, ?_⟩
  filter_upwards [(amplitude_tendsto hd).eventually hform, eventually_parameter_interval hd]
    with μ hμ hint
  have hpar : parameter hd (amplitude hd μ) = μ := (amplitude_spec hd hint).2
  have hδ : branchDelta hd (amplitude hd μ) = onset μ := by
    unfold branchDelta onset
    rw [hpar]
  rw [hδ] at hμ
  exact hμ

/-- **Common-branch interface.**  The branch used for the pressure/derivative statements is the
branch of the profile `(5.full-branch-profile)`, and its dual value carries one analytic
cubic remainder. -/
theorem common_branch_interface {d : ℕ} (hd : 12 ≤ d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ μ in 𝓝[>] (1 : ℝ),
      (DiagonalScalarBranch.branchPotential hd (DiagonalScalarBranch.amplitude hd μ) :
          ContinuousGibbs.Space d) =
        LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (1 - 1 / μ) ∧
      dualFunctional (μ * spectralThreshold d)
          (LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (1 - 1 / μ)) =
        (((d : ℝ) / (2 * kappa d) * (1 - 1 / μ) ^ 2 + (1 - 1 / μ) ^ 3 * R (1 - 1 / μ) : ℝ) : EReal) := by
  obtain ⟨R, hR, hform⟩ := supercriticalEnergy_remainder_form hd
  refine ⟨R, hR, ?_⟩
  filter_upwards [derivativeBranch_eq_profileBranch hd, hform, supercriticalEnergy_coe hd]
    with μ hid hf hc
  refine ⟨hid, ?_⟩
  rw [← hid, hc, hf]
  rfl

/-- The same interface in the coupling variable `β`: `μ = β/β_s`, `δ = 1 - β_s/β = onsetDelta d β`. -/
theorem common_branch_interface_beta {d : ℕ} (hd : 12 ≤ d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (DiagonalScalarBranch.physicalPotential hd β : ContinuousGibbs.Space d) =
        LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (onsetDelta d β) ∧
      dualFunctional β
          (LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (onsetDelta d β)) =
        (((d : ℝ) / (2 * kappa d) * onsetDelta d β ^ 2 +
          onsetDelta d β ^ 3 * R (onsetDelta d β) : ℝ) : EReal) := by
  obtain ⟨R, hR, hform⟩ := common_branch_interface hd
  refine ⟨R, hR, ?_⟩
  have hσ := (spectralThreshold_pos (by omega : 0 < d)).ne'
  filter_upwards [(normalized_parameter_tendsto hd).eventually hform] with β hβ
  have hon : 1 - 1 / (β / spectralThreshold d) = onsetDelta d β := by
    have := physical_onset_eq hd β
    unfold onset at this
    exact this
  have hmul : β / spectralThreshold d * spectralThreshold d = β := div_mul_cancel₀ _ hσ
  rw [hon, hmul] at hβ
  exact hβ

/-- **Pressure on the common branch** (conditional on the same two endpoint hypotheses as
`GlobalOptimizerClassification.branch_eventually_optimizer`): the pressure of the global problem is
`(d/(2κ_d)) δ² + δ³ R(δ)` with the analytic `R` of `common_branch_interface`. -/
theorem pressure_common_branch_form {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1 / 2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      pressure d β =
        (((d : ℝ) / (2 * kappa d) * onsetDelta d β ^ 2 +
          onsetDelta d β ^ 3 * R (onsetDelta d β) : ℝ) : EReal) := by
  obtain ⟨R, hR, hform⟩ := common_branch_interface_beta hd
  refine ⟨R, hR, ?_⟩
  filter_upwards [hform, GlobalOptimizerClassification.physical_branch_optimizer hd hEndpoint
    hRigidity, self_mem_nhdsWithin] with β ⟨hid, hdual⟩ hopt hβ
  have hσ := spectralThreshold_pos (by omega : 0 < d)
  have hβpos : 0 < β := hσ.trans hβ
  rw [GlobalPressureOnset.optimizer_pressure (by omega) hβpos _ hopt.1 hopt.2.2, hid, hdual]

/-- **Global minimizers are the translation orbit of the profile-family branch.**  Combined with the
existing classification (stated on the derivative family), the identification gives: the global
minimizing densities near onset are exactly the Gibbs densities of the translates of
`SupportedFamily.branch univ (1 - β_s/β)`, the branch of `(5.full-branch-profile)`.
(Conditional on the same two endpoint hypotheses as the existing classification.) -/
theorem minimizers_are_profile_branch_orbit {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1 / 2))
    (hRigidity : BecknerOnofri.OnsetCompactness.DensityRigidity d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      (∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
      (∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ ↔
        ∃ a : Torus d, ρ.value =ᵐ[torusMeasure d] normalizedGibbs (translate
          (LocalEleven.SupportedFamily.branch (by omega : 11 ≤ d) Finset.univ (onsetDelta d β) :
            ContinuousGibbs.Space d) a)) := by
  obtain ⟨R, -, hform⟩ := common_branch_interface_beta hd
  filter_upwards [hform, GlobalOptimizerClassification.physical_density_classification hd hEndpoint
    hRigidity] with β ⟨hid, _⟩ hcl
  rw [← hid]
  exact hcl

#print axioms common_branch_interface
#print axioms common_branch_interface_beta
#print axioms pressure_common_branch_form
#print axioms minimizers_are_profile_branch_orbit

end BecknerOnofri.V2.Reaudit.MorseBott
