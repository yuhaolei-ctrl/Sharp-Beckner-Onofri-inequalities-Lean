module

public import BecknerOnofri.V2.Reaudit.MorseBott.BranchInterface
public import BecknerOnofri.OrderParameterOnset

@[expose] public section

/-! # First-shell order parameter over all global minimizers, on the Onset route

`OrderParameterOnset.all_minimizers_bound` classifies the global minimizers by the earlier
global-minimizer route (`GlobalOptimizerClassification`).  The theorem below has the same conclusion
but classifies the minimizers by `MorseBott.minimizers_are_profile_branch_orbit`, i.e. by the
Sobolev-smallness / second-variation route of `V2/Onset` (manuscript `prop:section5-global-onset`),
and transports the pointwise bound for the derivative-family branch to the profile-family branch
`SupportedFamily.branch univ (1 - β_s/β)` by `common_branch_interface_beta`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.OrderParameterOnset

/-- One constant works for all global minimizing densities and all translations (Onset route). -/
theorem all_minimizers_bound_v2 {d : ℕ} (hd : 12 ≤ d) (E : V2.Onset.OnsetEndpointInputs d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
        |firstShellOrderParameter ρ.value -
          Real.sqrt (2 * (d : ℝ) / kappa d) * Real.sqrt (onsetDelta d β)| ≤
            C * onsetDelta d β := by
  obtain ⟨C, hC, hbound⟩ := branch_orderParameter_bound hd
  obtain ⟨R, -, hform⟩ := common_branch_interface_beta hd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hform, minimizers_are_profile_branch_orbit hd E] with β hb hid hc
  intro ρ hρ
  obtain ⟨a, ha⟩ := (hc.2 ρ).mp hρ
  rw [orderParameter_congr ha, normalizedGibbs_translate, orderParameter_translate]
  rw [hid.1] at hb
  exact hb

#print axioms all_minimizers_bound_v2

end BecknerOnofri.V2.Reaudit.MorseBott
