module

public import BecknerOnofri.V2.Reaudit.MorseBott.AnalyticRemainder
public import BecknerOnofri.V2.Reaudit.MorseBott.BranchIdentification
public import BecknerOnofri.BranchEnergyDerivatives
public import BecknerOnofri.SupercriticalEnergyDerivatives
public import BecknerOnofri.SupercriticalBranchEnergy
public import BecknerOnofri.DiagonalEnergyExpansion

@[expose] public section

/-! # The analytic cubic remainder of the energy on the common branch

On the derivative family `HighDim.DiagonalScalarBranch` (`12 ≤ d`) the energy
`branchEnergy hd t = Φ_{μ(t)β_s}(branchPotential t)` and the onset variable
`branchDelta hd t = 1 - 1/μ(t)` are real-analytic and even in the amplitude `t`
(evenness: the half-period translation).  By `exists_delta_remainder` the energy is, in the onset
variable `δ`, `(d/(2κ_d)) δ² + δ³ R(δ)` with `R` analytic at `0`.  This is display
`(5.analytic-pressure-remainder)` of `cor:section5-defect-onset`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.DiagonalScalarBranch

/-- The branch potential at `-t` is the half-period translate of the one at `t`. -/
theorem branchPotential_neg {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (branchPotential hd (-t) : ContinuousGibbs.Space d) =
      ContinuousSymmetry.translation (ContinuousSymmetry.allHalfTranslation d)
        (branchPotential hd t) := by
  filter_upwards [(branch_coordinates_tendsto hd).eventually (ContinuousSymmetry.potential_neg hd),
    parameter_even hd] with t hpn hpe
  unfold branchPotential
  rw [hpe, map_neg]
  exact hpn

theorem branchEnergy_even {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0 : ℝ), branchEnergy hd (-t) = branchEnergy hd t := by
  filter_upwards [branchPotential_neg hd, parameter_even hd] with t hp hpe
  unfold branchEnergy
  rw [hpe, hp, OptimizerTranslation.coe_translation, dualFunctional_translate]

theorem branchDelta_even {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0 : ℝ), branchDelta hd (-t) = branchDelta hd t := by
  filter_upwards [parameter_even hd] with t hpe
  unfold branchDelta
  rw [hpe]

theorem branchDelta_analytic {d : ℕ} (hd : 12 ≤ d) : AnalyticAt ℝ (branchDelta hd) 0 := by
  unfold branchDelta
  have h1 : parameter hd 0 ≠ 0 := by rw [parameter_base]; norm_num
  have h2 : AnalyticAt ℝ (fun t => (parameter hd t)⁻¹) 0 := (parameter_analytic hd).inv h1
  have h3 : AnalyticAt ℝ (fun t : ℝ => (1 : ℝ) - (parameter hd t)⁻¹) 0 :=
    analyticAt_const.sub h2
  simpa [one_div] using h3

/-- **Analytic cubic remainder on the branch, in the amplitude variable.** -/
theorem exists_branch_remainder {d : ℕ} (hd : 12 ≤ d) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ),
      branchEnergy hd t = (d : ℝ) / (2 * kappa d) * branchDelta hd t ^ 2 +
        branchDelta hd t ^ 3 * R (branchDelta hd t) := by
  have hk := (kappa_pos d hd).ne'
  have hE0 : branchEnergy hd 0 = 0 := by
    have h := (branchEnergy_amplitude_expansion hd).bound
    obtain ⟨C, hC⟩ := h
    have := hC.self_of_nhds
    simpa using this
  have hD0 : branchDelta hd 0 = 0 := by simp [branchDelta, parameter_base]
  exact exists_delta_remainder (E := branchEnergy hd) (D := branchDelta hd) (κ := kappa d)
    (a := (d : ℝ) / (2 * kappa d)) hk (branchEnergy_analytic hd) (branchDelta_analytic hd)
    (branchEnergy_even hd) (branchDelta_even hd) hE0 hD0 (branchDelta_expansion hd)
    (branchEnergy_delta_expansion hd)

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.branchPotential_neg
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.branchEnergy_even
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_branch_remainder
