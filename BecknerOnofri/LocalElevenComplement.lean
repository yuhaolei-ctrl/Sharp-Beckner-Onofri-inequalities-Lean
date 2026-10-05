import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.GreenLocalBranch

/-! The full complex first-shell Lyapunov–Schmidt complement for every d ≥ 11. No global-optimizer hypothesis is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven
open scoped Topology
open ContinuousGibbs ContinuousFirstShell ContinuousComplement
theorem exists_analytic_complement {d : ℕ} (hd : 11 ≤ d) :
    ∃ ψ : ℝ × Coordinates d → complement d,
      AnalyticAt ℝ ψ (1, 0) ∧ ψ (1, 0) = 0 ∧
      HasFDerivAt (𝕜 := ℝ) ψ 0 (1, 0) ∧
      (∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
        projectedEquation (greenContinuous d) (x, ψ x) = 0) ∧
      (∀ᶠ x in 𝓝 ((1, (0 : Coordinates d)), (0 : complement d)),
        projectedEquation (greenContinuous d) x = 0 ↔ ψ x.1 = x.2) := by
  apply exists_analytic_solution (greenContinuous d) (GreenLocalBranch.green_first_complement_zero (by omega))
    (continuousComplementContinuousLinearEquiv hd (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (1:ℝ) ≤ 2))
  rw [GreenLocalBranch.linearPart_eq (by omega)]
  exact continuousComplementContinuousLinearEquiv_one hd


#print axioms exists_analytic_complement
end BecknerOnofri.HighDim.LocalEleven
