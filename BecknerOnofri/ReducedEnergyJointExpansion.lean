import BecknerOnofri.ReducedEnergyParameterBound
import BecknerOnofri.ReducedQuarticParity

/-! Exact manuscript quartic coefficients in the full parameter-dependent physical energy. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousFirstShell ReducedEnergyGradient ReducedPhysicalEnergy ReducedQuarticExpansion

theorem physicalReducedEnergy_critical {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    physicalReducedEnergy hd (1,z) = criticalReducedEnergy hd z := by
  simp only [physicalReducedEnergy, criticalReducedEnergy, one_mul]
  rfl

/-- Exact quartic expansion of the trusted dual energy on the genuine complementary graph,
with the manuscript's δ=1−1/μ and a uniform remainder. -/
theorem physicalReducedEnergy_joint_quartic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => physicalReducedEnergy hd x - (1-1/x.1)*(∑ i : Fin d, ‖x.2 i‖^2) - quarticValue x.2)
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^6 + |x.1-1| * ‖x.2‖^4) := by
  have ht : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0) :=
    continuous_snd.continuousAt
  have hc := (criticalReducedEnergy_quartic_sixth hd).comp_tendsto ht
  have hh := hc.add_add (physicalReducedEnergy_parameter_expansion hd)
  dsimp only [Function.comp_apply] at hh
  simp only [norm_pow, norm_mul, norm_norm, Real.norm_eq_abs, abs_abs, abs_norm] at hh
  apply hh.congr_left
  intro x
  rw [physicalReducedEnergy_critical]
  abel

#print axioms physicalReducedEnergy_joint_quartic
end BecknerOnofri.HighDim.UniformComplementBounds
