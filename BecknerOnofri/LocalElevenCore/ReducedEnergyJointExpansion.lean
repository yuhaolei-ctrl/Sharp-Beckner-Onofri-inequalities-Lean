module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.ReducedEnergyJointExpansion
public import BecknerOnofri.LocalElevenCore.ReducedEnergyParameterBound
public import BecknerOnofri.LocalElevenCore.ReducedQuarticParity

@[expose] public section

/-! Exact manuscript quartic coefficients in the full parameter-dependent physical energy. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding complement_normalized_pairing complement_normalized_pairing_quartic correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen parameterEnergyDerivative parameterEnergyDerivative_quartic parameterEnergyRemainder parameterEnergyRemainder_hasDerivAt parameter_interval physicalReducedEnergy_critical physicalReducedEnergy_joint_quartic physicalReducedEnergy_parameter_expansion potential_tendsto potential_uniform_linear uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.ReducedEnergyGradient hiding fderiv_physicalReducedEnergy_apply graphGradient graphGradient_apply graphValue hasDerivAt_parameter_graphValue hasDerivAt_physicalReducedEnergy_parameter hasFDerivAt_graphValue hasFDerivAt_mean_mul hasFDerivAt_physicalReducedEnergy mean_mul_assembly pairing_cancellation parameter_pairing_cancellation physicalReducedEnergy physicalReducedEnergy_critical_iff physicalReducedEnergy_eq_graphValue projected_equation_value
open BecknerOnofri.HighDim.ReducedPhysicalEnergy hiding criticalReducedEnergy criticalReducedEnergy_eq criticalReducedEnergy_quartic criticalReducedEnergy_quartic_sixth dualFunctional_graphExpression
open BecknerOnofri.HighDim.ReducedQuarticExpansion hiding U_analytic W_analytic centeredLogPartition_analytic centeredLogPartition_translation graphExpression graphExpression_analytic graphExpression_error graphExpression_even graphExpression_quartic graphExpression_quartic_sixth graphExpression_translation pairing_quadraticCorrection pairing_remainder_order_five quadraticCorrection_analytic quarticValue quarticValue_analytic quarticValue_even translation_mul translation_pow
open ContinuousFirstShell ReducedEnergyGradient ReducedPhysicalEnergy ReducedQuarticExpansion

theorem physicalReducedEnergy_critical {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    physicalReducedEnergy hd (1,z) = criticalReducedEnergy hd z := by
  simp only [physicalReducedEnergy, criticalReducedEnergy, one_mul]
  rfl

/-- Exact quartic expansion of the trusted dual energy on the genuine complementary graph,
with the manuscript's δ=1−1/μ and a uniform remainder. -/
theorem physicalReducedEnergy_joint_quartic {d : ℕ} (hd : 11 ≤ d) :
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
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
