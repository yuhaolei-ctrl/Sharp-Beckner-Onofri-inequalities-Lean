import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ReducedEnergyParameterBound
import BecknerOnofri.LocalElevenCore.UniformGraphMoments
import BecknerOnofri.LocalElevenCore.ReducedParameterDerivative
import BecknerOnofri.ParameterMeanValue

/-! A joint parameter expansion for the actual physical reduced energy. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding complement_normalized_pairing complement_normalized_pairing_quartic correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen parameterEnergyDerivative parameterEnergyDerivative_quartic parameterEnergyRemainder parameterEnergyRemainder_hasDerivAt parameter_interval physicalReducedEnergy_parameter_expansion potential_tendsto potential_uniform_linear uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.ReducedEnergyGradient hiding fderiv_physicalReducedEnergy_apply graphGradient graphGradient_apply graphValue hasDerivAt_parameter_graphValue hasDerivAt_physicalReducedEnergy_parameter hasFDerivAt_graphValue hasFDerivAt_mean_mul hasFDerivAt_physicalReducedEnergy mean_mul_assembly pairing_cancellation parameter_pairing_cancellation physicalReducedEnergy physicalReducedEnergy_critical_iff physicalReducedEnergy_eq_graphValue projected_equation_value
open ReducedEnergyGradient GraphEnergy

def parameterEnergyRemainder {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) : ℝ :=
  physicalReducedEnergy hd x - (1-1/x.1)*(∑ i : Fin d, ‖x.2 i‖^2)

def parameterEnergyDerivative {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) : ℝ :=
  mean d ((correction hd x : Space d)*normalized (potential hd x))/(2*x.1)

theorem parameterEnergyDerivative_quartic {d : ℕ} (hd : 11 ≤ d) :
    parameterEnergyDerivative hd =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^4) := by
  have hf : ContinuousAt (fun x : ℝ × Coordinates d => 1/(2*x.1)) (1,0) :=
    continuousAt_const.div (continuousAt_const.mul continuous_fst.continuousAt) (by norm_num)
  have hh := (complement_normalized_pairing_quartic hd).mul hf.isBigO
  convert! hh using 1 <;> (ext x; simp only [mul_one, parameterEnergyDerivative, div_eq_mul_inv, one_mul])

/-- The leading quadratic parameter contribution is subtracted exactly. -/
theorem parameterEnergyRemainder_hasDerivAt {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      HasDerivAt (fun μ => parameterEnergyRemainder hd (μ,x.2)) (parameterEnergyDerivative hd x) x.1 := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hasDerivAt_physicalReducedEnergy_parameter hd, correction_solves hd, hp] with x hx he hpos
  have hlead : HasDerivAt (fun μ : ℝ => (1-1/μ)*(∑ i : Fin d, ‖x.2 i‖^2))
      ((∑ i : Fin d, ‖x.2 i‖^2)/x.1^2) x.1 := by
    convert! ((hasDerivAt_const x.1 (1:ℝ)).sub ((hasDerivAt_id x.1).inv hpos.ne')).mul_const
      (∑ i : Fin d, ‖x.2 i‖^2) using 1 <;> simp [div_eq_mul_inv, mul_comm]
  have henergy := graph_normalizedPotentialEnergy (by omega : 0<d) x.1 x.2 (correction hd x) he
  have hde : normalizedPotentialEnergy (potential hd x)/(2*x.1^2) -
      (∑ i : Fin d, ‖x.2 i‖^2)/x.1^2 = parameterEnergyDerivative hd x := by
    change normalizedPotentialEnergy (reconstruction d (x.2,correction hd x))/(2*x.1^2) - _ = _
    rw [henergy]
    unfold parameterEnergyDerivative
    change (2*(∑ i : Fin d, ‖x.2 i‖^2)+x.1*mean d ((correction hd x : Space d)*normalized (potential hd x)))/(2*x.1^2) - _ = _
    field_simp
    ring
  rw [← hde]
  exact hx.sub hlead

/-- Integrating the actual parameter derivative retains all four amplitude powers. -/
theorem physicalReducedEnergy_parameter_expansion {d : ℕ} (hd : 11 ≤ d) :
    (fun x => physicalReducedEnergy hd x - physicalReducedEnergy hd (1,x.2) -
      (1-1/x.1)*(∑ i : Fin d, ‖x.2 i‖^2))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| * ‖x.2‖^4) := by
  have hh := parameter_difference_isBigO 4 (parameterEnergyRemainder_hasDerivAt hd)
    (parameterEnergyDerivative_quartic hd)
  apply hh.congr_left
  intro x
  simp only [parameterEnergyRemainder, div_one, sub_self, zero_mul, sub_zero]
  ring

#print axioms parameterEnergyDerivative_quartic
#print axioms physicalReducedEnergy_parameter_expansion
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
