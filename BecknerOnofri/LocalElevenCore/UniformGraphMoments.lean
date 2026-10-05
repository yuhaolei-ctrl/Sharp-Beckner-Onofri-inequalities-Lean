module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.UniformGraphMoments
public import BecknerOnofri.LocalElevenCore.UniformComplementBounds

@[expose] public section

/-! Uniform complementary Gibbs pairings along the actual two-parameter graph. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds

open BecknerOnofri.HighDim.UniformComplementBounds hiding complement_normalized_pairing complement_normalized_pairing_quartic correction_coe_uniform_quadratic correction_controlled_by_nonlinear correction_inverse_parameter correction_potential_quadratic correction_tendsto correction_uniform_quadratic nonlinearGreen parameter_interval potential_tendsto potential_uniform_linear uniformInverseBound uniformInverseBound_pos
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open BecknerOnofri.HighDim.SlavedMoments hiding U U_eq U_fourth_error U_order U_second U_third_error V VW_mean V_order W W_mean W_order_one W_order_two mean_mul_assembly
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation SlavedMoments

/-- Orthogonality removes the constant and first-shell terms of the Gibbs density exactly. -/
theorem complement_normalized_pairing {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) :
    mean d ((correction hd x : Space d) * normalized (potential hd x)) =
      mean d ((correction hd x : Space d)^2) +
      mean d ((correction hd x : Space d) * nonlinearRemainder (potential hd x)) := by
  have hm : mean d (potential hd x) = 0 := mean_reconstruction _
  have hc : center d (potential hd x) = potential hd x := by
    ext y
    simp only [center_apply, hm, sub_zero]
  have hN : normalized (potential hd x) = 1 + potential hd x + nonlinearRemainder (potential hd x) := by
    unfold nonlinearRemainder
    rw [hc]
    abel
  rw [hN, mul_add, mul_add, map_add, map_add, mul_one]
  have hw : mean d (correction hd x : Space d) = 0 := (correction hd x).property.1
  rw [hw, zero_add]
  congr 1
  change mean d ((correction hd x : Space d) *
    (assembly d x.2 + (correction hd x : Space d))) = _
  rw [mul_add, map_add, mean_mul_assembly, zero_add, pow_two]

/-- This is a joint bound in μ and z, with no pure-parameter error. -/
theorem complement_normalized_pairing_quartic {d : ℕ} (hd : 11 ≤ d) :
    (fun x => mean d ((correction hd x : Space d) * normalized (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^4) := by
  have hw := correction_coe_uniform_quadratic hd
  have hww := hw.pow 2
  simp only [← pow_mul, show 2*2=4 from rfl] at hww
  have hN := ((nonlinearRemainder_quadratic d).comp_tendsto (potential_tendsto hd)).trans
    ((potential_uniform_linear hd).norm_left.pow 2)
  have hWN : (fun x => (correction hd x : Space d) * nonlinearRemainder (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^4) := by
    convert! hw.mul hN using 1 <;> (ext x; ring)
  apply ((((mean d).isBigO_comp _ _).trans hww).add
    (((mean d).isBigO_comp _ _).trans hWN)).congr_left
  intro x
  exact (complement_normalized_pairing hd x).symm

#print axioms complement_normalized_pairing_quartic
end BecknerOnofri.HighDim.LocalEleven.UniformComplementBounds
