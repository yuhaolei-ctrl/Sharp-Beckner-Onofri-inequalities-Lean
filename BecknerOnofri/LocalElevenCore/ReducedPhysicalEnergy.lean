import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ReducedPhysicalEnergy
import BecknerOnofri.LocalElevenCore.GraphEnergy
import BecknerOnofri.LocalElevenCore.ReducedQuarticExpansion

/-! The quartic expansion is an expansion of the actual trusted physical
dual functional on the solved complementary graph. -/
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy

open BecknerOnofri.HighDim.ReducedPhysicalEnergy hiding criticalReducedEnergy criticalReducedEnergy_eq criticalReducedEnergy_quartic dualFunctional_graphExpression
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.QuadraticSlaving hiding correction_quadratic_expansion inverseGreen mean_slicePotential nonlinear_error_cubic normalized_error_cubic pow_down quadraticCorrection quadraticTerm_difference_cubic sliceCorrection sliceCorrection_coe_quadratic sliceCorrection_inverse sliceCorrection_quadratic slicePotential slicePotential_linear slicePotential_tendsto
open BecknerOnofri.HighDim.ReducedQuarticExpansion hiding graphExpression graphExpression_error graphExpression_quartic pairing_quadraticCorrection pairing_remainder_order_five quarticValue
open BecknerOnofri.HighDim.SlavedMoments hiding U U_eq U_fourth_error U_order U_second U_second_square_error U_third_error V VW_mean V_order W W_mean W_normalized_error W_order_one W_order_two W_quadraticPolynomial_mean log_graph_error mean_mul_assembly mean_mul_center
open QuadraticSlaving SlavedMoments ReducedQuarticExpansion GraphEnergy

/-- The actual trusted dual energy, restricted to the genuine implicit graph
at the critical physical parameter. -/
def criticalReducedEnergy {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) : ℝ :=
  (dualFunctional (spectralThreshold d) (U hd z)).toReal

theorem dualFunctional_graphExpression {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d),
      dualFunctional (spectralThreshold d) (U hd z) = (graphExpression hd z : EReal) := by
  have ht : Tendsto (fun z : Coordinates d => ((1:ℝ),z)) (𝓝 0) (𝓝 (1,0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  filter_upwards [ht.eventually (correction_solves hd)] with z hz
  have hh := graph_dualFunctional (by omega : 0 < d) (by norm_num : (0:ℝ)<1)
    z (sliceCorrection hd z) hz
  change dualFunctional (1 * spectralThreshold d) (U hd z) = _ at hh
  rw [one_mul, div_one] at hh
  rw [hh]
  congr 1
  unfold graphExpression
  rw [centeredLogPartition_eq, mean_slicePotential, sub_zero, assembly_square_mean]
  change logPartitionReal (U hd z) - (∑ i, ‖z i‖^2) -
    (1/2:ℝ)*mean d (W hd z * normalized (U hd z)) =
      logPartitionReal (U hd z) - (2 * ∑ i, ‖z i‖^2)/2 -
        mean d (W hd z * normalized (U hd z))/2
  ring

theorem criticalReducedEnergy_eq {d : ℕ} (hd : 11 ≤ d) :
    criticalReducedEnergy hd =ᶠ[𝓝 (0 : Coordinates d)] graphExpression hd := by
  filter_upwards [dualFunctional_graphExpression hd] with z hz
  simp only [criticalReducedEnergy, hz, EReal.toReal_coe]

/-- Exact manuscript quartic coefficients and fifth-order norm remainder for
the physical dual functional, not an auxiliary formal polynomial. -/
theorem criticalReducedEnergy_quartic {d : ℕ} (hd : 11 ≤ d) :
    (fun z => criticalReducedEnergy hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  exact (graphExpression_quartic hd).congr'
    ((criticalReducedEnergy_eq hd).sub (Filter.EventuallyEq.rfl)).symm Filter.EventuallyEq.rfl

#print axioms dualFunctional_graphExpression
#print axioms criticalReducedEnergy_quartic
end BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy
