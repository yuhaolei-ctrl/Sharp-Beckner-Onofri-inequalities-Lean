import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ReducedQuarticParity
import BecknerOnofri.LocalElevenCore.ReducedQuarticAnalytic
import BecknerOnofri.AnalyticEvenOrder
import BecknerOnofri.LocalElevenCore.FirstShellOrbits
import BecknerOnofri.LocalElevenCore.ReducedPhysicalEnergy

/-! The actual critical reduced pressure has a sixth-order remainder.
The improvement follows from analyticity and genuine half-period translation symmetry. -/
noncomputable section

open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ReducedQuarticExpansion

open BecknerOnofri.HighDim.ReducedQuarticExpansion hiding U_analytic W_analytic centeredLogPartition_analytic centeredLogPartition_translation graphExpression graphExpression_analytic graphExpression_error graphExpression_even graphExpression_quartic graphExpression_quartic_sixth graphExpression_translation pairing_quadraticCorrection pairing_remainder_order_five quadraticCorrection_analytic quarticValue quarticValue_analytic quarticValue_even translation_mul translation_pow
open BecknerOnofri.HighDim.ContinuousSymmetry hiding allHalfTranslation axis_phase_eq_one_iff center_permutation coefficient_permutation complementMap_permutation complementPermutation complementPermutation_coe complementProjection_permutation coordinatePermutation coordinatePermutation_apply coordinates_permutation correction_permutation correction_translation exists_phase_nonnegative exponential_permutation firstShell_permutation_iff fourier_one_half frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_translation halfTranslation halfTranslation_fixes_of_zero integral_pointPermutation latticeSquare_permutation meanProjection_permutation mean_permutation nonlinearRemainder_permutation normalized_permutation partition_permutation permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm phaseNormalizer phaseNormalizer_spec phaseNormalizer_toCircle phase_allHalfTranslation phase_coordinate_norm phase_halfTranslation phase_orbit_iff phase_stabilizer_iff phase_stabilizer_trivial_of_full_support pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_neg potential_permutation potential_translation projectedEquation_permutation projection_permutation reconstructed_correction_translation reconstruction_permutation reduced_neg reduced_nonnegative_zero_iff reduced_permutation reduced_translation reduced_zero_on_inactive reduced_zero_permutation_iff reduced_zero_translation_iff zero_coordinate_of_stabilizer
open BecknerOnofri.HighDim.QuadraticModes hiding actual_quartic_coefficients amplitude_sum_square assembly_fourth_moment assembly_quartic_cumulant assembly_second_moment assembly_third_moment complementGreen_synthesis complementMap_center complementMap_const complementMap_synthesis complementMap_synthesis_zero complementSynthesis green_complementMap green_synthesis inverseGreen_factor mixedAmplitudeSum off_diagonal_sum quadraticCorrection_eq_resolvent quadraticSource_expansion quadraticSource_value quadratic_schur_identity quartic_slaving_contribution resolvent resolventPair resolventPair_apply resolventPair_synthesis resolvent_synthesis schur_diagonal schur_double_sum schur_off_diagonal shellSquare_first_coefficient shellSquare_mean shellSquare_projection sourcePair sourcePair_diagonal sourcePair_off_diagonal source_norm_moment source_norm_sq synthesis_mem_complement
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry QuadraticModes

theorem graphExpression_even {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ z in 𝓝 (0 : Coordinates d), graphExpression hd (-z) = graphExpression hd z := by
  filter_upwards [graphExpression_translation hd] with z hz
  simpa only [phase_allHalfTranslation] using hz (allHalfTranslation d)

theorem quarticValue_even {d : ℕ} (z : Coordinates d) : quarticValue (-z) = quarticValue z := by
  simp only [quarticValue, mixedAmplitudeSum, Pi.neg_apply, norm_neg]

/-- The exact quartic expansion of the genuine critical graph expression. -/
theorem graphExpression_quartic_sixth {d : ℕ} (hd : 11 ≤ d) :
    (fun z => graphExpression hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^6) := by
  apply analytic_even_fifth_order
    ((graphExpression_analytic hd).sub (quarticValue_analytic hd)) (graphExpression_quartic hd)
  filter_upwards [graphExpression_even hd] with z hz
  change graphExpression hd (-z) - quarticValue (-z) = graphExpression hd z - quarticValue z
  rw [hz, quarticValue_even]

end BecknerOnofri.HighDim.LocalEleven.ReducedQuarticExpansion

namespace BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy

open BecknerOnofri.HighDim.ReducedPhysicalEnergy hiding criticalReducedEnergy criticalReducedEnergy_eq criticalReducedEnergy_quartic criticalReducedEnergy_quartic_sixth dualFunctional_graphExpression
open BecknerOnofri.HighDim.ReducedQuarticExpansion hiding U_analytic W_analytic centeredLogPartition_analytic centeredLogPartition_translation graphExpression graphExpression_analytic graphExpression_error graphExpression_even graphExpression_quartic graphExpression_quartic_sixth graphExpression_translation pairing_quadraticCorrection pairing_remainder_order_five quadraticCorrection_analytic quarticValue quarticValue_analytic quarticValue_even translation_mul translation_pow
open ContinuousFirstShell ReducedQuarticExpansion

/-- This remainder estimate is for the original trusted physical dual functional. -/
theorem criticalReducedEnergy_quartic_sixth {d : ℕ} (hd : 11 ≤ d) :
    (fun z => criticalReducedEnergy hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^6) := by
  exact (graphExpression_quartic_sixth hd).congr'
    ((criticalReducedEnergy_eq hd).sub (Filter.EventuallyEq.rfl)).symm Filter.EventuallyEq.rfl

#print axioms criticalReducedEnergy_quartic_sixth
end BecknerOnofri.HighDim.LocalEleven.ReducedPhysicalEnergy
