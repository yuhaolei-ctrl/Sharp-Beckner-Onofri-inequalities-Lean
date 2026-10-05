import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.DiagonalProfile
import BecknerOnofri.LocalElevenCore.DiagonalAmplitude

/-! The actual diagonal stationary profile in the trusted physical beta and
translation notation, with a uniform C-norm remainder estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.DiagonalScalarBranch

open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open BecknerOnofri.HighDim.ContinuousSymmetry hiding allHalfTranslation axis_phase_eq_one_iff center_permutation coefficient_permutation coefficient_reflection complementMap_permutation complementMap_reflection complementPermutation complementPermutation_coe complementProjection_permutation complementProjection_reflection complementReflection complementReflection_coe conjugateCoordinates conjugateCoordinates_apply conjugateCoordinates_norm coordinatePermutation coordinatePermutation_apply coordinates_permutation coordinates_reflection correction_permutation correction_reflection correction_translation exists_phase_nonnegative exponential_permutation exponential_reflection firstShell_permutation_iff fourier_one_half frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_reflection green_translation halfTranslation halfTranslation_fixes_of_zero integral_pointPermutation latticeSquare_permutation meanProjection_permutation meanProjection_reflection mean_permutation mean_reflection nonlinearRemainder_permutation normalized_permutation normalized_reflection partition_permutation partition_reflection permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm phaseNormalizer phaseNormalizer_spec phaseNormalizer_toCircle phase_allHalfTranslation phase_coordinate_norm phase_halfTranslation phase_orbit_iff phase_stabilizer_iff phase_stabilizer_trivial_of_full_support pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_neg potential_permutation potential_reflection potential_translation projectedEquation_permutation projectedEquation_reflection projection_permutation projection_reflection reconstructed_correction_translation reconstruction_permutation reconstruction_reflection reduced_neg reduced_nonnegative_zero_iff reduced_permutation reduced_reflection reduced_translation reduced_zero_on_inactive reduced_zero_permutation_iff reduced_zero_translation_iff reflection reflection_apply reflection_assembly reflection_const reflection_involutive reflection_mem_complement_iff reflection_one reflection_synthesis zero_coordinate_of_stabilizer
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ContinuousGibbs ContinuousFirstShell ReducedCubicExpansion ContinuousSymmetry

theorem assembly_realDiagonal_apply (d : ℕ) (t : ℝ) (x : Torus d) :
    assembly d (realDiagonal d t) x = 2*t*firstShellProfile 0 x := by
  rw [assembly_apply]
  simp only [ContinuousMap.sum_apply,synthesis_apply,realDiagonal_apply,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mFourier_axisFrequency,
    firstShellProfile,Pi.zero_apply,sub_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def physicalPotential {d : ℕ} (hd : 11 ≤ d) (β : ℝ) : Space d :=
  branchPotential hd (amplitude hd (β/spectralThreshold d))

theorem normalized_parameter_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (fun β : ℝ => β/spectralThreshold d) (𝓝[>] (spectralThreshold d)) (𝓝[>] (1:ℝ)) := by
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos (by omega)
  have hc : ContinuousAt (fun β : ℝ => β/spectralThreshold d) (spectralThreshold d) :=
    continuousAt_id.div_const _
  have ht : Tendsto (fun β : ℝ => β/spectralThreshold d) (𝓝[>] (spectralThreshold d)) (𝓝 1) := by
    simpa only [div_self hσ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht
  filter_upwards [self_mem_nhdsWithin] with β hβ
  change 1 < β/spectralThreshold d
  exact (one_lt_div hσ).mpr hβ

theorem physical_onset_eq {d : ℕ} (hd : 11 ≤ d) (β : ℝ) :
    onset (β/spectralThreshold d) = onsetDelta d β := by
  have hσ : spectralThreshold d ≠ 0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  unfold onset onsetDelta
  rw [one_div_div]

def profileRemainder {d : ℕ} (hd : 11 ≤ d) (β : ℝ) (a : Torus d) : Space d :=
  translation a (physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d))))

theorem profileRemainder_apply {d : ℕ} (hd : 11 ≤ d) (β : ℝ) (a x : Torus d) :
    profileRemainder hd β a x = branchRemainder β (physicalPotential hd β) a x := by
  simp only [profileRemainder,translation_apply,ContinuousMap.sub_apply,assembly_realDiagonal_apply,
    branchRemainder,translate,firstShellProfile,Pi.sub_apply,Pi.zero_apply,sub_zero]

theorem profileRemainder_norm {d : ℕ} (hd : 11 ≤ d) (β : ℝ) (a : Torus d) :
    ‖profileRemainder hd β a‖ =
      ‖physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d)))‖ :=
  (translation a).norm_map _

theorem physical_profile_bound {d : ℕ} (hd : 11 ≤ d) :
    (fun β => physicalPotential hd β - assembly d (realDiagonal d (Real.sqrt (onsetDelta d β/kappa d))))
      =O[𝓝[>] (spectralThreshold d)] (onsetDelta d) := by
  apply ((amplitude_potential_profile hd).comp_tendsto (normalized_parameter_tendsto hd)).congr
  · intro β
    change branchPotential hd (amplitude hd (β/spectralThreshold d)) -
      assembly d (realDiagonal d (Real.sqrt (onset (β/spectralThreshold d)/kappa d))) = _
    rw [physical_onset_eq hd]
    rfl
  · intro β
    exact physical_onset_eq hd β

/-- One error constant works for all torus translations in the trusted remainder. -/
theorem physical_profile_uniform {d : ℕ} (hd : 11 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      ∀ a : Torus d, ‖profileRemainder hd β a‖ ≤ C*onsetDelta d β := by
  obtain ⟨C,hC⟩ := (physical_profile_bound hd).exists_pos
  refine ⟨C,hC.1,?_⟩
  filter_upwards [hC.2.bound,(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin]
    with β hb hβ
  have hp : 0 < onsetDelta d β := by
    rw [← physical_onset_eq hd]
    exact onset_pos hβ
  intro a
  rw [profileRemainder_norm]
  simpa only [Real.norm_eq_abs,abs_of_pos hp] using hb

#print axioms physical_profile_uniform
#print axioms profileRemainder_apply
end BecknerOnofri.HighDim.LocalEleven.DiagonalScalarBranch
