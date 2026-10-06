module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.PhysicalBranchProperties
public import BecknerOnofri.LocalElevenCore.DiagonalProfile
public import BecknerOnofri.LocalElevenCore.GraphTranslationTangents
public import BecknerOnofri.LocalElevenCore.GraphCritical
public import BecknerOnofri.LocalElevenCore.EulerEquation

@[expose] public section

/-! All non-Hessian fields of the actual physical full-mode branch, including
its exact Fourier stationarity and actual raw translation tangent independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.PhysicalBranchProperties

open BecknerOnofri.HighDim.PhysicalBranchProperties hiding BasicProperties physical_axis_coefficient physical_branch_properties physical_coordinates physical_full_zero physical_graph_tendsto physical_meanZero
open BecknerOnofri.HighDim.ContinuousSymmetry hiding allHalfTranslation axis_phase_eq_one_iff center_permutation coefficient_permutation coefficient_reflection complementMap_permutation complementMap_reflection complementPermutation complementPermutation_coe complementProjection_permutation complementProjection_reflection complementReflection complementReflection_coe conjugateCoordinates conjugateCoordinates_apply conjugateCoordinates_norm coordinatePermutation coordinatePermutation_apply coordinates_permutation coordinates_reflection correction_permutation correction_reflection correction_translation exists_phase_nonnegative exponential_permutation exponential_reflection firstShell_permutation_iff fourier_one_half frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_reflection green_translation halfTranslation halfTranslation_fixes_of_zero integral_pointPermutation latticeSquare_permutation meanProjection_permutation meanProjection_reflection mean_permutation mean_reflection nonlinearRemainder_permutation normalized_permutation normalized_reflection partition_permutation partition_reflection permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm phaseNormalizer phaseNormalizer_spec phaseNormalizer_toCircle phase_allHalfTranslation phase_coordinate_norm phase_halfTranslation phase_orbit_iff phase_stabilizer_iff phase_stabilizer_trivial_of_full_support pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_neg potential_permutation potential_reflection potential_translation projectedEquation_permutation projectedEquation_reflection projection_permutation projection_reflection reconstructed_correction_translation reconstruction_permutation reconstruction_reflection reduced_neg reduced_nonnegative_zero_iff reduced_permutation reduced_reflection reduced_translation reduced_zero_on_inactive reduced_zero_permutation_iff reduced_zero_translation_iff reflection reflection_apply reflection_assembly reflection_const reflection_involutive reflection_mem_complement_iff reflection_one reflection_synthesis zero_coordinate_of_stabilizer
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicModel_norm_lower cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_critical_norm_lower reduced_critical_zero_iff reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry ReducedCubicExpansion
open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open BecknerOnofri.HighDim.ReducedEquation hiding coefficient_full_zero_iff complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction critical_full_locally_isolated critical_stationary_locally_isolated full full_complement full_coordinates full_mean full_zero_iff full_zero_iff_stationary graph_full_iff_reduced graph_stationary_iff local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open DiagonalScalarBranch ReducedEquation

/-- The first seven fields of the trusted Morse--Bott statement, with Sobolev
membership proved for every real index. Hessian conclusions are separate. -/
structure BasicProperties {d : ℕ} (β : ℝ) (u : Torus d → ℝ) : Prop where
  smooth : SmoothOnTorus u
  sobolev : ∀ s : ℝ, InSobolev s u
  criticalSobolev : InCriticalSobolev u
  meanZero : MeanZero u
  stationary : ∀ k : NonzeroFrequency d,
    (frequencyLength k.val ^ d : ℂ) * fourierCoeff u k.val =
      (β / spectralThreshold d : ℝ) * fourierCoeff (normalizedGibbs u) k.val
  fullModes : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0
  tangentIndependent : ∀ a : Fin d → ℝ,
    tangentCombination u a =ᵐ[torusMeasure d] (fun _ => 0) → a = 0

@[simp] theorem physical_meanZero {d : ℕ} (hd : 11 ≤ d) (β : ℝ) :
    MeanZero (physicalPotential hd β) := branchPotential_mean hd _

@[simp] theorem physical_coordinates {d : ℕ} (hd : 11 ≤ d) (β : ℝ) :
    coordinates d (physicalPotential hd β) =
      realDiagonal d (amplitude hd (β/spectralThreshold d)) :=
  branchPotential_coordinates hd _

@[simp] theorem physical_axis_coefficient {d : ℕ} (hd : 11 ≤ d) (β : ℝ) (j : Fin d) :
    fourierCoeff (physicalPotential hd β) (axisFrequency j) =
      (amplitude hd (β/spectralThreshold d) : ℂ) := by
  rw [← coefficient_eq_fourierCoeff]
  exact congrFun (physical_coordinates hd β) j

/-- The coordinates at which the physical branch evaluates the genuine graph
converge to its analytic base point. -/
theorem physical_graph_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (fun β : ℝ =>
      (parameter hd (amplitude hd (β/spectralThreshold d)),
        realDiagonal d (amplitude hd (β/spectralThreshold d))))
      (𝓝[>] (spectralThreshold d)) (𝓝 (1,(0 : Coordinates d))) :=
  (branch_coordinates_tendsto hd).comp ((amplitude_tendsto hd).comp (normalized_parameter_tendsto hd))

/-- The actual inverse diagonal branch satisfies the exact continuous Euler
operator at its physical normalized parameter. -/
theorem physical_full_zero {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d),
      full d (β/spectralThreshold d) (physicalPotential hd β)=0 := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin,
    (normalized_parameter_tendsto hd).eventually (eventually_parameter_interval hd)] with β hp hi
  exact (amplitude_stationary hd hp hi.2).2.2.2.2

theorem physical_branch_properties {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), BasicProperties β (physicalPotential hd β) := by
  have ht := physical_graph_tendsto hd
  filter_upwards [(normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin,
    (normalized_parameter_tendsto hd).eventually (eventually_parameter_interval hd),
    ht.eventually (GraphCritical.potential_inCriticalSobolev hd),
    ht.eventually (GraphTranslationTangents.tangentIndependent hd)] with β hp hi hcrit htangent
  have hs := amplitude_stationary hd hp hi.2
  have hfull : ∀ j : Fin d, realDiagonal d (amplitude hd (β/spectralThreshold d)) j ≠ 0 := by
    intro j
    exact Complex.ofReal_ne_zero.mpr (amplitude_pos hd hp hi.2).ne'
  refine ⟨hs.2.2.1,hs.2.2.2.1,hcrit,physical_meanZero hd β,?_,?_,htangent hfull⟩
  · simpa only [physicalPotential,Complex.ofReal_pow] using
      ((full_zero_iff_stationary (by omega) _ _).mp hs.2.2.2.2).2
  · intro j
    rw [physical_axis_coefficient]
    exact Complex.ofReal_ne_zero.mpr (amplitude_pos hd hp hi.2).ne'

#print axioms physical_full_zero
#print axioms physical_branch_properties
end BecknerOnofri.HighDim.LocalEleven.PhysicalBranchProperties
