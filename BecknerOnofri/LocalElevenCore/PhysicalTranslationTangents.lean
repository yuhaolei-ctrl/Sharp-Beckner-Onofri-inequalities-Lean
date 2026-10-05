import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.PhysicalTranslationTangents
import BecknerOnofri.LocalElevenCore.PhysicalBranchProperties

/-! Actual continuous representatives of each spatial translation tangent of
the physical branch, for the raw L² orthogonality in the trusted statement. -/
noncomputable section

open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.PhysicalTranslationTangents

open BecknerOnofri.HighDim.PhysicalTranslationTangents hiding coordinateDerivative_eq coordinateDerivative_memLp physicalTangent
open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open BecknerOnofri.HighDim.GraphTranslationTangents hiding angularDirection axisTranslation coordinates_tangent hasDerivAt_phase_axisTranslation phase_axisTranslation phase_axisTranslation_zero tangent tangentIndependent tangent_eq_coordinateDerivative
open ContinuousGibbs ContinuousFirstShell GraphTranslationTangents DiagonalScalarBranch

def physicalTangent {d : ℕ} (hd : 11 ≤ d) (β : ℝ) (j : Fin d) : Space d :=
  tangent hd (parameter hd (amplitude hd (β/spectralThreshold d)),
    ReducedCubicExpansion.realDiagonal d (amplitude hd (β/spectralThreshold d))) j

theorem coordinateDerivative_eq {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ j : Fin d,
      coordinateDerivative (physicalPotential hd β) j = (physicalTangent hd β j : Torus d → ℝ) := by
  filter_upwards [(PhysicalBranchProperties.physical_graph_tendsto hd).eventually
    (tangent_eq_coordinateDerivative hd)] with β hb j
  funext x
  exact (hb j x).symm

theorem coordinateDerivative_memLp {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ j : Fin d,
      MemLp (coordinateDerivative (physicalPotential hd β) j) 2 (torusMeasure d) := by
  filter_upwards [coordinateDerivative_eq hd] with β hb j
  rw [hb j]
  exact (physicalTangent hd β j).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

#print axioms coordinateDerivative_memLp
end BecknerOnofri.HighDim.LocalEleven.PhysicalTranslationTangents
