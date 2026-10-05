module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.PhysicalNormalCoercivity
public import BecknerOnofri.LocalElevenCore.NormalHessianCoercivity
public import BecknerOnofri.LocalElevenCore.PhysicalTranslationTangents
public import BecknerOnofri.LocalElevenCore.FullBranchHessian

@[expose] public section

/-! Strict normal coercivity of the actual physical full-mode branch, with
the exact raw H^(d/2) orthogonality and norm in the trusted theorem. -/
noncomputable section

open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.PhysicalNormalCoercivity

open BecknerOnofri.HighDim.PhysicalNormalCoercivity hiding physical_normalCoercivity
open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open DiagonalScalarBranch

theorem physical_normalCoercivity {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∃ c : ℝ, 0<c ∧
      ∀ h : Torus d → ℝ, InCriticalSobolev h → InSobolev ((d:ℝ)/2) h → MeanZero h →
        (∀ j : Fin d, (∫ x, h x*coordinateDerivative (physicalPotential hd β) j x ∂torusMeasure d)=0) →
        secondVariation β (physicalPotential hd β) h≤-c*sobolevNorm ((d:ℝ)/2) h^2 := by
  filter_upwards [FullBranchHessian.physical_hessian_nonpos_kernel hd,
    PhysicalTranslationTangents.coordinateDerivative_memLp hd,self_mem_nhdsWithin] with β hH ht hβ
  have hp : 0<β := lt_trans (Legacy.TorusEndpoint.endpointSigma_pos (by omega)) hβ
  exact NormalHessianCoercivity.normal_sobolev_coercivity (by omega) hp (physicalPotential hd β) ht
    (fun h hh hm => (hH h hh hm).1) (fun h hh hm hz => (hH h hh hm).2.mp hz)

#print axioms physical_normalCoercivity
end BecknerOnofri.HighDim.LocalEleven.PhysicalNormalCoercivity
