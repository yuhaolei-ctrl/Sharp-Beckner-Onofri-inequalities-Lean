module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.FullBranchHessian
public import BecknerOnofri.LocalElevenCore.FullReducedHessian
public import BecknerOnofri.LocalElevenCore.FullHessianDecomposition
public import BecknerOnofri.LocalElevenCore.AngularTangentRepresentation

@[expose] public section

/-! The complete actual raw critical-Sobolev Hessian on the diagonal branch:
nonpositivity, a quantitative split gap, and the exact translation kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalEleven.FullBranchHessian

open BecknerOnofri.HighDim.FullBranchHessian hiding complement_energy_zero diagonalInput diagonalInput_tendsto diagonalPotential_tendsto diagonal_hessian_nonpos_kernel diagonal_secondVariation_bound physical_hessian_nonpos_kernel physical_secondVariation_bound
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ReducedEquation ReducedCubicExpansion
open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open BecknerOnofri.HighDim.FullReducedHessian hiding diagonalJacobian diagonal_graph_hessian_bound diagonal_graph_hessian_nonpos_kernel diagonal_imaginary_derivative diagonal_jacobian_coercive diagonal_pairing_nonneg_kernel diagonal_pairing_real_part diagonal_real_derivative imaginaryPart physical_graph_hessian_bound physical_graph_hessian_nonpos_kernel realPart real_imaginary_decomposition real_input_tendsto reduced_real_derivative reduced_real_input
open BecknerOnofri.HighDim.ReducedHessianCoercivity hiding amplitudeBranch_real_jacobian_coercive amplitudeDerivative amplitudeDerivative_base amplitudeDerivative_coercive amplitudeDerivative_continuousAt amplitudeSquare amplitudeSquare_nonneg amplitudeSquare_pos amplitude_norm_square_le diagonalRescaling diagonalRescaling_tendsto diagonal_real_graph_hessian_bound diagonal_real_jacobian_coercive jacobian_coercive normalized_diagonal_amplitude_tendsto physicalScale physicalScale_pos physicalScale_sq physicalScale_tendsto physical_real_graph_hessian_bound physical_real_graph_hessian_negative quadratic_pairing_norm_bound reduced_derivative_rescaled reduced_real_jacobian_coercive rescaleInput_diagonal sum_square_le_dimension
open DiagonalScalarBranch FullReducedHessian ReducedHessianCoercivity
open BecknerOnofri.HighDim.AngularTangentRepresentation hiding imaginary_tangent_representation of_re_zero real_part_angle_sum_zero tangentMap_angles
open BecknerOnofri.HighDim.FullHessianDecomposition hiding critical_add critical_sub fourierCoeff_add fourierCoeff_sub fourierCoeff_zero_of_meanZero graphComplement graphComplement_properties graph_decomposition normalizedEnergyPairing_summable normalizedEnergy_add rawCoordinates raw_sub_complement_supported reconstruction_meanZero reconstruction_rawCoordinates secondVariation_add secondVariation_congr_ae secondVariation_decomposition weighted_first_integrable weighted_pair_integrable
open BecknerOnofri.HighDim.GraphHessian hiding continuous_mul_raw_integrable differentiated_projected_equation hasFDerivAt_graphResidual hessianPairing hessianPairing_continuous hessianPairing_linearized_complement hessianPairing_linearized_raw_complement hessianPairing_raw hessianPairing_self hessianPairing_tangentMap_complement hessianPairing_tangentMap_raw_complement linearized_energy_term linearized_fourier_euler linearized_inCriticalSobolev linearized_normalizedEnergy linearized_pairing_complement linearized_pairing_raw_complement normalizedEnergyPairing normalizedEnergyPairing_self physical_factor raw_pairing_hasSum secondVariation_graph secondVariation_linearized secondVariation_tangentMap shell_residual_pairing tangentMap tangentMap_apply tangentMap_eq tangentMap_equation weighted_norm_pairing
open GraphHessian FullHessianDecomposition AngularTangentRepresentation
open BecknerOnofri.HighDim.ComplementHessian hiding normalized_le_two_near_zero secondVariation_complement_bound secondVariation_complement_uniform weighted_square_bound weighted_square_integrable
open BecknerOnofri.HighDim.GraphTranslationTangents hiding angularDirection axisTranslation coordinates_tangent hasDerivAt_phase_axisTranslation phase_axisTranslation phase_axisTranslation_zero tangent tangentIndependent tangent_eq_coordinateDerivative
open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum
open ComplementHessian RawComplementGap GraphTranslationTangents

def diagonalInput {d : ℕ} (hd : 11 ≤ d) (μ : ℝ) : ℝ × Coordinates d :=
  (μ,realDiagonal d (amplitude hd μ))

theorem diagonalInput_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (diagonalInput hd) (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
  have hz := ((realDiagonal d).continuous.continuousAt.tendsto (x := 0)).comp (amplitude_tendsto hd)
  simp only [map_zero] at hz
  exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz

theorem diagonalPotential_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (fun μ => potential hd (diagonalInput hd μ)) (𝓝[>] (1:ℝ)) (𝓝 0) :=
  (UniformComplementBounds.potential_tendsto hd).comp (diagonalInput_tendsto hd)

/-- Zero Fourier energy on the actual complement means zero almost everywhere. -/
theorem complement_energy_zero {d : ℕ} (hd : 11 ≤ d) (q : Torus d → ℝ)
    (hq : InCriticalSobolev q) (hc : ComplementSupported (fourierCoeff q))
    (he : normalizedPotentialEnergy q=0) : q =ᵐ[torusMeasure d] (fun _ => 0) := by
  have hg := normalizedEnergy_gap hd q hq hc
  rw [he] at hg
  have hn : 0≤∫ x, (q x)^2 ∂torusMeasure d := integral_nonneg (fun _ => sq_nonneg _)
  have hz : (∫ x, (q x)^2 ∂torusMeasure d)=0 := by linarith
  have hi : Integrable (fun x => (q x)^2) (torusMeasure d) := by
    convert! hq.1.integrable_mul hq.1 using 1
    funext x
    change q x^2=q x*q x
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (q x)) hi).mp hz
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx

/-- The actual raw Hessian has a quantitative gap on both the real shell
and the entire complementary critical-Sobolev subspace. -/
theorem diagonal_secondVariation_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤
        -2*onset μ*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-
          (7/16:ℝ)*normalizedPotentialEnergy (graphComplement hd (diagonalInput hd μ) h) := by
  filter_upwards [(diagonalInput_tendsto hd).eventually (secondVariation_decomposition hd),
    (diagonalInput_tendsto hd).eventually (graphComplement_properties hd),
    diagonal_graph_hessian_bound hd,(diagonalPotential_tendsto hd).eventually
      (normalized_le_two_near_zero d),self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds]
    with μ hsplit hprops hfinite hpot hμ hμ2 h hh hm
  change 1<μ at hμ
  obtain ⟨hv,hvm,hq,hc⟩ := hprops h hh hm
  have hcomp := secondVariation_complement_bound hd (show 0<μ by linarith) hμ2.le
    _ hpot _ hq hc
  have hfin := hfinite (rawCoordinates h)
  simp only [diagonalInput] at hsplit hcomp ⊢
  rw [hsplit h hh hm]
  linarith

/-- Full raw-domain nonpositivity and exactly the translation tangent kernel. -/
theorem diagonal_hessian_nonpos_kernel {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤ 0 ∧
      (secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h=0 ↔
        ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination (potential hd (diagonalInput hd μ)) a) := by
  filter_upwards [diagonal_secondVariation_bound hd,
    (diagonalInput_tendsto hd).eventually (graphComplement_properties hd),
    (diagonalInput_tendsto hd).eventually (imaginary_tangent_representation hd),
    (diagonalInput_tendsto hd).eventually (tangentMap_angles hd),
    diagonal_graph_hessian_nonpos_kernel hd,eventually_parameter_interval hd,self_mem_nhdsWithin]
    with μ hbound hprops hrepr hang hfinite hinterval hμ h hh hm
  change 1<μ at hμ
  let q := graphComplement hd (diagonalInput hd μ) h
  obtain ⟨hv,hvm,hq,hc⟩ := hprops h hh hm
  have hE : 0≤normalizedPotentialEnergy q := normalizedEnergy_nonneg (by omega) q hq
  have hS : 0≤amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h)) := amplitudeSquare_nonneg _
  have hδ := onset_pos hμ
  have hb := hbound h hh hm
  change secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤
    -2*onset μ*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-(7/16:ℝ)*normalizedPotentialEnergy q at hb
  refine ⟨le_trans hb (by nlinarith [mul_nonneg hδ.le hS]),?_⟩
  constructor
  · intro hz
    rw [hz] at hb
    have hEq : normalizedPotentialEnergy q=0 := by nlinarith [mul_nonneg hδ.le hS]
    have hSq : amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))=0 := by nlinarith
    have hr : FullReducedHessian.realPart (rawCoordinates h)=0 := by
      by_contra hr
      have := amplitudeSquare_pos hr
      linarith
    have hqa := complement_energy_zero hd q hq hc hEq
    have hre : ∀ i, (rawCoordinates h i).re=0 := fun i => congrFun hr i
    obtain ⟨a,ha⟩ := hrepr (amplitude hd μ) (amplitude_pos hd hμ hinterval.2).ne' rfl
      (rawCoordinates h) hre
    refine ⟨a,?_⟩
    filter_upwards [hqa] with y hy
    have he := congrFun (graph_decomposition hd (diagonalInput hd μ) h) y
    change h y=tangentMap hd (diagonalInput hd μ) (rawCoordinates h) y+q y at he
    rw [hy,add_zero] at he
    exact he.trans (congrFun ha y)
  · rintro ⟨a,ha⟩
    let z : Coordinates d := ∑ j : Fin d, a j • angularDirection (diagonalInput hd μ).2 j
    have hr : FullReducedHessian.realPart z=0 := by
      funext i
      exact real_part_angle_sum_zero (amplitude hd μ) a i
    have hz : secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ))
        (tangentMap hd (diagonalInput hd μ) z)=0 := (hfinite z).2.mpr hr
    have htan := hang a
    have hae : h =ᵐ[torusMeasure d] (tangentMap hd (diagonalInput hd μ) z : Torus d → ℝ) := by
      rw [show (tangentMap hd (diagonalInput hd μ) z : Torus d → ℝ)=
        tangentCombination (potential hd (diagonalInput hd μ)) a from htan]
      exact ha
    exact (secondVariation_congr_ae (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) hae).trans hz

/-- The same full Hessian theorem in the exact trusted physical branch notation. -/
theorem physical_hessian_nonpos_kernel {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      secondVariation β (physicalPotential hd β) h ≤ 0 ∧
      (secondVariation β (physicalPotential hd β) h=0 ↔
        ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination (physicalPotential hd β) a) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_hessian_nonpos_kernel hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h hh hm
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (diagonalInput hd (β/spectralThreshold d)) := by
    simp only [physicalPotential,branchPotential,hi,diagonalInput]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ] using hb h hh hm

theorem physical_secondVariation_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      secondVariation β (physicalPotential hd β) h ≤
        -2*onsetDelta d β*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-
          (7/16:ℝ)*normalizedPotentialEnergy
            (graphComplement hd (diagonalInput hd (β/spectralThreshold d)) h) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_secondVariation_bound hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h hh hm
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (diagonalInput hd (β/spectralThreshold d)) := by
    simp only [physicalPotential,branchPotential,hi,diagonalInput]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ,physical_onset_eq hd] using hb h hh hm

#print axioms physical_secondVariation_bound
#print axioms diagonal_secondVariation_bound
#print axioms diagonal_hessian_nonpos_kernel
#print axioms physical_hessian_nonpos_kernel
end BecknerOnofri.HighDim.LocalEleven.FullBranchHessian
