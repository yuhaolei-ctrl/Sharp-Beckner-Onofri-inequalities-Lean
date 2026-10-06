module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.FullReducedHessian
public import BecknerOnofri.LocalElevenCore.ReducedHessianCoercivity
public import BecknerOnofri.LocalElevenCore.AngularReducedKernel

@[expose] public section

/-! The full complex reduced Hessian: real amplitude directions are strictly
negative for the energy, and exactly the phase directions form its kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.FullReducedHessian

open BecknerOnofri.HighDim.FullReducedHessian hiding diagonalJacobian diagonal_graph_hessian_bound diagonal_graph_hessian_nonpos_kernel diagonal_imaginary_derivative diagonal_jacobian_coercive diagonal_pairing_nonneg_kernel diagonal_pairing_real_part diagonal_real_derivative imaginaryPart physical_graph_hessian_bound physical_graph_hessian_nonpos_kernel realPart real_imaginary_decomposition real_input_tendsto reduced_real_derivative reduced_real_input
open BecknerOnofri.HighDim.ContinuousSymmetry hiding allHalfTranslation axis_phase_eq_one_iff center_permutation coefficient_permutation coefficient_reflection complementMap_permutation complementMap_reflection complementPermutation complementPermutation_coe complementProjection_permutation complementProjection_reflection complementReflection complementReflection_coe conjugateCoordinates conjugateCoordinates_apply conjugateCoordinates_norm coordinatePermutation coordinatePermutation_apply coordinates_permutation coordinates_reflection correction_permutation correction_reflection correction_translation exists_phase_nonnegative exponential_permutation exponential_reflection firstShell_permutation_iff fourier_one_half frequencyLength_permutation frequencyPermutation frequencyPermutation_axis frequencyPermutation_eq_zero_iff frequencyPermutation_neg full_translation green_permutation green_reflection green_translation halfTranslation halfTranslation_fixes_of_zero integral_pointPermutation latticeSquare_permutation meanProjection_permutation meanProjection_reflection mean_permutation mean_reflection nonlinearRemainder_permutation normalized_permutation normalized_reflection partition_permutation partition_reflection permutation permutation_apply permutation_assembly permutation_const permutation_mem_complement_iff permutation_one permuteCoordinates permuteCoordinates_norm phaseNormalizer phaseNormalizer_spec phaseNormalizer_toCircle phase_allHalfTranslation phase_coordinate_norm phase_halfTranslation phase_orbit_iff phase_stabilizer_iff phase_stabilizer_trivial_of_full_support pointPermutation pointPermutation_apply pointPermutation_continuous pointPermutation_isometry pointPermutation_measurePreserving potential_neg potential_permutation potential_reflection potential_translation projectedEquation_permutation projectedEquation_reflection projection_permutation projection_reflection reconstructed_correction_translation reconstruction_permutation reconstruction_reflection reduced_neg reduced_nonnegative_zero_iff reduced_permutation reduced_reflection reduced_translation reduced_zero_on_inactive reduced_zero_permutation_iff reduced_zero_translation_iff reflection reflection_apply reflection_assembly reflection_const reflection_involutive reflection_mem_complement_iff reflection_one reflection_synthesis zero_coordinate_of_stabilizer
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousFirstShell ContinuousSymmetry ReducedEquation ReducedCubicExpansion
open BecknerOnofri.HighDim.AmplitudeLinearization hiding Amplitudes inverseJacobian inverseJacobian_apply inverseJacobian_left inverseJacobian_right jacobian jacobianEquiv jacobian_apply limitingEquation limitingEquation_cubic limitingEquation_hasFDerivAt limitingEquation_one sumCLM sumCLM_apply sumProjection sumProjection_apply
open BecknerOnofri.HighDim.ReducedHessianCoercivity hiding amplitudeBranch_real_jacobian_coercive amplitudeDerivative amplitudeDerivative_base amplitudeDerivative_coercive amplitudeDerivative_continuousAt amplitudeSquare amplitudeSquare_nonneg amplitudeSquare_pos amplitude_norm_square_le diagonalRescaling diagonalRescaling_tendsto diagonal_real_graph_hessian_bound diagonal_real_jacobian_coercive jacobian_coercive normalized_diagonal_amplitude_tendsto physicalScale physicalScale_pos physicalScale_sq physicalScale_tendsto physical_real_graph_hessian_bound physical_real_graph_hessian_negative quadratic_pairing_norm_bound reduced_derivative_rescaled reduced_real_jacobian_coercive rescaleInput_diagonal sum_square_le_dimension
open BecknerOnofri.HighDim.RescaledReducedEquation hiding amplitudeBranch amplitudeBranch_analytic amplitudeBranch_base amplitudeBranch_equal_coordinates amplitudeBranch_pair_tendsto amplitudeBranch_permutation amplitudeBranch_solves amplitudeBranch_unique cubicModel_real_smul exists_amplitude_branch extension extension_analytic extension_axis extension_base extension_factor extension_factor_complex realCoordinates realCoordinates_apply reduced_rescaled_real reduced_zero_equal_amplitudes reduced_zero_iff_extension rescaleInput rescaleInput_analytic rescaleInput_axis rescaleInput_tendsto rescaled_model scalarResidual scalarResidual_analytic scalarResidual_slice_expansion scalarResidual_slice_order
open AmplitudeLinearization RescaledReducedEquation ReducedHessianCoercivity
open BecknerOnofri.HighDim.AngularReducedKernel hiding angular_kernel imaginaryCoordinates imaginary_as_angles imaginary_kernel
open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open DiagonalScalarBranch AngularReducedKernel

def diagonalJacobian {d : ℕ} (hd : 11 ≤ d) (μ : ℝ) : Coordinates d →L[ℝ] Coordinates d :=
  fderiv ℝ (fun z => reduced hd (μ,z)) (realDiagonal d (amplitude hd μ))

theorem real_input_tendsto (d : ℕ) :
    Tendsto (fun x : ℝ × Amplitudes d => (x.1,realCoordinates d x.2))
      (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,realCoordinates d x.2)) :=
    continuous_fst.prodMk ((realCoordinates d).continuous.comp continuous_snd)
  simpa only [map_zero] using hc.continuousAt.tendsto (x := (1,(0 : Amplitudes d)))

theorem reduced_real_input {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), ∀ i,
      (reduced hd (x.1,realCoordinates d x.2) i).im=0 := by
  filter_upwards [(real_input_tendsto d).eventually (reduced_reflection hd)] with x hx i
  have he : conjugateCoordinates (realCoordinates d x.2)=realCoordinates d x.2 := by
    ext j
    simp only [conjugateCoordinates_apply,realCoordinates_apply,Complex.conj_ofReal]
  rw [he] at hx
  have hh := congrArg Complex.im (congrFun hx i)
  simp only [conjugateCoordinates_apply,Complex.conj_im] at hh
  linarith

/-- Reflection symmetry forces the derivative to preserve the real-amplitude subspace. -/
theorem reduced_real_derivative {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0), ∀ (h : Amplitudes d) (i : Fin d),
      (fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) (realCoordinates d h) i).im=0 := by
  filter_upwards [(reduced_real_input hd).eventually_nhds,
    (real_input_tendsto d).eventually (reduced_analytic hd).eventually_analyticAt]
    with x hreal ha h i
  have hinc : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      (ContinuousLinearMap.inr ℝ ℝ (Coordinates d)) (realCoordinates d x.2) := by
    convert! (hasFDerivAt_const x.1 (realCoordinates d x.2)).prodMk
      (hasFDerivAt_id (realCoordinates d x.2)) using 1
  have hpartial : DifferentiableAt ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2) := by
    convert! ha.differentiableAt.comp (realCoordinates d x.2) hinc.differentiableAt using 1
  let ev : Coordinates d →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj i)
  have hr : HasFDerivAt (fun r : Amplitudes d => (reduced hd (x.1,realCoordinates d r) i).im)
      (ev.comp ((fderiv ℝ (fun z => reduced hd (x.1,z)) (realCoordinates d x.2)).comp
        (realCoordinates d))) x.2 := by
    convert! ev.hasFDerivAt.comp x.2 (hpartial.hasFDerivAt.comp x.2 (realCoordinates d).hasFDerivAt) using 1
  have ht : Tendsto (fun r : Amplitudes d => (x.1,r)) (𝓝 x.2) (𝓝 x) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hz : HasFDerivAt (fun r : Amplitudes d => (reduced hd (x.1,realCoordinates d r) i).im)
      (0 : Amplitudes d →L[ℝ] ℝ) x.2 := by
    apply (hasFDerivAt_const (0:ℝ) x.2).congr_of_eventuallyEq
    filter_upwards [ht.eventually hreal] with r hr
    exact hr i
  exact congrArg (fun L : Amplitudes d →L[ℝ] ℝ => L h) (hr.unique hz)

theorem diagonal_real_derivative {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ (h : Amplitudes d) (i : Fin d),
      (diagonalJacobian hd μ (realCoordinates d h) i).im=0 := by
  have ht : Tendsto (fun μ => (μ,(fun _ : Fin d => amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Amplitudes d))) := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds
      (tendsto_pi_nhds.mpr (fun _ => amplitude_tendsto hd))
  exact ht.eventually (reduced_real_derivative hd)

theorem diagonal_imaginary_derivative {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Amplitudes d,
      diagonalJacobian hd μ (imaginaryCoordinates d h)=0 := by
  have ht : Tendsto (fun μ => (μ,amplitude hd μ)) (𝓝[>] (1:ℝ)) (𝓝 ((1:ℝ),(0:ℝ))) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds (amplitude_tendsto hd)
  filter_upwards [ht.eventually (imaginary_kernel hd),
    (amplitude_tendsto hd).eventually (parameter_reduced_zero hd),amplitude_eventually_inverse hd,
    eventually_parameter_interval hd,self_mem_nhdsWithin] with μ hk hs hi hinterval hμ h
  rw [hi] at hs
  exact hk (amplitude_pos hd hμ hinterval.2).ne' hs h

def realPart {d : ℕ} (h : Coordinates d) : Amplitudes d := fun i => (h i).re

def imaginaryPart {d : ℕ} (h : Coordinates d) : Amplitudes d := fun i => (h i).im

theorem real_imaginary_decomposition {d : ℕ} (h : Coordinates d) :
    h=realCoordinates d (realPart h)+imaginaryCoordinates d (imaginaryPart h) := by
  funext i
  change h i=(h i).re+(h i).im*Complex.I
  exact (Complex.re_add_im (h i)).symm

/-- The actual complex quadratic form is exactly its real-amplitude part. -/
theorem diagonal_pairing_real_part {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      (∑ i,conj (h i)*diagonalJacobian hd μ h i).re =
        (∑ i,conj (realCoordinates d (realPart h) i)*
          diagonalJacobian hd μ (realCoordinates d (realPart h)) i).re := by
  filter_upwards [diagonal_real_derivative hd,diagonal_imaginary_derivative hd] with μ hr hi h
  have he : diagonalJacobian hd μ h=diagonalJacobian hd μ (realCoordinates d (realPart h)) := by
    conv_lhs => rw [real_imaginary_decomposition h]
    rw [map_add,hi,add_zero]
  rw [he]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,realCoordinates_apply,
    Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,sub_zero,realPart,hr]
  ring

/-- Full complex coercivity transverse to the exact phase kernel. -/
theorem diagonal_jacobian_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      (μ-1)*amplitudeSquare (realPart h) ≤ (∑ i,conj (h i)*diagonalJacobian hd μ h i).re := by
  filter_upwards [diagonal_pairing_real_part hd,diagonal_real_jacobian_coercive hd] with μ he hc h
  rw [he h]
  exact hc (realPart h)

theorem diagonal_pairing_nonneg_kernel {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      0≤(∑ i,conj (h i)*diagonalJacobian hd μ h i).re ∧
        ((∑ i,conj (h i)*diagonalJacobian hd μ h i).re=0 ↔ realPart h=0) := by
  filter_upwards [diagonal_jacobian_coercive hd,diagonal_pairing_real_part hd,self_mem_nhdsWithin]
    with μ hc he hμ h
  change 1<μ at hμ
  refine ⟨(mul_nonneg (sub_nonneg.mpr hμ.le) (amplitudeSquare_nonneg _)).trans (hc h),?_⟩
  constructor
  · intro hz
    by_contra hr
    have hp := mul_pos (sub_pos.mpr hμ) (amplitudeSquare_pos hr)
    have hh := hc h
    rw [hz] at hh
    linarith
  · intro hr
    rw [he h,hr,map_zero,map_zero]
    simp

/-- The actual trusted Hessian on all complex graph tangents is nonpositive,
and its kernel consists exactly of the imaginary first-shell directions. -/
theorem diagonal_graph_hessian_nonpos_kernel {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      secondVariation (μ*spectralThreshold d) (potential hd (μ,realDiagonal d (amplitude hd μ)))
        (GraphHessian.tangentMap hd (μ,realDiagonal d (amplitude hd μ)) h) ≤ 0 ∧
      (secondVariation (μ*spectralThreshold d) (potential hd (μ,realDiagonal d (amplitude hd μ)))
        (GraphHessian.tangentMap hd (μ,realDiagonal d (amplitude hd μ)) h)=0 ↔ realPart h=0) := by
  have ht : Tendsto (fun μ => (μ,realDiagonal d (amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hz := ((realDiagonal d).continuous.continuousAt.tendsto (x := 0)).comp (amplitude_tendsto hd)
    simp only [map_zero] at hz
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz
  filter_upwards [ht.eventually (GraphHessian.secondVariation_tangentMap hd),
    diagonal_pairing_nonneg_kernel hd,self_mem_nhdsWithin] with μ he hk hμ h
  change 1<μ at hμ
  rw [he h]
  have hm : 0<μ := by linarith
  have hn : -(2/μ)<0 := neg_neg_of_pos (div_pos (by norm_num) hm)
  have hpair := hk h
  refine ⟨mul_nonpos_of_nonpos_of_nonneg hn.le hpair.1,?_⟩
  rw [mul_eq_zero,or_iff_right hn.ne]
  exact hpair.2

theorem diagonal_graph_hessian_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      secondVariation (μ*spectralThreshold d) (potential hd (μ,realDiagonal d (amplitude hd μ)))
        (GraphHessian.tangentMap hd (μ,realDiagonal d (amplitude hd μ)) h) ≤
          -2*onset μ*amplitudeSquare (realPart h) := by
  have ht : Tendsto (fun μ => (μ,realDiagonal d (amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hz := ((realDiagonal d).continuous.continuousAt.tendsto (x := 0)).comp (amplitude_tendsto hd)
    simp only [map_zero] at hz
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz
  filter_upwards [ht.eventually (GraphHessian.secondVariation_tangentMap hd),
    diagonal_jacobian_coercive hd,self_mem_nhdsWithin] with μ he hc hμ h
  change 1<μ at hμ
  rw [he]
  have hm : 0<μ := by linarith
  have hb := mul_le_mul_of_nonpos_left (hc h)
    (show -(2/μ)≤0 from neg_nonpos.mpr (div_nonneg (by norm_num) hm.le))
  refine hb.trans_eq ?_
  have hδ := onset_identity hm.ne'
  rw [← hδ]
  field_simp

theorem physical_graph_hessian_nonpos_kernel {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Coordinates d,
      secondVariation β (physicalPotential hd β)
        (GraphHessian.tangentMap hd (β/spectralThreshold d,
          realDiagonal d (amplitude hd (β/spectralThreshold d))) h) ≤ 0 ∧
      (secondVariation β (physicalPotential hd β)
        (GraphHessian.tangentMap hd (β/spectralThreshold d,
          realDiagonal d (amplitude hd (β/spectralThreshold d))) h)=0 ↔ realPart h=0) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_graph_hessian_nonpos_kernel hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (β/spectralThreshold d,
      realDiagonal d (amplitude hd (β/spectralThreshold d))) := by
    simp only [physicalPotential,branchPotential,hi]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ] using hb h

theorem physical_graph_hessian_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Coordinates d,
      secondVariation β (physicalPotential hd β)
        (GraphHessian.tangentMap hd (β/spectralThreshold d,
          realDiagonal d (amplitude hd (β/spectralThreshold d))) h) ≤
          -2*onsetDelta d β*amplitudeSquare (realPart h) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_graph_hessian_bound hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (β/spectralThreshold d,
      realDiagonal d (amplitude hd (β/spectralThreshold d))) := by
    simp only [physicalPotential,branchPotential,hi]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ,physical_onset_eq hd] using hb h

#print axioms physical_graph_hessian_nonpos_kernel
#print axioms physical_graph_hessian_bound
#print axioms diagonal_pairing_nonneg_kernel
#print axioms diagonal_graph_hessian_nonpos_kernel
end BecknerOnofri.HighDim.LocalEleven.FullReducedHessian
