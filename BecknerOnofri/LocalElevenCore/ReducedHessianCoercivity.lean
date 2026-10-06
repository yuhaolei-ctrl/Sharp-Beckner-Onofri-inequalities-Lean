module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.ReducedHessianCoercivity
public import BecknerOnofri.LocalElevenCore.RescaledAmplitudeUniqueness
public import BecknerOnofri.LocalElevenCore.GraphHessian
public import BecknerOnofri.LocalElevenCore.DiagonalProfile

@[expose] public section

/-! Positive amplitude Jacobian of the actual reduced equation near the
all-active onset branch, obtained by continuity from its exact limiting matrix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators ContDiff ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.ReducedHessianCoercivity

open BecknerOnofri.HighDim.ReducedHessianCoercivity hiding amplitudeBranch_real_jacobian_coercive amplitudeDerivative amplitudeDerivative_base amplitudeDerivative_coercive amplitudeDerivative_continuousAt amplitudeSquare amplitudeSquare_nonneg amplitudeSquare_pos amplitude_norm_square_le diagonalRescaling diagonalRescaling_tendsto diagonal_real_graph_hessian_bound diagonal_real_jacobian_coercive jacobian_coercive normalized_diagonal_amplitude_tendsto physicalScale physicalScale_pos physicalScale_sq physicalScale_tendsto physical_real_graph_hessian_bound physical_real_graph_hessian_negative quadratic_pairing_norm_bound reduced_derivative_rescaled reduced_real_jacobian_coercive rescaleInput_diagonal sum_square_le_dimension
open BecknerOnofri.HighDim.AmplitudeLinearization hiding Amplitudes inverseJacobian inverseJacobian_apply inverseJacobian_left inverseJacobian_right jacobian jacobianEquiv jacobian_apply limitingEquation limitingEquation_cubic limitingEquation_hasFDerivAt limitingEquation_one sumCLM sumCLM_apply sumProjection sumProjection_apply
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open BecknerOnofri.HighDim.RescaledReducedEquation hiding amplitudeBranch amplitudeBranch_analytic amplitudeBranch_base amplitudeBranch_equal_coordinates amplitudeBranch_pair_tendsto amplitudeBranch_permutation amplitudeBranch_solves amplitudeBranch_unique cubicModel_real_smul exists_amplitude_branch extension extension_analytic extension_axis extension_base extension_factor extension_factor_complex realCoordinates realCoordinates_apply reduced_rescaled_real reduced_zero_equal_amplitudes reduced_zero_iff_extension rescaleInput rescaleInput_analytic rescaleInput_axis rescaleInput_tendsto rescaled_model scalarResidual scalarResidual_analytic scalarResidual_slice_expansion scalarResidual_slice_order
open ContinuousFirstShell ReducedEquation AmplitudeLinearization RescaledReducedEquation

def amplitudeSquare {d : ℕ} (h : Amplitudes d) : ℝ := ∑ i, (h i)^2

theorem amplitudeSquare_nonneg {d : ℕ} (h : Amplitudes d) : 0≤amplitudeSquare h :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sum_square_le_dimension {d : ℕ} (h : Amplitudes d) :
    (∑ i,h i)^2 ≤ (d:ℝ)*amplitudeSquare h := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1:ℝ)) h
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    amplitudeSquare] using hh

theorem amplitude_norm_square_le {d : ℕ} (h : Amplitudes d) : ‖h‖^2≤amplitudeSquare h := by
  have hn : ‖h‖≤Real.sqrt (amplitudeSquare h) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs,sq_abs,amplitudeSquare] using
      Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
  have hs := Real.sq_sqrt (amplitudeSquare_nonneg h)
  nlinarith [norm_nonneg h,Real.sqrt_nonneg (amplitudeSquare h)]

/-- The exact limiting Hessian has gap 2κ in every real-amplitude direction. -/
theorem jacobian_coercive {d : ℕ} (hd : 11 ≤ d) (h : Amplitudes d) :
    2*kappa d*amplitudeSquare h ≤ ∑ i,h i*jacobian d h i := by
  have hb := (BecknerOnofri.HighDim.LocalQuartic.quarticB_positive hd).le
  have hcs := sum_square_le_dimension h
  have he : (∑ i,h i*jacobian d h i) =
      2*(quarticB d-2*quarticA d)*amplitudeSquare h-2*quarticB d*(∑ i,h i)^2 := by
    simp only [jacobian_apply,mul_sub,Finset.sum_sub_distrib,amplitudeSquare]
    rw [show (∑ i,h i*(2*quarticB d*(∑ j,h j)))=2*quarticB d*(∑ i,h i)^2 by
      rw [← Finset.sum_mul]; ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have hk : kappa d=quarticB d-2*quarticA d-(d:ℝ)*quarticB d := by unfold kappa; ring
  rw [hk]
  nlinarith [mul_le_mul_of_nonneg_left hcs (show 0≤2*quarticB d by positivity)]

theorem quadratic_pairing_norm_bound {d : ℕ} (A : Amplitudes d →L[ℝ] Amplitudes d) (h : Amplitudes d) :
    |∑ i,h i*A h i| ≤ ((d:ℝ)*‖A‖)*amplitudeSquare h := by
  calc
    _ ≤ ∑ i,|h i*A h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖A‖*‖h‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,← Real.norm_eq_abs,← Real.norm_eq_abs]
      have hh := norm_le_pi_norm h i
      have ha := (norm_le_pi_norm (A h) i).trans (A.le_opNorm h)
      calc
        _ ≤ ‖h‖*(‖A‖*‖h‖) := mul_le_mul hh ha (norm_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    _ = ((d:ℝ)*‖A‖)*‖h‖^2 := by simp [mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (amplitude_norm_square_le h) (by positivity)

def amplitudeDerivative {d : ℕ} (hd : 11 ≤ d) (x : Amplitudes d × ℝ) :
    Amplitudes d →L[ℝ] Amplitudes d :=
  (fderiv ℝ (extension hd) x).comp (ContinuousLinearMap.inl ℝ (Amplitudes d) ℝ)

theorem amplitudeDerivative_base {d : ℕ} (hd : 11 ≤ d) :
    amplitudeDerivative hd ((fun _ => 1),0)=jacobian d := by
  have hs : HasFDerivAt (fun r : Amplitudes d => extension hd (r,0)) (jacobian d) (fun _ => 1) :=
    (limitingEquation_hasFDerivAt d).congr_of_eventuallyEq (extension_axis hd)
  have hh : HasFDerivAt (fun r : Amplitudes d => extension hd (r,0))
      (amplitudeDerivative hd ((fun _ => 1),0)) (fun _ => 1) := by
    convert! (((extension_analytic hd).differentiableAt.hasFDerivAt).comp (fun _ => 1)
      (ContinuousLinearMap.inl ℝ (Amplitudes d) ℝ).hasFDerivAt) using 1
  exact hh.unique hs

theorem amplitudeDerivative_continuousAt {d : ℕ} (hd : 11 ≤ d) :
    ContinuousAt (amplitudeDerivative hd) ((fun _ => 1),0) := by
  have ha : ContDiffAt ℝ 1 (extension hd) ((fun _ => 1),0) := (extension_analytic hd).contDiffAt
  have hc := ha.continuousAt_fderiv (by norm_num)
  exact hc.clm_comp continuousAt_const

/-- Continuity of the genuine analytic derivative preserves a fixed positive gap. -/
theorem amplitudeDerivative_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)), ∀ h : Amplitudes d,
      kappa d*amplitudeSquare h ≤ ∑ i,h i*amplitudeDerivative hd x h i := by
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hk := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd
  have hc : Tendsto (fun x => ‖amplitudeDerivative hd x-jacobian d‖)
      (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ))) (𝓝 0) := by
    simpa only [amplitudeDerivative_base,sub_self,norm_zero] using
      ((amplitudeDerivative_continuousAt hd).tendsto.sub_const (jacobian d)).norm
  filter_upwards [hc.eventually_le_const (div_pos hk hd0)] with x hx h
  have hb := quadratic_pairing_norm_bound (amplitudeDerivative hd x-jacobian d) h
  have hlow := jacobian_coercive hd h
  have he : (∑ i,h i*(amplitudeDerivative hd x-jacobian d) h i)=
      (∑ i,h i*amplitudeDerivative hd x h i)-(∑ i,h i*jacobian d h i) := by
    simp only [sub_apply,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [he] at hb
  have hpert : (d:ℝ)*‖amplitudeDerivative hd x-jacobian d‖≤kappa d := by
    have hh := (le_div_iff₀ hd0).mp hx
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hpert (amplitudeSquare_nonneg h)
  have hab := (abs_le.mp hb).1
  linarith

/-- Differentiating the actual cubic factorization gives the precise t² scaling. -/
theorem reduced_derivative_rescaled {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)), x.2≠0 →
      ∀ (h : Amplitudes d) (i : Fin d),
        (fderiv ℝ (fun z => reduced hd ((rescaleInput d x).1,z))
          (rescaleInput d x).2 (realCoordinates d h) i).re = x.2^2*amplitudeDerivative hd x h i := by
  filter_upwards [(extension_factor_complex hd).eventually_nhds,
    (extension_analytic hd).eventually_analyticAt,
    (rescaleInput_tendsto d).eventually (reduced_analytic hd).eventually_analyticAt]
    with x he hx hR ht h i
  let inc : Amplitudes d →L[ℝ] Amplitudes d × ℝ := ContinuousLinearMap.inl ℝ (Amplitudes d) ℝ
  have hi : HasFDerivAt (fun r : Amplitudes d => (r,x.2)) inc x.1 := by
    convert! (hasFDerivAt_id x.1).prodMk (hasFDerivAt_const x.2 x.1) using 1
  have hExt : HasFDerivAt (fun r : Amplitudes d => extension hd (r,x.2))
      (amplitudeDerivative hd x) x.1 := by
    convert! hx.differentiableAt.hasFDerivAt.comp x.1 hi using 1
  have hins : HasFDerivAt (fun z : Coordinates d => ((rescaleInput d x).1,z))
      (ContinuousLinearMap.inr ℝ ℝ (Coordinates d)) (rescaleInput d x).2 := by
    convert! (hasFDerivAt_const (rescaleInput d x).1 (rescaleInput d x).2).prodMk
      (hasFDerivAt_id (rescaleInput d x).2) using 1
  have hpartial : DifferentiableAt ℝ (fun z => reduced hd ((rescaleInput d x).1,z))
      (rescaleInput d x).2 := by
    convert! hR.differentiableAt.comp (rescaleInput d x).2 hins.differentiableAt using 1
  have hl : HasFDerivAt (fun r : Amplitudes d => reduced hd ((rescaleInput d x).1,x.2 • realCoordinates d r))
      ((fderiv ℝ (fun z => reduced hd ((rescaleInput d x).1,z)) (rescaleInput d x).2).comp
        (x.2 • realCoordinates d)) x.1 := by
    convert! hpartial.hasFDerivAt.comp x.1 (x.2 • realCoordinates d).hasFDerivAt using 1
  have hr : HasFDerivAt (fun r : Amplitudes d => realCoordinates d (x.2^3 • extension hd (r,x.2)))
      ((realCoordinates d).comp (x.2^3 • amplitudeDerivative hd x)) x.1 := by
    convert! (realCoordinates d).hasFDerivAt.comp x.1 (hExt.const_smul (x.2^3)) using 1
  have heq : (fun r : Amplitudes d => reduced hd ((rescaleInput d x).1,x.2 • realCoordinates d r)) =ᶠ[𝓝 x.1]
      (fun r : Amplitudes d => realCoordinates d (x.2^3 • extension hd (r,x.2))) := by
    filter_upwards [hi.continuousAt.tendsto.eventually he] with r hr
    exact hr
  have hh := congrArg (fun L : Amplitudes d →L[ℝ] Coordinates d => (L h i).re)
    (hl.unique (hr.congr_of_eventuallyEq heq))
  simp only [ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    Pi.smul_apply,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,realCoordinates_apply] at hh
  apply mul_left_cancel₀ ht
  calc
    _ = x.2^3*amplitudeDerivative hd x h i := hh
    _ = _ := by ring

/-- The true real-amplitude reduced Jacobian has the positive t² onset gap. -/
theorem reduced_real_jacobian_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ)), x.2≠0 → ∀ h : Amplitudes d,
      kappa d*x.2^2*amplitudeSquare h ≤
        (∑ i,conj (realCoordinates d h i)*
          fderiv ℝ (fun z => reduced hd ((rescaleInput d x).1,z))
            (rescaleInput d x).2 (realCoordinates d h) i).re := by
  filter_upwards [reduced_derivative_rescaled hd,amplitudeDerivative_coercive hd]
    with x hscale hpos ht h
  simp only [Complex.re_sum,realCoordinates_apply,Complex.conj_ofReal,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [hscale ht h]
  have he : (∑ i,h i*(x.2^2*amplitudeDerivative hd x h i)) =
      x.2^2*(∑ i,h i*amplitudeDerivative hd x h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left (hpos h) (sq_nonneg x.2)]

theorem amplitudeBranch_real_jacobian_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), t≠0 → ∀ h : Amplitudes d,
      kappa d*t^2*amplitudeSquare h ≤
        (∑ i,conj (realCoordinates d h i)*
          fderiv ℝ (fun z => reduced hd (1+kappa d*t^2,z))
            (t • realCoordinates d (amplitudeBranch hd t)) (realCoordinates d h) i).re :=
  (amplitudeBranch_pair_tendsto hd).eventually (reduced_real_jacobian_coercive hd)

open BecknerOnofri.HighDim.DiagonalScalarBranch hiding amplitude amplitudeRadius amplitudeRadius_pos amplitude_eventually_inverse amplitude_nonneg amplitude_pos amplitude_potential_profile amplitude_spec amplitude_sqrt_bound amplitude_sqrt_remainder amplitude_square_bound amplitude_square_expansion amplitude_stationary amplitude_tendsto amplitude_unique assembly_realDiagonal_apply branchPotential branchPotential_analytic branchPotential_base branchPotential_coordinates branchPotential_full_zero branchPotential_mean branchPotential_nonzero branchPotential_regular branch_coordinates_tendsto eventually_parameter_interval exists_parameter_branch exists_stationary_for_every_parameter normalized_parameter_tendsto onset onset_identity onset_pos onset_tendsto parameter parameter_analytic parameter_base parameter_derivative_expansion parameter_derivative_pos parameter_derivative_zero parameter_difference_onset_bound parameter_even parameter_expansion parameter_lower_bound parameter_pair_tendsto parameter_positive_unique parameter_quadratic_bound parameter_reduced_zero parameter_solves parameter_strictMonoOn parameter_tendsto parameter_unique physicalPotential physical_onset_eq physical_profile_bound physical_profile_uniform profileRemainder profileRemainder_apply profileRemainder_norm quotient quotient_analytic quotient_axis quotient_base quotient_critical_expansion quotient_even residual_eq_mul_quotient upperParameter upperParameter_gt_one
open BecknerOnofri.HighDim.ReducedCubicExpansion hiding U_cube_difference U_square_difference coordinates_U coordinates_center coordinates_const coordinates_quadraticTerm_difference coordinates_shellSquare cubicModel cubicModel_analytic cubicModel_apply cubicModel_diagonal cubicModel_neg cubicTerm_assembly_analytic cubicTerm_difference nonlinear_graph_derivative_axis potential_axis quadraticCorrection_analytic quadraticCorrection_product_error realDiagonal realDiagonal_apply reduced_cubic_expansion reduced_cubic_expansion_fifth reduced_derivative_axis reduced_diagonal_cubic_expansion reduced_diagonal_cubic_expansion_fifth reduced_diagonal_derivative_axis reduced_eq_linear_remainder
open DiagonalScalarBranch ReducedCubicExpansion

def physicalScale (d : ℕ) (μ : ℝ) : ℝ := Real.sqrt ((μ-1)/kappa d)

theorem physicalScale_pos {d : ℕ} (hd : 11 ≤ d) {μ : ℝ} (hμ : 1<μ) : 0<physicalScale d μ :=
  Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hμ) (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd))

theorem physicalScale_sq {d : ℕ} (hd : 11 ≤ d) {μ : ℝ} (hμ : 1≤μ) :
    (physicalScale d μ)^2=(μ-1)/kappa d :=
  Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hμ) (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd).le)

theorem physicalScale_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (physicalScale d) (𝓝[>] (1:ℝ)) (𝓝 0) := by
  have hc : ContinuousAt (fun μ : ℝ => Real.sqrt ((μ-1)/kappa d)) 1 :=
    ((continuousAt_id.sub continuousAt_const).div_const (kappa d)).sqrt
  convert! hc.tendsto.mono_left nhdsWithin_le_nhds using 1
  simp

/-- The previously constructed physical branch approaches the all-active
amplitude point in the exact cubic rescaling. -/
theorem normalized_diagonal_amplitude_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (fun μ => amplitude hd μ/physicalScale d μ) (𝓝[>] (1:ℝ)) (𝓝 1) := by
  obtain ⟨C,hC,hB⟩ := (amplitude_square_expansion hd).exists_pos
  have hsmall : ∀ᶠ μ in 𝓝[>] (1:ℝ),
      ‖(amplitude hd μ)^2/(physicalScale d μ)^2-1/μ‖ ≤ (C*kappa d)*onset μ := by
    filter_upwards [hB.bound,self_mem_nhdsWithin] with μ hb hμ
    change 1<μ at hμ
    have hm : 0<μ := by linarith
    have hk := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd
    have hδ := onset_pos hμ
    have hs := physicalScale_pos hd hμ
    have hsq : (physicalScale d μ)^2=μ*onset μ/kappa d := by
      rw [physicalScale_sq hd hμ.le,onset_identity hm.ne']
    have he : (amplitude hd μ)^2/(physicalScale d μ)^2-1/μ =
        ((amplitude hd μ)^2-onset μ/kappa d)/(physicalScale d μ)^2 := by
      rw [hsq]
      field_simp
      <;> ring
    simp only [norm_pow,Real.norm_eq_abs,abs_of_pos hδ] at hb
    rw [he,Real.norm_eq_abs,abs_div,abs_of_pos (sq_pos_of_pos hs)]
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    calc
      _ ≤ C*(onset μ)^2 := hb
      _ ≤ (C*kappa d*onset μ)*(physicalScale d μ)^2 := by
        rw [hsq]
        have hfactor : (C*kappa d*onset μ)*(μ*onset μ/kappa d)=μ*(C*(onset μ)^2) := by
          field_simp
          <;> ring
        rw [hfactor]
        exact le_mul_of_one_le_left (by positivity) hμ.le
  have hz : Tendsto (fun μ => (amplitude hd μ)^2/(physicalScale d μ)^2-1/μ)
      (𝓝[>] (1:ℝ)) (𝓝 0) := by
    have ht := onset_tendsto.const_mul (C*kappa d)
    simp only [mul_zero] at ht
    exact squeeze_zero_norm' hsmall ht
  have hi : Tendsto (fun μ : ℝ => 1/μ) (𝓝[>] (1:ℝ)) (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (1:ℝ)) (𝓝 1)).div
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun μ : ℝ => μ) (𝓝[>] (1:ℝ)) (𝓝 1)) (by norm_num : (1:ℝ)≠0)
    convert! hh using 1 <;> simp
  have hratio : Tendsto (fun μ => (amplitude hd μ)^2/(physicalScale d μ)^2)
      (𝓝[>] (1:ℝ)) (𝓝 1) := by
    convert hz.add hi using 1 <;> simp
  have hroot := hratio.sqrt
  have he (μ : ℝ) : Real.sqrt ((amplitude hd μ)^2/(physicalScale d μ)^2) =
      amplitude hd μ/physicalScale d μ := by
    rw [← div_pow,Real.sqrt_sq_eq_abs,abs_of_nonneg
      (div_nonneg (amplitude_nonneg hd μ) (show 0≤physicalScale d μ from Real.sqrt_nonneg _))]
  simpa only [he,Real.sqrt_one] using hroot

def diagonalRescaling {d : ℕ} (hd : 11 ≤ d) (μ : ℝ) : Amplitudes d × ℝ :=
  ((fun _ => amplitude hd μ/physicalScale d μ),physicalScale d μ)

theorem diagonalRescaling_tendsto {d : ℕ} (hd : 11 ≤ d) :
    Tendsto (diagonalRescaling hd) (𝓝[>] (1:ℝ))
      (𝓝 ((fun _ : Fin d => (1:ℝ)),(0:ℝ))) :=
  (tendsto_pi_nhds.mpr (fun _ => normalized_diagonal_amplitude_tendsto hd)).prodMk_nhds
    (physicalScale_tendsto hd)

theorem rescaleInput_diagonal {d : ℕ} (hd : 11 ≤ d) {μ : ℝ} (hμ : 1<μ) :
    rescaleInput d (diagonalRescaling hd μ)=(μ,realDiagonal d (amplitude hd μ)) := by
  have hs := physicalScale_pos hd hμ
  have hk := BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd
  apply Prod.ext
  · change 1+kappa d*(physicalScale d μ)^2=μ
    rw [physicalScale_sq hd hμ.le]
    field_simp
    <;> ring
  · ext i
    change (physicalScale d μ:ℂ)*(↑(amplitude hd μ/physicalScale d μ):ℂ)=(amplitude hd μ:ℂ)
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne']

/-- Positive definiteness of the actual real-amplitude Jacobian on the
physical diagonal branch, with the explicit lower bound μ−1. -/
theorem diagonal_real_jacobian_coercive {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Amplitudes d,
      (μ-1)*amplitudeSquare h ≤
        (∑ i,conj (realCoordinates d h i)*
          fderiv ℝ (fun z => reduced hd (μ,z)) (realDiagonal d (amplitude hd μ))
            (realCoordinates d h) i).re := by
  filter_upwards [(diagonalRescaling_tendsto hd).eventually (reduced_real_jacobian_coercive hd),
    self_mem_nhdsWithin] with μ hh hμ h
  change 1<μ at hμ
  have hb := hh (physicalScale_pos hd hμ).ne' h
  rw [rescaleInput_diagonal hd hμ] at hb
  have hscale : kappa d*(diagonalRescaling hd μ).2^2=μ-1 := by
    change kappa d*(physicalScale d μ)^2=μ-1
    rw [physicalScale_sq hd hμ.le]
    exact mul_div_cancel₀ _ (BecknerOnofri.HighDim.LocalQuartic.kappa_positive hd).ne'
  simpa only [hscale] using hb

/-- Hence the genuine physical Hessian is strictly negative in every
nonzero real-amplitude graph direction on the diagonal branch. -/
theorem diagonal_real_graph_hessian_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Amplitudes d,
      secondVariation (μ*spectralThreshold d)
        (potential hd (μ,realDiagonal d (amplitude hd μ)))
        (GraphHessian.tangentMap hd (μ,realDiagonal d (amplitude hd μ)) (realCoordinates d h)) ≤
          -2*onset μ*amplitudeSquare h := by
  have ht : Tendsto (fun μ => (μ,realDiagonal d (amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hz := ((realDiagonal d).continuous.continuousAt.tendsto (x := 0)).comp (amplitude_tendsto hd)
    simp only [map_zero] at hz
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz
  filter_upwards [ht.eventually (GraphHessian.secondVariation_tangentMap hd),
    diagonal_real_jacobian_coercive hd,self_mem_nhdsWithin] with μ he hc hμ h
  change 1<μ at hμ
  rw [he]
  have hm : 0<μ := by linarith
  have hb := mul_le_mul_of_nonpos_left (hc h) (show -(2/μ)≤0 from neg_nonpos.mpr (div_nonneg (by norm_num) hm.le))
  refine hb.trans_eq ?_
  have hδ := onset_identity hm.ne'
  rw [← hδ]
  field_simp

theorem amplitudeSquare_pos {d : ℕ} {h : Amplitudes d} (hh : h≠0) : 0<amplitudeSquare h :=
  (sq_pos_of_pos (norm_pos_iff.mpr hh)).trans_le (amplitude_norm_square_le h)

/-- The same bound in the exact physical β and constructed potential notation. -/
theorem physical_real_graph_hessian_bound {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Amplitudes d,
      secondVariation β (physicalPotential hd β)
        (GraphHessian.tangentMap hd (β/spectralThreshold d,
          realDiagonal d (amplitude hd (β/spectralThreshold d))) (realCoordinates d h)) ≤
          -2*onsetDelta d β*amplitudeSquare h := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_real_graph_hessian_bound hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (β/spectralThreshold d,
      realDiagonal d (amplitude hd (β/spectralThreshold d))) := by
    simp only [physicalPotential,branchPotential,hi]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ,physical_onset_eq hd] using hb h

theorem physical_real_graph_hessian_negative {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Amplitudes d, h≠0 →
      secondVariation β (physicalPotential hd β)
        (GraphHessian.tangentMap hd (β/spectralThreshold d,
          realDiagonal d (amplitude hd (β/spectralThreshold d))) (realCoordinates d h)) < 0 := by
  filter_upwards [physical_real_graph_hessian_bound hd,
    (normalized_parameter_tendsto hd).eventually self_mem_nhdsWithin] with β hb hβ h hh
  have hδ : 0<onsetDelta d β := by
    rw [← physical_onset_eq hd]
    exact onset_pos hβ
  exact (hb h).trans_lt (by have := amplitudeSquare_pos hh; nlinarith [mul_pos hδ this])

#print axioms physical_real_graph_hessian_bound
#print axioms physical_real_graph_hessian_negative
#print axioms normalized_diagonal_amplitude_tendsto
#print axioms diagonal_real_jacobian_coercive
#print axioms diagonal_real_graph_hessian_bound
#print axioms reduced_derivative_rescaled
#print axioms reduced_real_jacobian_coercive
#print axioms amplitudeBranch_real_jacobian_coercive
#print axioms jacobian_coercive
#print axioms amplitudeDerivative_coercive
end BecknerOnofri.HighDim.LocalEleven.ReducedHessianCoercivity
