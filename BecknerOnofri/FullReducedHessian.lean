module

public import BecknerOnofri.ReducedHessianCoercivity
public import BecknerOnofri.AngularReducedKernel

@[expose] public section

/-! The full complex reduced Hessian: real amplitude directions are strictly
negative for the energy, and exactly the phase directions form its kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.FullReducedHessian
open ContinuousFirstShell ContinuousSymmetry ReducedEquation ReducedCubicExpansion
open AmplitudeLinearization RescaledReducedEquation ReducedHessianCoercivity
open DiagonalScalarBranch AngularReducedKernel

def diagonalJacobian {d : ℕ} (hd : 12≤d) (μ : ℝ) : Coordinates d →L[ℝ] Coordinates d :=
  fderiv ℝ (fun z => reduced hd (μ,z)) (realDiagonal d (amplitude hd μ))

theorem real_input_tendsto (d : ℕ) :
    Tendsto (fun x : ℝ × Amplitudes d => (x.1,realCoordinates d x.2))
      (𝓝 (1,0)) (𝓝 (1,(0 : Coordinates d))) := by
  have hc : Continuous (fun x : ℝ × Amplitudes d => (x.1,realCoordinates d x.2)) :=
    continuous_fst.prodMk ((realCoordinates d).continuous.comp continuous_snd)
  simpa only [map_zero] using hc.continuousAt.tendsto (x := (1,(0 : Amplitudes d)))

theorem reduced_real_input {d : ℕ} (hd : 12≤d) :
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
theorem reduced_real_derivative {d : ℕ} (hd : 12≤d) :
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

theorem diagonal_real_derivative {d : ℕ} (hd : 12≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ (h : Amplitudes d) (i : Fin d),
      (diagonalJacobian hd μ (realCoordinates d h) i).im=0 := by
  have ht : Tendsto (fun μ => (μ,(fun _ : Fin d => amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Amplitudes d))) := by
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds
      (tendsto_pi_nhds.mpr (fun _ => amplitude_tendsto hd))
  exact ht.eventually (reduced_real_derivative hd)

theorem diagonal_imaginary_derivative {d : ℕ} (hd : 12≤d) :
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
theorem diagonal_pairing_real_part {d : ℕ} (hd : 12≤d) :
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
theorem diagonal_jacobian_coercive {d : ℕ} (hd : 12≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Coordinates d,
      (μ-1)*amplitudeSquare (realPart h) ≤ (∑ i,conj (h i)*diagonalJacobian hd μ h i).re := by
  filter_upwards [diagonal_pairing_real_part hd,diagonal_real_jacobian_coercive hd] with μ he hc h
  rw [he h]
  exact hc (realPart h)

theorem diagonal_pairing_nonneg_kernel {d : ℕ} (hd : 12≤d) :
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
theorem diagonal_graph_hessian_nonpos_kernel {d : ℕ} (hd : 12≤d) :
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

theorem diagonal_graph_hessian_bound {d : ℕ} (hd : 12≤d) :
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

theorem physical_graph_hessian_nonpos_kernel {d : ℕ} (hd : 12≤d) :
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

theorem physical_graph_hessian_bound {d : ℕ} (hd : 12≤d) :
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
end BecknerOnofri.HighDim.FullReducedHessian
