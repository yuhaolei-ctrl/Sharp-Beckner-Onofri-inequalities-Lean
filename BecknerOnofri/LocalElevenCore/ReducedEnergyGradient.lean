import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.ReducedEnergyGradient
import BecknerOnofri.LocalElevenCore.GreenPairing

/-! The exact derivative of the physical reduced energy on the actual
complementary Gibbs graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient

open BecknerOnofri.HighDim.ReducedEnergyGradient hiding fderiv_physicalReducedEnergy_apply graphGradient graphGradient_apply graphValue hasFDerivAt_graphValue hasFDerivAt_mean_mul hasFDerivAt_physicalReducedEnergy mean_mul_assembly pairing_cancellation physicalReducedEnergy physicalReducedEnergy_critical_iff physicalReducedEnergy_eq_graphValue projected_equation_value
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.GreenPairing hiding coefficient_projectedGreen green_one mean_mul_green mean_mul_projectedGreen mean_mul_selfAdjoint_of_multiplier mean_projectedGreen projectedGreen projectedGreen_apply projectedGreen_one projectedGreen_sub_one
open BecknerOnofri.HighDim.QuadraticModes
open QuadraticModes GraphEnergy GreenPairing

theorem projected_equation_value {d : ℕ} (hd : 0 < d) (μ : ℝ)
    (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    (w : Space d) = μ • projectedGreen d (normalized (reconstruction d (z,w))) := by
  have hh : w = μ • complementMap d (greenContinuous d (normalized (reconstruction d (z,w))-1)) :=
    sub_eq_zero.mp he
  have hc := congrArg (fun v : complement d => (v : Space d)) hh
  change (w : Space d) = μ • projectedGreen d (normalized (reconstruction d (z,w))-1) at hc
  rw [projectedGreen_sub_one hd] at hc
  exact hc

/-- The complementary variation cancels by the actual self-adjoint Green
equation; no variational identity is postulated. -/
theorem pairing_cancellation {d : ℕ} (hd : 0 < d) (μ : ℝ)
    (w N a dw : Space d) (hw : w = μ • projectedGreen d N)
    (hdw : dw = μ • projectedGreen d a) : mean d (w*a) = mean d (dw*N) := by
  rw [hw, hdw, smul_mul_assoc, smul_mul_assoc, map_smul, map_smul]
  congr 1
  rw [← mean_mul_projectedGreen hd, mul_comm N]

theorem hasFDerivAt_mean_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {f g : E → Space d} {f' g' : E →L[ℝ] Space d} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => mean d (f y*g y))
      ((meanProduct d (f x)).comp g' + (meanProduct d (g x)).comp f') x := by
  have hh := (meanProduct d).hasFDerivAt_of_bilinear hf hg
  convert! hh using 1
  ext h
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    meanProduct_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply]
  rw [mul_comm (f' h)]
  rfl

def graphValue {d : ℕ} (μ : ℝ) (ψ : Coordinates d → complement d) (z : Coordinates d) : ℝ :=
  logPartitionReal (reconstruction d (z,ψ z)) - mean d ((assembly d z)^2)/(2*μ) -
    (1/2:ℝ)*mean d ((ψ z : Space d)*normalized (reconstruction d (z,ψ z)))

def graphGradient {d : ℕ} (μ : ℝ) (ψ : Coordinates d → complement d) (z : Coordinates d) :
    Coordinates d →L[ℝ] ℝ :=
  (weightedMean (reconstruction d (z,ψ z))).comp (assembly d) -
    (1/μ:ℝ) • ((meanProduct d (assembly d z)).comp (assembly d))

/-- Frechet differentiability of the genuine graph energy.  The sole equation
hypothesis is the actual projected Gibbs equation in a neighborhood. -/
theorem hasFDerivAt_graphValue {d : ℕ} (hd : 0 < d) (μ : ℝ)
    {ψ : Coordinates d → complement d} {ψ' : Coordinates d →L[ℝ] complement d}
    {z : Coordinates d} (hψ : HasFDerivAt ψ ψ' z)
    (he : ∀ᶠ y in 𝓝 z, projectedEquation (greenContinuous d) ((μ,y),ψ y) = 0) :
    HasFDerivAt (graphValue μ ψ) (graphGradient μ ψ z) z := by
  let w' : Coordinates d →L[ℝ] Space d := (complement d).subtypeL.comp ψ'
  let u' : Coordinates d →L[ℝ] Space d := assembly d + w'
  let u := reconstruction d (z,ψ z)
  have hw : HasFDerivAt (fun y => (ψ y : Space d)) w' z := by
    convert! (complement d).subtypeL.hasFDerivAt.comp z hψ using 1
  have hv : HasFDerivAt (fun y : Coordinates d => assembly d y) (assembly d) z :=
    (assembly d).hasFDerivAt
  have hu : HasFDerivAt (fun y => reconstruction d (y,ψ y)) u' z := by
    convert! hv.add hw using 1
  have hn : HasFDerivAt (fun y => normalized (reconstruction d (y,ψ y)))
      ((normalizedDerivative u).comp u') z := by
    convert! (hasFDerivAt_normalized u).comp z hu using 1
  have hec : (fun y => (ψ y : Space d)) =ᶠ[𝓝 z]
      (fun y => μ • projectedGreen d (normalized (reconstruction d (y,ψ y)))) := by
    filter_upwards [he] with y hy
    exact projected_equation_value hd μ y (ψ y) hy
  have hg : HasFDerivAt
      (fun y => μ • projectedGreen d (normalized (reconstruction d (y,ψ y))))
      (μ • ((projectedGreen d).comp ((normalizedDerivative u).comp u'))) z := by
    convert! ((projectedGreen d).hasFDerivAt.comp z hn).const_smul μ using 1
  have hdw : w' = μ • ((projectedGreen d).comp ((normalizedDerivative u).comp u')) :=
    hw.unique (hg.congr_of_eventuallyEq hec)
  have hc (h : Coordinates d) :
      mean d ((ψ z : Space d) * normalizedDerivative u (u' h)) =
        mean d (w' h * normalized u) := by
    apply pairing_cancellation hd μ
    · exact hec.self_of_nhds
    · exact congrArg (fun L : Coordinates d →L[ℝ] Space d => L h) hdw
  have hl : HasFDerivAt (fun y => logPartitionReal (reconstruction d (y,ψ y)))
      ((weightedMean u).comp u') z := by
    convert! (hasFDerivAt_logPartitionReal u).comp z hu using 1
  have hvv := (hasFDerivAt_mean_mul hv hv).mul_const (2*μ)⁻¹
  have hwn := (hasFDerivAt_mean_mul hw hn).const_mul (1/2:ℝ)
  convert! (hl.sub hvv).sub hwn using 1
  · ext y
    simp only [graphValue, pow_two, div_eq_mul_inv]
    rfl
  · ext h
    change mean d (normalized u * assembly d h) -
      (1/μ)*mean d (assembly d z * assembly d h) =
        mean d (normalized u * u' h) -
          (2*μ)⁻¹*(mean d (assembly d z * assembly d h) + mean d (assembly d z * assembly d h)) -
          (1/2)*(mean d ((ψ z : Space d)*normalizedDerivative u (u' h)) +
            mean d (normalized u * w' h))
    rw [hc h]
    simp only [u', add_apply, mul_add, map_add]
    rw [mul_comm (w' h) (normalized u)]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring

theorem mean_mul_assembly {d : ℕ} (f : Space d) (h : Coordinates d) :
    mean d (f * assembly d h) = 2 * (∑ i, conj (h i) * coordinates d f i).re := by
  change pairing f (assembly d h) = _
  rw [assembly_apply, map_sum]
  simp only [pairing_synthesis, coordinates_apply, Complex.re_sum, Finset.mul_sum]

theorem graphGradient_apply {d : ℕ} {μ : ℝ} (hμ : μ ≠ 0)
    (ψ : Coordinates d → complement d) (z h : Coordinates d) :
    graphGradient μ ψ z h = -(2/μ) *
      (∑ i, conj (h i) * (z - μ • coordinates d (normalized (reconstruction d (z,ψ z)))) i).re := by
  change mean d (normalized (reconstruction d (z,ψ z)) * assembly d h) -
    (1/μ)*mean d (assembly d z * assembly d h) = _
  rw [mean_mul_assembly, mean_mul_assembly, coordinates_assembly]
  have hs : (∑ i, conj (h i) * (z - μ • coordinates d (normalized (reconstruction d (z,ψ z)))) i) =
      (∑ i, conj (h i)*z i) - (μ:ℂ)*(∑ i, conj (h i)*coordinates d (normalized (reconstruction d (z,ψ z))) i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    ring
  rw [hs]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp
  ring

/-- The actual trusted dual energy for arbitrary nearby physical parameters. -/
def physicalReducedEnergy {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d) : ℝ :=
  (dualFunctional (x.1 * spectralThreshold d) (potential hd x)).toReal

theorem physicalReducedEnergy_eq_graphValue {d : ℕ} (hd : 11 ≤ d) {μ : ℝ}
    (hμ : 0 < μ) (z : Coordinates d)
    (he : projectedEquation (greenContinuous d) ((μ,z),correction hd (μ,z)) = 0) :
    physicalReducedEnergy hd (μ,z) = graphValue μ (fun y => correction hd (μ,y)) z := by
  unfold physicalReducedEnergy potential
  rw [graph_dualFunctional (by omega) hμ z (correction hd (μ,z)) he, EReal.toReal_coe]
  unfold graphValue
  rw [assembly_square_mean]
  field_simp

/-- A genuine Fréchet derivative of the trusted physical dual energy along
the first-shell variables on the actual local implicit graph. -/
theorem hasFDerivAt_physicalReducedEnergy {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      HasFDerivAt (fun z => physicalReducedEnergy hd (x.1,z))
        (graphGradient x.1 (fun z => correction hd (x.1,z)) x.2) x.2 := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 < x.1 := by
    exact continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [(correction_solves hd).eventually_nhds,
    (correction_analytic hd).eventually_analyticAt, hp] with x hx ha hpos
  have ht : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d))) x.2 := by
    exact (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hψ : DifferentiableAt ℝ (fun z => correction hd (x.1,z)) x.2 := by
    convert! ha.differentiableAt.comp x.2 ht.differentiableAt using 1
  have hes : ∀ᶠ z in 𝓝 x.2,
      projectedEquation (greenContinuous d) ((x.1,z),correction hd (x.1,z)) = 0 :=
    ht.continuousAt.tendsto.eventually hx
  have hh := hasFDerivAt_graphValue (by omega : 0 < d) x.1 hψ.hasFDerivAt hes
  apply hh.congr_of_eventuallyEq
  filter_upwards [hes] with z hz
  exact physicalReducedEnergy_eq_graphValue hd hpos z hz

/-- Exact normalization of the reduced variational equation: the physical
energy gradient is −2/μ times the real complex-coordinate pairing with the
actual reduced Gibbs equation. -/
theorem fderiv_physicalReducedEnergy_apply {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)), ∀ h : Coordinates d,
      fderiv ℝ (fun z => physicalReducedEnergy hd (x.1,z)) x.2 h =
        -(2/x.1) * (∑ i, conj (h i) * reduced hd x i).re := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hasFDerivAt_physicalReducedEnergy hd, hp] with x hx hpos h
  rw [hx.fderiv, graphGradient_apply hpos.ne']
  rfl

theorem physicalReducedEnergy_critical_iff {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      fderiv ℝ (fun z => physicalReducedEnergy hd (x.1,z)) x.2 = 0 ↔ reduced hd x = 0 := by
  have hp : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [fderiv_physicalReducedEnergy_apply hd, hp] with x hx hpos
  constructor
  · intro hz
    have hh := hx (reduced hd x)
    rw [hz, zero_apply] at hh
    simp only [Complex.re_sum, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hh
    have hfactor : -(2/x.1) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (by norm_num) hpos.ne')
    have hs : ∑ i, ‖reduced hd x i‖^2 = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left hfactor
    funext i
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    have hi : ‖reduced hd x i‖^2 ≤ ∑ j, ‖reduced hd x j‖^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖reduced hd x j‖) (Finset.mem_univ i)
    rw [hs] at hi
    exact le_antisymm hi (sq_nonneg _)
  · intro hz
    apply ContinuousLinearMap.ext
    intro h
    rw [hx h, hz]
    simp

#print axioms hasFDerivAt_graphValue
#print axioms fderiv_physicalReducedEnergy_apply
#print axioms physicalReducedEnergy_critical_iff
end BecknerOnofri.HighDim.LocalEleven.ReducedEnergyGradient
