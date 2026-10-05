import BecknerOnofri.NearOptimalAmplitudeLimit
import BecknerOnofri.DiagonalAmplitude

/-! Actual local orbit selection for near-optimal stationary points, through
positive-amplitude normalization and the full rescaled implicit theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.LocalOrbitClassification
open ContinuousFirstShell LocalReducedEnergyUpper ReducedEnergyGradient
open NearOptimalAmplitudeLimit RescaledReducedEquation ContinuousSymmetry ReducedEquation

theorem rescale_normalized {d : ℕ} (hd : 12 ≤ d) {μ : ℝ} (hμ : 1<μ) (z : Coordinates d) :
    rescaleInput d (normalizedAmplitudes μ z,scale d μ) = (μ,fun i => (‖z i‖:ℂ)) := by
  apply Prod.ext
  · change 1+kappa d*(scale d μ)^2=μ
    rw [scale_sq hd hμ.le]
    field_simp [(kappa_pos d hd).ne']
    <;> ring
  · ext i
    change scale d μ • ((‖z i‖/scale d μ:ℝ):ℂ) = (‖z i‖:ℂ)
    rw [Complex.real_smul,← Complex.ofReal_mul]
    congr 1
    exact mul_div_cancel₀ _ (scale_pos hd hμ).ne'

theorem stationary_equal_norms {d : ℕ} (hd : 12 ≤ d) {α : Type*} {l : Filter α}
    {μ : α → ℝ} {z : α → Coordinates d} (hμ : Tendsto μ l (𝓝 1)) (hz : Tendsto z l (𝓝 0))
    (hμpos : ∀ᶠ n in l, 1<μ n) (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hE : ∀ᶠ n in l, 0≤physicalReducedEnergy hd (μ n,z n))
    (hlow : ∀ᶠ n in l,
      (d:ℝ)/(2*kappa d)*(onsetParameter (μ n))^2-C₀*(onsetParameter (μ n))^3 ≤
        physicalReducedEnergy hd (μ n,z n))
    (hstat : ∀ᶠ n in l, reduced hd (μ n,z n)=0) :
    ∀ᶠ n in l, ∀ i j : Fin d, ‖z n i‖=‖z n j‖ := by
  have hr := normalizedAmplitudes_tendsto hd hμ hz hμpos C₀ hC₀ hE hlow
  have ht := scale_tendsto hd hμ
  have hres := (hr.prodMk_nhds ht).eventually (reduced_zero_equal_amplitudes hd)
  have hnonneg := (hμ.prodMk_nhds hz).eventually (reduced_nonnegative_zero_iff hd)
  filter_upwards [hres,hnonneg,hμpos,hstat] with n hr hn hp hs
  have hR : reduced hd (rescaleInput d (normalizedAmplitudes (μ n) (z n),scale d (μ n)))=0 := by
    rw [rescale_normalized hd hp]
    exact hn.mpr hs
  have he := hr (scale_pos hd hp).ne' hR
  intro i j
  have hij := congrArg (fun t : ℝ => t*scale d (μ n)) (he i j)
  simpa only [normalizedAmplitudes,div_mul_cancel₀ _ (scale_pos hd hp).ne'] using hij

/-- Near-optimal actual stationary graph potentials have an equal-positive-
amplitude translate. All phases are handled by actual torus translations. -/
theorem stationary_equal_amplitude_translate {d : ℕ} (hd : 12 ≤ d) {α : Type*} {l : Filter α}
    {μ : α → ℝ} {z : α → Coordinates d} (hμ : Tendsto μ l (𝓝 1)) (hz : Tendsto z l (𝓝 0))
    (hμpos : ∀ᶠ n in l, 1<μ n) (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hE : ∀ᶠ n in l, 0≤physicalReducedEnergy hd (μ n,z n))
    (hlow : ∀ᶠ n in l,
      (d:ℝ)/(2*kappa d)*(onsetParameter (μ n))^2-C₀*(onsetParameter (μ n))^3 ≤
        physicalReducedEnergy hd (μ n,z n))
    (hstat : ∀ᶠ n in l, reduced hd (μ n,z n)=0) :
    ∀ᶠ n in l, ∃ a : Torus d, ∃ s : ℝ, 0<s ∧
      phaseCoordinates a (z n)=ReducedCubicExpansion.realDiagonal d s ∧
      potential hd (μ n,ReducedCubicExpansion.realDiagonal d s)=
        translation a (potential hd (μ n,z n)) := by
  have hpair := hμ.prodMk_nhds hz
  filter_upwards [stationary_equal_norms hd hμ hz hμpos C₀ hC₀ hE hlow hstat,
    hpair.eventually (near_optimal_full_support hd C₀ hC₀),
    hpair.eventually (potential_translation hd),hμpos,hE,hlow] with n he hsupport htrans hp hE hlow
  let i : Fin d := RealDiagonalReduction.firstIndex hd
  have hpos : 0<‖z n i‖ := norm_pos_iff.mpr (hsupport hp hE hlow i)
  have hphase : phaseCoordinates (phaseNormalizer (z n)) (z n)=
      ReducedCubicExpansion.realDiagonal d ‖z n i‖ := by
    rw [phaseNormalizer_spec]
    funext j
    exact congrArg (fun t : ℝ => (t:ℂ)) (he j i)
  refine ⟨phaseNormalizer (z n),‖z n i‖,hpos,hphase,?_⟩
  simpa only [hphase] using htrans (phaseNormalizer (z n))

open DiagonalScalarBranch RealDiagonalReduction ReducedCubicExpansion

/-- The selected orbit is exactly the previously constructed positive inverse
of the analytic diagonal branch. -/
theorem stationary_branch_orbit {d : ℕ} (hd : 12 ≤ d) {α : Type*} {l : Filter α}
    {μ : α → ℝ} {z : α → Coordinates d} (hμ : Tendsto μ l (𝓝 1)) (hz : Tendsto z l (𝓝 0))
    (hμpos : ∀ᶠ n in l, 1<μ n) (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hE : ∀ᶠ n in l, 0≤physicalReducedEnergy hd (μ n,z n))
    (hlow : ∀ᶠ n in l,
      (d:ℝ)/(2*kappa d)*(onsetParameter (μ n))^2-C₀*(onsetParameter (μ n))^3 ≤
        physicalReducedEnergy hd (μ n,z n))
    (hstat : ∀ᶠ n in l, reduced hd (μ n,z n)=0) :
    ∀ᶠ n in l, ∃ a : Torus d, potential hd (μ n,z n)=
      translation a (branchPotential hd (amplitude hd (μ n))) := by
  let i := firstIndex hd
  let s : α → ℝ := fun n => ‖z n i‖
  have hs : Tendsto s l (𝓝 0) := by
    simpa only [Pi.zero_apply,norm_zero] using (tendsto_pi_nhds.mp hz i).norm
  have hpair := hμ.prodMk_nhds hz
  have hscalar := hμ.prodMk_nhds hs
  filter_upwards [stationary_equal_norms hd hμ hz hμpos C₀ hC₀ hE hlow hstat,
    hpair.eventually (near_optimal_full_support hd C₀ hC₀),
    hpair.eventually (potential_translation hd),
    hpair.eventually (reduced_nonnegative_zero_iff hd),
    hscalar.eventually (residual_eq_mul_quotient hd),
    hscalar.eventually (parameter_unique hd),
    hs.eventually (gt_mem_nhds (amplitudeRadius_pos hd)),
    hμ.eventually (gt_mem_nhds (upperParameter_gt_one hd)),
    hμpos,hE,hlow,hstat] with n he hsupport htrans hreal hfactor hunique hsr hmu hp hE hlow hstat
  have hspos : 0<s n := norm_pos_iff.mpr (hsupport hp hE hlow i)
  have hnorm : (fun j => (‖z n j‖:ℂ))=realDiagonal d (s n) := by
    funext j
    exact congrArg (fun t : ℝ => (t:ℂ)) (he j i)
  have hR : reduced hd (μ n,realDiagonal d (s n))=0 := by
    rw [← hnorm]
    exact hreal.mpr hstat
  have hres : diagonalResidual hd (μ n,s n)=0 := by
    simp only [diagonalResidual,hR,Pi.zero_apply,Complex.zero_re]
  have hq : quotient hd (μ n,s n)=0 := by
    have := hfactor.symm.trans hres
    exact (mul_eq_zero.mp this).resolve_left hspos.ne'
  have hparam : parameter hd (s n)=μ n := hunique.mp hq
  have ha : s n=amplitude hd (μ n) :=
    amplitude_unique hd ⟨hp.le,hmu.le⟩ ⟨hspos.le,hsr.le⟩ hparam
  have hphase : phaseCoordinates (phaseNormalizer (z n)) (z n)=realDiagonal d (s n) := by
    rw [phaseNormalizer_spec,hnorm]
  have hpot : branchPotential hd (amplitude hd (μ n))=
      translation (phaseNormalizer (z n)) (potential hd (μ n,z n)) := by
    rw [← ha]
    simpa only [branchPotential,hparam,hphase] using htrans (phaseNormalizer (z n))
  refine ⟨-phaseNormalizer (z n),?_⟩
  rw [hpot,translation_add]
  simp

#print axioms stationary_branch_orbit
#print axioms stationary_equal_norms
#print axioms stationary_equal_amplitude_translate
end BecknerOnofri.HighDim.LocalOrbitClassification
