module

public import Legacy.TorusEndpoint.GreenKernelApproximation
public import Legacy.TorusEndpoint.CoefficientEndpointReduction
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Physical Green interaction for actual L² densities

The singular kernel is the previously constructed real Haar L² Green function.
Its physical double integral is identified with its spectral series, not
defined by that series. The L² density assumption is explicit; no general
L log L claim or common lower bound is asserted.
-/

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal InnerProductSpace

namespace Legacy.TorusEndpoint.PhysicalGreenL2

open GreenMultiplierSummability GreenKernelReal GreenKernelApproximation
open PhysicalFiniteFourier

set_option maxHeartbeats 800000

theorem subtraction_measurePreserving (d : ℕ) :
    MeasurePreserving (fun xy : Torus d × Torus d => xy.1 - xy.2)
      ((torusMeasure d).prod (torusMeasure d)) (torusMeasure d) := by
  letI : (torusMeasure d).IsAddRightInvariant := by
    rw [torusMeasure_explicit]
    infer_instance
  exact measurePreserving_fst.comp
    (measurePreserving_sub_prod (torusMeasure d) (torusMeasure d))

theorem densityProduct_memLp {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    MemLp (fun xy : Torus d × Torus d => rho.value xy.1 * rho.value xy.2) 2
      ((torusMeasure d).prod (torusMeasure d)) := by
  have hm := (hρ.comp_measurePreserving measurePreserving_fst).aestronglyMeasurable.mul
    (hρ.comp_measurePreserving measurePreserving_snd).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  change Integrable (fun xy : Torus d × Torus d =>
    (rho.value xy.1 * rho.value xy.2) ^ 2) _
  simpa only [mul_pow] using hρ.integrable_sq.mul_prod hρ.integrable_sq

noncomputable def densityProductLp {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    Lp ℝ 2 ((torusMeasure d).prod (torusMeasure d)) :=
  (densityProduct_memLp rho hρ).toLp _

noncomputable def interactionFunctional {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    Lp ℝ 2 (torusMeasure d) →L[ℝ] ℝ :=
  (innerSL ℝ (densityProductLp rho hρ)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ _ (subtraction_measurePreserving d)).toContinuousLinearMap

theorem kernelInteraction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) (K : Torus d → ℝ)
    (hK : MemLp K 2 (torusMeasure d)) :
    Integrable (fun xy : Torus d × Torus d =>
      K (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have h := (hK.comp_measurePreserving (subtraction_measurePreserving d)).integrable_mul
    (densityProduct_memLp rho hρ)
  change Integrable (fun xy : Torus d × Torus d =>
    K (xy.1 - xy.2) * (rho.value xy.1 * rho.value xy.2)) _ at h
  simpa only [mul_assoc] using h

theorem interactionFunctional_eq_integral {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) (f : Lp ℝ 2 (torusMeasure d))
    (K : Torus d → ℝ) (hf : f =ᵐ[torusMeasure d] K) :
    interactionFunctional rho hρ f =
      ∫ xy : Torus d × Torus d,
        K (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2
        ∂(torusMeasure d).prod (torusMeasure d) := by
  change inner ℝ (densityProductLp rho hρ)
      (Lp.compMeasurePreserving _ (subtraction_measurePreserving d) f) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(densityProduct_memLp rho hρ).coeFn_toLp,
    Lp.coeFn_compMeasurePreserving f (subtraction_measurePreserving d),
    (subtraction_measurePreserving d).quasiMeasurePreserving.ae_eq hf] with xy hq hp hk
  change densityProductLp rho hρ xy = _ at hq
  change f (xy.1 - xy.2) = K (xy.1 - xy.2) at hk
  simp only [Real.inner_apply, hq, hp, Function.comp_apply, hk]
  ring

theorem realGreen_interaction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    Integrable (fun xy : Torus d × Torus d =>
      realGreen d (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) :=
  kernelInteraction_integrable rho hρ _ (realGreen_memLp d)

/-- This definition is the genuine double interaction integral. -/
noncomputable def physicalGreenEnergy {d : ℕ} (rho : ProbabilityDensity d) : ℝ :=
  ∫ x, ∫ y, realGreen d (x - y) * rho.value x * rho.value y
    ∂torusMeasure d ∂torusMeasure d

theorem realPartialLp_tendsto_finset (d : ℕ) :
    Tendsto (fun s : Finset (Frequency d) => realPartialLp s) atTop
      (𝓝 (realGreenLp d)) := by
  have hc : Continuous
      (Complex.reCLM.compLp : Lp ℂ 2 (torusMeasure d) → Lp ℝ 2 (torusMeasure d)) :=
    Complex.reCLM.lipschitz.continuous_compLp (map_zero Complex.reCLM)
  have hcomplex : Tendsto (fun s : Finset (Frequency d) => complexPartialLp s)
      atTop (𝓝 (greenL2 d)) := by
    have hsum := hasSum_greenL2 d
    change Tendsto (fun s : Finset (Frequency d) =>
      ∑ k ∈ s, (greenMultiplier d k : ℂ) • UnitAddTorus.mFourierLp 2 k)
      atTop (𝓝 (greenL2 d)) at hsum
    convert! hsum using 1
    funext s
    exact complexPartialLp_eq_sum s
  exact (hc.tendsto (greenL2 d)).comp hcomplex

/-- Actual physical interaction is the sum of the actual weighted Fourier coefficients. -/
theorem hasSum_physicalGreenEnergy {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d =>
      greenMultiplier d k * ‖densityFourier rho.value k‖ ^ 2) (physicalGreenEnergy rho) := by
  have heq : interactionFunctional rho hρ (realGreenLp d) = physicalGreenEnergy rho := by
    rw [interactionFunctional_eq_integral rho hρ _ _ (realGreenLp_coe_ae d)]
    exact integral_prod _ (realGreen_interaction_integrable rho hρ)
  rw [← heq]
  have hlim := (interactionFunctional rho hρ).continuous.tendsto (realGreenLp d) |>.comp
    (realPartialLp_tendsto_finset d)
  change Tendsto (fun s : Finset (Frequency d) =>
    ∑ k ∈ s, greenMultiplier d k * ‖densityFourier rho.value k‖ ^ 2) atTop _
  convert! hlim using 1
  funext s
  simp only [Function.comp_apply]
  rw [interactionFunctional_eq_integral rho hρ _ _ (realPartialLp_coe_ae s)]
  exact (finiteKernel_product_integral rho s (greenMultiplier d)).symm

theorem hasSum_nonzero_physicalGreenEnergy {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) :
    HasSum (fun k : NonzeroFrequency d =>
      greenMultiplier d k.val * ‖densityFourier rho.value k.val‖ ^ 2)
      (physicalGreenEnergy rho) := by
  have hsupp : Function.support (fun k : Frequency d =>
      greenMultiplier d k * ‖densityFourier rho.value k‖ ^ 2) ⊆ {k | k ≠ 0} := by
    intro k hk hzero
    subst k
    simp at hk
  exact (hasSum_subtype_iff_of_support_subset hsupp).2 (hasSum_physicalGreenEnergy rho hρ)

/-- Summability and physical/spectral equality require no coefficient cap or kernel lower bound. -/
theorem physicalGreenEnergy_eq_spectral {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hρ : MemLp rho.value 2 (torusMeasure d)) :
    Summable (densitySpectralTerm rho) ∧ physicalGreenEnergy rho = densitySpectralEnergy rho := by
  have hsum := hasSum_nonzero_physicalGreenEnergy rho hρ
  have heq (k : NonzeroFrequency d) :
      greenMultiplier d k.val * ‖densityFourier rho.value k.val‖ ^ 2 =
        (1 / endpointSigma d) * densitySpectralTerm rho k := by
    simp only [greenMultiplier, if_neg k.property, densitySpectralTerm]
    ring
  have hs := hsum.summable.congr heq
  refine ⟨(summable_mul_left_iff (one_div_ne_zero (endpointSigma_pos hd).ne')).mp hs, ?_⟩
  calc
    physicalGreenEnergy rho = ∑' k : NonzeroFrequency d,
        greenMultiplier d k.val * ‖densityFourier rho.value k.val‖ ^ 2 := hsum.tsum_eq.symm
    _ = ∑' k : NonzeroFrequency d, (1 / endpointSigma d) * densitySpectralTerm rho k :=
      tsum_congr heq
    _ = densitySpectralEnergy rho := by rw [tsum_mul_left]; rfl

/-- Every actual L² probability density has finite entropy. -/
theorem finiteEntropy_of_memLp {d : ℕ} (rho : ProbabilityDensity d)
    (hρ : MemLp rho.value 2 (torusMeasure d)) : rho.FiniteEntropy := by
  have hm : AEStronglyMeasurable (fun x => rho.value x * Real.log (rho.value x))
      (torusMeasure d) := by
    have hr := hρ.aemeasurable
    exact (hr.mul (Real.measurable_log.comp_aemeasurable hr)).aestronglyMeasurable
  apply (hρ.integrable_sq.add (integrable_const (1 : ℝ))).mono' hm
  filter_upwards [rho.nonneg] with x hx
  change ‖rho.value x * Real.log (rho.value x)‖ ≤ rho.value x ^ 2 + 1
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hlo := entropy_young (rho.value x) 0 hx
  have hhi := mul_le_mul_of_nonneg_left (Real.log_le_self hx) hx
  simp only [mul_zero, Real.exp_zero] at hlo
  constructor <;> nlinarith [sq_nonneg (rho.value x)]

/-- The L²-density physical endpoint still has the actual coefficient cap as an explicit premise. -/
theorem physicalGreen_entropy_of_coefficient_cap {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hρ : MemLp rho.value 2 (torusMeasure d))
    (hcap : GlobalFiniteAtomCap (endpointAtomWeight d)) :
    (d : ℝ) * physicalGreenEnergy rho ≤ densityEntropy rho.value := by
  rw [(physicalGreenEnergy_eq_spectral hd rho hρ).2]
  exact (spectral_entropy_of_endpoint_coefficient_cap hd rho (finiteEntropy_of_memLp rho hρ) hcap).2

end Legacy.TorusEndpoint.PhysicalGreenL2

#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.subtraction_measurePreserving
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.densityProduct_memLp
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.interactionFunctional_eq_integral
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.realGreen_interaction_integrable
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.hasSum_physicalGreenEnergy
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy_eq_spectral
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.finiteEntropy_of_memLp
#print axioms Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreen_entropy_of_coefficient_cap
