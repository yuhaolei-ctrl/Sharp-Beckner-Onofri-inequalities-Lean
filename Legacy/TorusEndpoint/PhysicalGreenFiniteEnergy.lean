module

public import Legacy.TorusEndpoint.GreenHeatApproximation
public import Legacy.TorusEndpoint.GreenHeatLowerBound
public import Legacy.TorusEndpoint.GreenHeatEnergy
public import Legacy.TorusEndpoint.PhysicalGreenL2
public import Legacy.TorusEndpoint.LowerBoundedFatou

@[expose] public section

/-!
# The physical Green energy for general finite-energy densities

The only density regularity is L1 and unit mass. Finite critical spectral
energy implies integrability of the actual singular-kernel interaction and
the physical upper bound, using a constructed lower-bounded heat approximation.
The final endpoint theorem has just the actual global coefficient cap as
its remaining mathematical premise, not a kernel approximation hypothesis.
-/

open MeasureTheory Filter
open scoped Topology

namespace Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy

open GreenKernelReal GreenHeatRegularization GreenHeatApproximation GreenHeatLowerBound
  GreenHeatEnergy GreenLowerBound PhysicalGreenL2 LowerBoundedFatou

theorem density_product_nonneg_ae {d : ℕ} (rho : ProbabilityDensity d) :
    ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
      0 ≤ rho.value xy.1 ∧ 0 ≤ rho.value xy.2 := by
  have h1 : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d), 0 ≤ rho.value xy.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae rho.nonneg
  have h2 : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d), 0 ≤ rho.value xy.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae rho.nonneg
  exact h1.and h2

theorem density_product_integrable {d : ℕ} (rho : ProbabilityDensity d) :
    Integrable (fun xy : Torus d × Torus d => rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) :=
  rho.integrable.mul_prod rho.integrable

/-- Every probability density with finite critical spectral energy has an
integrable actual Green interaction. Its integrability is a conclusion. -/
theorem physicalGreen_integrable_and_le_spectral {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hs : Summable (densitySpectralTerm rho)) :
    Integrable (fun xy : Torus d × Torus d =>
      realGreen d (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) ∧
      physicalGreenEnergy rho ≤ densitySpectralEnergy rho := by
  obtain ⟨t, ht, _, hae⟩ := exists_heatGreen_tendsto_sub_ae d
  let F : ℕ → Torus d × Torus d → ℝ := fun n xy =>
    (heatGreenKernel d (t n) (xy.1 - xy.2)).re * rho.value xy.1 * rho.value xy.2
  let L : Torus d × Torus d → ℝ := fun xy =>
    -greenLowerConstant d * (rho.value xy.1 * rho.value xy.2)
  have hF (n : ℕ) : Integrable (F n) ((torusMeasure d).prod (torusMeasure d)) :=
    heatGreen_interaction_integrable rho (ht n)
  have hL : Integrable L ((torusMeasure d).prod (torusMeasure d)) :=
    (density_product_integrable rho).const_mul _
  have hlower (n : ℕ) : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d), L xy ≤ F n xy := by
    filter_upwards [density_product_nonneg_ae rho] with xy hxy
    have h := mul_le_mul_of_nonneg_right (heatGreenKernel_re_lower_bound hd (ht n) (xy.1 - xy.2))
      (mul_nonneg hxy.1 hxy.2)
    simpa only [L, F, mul_assoc] using h
  have hlim : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
      Tendsto (fun n => F n xy) atTop
        (𝓝 (realGreen d (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)) := by
    filter_upwards [hae] with xy hxy
    exact (hxy.mul_const (rho.value xy.1)).mul_const (rho.value xy.2)
  have hbound (n : ℕ) : (∫ xy, F n xy ∂(torusMeasure d).prod (torusMeasure d)) ≤
      densitySpectralEnergy rho := by
    rw [integral_prod _ (hF n)]
    exact heatGreen_energy_le_spectral hd rho hs (ht n)
  obtain ⟨hi, hle⟩ := integrable_and_integral_le_of_lower_bound
    ((torusMeasure d).prod (torusMeasure d)) F _ L (densitySpectralEnergy rho)
    hF hL hlower hlim hbound
  refine ⟨hi, ?_⟩
  change (∫ x, ∫ y, realGreen d (x - y) * rho.value x * rho.value y
    ∂torusMeasure d ∂torusMeasure d) ≤ densitySpectralEnergy rho
  rw [← integral_prod _ hi]
  exact hle

/-- The actual physical endpoint for every finite-entropy density, conditional
only on the global finite-atom cap that must still be established by dimension. -/
theorem physicalGreen_entropy_of_endpoint_coefficient_cap {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (hEntropy : rho.FiniteEntropy)
    (hcap : GlobalFiniteAtomCap (endpointAtomWeight d)) :
    Integrable (fun xy : Torus d × Torus d =>
      realGreen d (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) ∧
      (d : ℝ) * physicalGreenEnergy rho ≤ densityEntropy rho.value := by
  obtain ⟨hs, hb⟩ := spectral_entropy_of_endpoint_coefficient_cap hd rho hEntropy hcap
  obtain ⟨hi, he⟩ := physicalGreen_integrable_and_le_spectral hd rho hs
  exact ⟨hi, (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg d)).trans hb⟩

end Legacy.TorusEndpoint.PhysicalGreenFiniteEnergy
