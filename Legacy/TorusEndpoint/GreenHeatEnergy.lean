import Legacy.TorusEndpoint.GreenHeatRegularization
import Legacy.TorusEndpoint.GreenMellinSeries
import Legacy.TorusEndpoint.CoefficientEndpointReduction

/-!
# Heat-regularized physical energy dominated by the full spectrum

The density is only an L1 probability density. The required critical spectral
summability is explicit and is not replaced by a totalized divergent sum.
-/

open MeasureTheory

namespace Legacy.TorusEndpoint.GreenHeatEnergy

open GreenMultiplierSummability GreenMellinSeries GreenHeatRegularization
  TorusHeatBounds AbsolutePhysicalFourier

theorem hasSum_green_density_spectrum {d : ℕ} (rho : ProbabilityDensity d)
    (hs : Summable (densitySpectralTerm rho)) :
    HasSum (fun k : Frequency d => greenMultiplier d k * ‖densityFourier rho.value k‖ ^ 2)
      (densitySpectralEnergy rho) := by
  have hsub : HasSum (fun k : NonzeroFrequency d =>
      greenMultiplier d k.val * ‖densityFourier rho.value k.val‖ ^ 2)
      (densitySpectralEnergy rho) := by
    apply (hs.hasSum.mul_left (1 / endpointSigma d)).congr_fun
    intro k
    simp only [greenMultiplier, if_neg k.property, densitySpectralTerm]
    ring
  have hsupp : Function.support (fun k : Frequency d =>
      greenMultiplier d k * ‖densityFourier rho.value k‖ ^ 2) ⊆ {k | k ≠ 0} := by
    intro k hk hz
    subst k
    simp at hk
  exact (hasSum_subtype_iff_of_support_subset hsupp).1 hsub

theorem heatGreenWeight_le_green {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    (k : Frequency d) : heatGreenWeight d t k ≤ greenMultiplier d k := by
  simpa only [heatGreenWeight, mul_one] using
    mul_le_mul_of_nonneg_left (heatWeight_le_one ht k) (greenMultiplier_nonneg hd k)

theorem heatGreen_interaction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun xy : Torus d × Torus d =>
      (heatGreenKernel d t (xy.1 - xy.2)).re * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) :=
  realAbsoluteKernel_interaction_integrable rho _ (heatGreenWeight_norm_summable ht)

theorem heatGreen_energy_le_spectral {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hs : Summable (densitySpectralTerm rho)) {t : ℝ} (ht : 0 < t) :
    (∫ x, ∫ y, (heatGreenKernel d t (x - y)).re * rho.value x * rho.value y
      ∂torusMeasure d ∂torusMeasure d) ≤ densitySpectralEnergy rho := by
  change (∫ x, ∫ y, realAbsoluteKernel (heatGreenWeight d t) (x - y) *
    rho.value x * rho.value y ∂torusMeasure d ∂torusMeasure d) ≤ _
  rw [realAbsoluteKernel_energy_eq_series rho _ (heatGreenWeight_norm_summable ht)]
  have hfull := hasSum_green_density_spectrum rho hs
  rw [← hfull.tsum_eq]
  apply (hasSum_realAbsoluteKernel_interaction rho _
    (heatGreenWeight_norm_summable ht)).summable.tsum_le_tsum _ hfull.summable
  intro k
  exact mul_le_mul_of_nonneg_right (heatGreenWeight_le_green hd ht.le k) (sq_nonneg _)

end Legacy.TorusEndpoint.GreenHeatEnergy
