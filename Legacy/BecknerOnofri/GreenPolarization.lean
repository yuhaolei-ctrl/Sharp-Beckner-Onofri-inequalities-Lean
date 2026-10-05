import Legacy.BecknerOnofri.TorusHeatPolarization
import Legacy.TorusEndpoint.GreenHeatEnergy

/-! Actual heat pairings, their full Mellin integral, and unconditional Green-energy polarization. -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.CoordinatePolarization
open HeatDensityApproximation TorusHeatBounds AbsolutePhysicalFourier
  GreenMellinSeries GreenHeatEnergy GreenMultiplierSummability

def centeredHeatPairing {d : ℕ} (rho : ProbabilityDensity d) (t : ℝ) : ℝ :=
  pairing (fun x y => heatKernel t (x-y)-1) rho.value

theorem heatKernel_sub_one_eq_absolute {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    heatKernel t x-1 = realAbsoluteKernel (nonzeroHeatWeight t) x := by
  change (TorusHeatPositivity.torusTheta t x).re-1 =
    (∑' k : Frequency d, (nonzeroHeatWeight t k : ℂ)*UnitAddTorus.mFourier k x).re
  rw [← torusTheta_sub_one ht]
  simp

theorem nonzeroHeatWeight_norm_summable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun k : Frequency d => ‖nonzeroHeatWeight t k‖) := by
  simpa only [Real.norm_of_nonneg (nonzeroHeatWeight_nonneg t _)] using
    (nonzeroHeatWeight_summable ht : Summable (nonzeroHeatWeight t : Frequency d → ℝ))

theorem centeredHeatPairing_hasSum {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : Frequency d => nonzeroHeatWeight t k*‖densityFourier rho.value k‖^2)
      (centeredHeatPairing rho t) := by
  simpa only [centeredHeatPairing,pairing,pairingIntegrand,heatKernel_sub_one_eq_absolute ht] using
    hasSum_realAbsoluteKernel_interaction rho (nonzeroHeatWeight t) (nonzeroHeatWeight_norm_summable ht)

theorem centeredHeatPairing_integrand_integrable {d : ℕ} (rho : ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) :
    Integrable (pairingIntegrand (fun x y => heatKernel t (x-y)-1) rho.value)
      ((torusMeasure d).prod (torusMeasure d)) := by
  simpa only [pairingIntegrand,heatKernel_sub_one_eq_absolute ht] using!
    realAbsoluteKernel_interaction_integrable rho (nonzeroHeatWeight t) (nonzeroHeatWeight_norm_summable ht)

theorem centeredHeatPairing_eq_sub_one {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    centeredHeatPairing rho t = pairing (fun x y => heatKernel t (x-y)) rho.value-1 := by
  have hc := centeredHeatPairing_integrand_integrable rho ht
  change Integrable (fun p : Torus d × Torus d => (heatKernel t (p.1-p.2)-1)*rho.value p.1*rho.value p.2) ((torusMeasure d).prod (torusMeasure d)) at hc
  have hm := rho.integrable.mul_prod rho.integrable
  have he : (fun p : Torus d × Torus d => heatKernel t (p.1-p.2)*rho.value p.1*rho.value p.2) =
      (fun p : Torus d × Torus d => (heatKernel t (p.1-p.2)-1)*rho.value p.1*rho.value p.2)+
      (fun p : Torus d × Torus d => rho.value p.1*rho.value p.2) := by funext p; simp only [Pi.add_apply]; ring
  have hi : pairing (fun x y => heatKernel t (x-y)) rho.value = centeredHeatPairing rho t+1 := by
    change (∫ p, heatKernel t (p.1-p.2)*rho.value p.1*rho.value p.2 ∂(torusMeasure d).prod (torusMeasure d)) = _
    rw [he, integral_add' hc hm, integral_prod_mul, rho.mass, one_mul]
    rfl
  linarith

theorem centeredHeatPairing_polarize_le {d : ℕ} {t : ℝ} (ht : 0 < t) (i : Fin d) (a : ℝ)
    (rho : ProbabilityDensity d) : centeredHeatPairing rho t ≤ centeredHeatPairing (density i a rho) t := by
  rw [centeredHeatPairing_eq_sub_one rho ht,centeredHeatPairing_eq_sub_one (density i a rho) ht]
  exact sub_le_sub_right (heat_pairing_density_le ht i a rho) 1

def mellinPairing {d : ℕ} (rho : ProbabilityDensity d) (t : ℝ) : ℝ :=
  t^((d:ℝ)/2-1)*centeredHeatPairing rho t

theorem mellinPairing_eq_series {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    mellinPairing rho t = ∑' k : Frequency d, mellinTerm (fun j => ‖densityFourier rho.value j‖^2) k t := by
  rw [mellinPairing, ← (centeredHeatPairing_hasSum rho ht).tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [mellinTerm]
  ring

theorem mellinPairing_integrable {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hs : Summable (densitySpectralTerm rho)) : IntegrableOn (mellinPairing rho) (Ioi 0) := by
  have habs : Summable (fun k : Frequency d => ‖greenMultiplier d k*‖densityFourier rho.value k‖^2‖) :=
    (hasSum_green_density_spectrum rho hs).summable.norm
  have hi := IntegrableSeries.integrable_tsum_of_summable_integral_norm
    (mellinTerm_integrable hd (fun k => ‖densityFourier rho.value k‖^2))
    (summable_integral_norm_mellinTerm hd _ habs)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (mellinPairing_eq_series rho ht).symm

theorem integral_mellinPairing {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hs : Summable (densitySpectralTerm rho)) :
    (∫ t in Ioi 0, mellinPairing rho t) = 2*densitySpectralEnergy rho := by
  have habs : Summable (fun k : Frequency d => ‖greenMultiplier d k*‖densityFourier rho.value k‖^2‖) :=
    (hasSum_green_density_spectrum rho hs).summable.norm
  calc
    _ = ∫ t in Ioi 0, ∑' k : Frequency d, mellinTerm (fun j => ‖densityFourier rho.value j‖^2) k t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => mellinPairing_eq_series rho ht)
    _ = 2*∑' k : Frequency d, greenMultiplier d k*‖densityFourier rho.value k‖^2 :=
      integral_mellinSeries hd _ habs
    _ = 2*densitySpectralEnergy rho := by rw [(hasSum_green_density_spectrum rho hs).tsum_eq]

theorem fourierEnergy_polarize_le {d : ℕ} (hd : 0 < d) (i : Fin d) (a : ℝ)
    (rho : ProbabilityDensity d) (hr : MemLp rho.value 2 (torusMeasure d)) :
    fourierEnergy rho ≤ fourierEnergy (density i a rho) := by
  have hs := (PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd rho hr).1
  have hp := (PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd (density i a rho) (density_memLp_two i a hr)).1
  have hi := integral_mono_ae (mellinPairing_integrable hd rho hs)
    (mellinPairing_integrable hd (density i a rho) hp) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_left (centeredHeatPairing_polarize_le ht i a rho)
        (Real.rpow_nonneg ht.le _))
  rw [integral_mellinPairing hd rho hs,integral_mellinPairing hd (density i a rho) hp,
    normalized_energy,normalized_energy] at hi
  have hq : fourierEnergy rho/endpointSigma d ≤ fourierEnergy (density i a rho)/endpointSigma d := by linarith
  exact (div_le_div_iff_of_pos_right (endpointSigma_pos hd)).mp hq

#print axioms fourierEnergy_polarize_le
end Legacy.BecknerOnofri.CoordinatePolarization
