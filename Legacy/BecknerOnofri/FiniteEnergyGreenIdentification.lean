import Legacy.BecknerOnofri.BoundedDensityApproximation
import Legacy.BecknerOnofri.LowDimensionPhysicalEndpoint

/-! Exact equality of the singular Green double integral and the full Fourier
energy for every L1 probability density of finite spectral energy. Bounded
normalized truncations supply the reverse bound through dominated convergence. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.FiniteEnergyGreenIdentification
open GreenKernelReal PhysicalGreenL2 PhysicalGreenFiniteEnergy BoundedDensityApproximation

theorem interaction_tendsto {d : ℕ} (r : ProbabilityDensity d)
    (hi : Integrable (fun z : Torus d × Torus d =>
      realGreen d (z.1-z.2)*r.value z.1*r.value z.2)
      ((torusMeasure d).prod (torusMeasure d))) :
    Tendsto (fun n => physicalGreenEnergy (density r n)) atTop (𝓝 (physicalGreenEnergy r)) := by
  let G := fun z : Torus d × Torus d => realGreen d (z.1-z.2)
  have hm := mass_pos r 0
  have hI (n : ℕ) : Integrable (fun z : Torus d × Torus d =>
      G z*(density r n).value z.1*(density r n).value z.2)
      ((torusMeasure d).prod (torusMeasure d)) :=
    realGreen_interaction_integrable _ (density_memLp r n)
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n z => G z*(density r n).value z.1*(density r n).value z.2)
    (f := fun z => G z*r.value z.1*r.value z.2)
    (fun z => ‖G z*r.value z.1*r.value z.2‖/(mass r 0)^2)
    (fun n => (hI n).aestronglyMeasurable) (hi.norm.div_const _) (fun n => by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (density_le r n),
        Measure.quasiMeasurePreserving_snd.ae (density_le r n),
        density_product_nonneg_ae r] with z hx hy hz
      have hprod := mul_le_mul hx hy (density_nonnegative r n z.2) (div_nonneg hz.1 hm.le)
      have hmul := mul_le_mul_of_nonneg_left hprod (norm_nonneg (G z))
      calc
        ‖G z*(density r n).value z.1*(density r n).value z.2‖ =
            ‖G z‖*((density r n).value z.1*(density r n).value z.2) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (density_nonnegative r n z.1),
            Real.norm_of_nonneg (density_nonnegative r n z.2), mul_assoc]
        _ ≤ ‖G z‖*((r.value z.1/mass r 0)*(r.value z.2/mass r 0)) := hmul
        _ = ‖G z*r.value z.1*r.value z.2‖/(mass r 0)^2 := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg hz.1, Real.norm_of_nonneg hz.2]
          ring) (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (density_tendsto r),
        Measure.quasiMeasurePreserving_snd.ae (density_tendsto r)] with z hx hy
      exact ((tendsto_const_nhds (x := G z)).mul hx).mul hy)
  have he (n : ℕ) : (∫ z, G z*(density r n).value z.1*(density r n).value z.2
      ∂(torusMeasure d).prod (torusMeasure d)) = physicalGreenEnergy (density r n) := by
    rw [integral_prod _ (hI n)]
    rfl
  have he' : (∫ z, G z*r.value z.1*r.value z.2 ∂(torusMeasure d).prod (torusMeasure d)) =
      physicalGreenEnergy r := by
    rw [integral_prod _ hi]
    rfl
  simpa only [he, he'] using h

/-- No entropy, boundedness or L2 premise is needed for this identification. -/
theorem physicalGreen_eq_spectral {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hs : Summable (densitySpectralTerm r)) :
    physicalGreenEnergy r = densitySpectralEnergy r := by
  obtain ⟨hi, hle⟩ := physicalGreen_integrable_and_le_spectral hd r hs
  apply le_antisymm hle
  have hσ := endpointSigma_pos hd
  have hsum (s : Finset (NonzeroFrequency d)) :
      ∑ k ∈ s, densitySpectralTerm r k ≤ endpointSigma d*physicalGreenEnergy r := by
    have ht : Tendsto (fun n => ∑ k ∈ s, densitySpectralTerm (density r n) k)
        atTop (𝓝 (∑ k ∈ s, densitySpectralTerm r k)) := by
      apply tendsto_finsetSum
      intro k hk
      exact ((fourier_tendsto r k.val).norm.pow 2).div_const _
    apply le_of_tendsto_of_tendsto' ht ((interaction_tendsto r hi).const_mul (endpointSigma d))
    intro n
    obtain ⟨hsn, hen⟩ := physicalGreenEnergy_eq_spectral hd (density r n) (density_memLp r n)
    have he : endpointSigma d*physicalGreenEnergy (density r n) = fourierEnergy (density r n) := by
      rw [hen, normalized_energy]
      field_simp
    rw [he]
    exact hsn.sum_le_tsum s (fun k _ =>
      div_nonneg (sq_nonneg _) (pow_nonneg (frequencyRadius_nonneg _) _))
  have ht := Real.tsum_le_of_sum_le (fun k : NonzeroFrequency d =>
    div_nonneg (sq_nonneg ‖densityFourier r.value k.val‖)
      (pow_nonneg (frequencyRadius_nonneg _) _)) hsum
  rw [normalized_energy]
  exact (div_le_iff₀ hσ).mpr (by simpa only [fourierEnergy, densitySpectralTerm, mul_comm] using ht)

theorem finiteEntropy_physicalGreen_eq_spectral {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    physicalGreenEnergy r = densitySpectralEnergy r :=
  physicalGreen_eq_spectral (by omega) r (endpoint_through_ten d hd hd10 r hr).1

#print axioms interaction_tendsto
#print axioms physicalGreen_eq_spectral
#print axioms finiteEntropy_physicalGreen_eq_spectral
end Legacy.BecknerOnofri.FiniteEnergyGreenIdentification
