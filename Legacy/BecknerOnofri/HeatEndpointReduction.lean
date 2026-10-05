module

public import Legacy.BecknerOnofri.HeatDensityApproximation
public import Legacy.BecknerOnofri.EndpointClosure

@[expose] public section

/-! A proved reduction of the full finite-entropy endpoint to continuous
strictly positive densities. The remaining bound on that class is an explicit
premise, not a claimed proof of EndpointThroughTen. -/

noncomputable section
open Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.HeatEndpointReduction
open HeatDensityApproximation

theorem endpoint_of_continuous_pos {d : ℕ} (hd : 0 < d)
    (hbound : ∀ rho : ProbabilityDensity d, Continuous rho.value →
      (∀ x, 0 < rho.value x) →
      Summable (densitySpectralTerm rho) ∧
        endpointConstant d * fourierEnergy rho ≤ densityEntropy rho.value) : Endpoint d := by
  intro rho hr
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have hlim : Filter.Tendsto t Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply EndpointClosure.spectral_bound_of_fourier_limits_entropy_le (endpointConstant d)
    (div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd))
    (fun n => heatDensity rho (ht n)) rho
  · intro n
    exact hbound (heatDensity rho (ht n)) (heatValue_continuous rho (ht n))
      (heatValue_pos rho (ht n))
  · exact heatDensity_fourier_tendsto rho t ht hlim
  · intro n
    exact heatDensity_entropy_le rho hr (ht n)

#print axioms endpoint_of_continuous_pos
end Legacy.BecknerOnofri.HeatEndpointReduction
