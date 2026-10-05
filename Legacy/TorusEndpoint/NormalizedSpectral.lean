import Legacy.TorusEndpoint.EndpointNormalization
import Legacy.TorusEndpoint.FullSpectral

/-!
# A conditional spectral endpoint with the exact constant

This is a spectral statement. The exponential estimate is an explicit
hypothesis, and identification with the physical singular Green-kernel
energy is not asserted. The conclusion includes summability, so that the
totalized `tsum` cannot mask a divergent series in applications.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint

noncomputable def densitySpectralTerm {d : ℕ} (rho : ProbabilityDensity d)
    (k : NonzeroFrequency d) : ℝ :=
  ‖densityFourier rho.value k.val‖ ^ 2 / frequencyRadius k.val ^ d

/-- Only a spectral definition; not a definition of the physical interaction integral. -/
noncomputable def densitySpectralEnergy {d : ℕ} (rho : ProbabilityDensity d) : ℝ :=
  (1 / endpointSigma d) * ∑' k : NonzeroFrequency d, densitySpectralTerm rho k

theorem dual_weight_spectral_term {d : ℕ} (rho : ProbabilityDensity d)
    (k : NonzeroFrequency d) :
    ‖densityFourier rho.value k.val‖ ^ 2 / endpointDualWeight d k.val =
      endpointCoupling d * densitySpectralTerm rho k := by
  simp [endpointDualWeight, densitySpectralTerm, div_eq_mul_inv, mul_comm, mul_left_comm]

theorem spectral_entropy_of_exponential_bound {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (h_entropy : rho.FiniteEntropy)
    (h_exp : ∀ s : Finset (Frequency d),
      (∀ k ∈ s, FiniteCone.LexPositive k) → ∀ c : Frequency d → ℂ,
      Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
        ∑ k ∈ s, endpointDualWeight d k * ‖c k‖ ^ 2) :
    Summable (densitySpectralTerm rho) ∧
      (d : ℝ) * densitySpectralEnergy rho ≤ densityEntropy rho.value := by
  obtain ⟨h_sum, h_bound⟩ := full_spectral_summable_and_entropy_bound
    rho h_entropy (endpointDualWeight d)
    (fun _ hk => endpointDualWeight_pos hd hk)
    (fun k _ => endpointDualWeight_neg d k) h_exp
  simp_rw [dual_weight_spectral_term] at h_sum h_bound
  have hcoupling := endpointCoupling_pos hd
  have hs := (summable_mul_left_iff hcoupling.ne').mp h_sum
  rw [tsum_mul_left] at h_bound
  refine ⟨hs, ?_⟩
  have hnormalized : (d : ℝ) * densitySpectralEnergy rho =
      (endpointCoupling d * ∑' k : NonzeroFrequency d, densitySpectralTerm rho k) / 2 := by
    unfold densitySpectralEnergy endpointCoupling
    ring
  rw [hnormalized]
  linarith

end Legacy.TorusEndpoint
