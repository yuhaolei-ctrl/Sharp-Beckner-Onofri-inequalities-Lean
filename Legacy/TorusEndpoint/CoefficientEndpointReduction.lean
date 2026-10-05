import Legacy.TorusEndpoint.GlobalCoefficientCriterion
import Legacy.TorusEndpoint.NormalizedSpectral

/-!
# The coefficient-to-spectral endpoint reduction

The exact radial coefficient bound is the explicit, undischarged hypothesis.
This theorem is not an unconditional endpoint proof in any dimension.
-/

namespace Legacy.TorusEndpoint

/-- Genuine summability and the exact spectral constant follow from the
full family of actual finite-atom caps. No exponential-integral premise remains. -/
theorem spectral_entropy_of_endpoint_coefficient_cap {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (h_entropy : rho.FiniteEntropy)
    (hcap : GlobalFiniteAtomCap (endpointAtomWeight d)) :
    Summable (densitySpectralTerm rho) ∧
      (d : ℝ) * densitySpectralEnergy rho ≤ densityEntropy rho.value := by
  apply spectral_entropy_of_exponential_bound hd rho h_entropy
  intro s hs c
  have ha : ∀ k : Frequency d, FiniteCone.LexPositive k → 0 < endpointAtomWeight d k := by
    intro k hk
    exact endpointAtomWeight_pos hd (FiniteCone.positive_ne_zero hk)
  have h := finite_fourier_log_integral_exp_le_reciprocal_of_global_cap
    (endpointAtomWeight d) ha hcap s hs c
  simpa only [one_div, ← endpointDualWeight_eq_inv] using h

end Legacy.TorusEndpoint
