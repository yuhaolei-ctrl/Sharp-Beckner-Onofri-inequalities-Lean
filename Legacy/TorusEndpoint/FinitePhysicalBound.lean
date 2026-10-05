module

public import Legacy.TorusEndpoint.CoefficientEndpointReduction
public import Legacy.TorusEndpoint.PhysicalFiniteFourier

@[expose] public section

/-! Finite interaction bounds for actual kernels with Fourier multipliers
dominated by the Green multiplier. Singular-kernel passage is a separate task. -/

open scoped BigOperators

namespace Legacy.TorusEndpoint

def nonzeroFrequencyEmbedding (d : ℕ) : NonzeroFrequency d ↪ Frequency d :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem finite_physical_energy_le_spectral {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (h_sum : Summable (densitySpectralTerm rho))
    (s : Finset (NonzeroFrequency d)) (b : Frequency d → ℝ)
    (hb : ∀ k ∈ s, b k.val ≤ 1 / (endpointSigma d * frequencyRadius k.val ^ d)) :
    PhysicalFiniteFourier.finitePhysicalEnergy rho
      (s.map (nonzeroFrequencyEmbedding d)) b ≤ densitySpectralEnergy rho := by
  classical
  rw [PhysicalFiniteFourier.finitePhysicalEnergy_eq_spectral, Finset.sum_map]
  have h_nonneg : ∀ k : NonzeroFrequency d, 0 ≤ densitySpectralTerm rho k := by
    intro k
    exact div_nonneg (sq_nonneg _) (pow_nonneg (frequencyRadius_nonneg _) _)
  have h_factor : 0 ≤ 1 / endpointSigma d := (one_div_pos.mpr (endpointSigma_pos hd)).le
  calc
    _ ≤ ∑ k ∈ s, (1 / endpointSigma d) * densitySpectralTerm rho k := by
      apply Finset.sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (hb k hk)
        (sq_nonneg ‖densityFourier rho.value k.val‖)
      convert h using 1 <;>
        simp [nonzeroFrequencyEmbedding, densitySpectralTerm, div_eq_mul_inv, mul_comm,
          mul_left_comm]
    _ = (1 / endpointSigma d) * ∑ k ∈ s, densitySpectralTerm rho k :=
      (Finset.mul_sum s _ _).symm
    _ ≤ densitySpectralEnergy rho :=
      mul_le_mul_of_nonneg_left (h_sum.sum_le_tsum s (fun k _ => h_nonneg k)) h_factor

/-- Conditional finite physical-kernel endpoint. The coefficient certificate
is still explicit; the left side is a genuine double integral. -/
theorem finite_physical_entropy_of_endpoint_coefficient_cap {d : ℕ} (hd : 0 < d)
    (rho : ProbabilityDensity d) (h_entropy : rho.FiniteEntropy)
    (hcap : GlobalFiniteAtomCap (endpointAtomWeight d))
    (s : Finset (NonzeroFrequency d)) (b : Frequency d → ℝ)
    (hb : ∀ k ∈ s, b k.val ≤ 1 / (endpointSigma d * frequencyRadius k.val ^ d)) :
    (d : ℝ) * PhysicalFiniteFourier.finitePhysicalEnergy rho
      (s.map (nonzeroFrequencyEmbedding d)) b ≤ densityEntropy rho.value := by
  obtain ⟨h_sum, h_bound⟩ := spectral_entropy_of_endpoint_coefficient_cap hd rho h_entropy hcap
  exact (mul_le_mul_of_nonneg_left
    (finite_physical_energy_le_spectral hd rho h_sum s b hb) (Nat.cast_nonneg d)).trans h_bound

end Legacy.TorusEndpoint
