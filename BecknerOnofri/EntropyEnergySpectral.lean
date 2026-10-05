module

public import BecknerOnofri.EntropyEnergySplit

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim.EntropyTail

theorem fullFourierEnergy_eq_spectral_tsum (ρ : ProbabilityDensity 12) :
    fullFourierEnergy ρ.value = ∑' k : NonzeroFrequency 12, spectralTerm ρ k := by
  classical
  let f : Frequency 12 → ℝ := fun k =>
    (frequencyLength k^12)⁻¹*‖fourierCoeff ρ.value k‖^2
  have hs : Function.support f ⊆ {k : Frequency 12 | k≠0} := by
    intro k hk hz
    subst k
    exact hk (by simp [f, frequencyLength])
  change (∑' k, f k) = _
  exact (tsum_subtype_eq_of_support_subset hs).symm

theorem spectralEnergy_eq_fullFourierEnergy (ρ : ProbabilityDensity 12) (hc : Continuous ρ.value) :
    spectralEnergy ρ = ENNReal.ofReal (fullFourierEnergy ρ.value) := by
  have hs : Summable (spectralTerm ρ) :=
    (fullFourierEnergy_summable hc).subtype {k : Frequency 12 | k≠0}
  have hn (k : NonzeroFrequency 12) : 0 ≤ spectralTerm ρ k := by
    unfold spectralTerm frequencyLength
    positivity
  rw [spectralEnergy, ← ENNReal.ofReal_tsum_of_nonneg hn hs,
    fullFourierEnergy_eq_spectral_tsum]

#print axioms spectralEnergy_eq_fullFourierEnergy
end BecknerOnofri.HighDim.EntropyTail
