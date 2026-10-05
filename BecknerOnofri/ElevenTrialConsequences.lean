import BecknerOnofri.ElevenCompetitorEnergy
import BecknerOnofri.ElevenConditionalEntropy
import BecknerOnofri.ElevenVariational

/-! Unconditional variational consequences of the specified competitor.
Both its entropy and its actual infinite Fourier energy are now proved. -/
noncomputable section
namespace BecknerOnofri.HighDim.Eleven

theorem spectral_pressure : (1/30:EReal) < pressure 11 (spectralThreshold 11) :=
  spectral_pressure_of_competitor competitorDensity competitorDensity_finiteEntropy
    competitor_entropy_bound (competitor_energy competitorDensity rfl)

theorem transition_upper : globalTransition < (2063:ℝ)/100 :=
  transition_lt_of_competitor competitorDensity competitorDensity_finiteEntropy
    competitor_entropy_fine (competitor_energy competitorDensity rfl)

theorem transition_spectral_gap : 0 < 1-globalTransition/spectralThreshold 11 :=
  hessian_gap_of_transition_upper transition_upper

#print axioms spectral_pressure
#print axioms transition_upper
end BecknerOnofri.HighDim.Eleven
