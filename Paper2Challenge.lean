import Challenge
import Paper2Definitions

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace BecknerOnofri.Paper2
open HighDim

theorem negativeSobolevEnergy_normalization {d : ℕ} (ρ : ProbabilityDensity d) :
    ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ =
      spectralEnergy ρ := by
  sorry

theorem negativeSobolevEnergy_fourier {d : ℕ} (ρ : ProbabilityDensity d) :
    negativeSobolevEnergy ρ = negativeSobolevFourierSeries ρ := by
  sorry

theorem low_density_extended (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) :
    (((d : ℝ) / spectralThreshold d : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  sorry

theorem high_density_extended (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) *
      (ENNReal.ofReal ((2 * Real.pi) ^ d) * negativeSobolevEnergy ρ).toEReal ≤
        extendedEntropy ρ := by
  sorry

theorem physicalSpectralPowerGraph_scaling {d : ℕ}
    (α : Friedrichs.MixedSpatial.MultiIndex d) (s : ℝ)
    (f g : Friedrichs.MixedSpatial.H α)
    (h : Friedrichs.MixedSpatial.SpectralPowerGraph α s f g) :
    physicalSpectralPowerGraph α s f (((2 * Real.pi) ^ 2) ^ s • g) := by
  sorry

end BecknerOnofri.Paper2
