import Paper2PhysicalFractionalDefinitions
import Paper2PeriodizationDefinitions
import Mathlib.Analysis.Normed.Group.FunctionSeries
import BecknerOnofri.ExtendedEntropyDefinitions
import BecknerOnofri.Friedrichs.MixedSpectralPowers

/-! Definitions for the October 3 paper, separate from the frozen September 21 targets.
The negative Sobolev energy is an extended nonnegative quantity; divergent
Fourier series are not interpreted as zero. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BecknerOnofri.Paper2
open HighDim

def negativeSobolevEnergy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 * Real.pi) ^ d))⁻¹ * spectralEnergy ρ

def negativeSobolevFourierSeries {d : ℕ} (ρ : ProbabilityDensity d) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d,
    ENNReal.ofReal ((2 * Real.pi * frequencyLength k.val) ^ d)⁻¹ *
      ENNReal.ofReal (‖fourierCoeff ρ.value k.val‖ ^ 2)

/-- Physical eigenvalue scaling on the original angular Hilbert space.
This definition alone does NOT identify the unit-period spatial Friedrichs
form; the coordinate/measure transport is a separate obligation. -/
def physicalSpectralPowerGraph {d : ℕ}
    (α : Friedrichs.MixedSpatial.MultiIndex d) (s : ℝ)
    (f g : Friedrichs.MixedSpatial.H α) : Prop :=
  ∀ n, inner ℝ g (Friedrichs.MixedSpatial.basisTensorVector α n) =
    ((2 * Real.pi) ^ 2 * Friedrichs.MixedSpatial.mixedEigenvalue α n) ^ s *
      inner ℝ f (Friedrichs.MixedSpatial.basisTensorVector α n)

end BecknerOnofri.Paper2
