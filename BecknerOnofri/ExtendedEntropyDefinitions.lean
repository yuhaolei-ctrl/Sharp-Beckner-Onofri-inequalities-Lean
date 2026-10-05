module

public import BecknerOnofri.Definitions

@[expose] public section

/-! Extended entropy with the negative part handled by a bounded shift.
The formula is meaningful even when the positive entropy integral is infinite. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BecknerOnofri.HighDim

def extendedEntropy {d : ℕ} (ρ : ProbabilityDensity d) : EReal :=
  (∫⁻ x, ENNReal.ofReal (ρ.value x*Real.log (ρ.value x)+1) ∂torusMeasure d).toEReal - 1

def circlePositiveEnergy (ρ : ProbabilityDensity 1) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (‖fourierCoeff ρ.value (fun _ => (n+1:ℤ))‖^2 / (n+1:ℝ))

end BecknerOnofri.HighDim
