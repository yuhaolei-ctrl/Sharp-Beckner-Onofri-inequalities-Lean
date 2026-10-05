module

public import BecknerOnofri.Definitions

@[expose] public section

/-! Literal heat semigroup at physical time t on the unit-volume torus.
The multiplier is exp(-4*pi^2*|k|^2*t); these are definitions only. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim

def physicalHeatKernel (d : ℕ) (t : ℝ) (x : Torus d) : ℝ :=
  (∑' k : Frequency d, (Real.exp (-4*Real.pi^2*t*(∑ i, (k i:ℝ)^2)):ℂ) *
    UnitAddTorus.mFourier k x).re

def heatRegularization {d : ℕ} (ρ : ProbabilityDensity d) (t : ℝ) (x : Torus d) : ℝ :=
  ∫ y, ρ.value y * physicalHeatKernel d t (x-y) ∂torusMeasure d

end BecknerOnofri.HighDim
