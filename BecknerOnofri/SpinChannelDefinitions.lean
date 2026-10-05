import BecknerOnofri.SpinCountDefinitions
import BecknerOnofri.Definitions

/-! The actual binary-spin channel and its joint moments. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def channel (c : Fin 12 → ℝ) (σ : Configuration) : ℝ :=
  (∏ i ∈ σ,(1+c i)/2)*(∏ i ∈ σᶜ,(1-c i)/2)

/-- The product of spins in S: plus coordinates contribute one, and every
minus coordinate belonging to S contributes minus one. -/
def jointSpin (S : Finset (Fin 12)) (σ : Configuration) : ℝ :=
  ∏ i ∈ σᶜ,if i∈S then (-1:ℝ) else 1

def torusCosines (x : Torus 12) (i : Fin 12) : ℝ := (fourier 1 (x i)).re
def channelLaw (ρ : ProbabilityDensity 12) (σ : Configuration) : ℝ :=
  ∫ x,ρ.value x*channel (torusCosines x) σ ∂torusMeasure 12

end BecknerOnofri.HighDim.Spin
