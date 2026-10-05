import PhysicalOperator
import BecknerOnofri.Friedrichs.MixedFractionalStatementDefinitions

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

def torusPower {d : ℕ} (s : ℝ) (u : HighDim.Torus d → ℝ) : HighDim.Torus d → ℝ :=
  fun x => (scale^2)^s * SmoothTorus.angularPower s u x

/-- Literal unit-period version of the manuscript's fractional intertwining.
Both vectors live in the actual unweighted mixed Lebesgue L² space. The power
is tied to the closure of the physical Dirichlet/periodic form by
`spectralPowerGraph_one` and `operatorGraph_transport`. -/
def FractionalIntertwining (d : ℕ) : Prop :=
  ∀ U : (Fin d → ℝ) → ℝ,
    ContDiffOn ℝ ∞ U (HighDim.SmoothEulerStatement.cosineCube d) →
    ∀ (α : MultiIndex d), α≠0 → ∀ s : ℝ, 0<s →
      ∃ Us : (Fin d → ℝ) → ℝ,
        ContDiffOn ℝ ∞ Us (HighDim.SmoothEulerStatement.cosineCube d) ∧
        (∀ x : Fin d → ℝ, torusPower s (cosineLift U) (fun i => (x i : UnitAddCircle)) =
          Us (fun i => Real.cos (scale*x i))) ∧
        (∀ k : HighDim.Frequency d, HighDim.fourierCoeff (torusPower s (cosineLift U)) k =
          (((scale * HighDim.frequencyLength k)^(2*s):ℝ):ℂ) * HighDim.fourierCoeff (cosineLift U) k) ∧
        ∃ f g : H α,
          (f : Space d → ℝ)=ᵐ[spatialMeasure α]
            (fun x => (∏ i, Real.sin (scale*x i)^(α i)) *
              HighDim.SmoothEulerStatement.mixedPartial (derivativeList α) U
                (fun i => Real.cos (scale*x i))) ∧
          (g : Space d → ℝ)=ᵐ[spatialMeasure α]
            (fun x => (∏ i, Real.sin (scale*x i)^(α i)) *
              HighDim.SmoothEulerStatement.mixedPartial (derivativeList α) Us
                (fun i => Real.cos (scale*x i))) ∧
          SpectralPowerGraph α s f g

end BecknerOnofri.Paper2.Physical
