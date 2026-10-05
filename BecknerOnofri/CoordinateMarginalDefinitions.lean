import BecknerOnofri.Definitions

/-! Coordinate marginals with respect to normalized product Haar measure.
`I` lists the retained coordinates. Integration over unused coordinates of `y`
and over unused coordinates of `x` has mass one. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim

def coordinateMarginal {d : ℕ} (ρ : ProbabilityDensity d) (I : Finset (Fin d))
    (x : Torus d) : ℝ :=
  ∫ y, ρ.value (fun i => if i ∈ I then x i else y i) ∂torusMeasure d

def coordinateMarginalEntropy {d : ℕ} (ρ : ProbabilityDensity d) (I : Finset (Fin d)) : ℝ :=
  ∫ x, coordinateMarginal ρ I x * Real.log (coordinateMarginal ρ I x) ∂torusMeasure d

end BecknerOnofri.HighDim
