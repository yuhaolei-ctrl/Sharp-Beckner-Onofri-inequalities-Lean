module

public import BecknerOnofri.Definitions
public import Mathlib.MeasureTheory.Integral.Marginal

@[expose] public section

/-! Actual ordered conditional densities on normalized product Haar space. -/

noncomputable section
open MeasureTheory Function

namespace BecknerOnofri.HighDim.ConditionalEntropy

/-- Coordinates integrated out when keeping the first `k` coordinates. -/
def suffixCoordinates (d k : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => k ≤ j.val)

/-- The unnormalized prefix marginal, expressed on the original product space. -/
def prefixDensity {d : ℕ} (f : Torus d → ℝ) (k : ℕ) (x : Torus d) : ℝ :=
  ∫ y : suffixCoordinates d k → UnitAddCircle,
    f (updateFinset x (suffixCoordinates d k) y)
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)

/-- The conditional density of coordinate `i` given the coordinates before it. -/
def conditionalDensity {d : ℕ} (f : Torus d → ℝ) (i : Fin d)
    (x : Torus d) (z : UnitAddCircle) : ℝ :=
  prefixDensity f (i.val + 1) (Function.update x i z) / prefixDensity f i.val x

def conditionalEntropy {d : ℕ} (f : Torus d → ℝ) (i : Fin d) (x : Torus d) : ℝ :=
  ∫ z, conditionalDensity f i x z * Real.log (conditionalDensity f i x z)
    ∂AddCircle.haarAddCircle

def conditionalCosineMoment {d : ℕ} (f : Torus d → ℝ) (i : Fin d)
    (n : ℕ) (x : Torus d) : ℝ :=
  ∫ z, conditionalDensity f i x z * (fourier (n : ℤ) z).re
    ∂AddCircle.haarAddCircle

end BecknerOnofri.HighDim.ConditionalEntropy
