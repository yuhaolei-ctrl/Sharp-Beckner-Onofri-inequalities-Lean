module

public import Legacy.BecknerOnofri.FiniteDifferenceSmooth
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-! Actual closed-cube coordinate derivatives and Taylor coefficients.
No convergence or representation statement is included in these definitions. -/
noncomputable section
open scoped BigOperators unitInterval
namespace BecknerOnofri.HighDim.ClosedCubeTaylor

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Index (d : ℕ) := Fin d →₀ ℕ
abbrev Cube (d : ℕ) := Fin d → unitInterval

def nonnegativePartials {d : ℕ} (f : Space d → ℝ) : Prop :=
  ∀ is x, x ∈ Set.Icc (0 : Space d) 1 →
    0 ≤ Legacy.BecknerOnofri.FiniteDifferences.mixedPartial is f x

def coefficient {d : ℕ} (f : Space d → ℝ) (a : Index d) : ℝ :=
  Legacy.BecknerOnofri.FiniteDifferences.mixedPartial
    (Legacy.BecknerOnofri.FiniteDifferences.directions a) f 0 /
      (∏ i, ((a i).factorial : ℝ))

def monomial {d : ℕ} (a : Index d) (y : Cube d) : ℝ :=
  ∏ i, (y i : ℝ) ^ a i

end BecknerOnofri.HighDim.ClosedCubeTaylor
