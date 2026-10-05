module

public import BecknerOnofri.CircleBesselDefinitions

@[expose] public section

/-! Exact factorial-series terms and finite sums used in scalar certificates. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar

def besselTerm (n : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  h^(2*j+n)/((j.factorial:ℝ)*((j+n).factorial:ℝ))
def besselPartial (n N : ℕ) (h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,besselTerm n h j

end BecknerOnofri.HighDim.CircleScalar
