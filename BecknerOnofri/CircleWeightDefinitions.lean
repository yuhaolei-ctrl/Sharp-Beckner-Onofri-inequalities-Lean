import Mathlib.Analysis.SpecificLimits.Basic

namespace BecknerOnofri.HighDim.CircleScalar
noncomputable def weight (n : ℕ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, t^(2*j)/(n+j+1:ℝ)
end BecknerOnofri.HighDim.CircleScalar
