import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact coefficients in (1.28); definitions only. -/
namespace BecknerOnofri.HighDim

noncomputable def quarticA (d : ℕ) : ℝ :=
  -(1 / 4 : ℝ) + 1 / (4 * ((2 : ℝ) ^ d - 1))

noncomputable def quarticB (d : ℕ) : ℝ :=
  2 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)

noncomputable def kappa (d : ℕ) : ℝ :=
  -(2 * quarticA d + ((d : ℝ) - 1) * quarticB d)

end BecknerOnofri.HighDim
