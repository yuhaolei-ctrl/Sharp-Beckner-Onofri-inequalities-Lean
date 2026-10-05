import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The real coefficient model of the Hardy space used in §5.2. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleHardy

abbrev Space := lp (fun _ : ℕ => ℝ) 2

/-- The cosine moments of the boundary square of a real Hardy function. -/
def moment (f : Space) (n : ℕ) : ℝ := ∑' m, f (m+n)*f m

end BecknerOnofri.HighDim.CircleHardy
