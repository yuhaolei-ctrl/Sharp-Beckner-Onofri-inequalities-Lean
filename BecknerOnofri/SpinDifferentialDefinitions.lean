import BecknerOnofri.SpinDefinitions

/-! The formula-defined full gradient in the global supporting-parabola
corollary. No bounds or differentiability assumptions are encoded here. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def gradient (p : Count → ℝ) (j : Count) : ℝ :=
  2*Real.log (p j/reference j)+2-2*(∑ k : Count,interaction j k*p k)

end BecknerOnofri.HighDim.Spin
