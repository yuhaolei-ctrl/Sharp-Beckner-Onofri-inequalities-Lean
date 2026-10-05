import BecknerOnofri.SpinDefinitions

/-! The manuscript's product-spin plus-count law and binary entropy cost. -/
noncomputable section
namespace BecknerOnofri.HighDim.Spin

def productProbability (t : ℝ) (j : Count) : ℝ :=
  reference j*(1+t)^j.val*(1-t)^(12-j.val)

def binaryCost (t : ℝ) : ℝ :=
  ((1+t)*Real.log (1+t)+(1-t)*Real.log (1-t))/2

end BecknerOnofri.HighDim.Spin
