import BecknerOnofri.SpinProductDefinitions

/-! The nonaffine energy-gradient term of the product comparison law.
The affine projection coefficient is the source's sum s w_s t^(2s-1). -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

def productAffineCoefficient (t : ℝ) : ℝ :=
  ∑ s : Order,weight s*(s.val+1:ℝ)*t^(2*s.val+1)

def productGradientCorrection (t : ℝ) (j : Count) : ℝ :=
  2*((∑ k : Count,interaction j k*productProbability t k)-
    quadratic (productProbability t)-productAffineCoefficient t*(meanCoordinate j-t))

end BecknerOnofri.HighDim.Spin
