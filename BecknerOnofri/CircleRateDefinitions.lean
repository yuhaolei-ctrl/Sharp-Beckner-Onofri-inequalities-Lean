import BecknerOnofri.CircleBesselDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BecknerOnofri.HighDim.CircleScalar
/-- The source's von Mises rate at the mean t=I₁(2h)/I₀(2h). -/
noncomputable def rateAt (h : ℝ) : ℝ :=
  2*h*besselMoment 1 h-Real.log (bessel 0 h)
end BecknerOnofri.HighDim.CircleScalar
