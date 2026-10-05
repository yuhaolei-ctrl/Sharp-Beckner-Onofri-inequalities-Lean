import BecknerOnofri.VariationalCurveDefinitions

namespace BecknerOnofri.HighDim.VariationalCurves
noncomputable def zeroDefectCoefficient (d : ℕ) : ℝ :=
  spectralThreshold d/(2*globalTransition d*(2*Real.pi)^d)
end BecknerOnofri.HighDim.VariationalCurves
