module

public import BecknerOnofri.CircleGammaDefinitions

@[expose] public section

namespace BecknerOnofri.HighDim.CircleScalar
/-- The source's J, obtained by discarding the nonnegative quadratic minimum. -/
noncomputable def tailBase (t : ℝ) : ℝ :=
  (13/40)*rate t+(27/40)*t^2-2*Spin.binaryCost t
end BecknerOnofri.HighDim.CircleScalar
