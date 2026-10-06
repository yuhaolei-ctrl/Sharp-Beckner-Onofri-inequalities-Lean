module

public import BecknerOnofri.CircleGammaDefinitions

@[expose] public section

namespace BecknerOnofri.HighDim.CircleScalar
/-- The source's J, obtained by discarding the nonnegative quadratic minimum. -/
noncomputable def tailBase (t : ℝ) : ℝ :=
  (33/100)*rate t+(67/100)*t^2-2*Spin.binaryCost t
end BecknerOnofri.HighDim.CircleScalar
