module

public import Legacy.BecknerOnofri.FiniteScalarCore

@[expose] public section
namespace BecknerOnofri.HighDim.Eleven.ScalarFinite
/-- Upward bound for (3543/200)/σ₁₁, using π > 314159/100000. -/
def betaLambda : ℚ := (3543 : ℚ)/200 * 945/64 / ((314159 : ℚ)/100000)^5
end BecknerOnofri.HighDim.Eleven.ScalarFinite
