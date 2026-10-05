module

public import BecknerOnofri.Definitions
public import Legacy.TorusEndpoint.GreenKernelReal

@[expose] public section

/-! The collapse coefficient in the same Fourier normalization as the
trusted raw-function statements. Since c_d σ_d = (2π)^d, this is 1/(4d c_d).
This file contains definitions only. -/
namespace BecknerOnofri.HighDim
noncomputable def collapseCoefficient (d : ℕ) : ℝ :=
  spectralThreshold d / (4 * (d : ℝ) * (2 * Real.pi)^d)
end BecknerOnofri.HighDim
