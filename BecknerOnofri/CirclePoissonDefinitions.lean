module

public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.CirclePoisson

/-- The normalized circle Poisson kernel, with radius `q`. Along the flow,
`q = exp (-s)`. -/
def kernel (q : ℝ) (x : UnitAddCircle) : ℝ :=
  (1-q^2)/(1-2*q*(fourier 1 x).re+q^2)

/-- Convolution with the Poisson kernel, on normalized Haar measure. -/
def smoothing (q : ℝ) (p : UnitAddCircle → ℝ) (x : UnitAddCircle) : ℝ :=
  ∫ y,kernel q y*p (x-y) ∂AddCircle.haarAddCircle

end BecknerOnofri.HighDim.CirclePoisson
