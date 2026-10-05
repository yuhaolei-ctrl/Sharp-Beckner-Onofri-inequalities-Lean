module

public import BecknerOnofri.Definitions

@[expose] public section

/-! The one-sided logarithmic Fourier coefficients used to construct the
outer function. On the zero hyperplane the coefficient is halved. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleOuter

def halfSpectrum {d : ℕ} (i : Fin d) (l : Frequency d → ℝ) (k : Frequency d) : ℂ :=
  if k i=0 then ((l k/2:ℝ):ℂ) else if 0<k i then (l k:ℂ) else 0

/-- The first absolute Fourier moment weight on the one-dimensional torus. -/
def linearWeight (k : Frequency 1) : ℝ := 1+|(k (0:Fin 1):ℝ)|

end BecknerOnofri.HighDim.CircleOuter
