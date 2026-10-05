import BecknerOnofri.Definitions

/-! Actual circle spectral operators, with period-one Fourier characters.
The multiplier of Λ is |n| (angular normalization), not 2π|n|.
The following proofs establish absolute convergence on their smooth domains. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleFisher

def signedSeries (a : Frequency 1 → ℂ) (x : Torus 1) : ℂ :=
  ∑' k,(k (0:Fin 1):ℂ)*a k*UnitAddTorus.mFourier k x

def lambda (g : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  (∑' k : Frequency 1,((|(k (0:Fin 1):ℝ)|:ℝ):ℂ)*
    UnitAddTorus.mFourierCoeff (fun y => (g y:ℂ)) k*UnitAddTorus.mFourier k x).re

end BecknerOnofri.HighDim.CircleFisher
