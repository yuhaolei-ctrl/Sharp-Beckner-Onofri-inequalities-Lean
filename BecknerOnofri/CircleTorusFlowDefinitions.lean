import BecknerOnofri.Definitions
import BecknerOnofri.CirclePoissonDefinitions

/-! The actual circle Poisson convolution on the one-dimensional product torus.
At time zero it is the identity; analytic assertions concern positive times. -/
noncomputable section
namespace BecknerOnofri.HighDim.CirclePoisson

def torusFlow (s : ℝ) (p : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  if s=0 then p x else
    smoothing (Real.exp (-s)) (fun z : UnitAddCircle => p (fun _ => z)) (x 0)

end BecknerOnofri.HighDim.CirclePoisson
