module

public import BecknerOnofri.CircleTorusFlowDefinitions

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim.CirclePoisson

def moment (p : Torus 1 → ℝ) (n : ℕ) : ℝ :=
  (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re

def deficit (p : Torus 1 → ℝ) (s : ℝ) : ℝ :=
  (∫ x,torusFlow s p x*Real.log (torusFlow s p x) ∂torusMeasure 1)-
    ∑' n : ℕ,Real.exp (-2*(n+1:ℝ)*s)*(moment p (n+1))^2/(n+1:ℝ)

end BecknerOnofri.HighDim.CirclePoisson
