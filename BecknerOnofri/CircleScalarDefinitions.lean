import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The piecewise quadratic appearing in the definition of γ in §5.2.
Here r will be t² and m the von Mises second moment. -/
namespace BecknerOnofri.HighDim.CircleScalar
noncomputable def cost (A B C D L r x : ℝ) : ℝ :=
  A*x^2+B*(x-r)^2+C*(max 0 (L-D*x))^2
noncomputable def candidateMinimum (A B C D L r m : ℝ) : ℝ :=
  min (min (cost A B C D L r m) (cost A B C D L r (max m (B*r/(A+B)))))
    (min (cost A B C D L r (max m ((B*r+C*D*L)/(A+B+C*D^2))))
      (cost A B C D L r (max m (L/D))))
end BecknerOnofri.HighDim.CircleScalar
