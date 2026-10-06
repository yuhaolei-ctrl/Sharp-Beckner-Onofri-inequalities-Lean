module

public import BecknerOnofri.ConditionalProfileDefinitions
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

/-! Actual coordinate partials on the closed cosine cube. -/
noncomputable section
namespace BecknerOnofri.HighDim

def cosinePartial {d : ℕ} (i : Fin d) (V : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderivWithin ℝ V (ConditionalEntropy.cosineCube d) x (Pi.single i 1)

end BecknerOnofri.HighDim
