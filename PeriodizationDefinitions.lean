module

public import BecknerOnofri.ElevenDefinitions
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

noncomputable section
namespace BecknerOnofri.Paper2.Periodization
abbrev E := Fin 11 → ℝ

def line (x : E) (i : Fin 11) (t : ℝ) : E := x + t • Pi.single i 1

def coordinatePartial (i : Fin 11) (f : E → ℝ) (x : E) : ℝ :=
  deriv (fun t => f (line x i t)) 0

def mixed : List (Fin 11) → (E → ℝ) → E → ℝ
  | [], f => f
  | i :: is, f => coordinatePartial i (mixed is f)

end BecknerOnofri.Paper2.Periodization
