import BecknerOnofri.ConditionalEntropyDefinitions
import Mathlib.Analysis.Convex.Function

noncomputable section
namespace BecknerOnofri.HighDim.ConditionalEntropy

def cosineCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.Icc (fun _ => -1) (fun _ => 1)

def cosineVector {d : ℕ} (x : Torus d) : Fin d → ℝ :=
  fun j => (fourier 1 (x j)).re

end BecknerOnofri.HighDim.ConditionalEntropy
