import BecknerOnofri.BranchDefinitions

/-! The Euclidean norm of the complete first nonzero Fourier shell.
The two frequencies for coordinate i are e_i and -e_i. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim

def firstShellOrderParameter {d : ℕ} (f : Torus d → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin d,
    (‖fourierCoeff f (axisFrequency i)‖^2 + ‖fourierCoeff f (-axisFrequency i)‖^2))

end BecknerOnofri.HighDim
