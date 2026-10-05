import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Trusted finite Euclidean lattice-rectangle definitions. -/
noncomputable section
open scoped BigOperators
open Finset
namespace BecknerOnofri.RectangleLattice

abbrev Lattice (d : ℕ) := Fin d → ℤ

def box {d : ℕ} (R : Fin d → ℕ) : Finset (Lattice d) :=
  Fintype.piFinset (fun i => Icc (-(R i : ℤ)) (R i : ℤ))

def puncturedBox {d : ℕ} (R : Fin d → ℕ) : Finset (Lattice d) :=
  (box R).filter (fun k => k ≠ 0)

def normSq {d : ℕ} (k : Lattice d) : ℝ := ∑ i : Fin d, (k i : ℝ) ^ 2

def weight {d : ℕ} (p : ℝ) (k : Lattice d) : ℝ := normSq k ^ (-(p / 2))

def latticeSum {d : ℕ} (p : ℝ) (R : Fin d → ℕ) : ℝ :=
  ∑ k ∈ puncturedBox R, weight p k

end BecknerOnofri.RectangleLattice
