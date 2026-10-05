import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-! The actual finite rectangular forward difference, with no differentiability assumptions. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.FiniteDifferences

abbrev Index (d : ℕ) := Fin d →₀ ℕ
abbrev Space (d : ℕ) := Fin d → ℝ
abbrev DifferenceGrid {d : ℕ} (a : Index d) := ∀ i : Fin d, Fin (a i + 1)

def rectangularDifference {d : ℕ} (a : Index d) (h : ℝ)
    (f : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ j : DifferenceGrid a,
    (∏ i : Fin d, (-1 : ℝ) ^ (a i - (j i).val) * ((a i).choose (j i).val : ℝ)) *
      f (x + fun i => ((j i).val : ℝ) * h)

def degree {d : ℕ} (a : Index d) : ℕ := ∑ i, a i

def closedCube (d : ℕ) : Set (Space d) := Set.Icc 0 1

def basis {d : ℕ} (i : Fin d) : Space d := Pi.single i 1

def translate {d : ℕ} (x : Space d) (i : Fin d) (t : ℝ) : Space d :=
  x + t • basis i

@[simp] theorem translate_apply_same {d : ℕ} (x : Space d) (i : Fin d) (t : ℝ) :
    translate x i t i = x i + t := by simp [translate, basis]

@[simp] theorem translate_apply_ne {d : ℕ} (x : Space d) (i k : Fin d)
    (t : ℝ) (h : k ≠ i) : translate x i t k = x k := by simp [translate, basis, h]

#print axioms translate_apply_same
#print axioms translate_apply_ne

end Legacy.BecknerOnofri.FiniteDifferences
