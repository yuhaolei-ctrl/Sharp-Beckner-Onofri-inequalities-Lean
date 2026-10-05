import BecknerOnofri.RectangleInduction
import BecknerOnofri.SpectralSliceBound

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace BecknerOnofri.RectangleLattice

/-- The actual analytic slice hypothesis follows from the proved Jacobi–Mellin
spectral estimate; no spectral bound is assumed. -/
theorem sliceBound {d : ℕ} (hd : 12 ≤ d) : SliceBound d := by
  intro q hq R
  simpa only [neg_div] using SpectralSlice.finite_slice (by exact_mod_cast hd) hq R

/-- The complete rectangular lattice inequality in every dimension d≥13. -/
theorem rectangle_comparison {d : ℕ} (hd : 13 ≤ d) (R : Fin d → ℕ) :
    latticeSum (d : ℝ) R ≤ (1 / ((d : ℝ) - 1)) *
      (∑ i : Fin d, latticeSum ((d : ℝ) - 1) (Function.update R i 0)) :=
  rectangle_comparison_of_slice hd (sliceBound (by omega)) R

#print axioms rectangle_comparison

end BecknerOnofri.RectangleLattice
