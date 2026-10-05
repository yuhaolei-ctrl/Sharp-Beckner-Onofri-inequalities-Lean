import Legacy.TorusEndpoint.GreenMultiplierSummability
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-! Finite coordinate boxes, independent of low-dimensional polynomial certificates. -/

namespace Legacy.BecknerOnofri.SobolevLattice
open Legacy.TorusEndpoint

noncomputable def latticeBox (d n : ℕ) : Finset (Frequency d) := by
  classical
  exact Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) (n : ℤ))

theorem mem_latticeBox {d n : ℕ} (k : Frequency d) :
    k ∈ latticeBox d n ↔ ∀ i, (k i).natAbs ≤ n := by
  classical
  simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  apply forall_congr'
  intro i
  omega

end Legacy.BecknerOnofri.SobolevLattice
