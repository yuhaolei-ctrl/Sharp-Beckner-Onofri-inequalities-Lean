module

public import Legacy.BecknerOnofri.RadialWiener
public import Legacy.BecknerOnofri.ChebyshevDerivativeBound

@[expose] public section

/-! The actual tensor-Chebyshev profile of a full lattice Fourier series. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.ChebyshevProfile

open Legacy.TorusEndpoint

abbrev Space (d : ℕ) := Fin d → ℝ

def closedCube (d : ℕ) : Set (Space d) := Set.Icc (-1) 1

def openCube (d : ℕ) : Set (Space d) :=
  Set.pi Set.univ (fun _ => Set.Ioo (-1 : ℝ) 1)

noncomputable def tensor {d : ℕ} (k : Frequency d) (z : Space d) : ℝ :=
  ∏ i, (Polynomial.Chebyshev.T ℝ (Int.natAbs (k i) : ℤ)).eval (z i)

noncomputable def profile {d : ℕ} (a : Frequency d → ℂ) (z : Space d) : ℝ :=
  ∑' k, (a k).re * tensor k z

theorem mem_closedCube {d : ℕ} {z : Space d} :
    z ∈ closedCube d ↔ ∀ i, z i ∈ Set.Icc (-1 : ℝ) 1 := by
  simp only [closedCube, Set.mem_Icc, Pi.le_def, Pi.neg_apply, Pi.one_apply]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem openCube_isOpen (d : ℕ) : IsOpen (openCube d) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem openCube_convex (d : ℕ) : Convex ℝ (openCube d) :=
  convex_pi (fun _ _ => convex_Ioo (-1 : ℝ) 1)

theorem closure_openCube (d : ℕ) : closure (openCube d) = closedCube d := by
  rw [openCube, closure_pi_set]
  simp only [closure_Ioo (by norm_num : (-1:ℝ)≠1)]
  exact Set.pi_univ_Icc _ _

end Legacy.BecknerOnofri.ChebyshevProfile
