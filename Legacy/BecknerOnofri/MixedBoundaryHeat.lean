module

public import Legacy.BecknerOnofri.CircleBoundaryHeat

@[expose] public section

/-! Actual product heat kernels on (0,pi)^d: Neumann in inactive coordinates,
Dirichlet in active coordinates. Strict comparison uses a genuine reflected heat factor. -/
noncomputable section
open Set
open scoped BigOperators
namespace Legacy.BecknerOnofri.MixedBoundaryHeat
open CircleHeat

def interiorCube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Ioo (0:ℝ) Real.pi}

def kernel {d : ℕ} (active : Finset (Fin d)) (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, if i ∈ active then dirichletPiHeat t (x i) (y i) else neumannPiHeat t (x i) (y i)

def neumannKernel {d : ℕ} (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, neumannPiHeat t (x i) (y i)

theorem kernel_empty {d : ℕ} (t : ℝ) (x y : Fin d → ℝ) : kernel ∅ t x y = neumannKernel t x y := by
  simp [kernel,neumannKernel]

theorem factor_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (active : Finset (Fin d))
    {x y : Fin d → ℝ} (hx : x ∈ interiorCube d) (hy : y ∈ interiorCube d) (i : Fin d) :
    0 < if i ∈ active then dirichletPiHeat t (x i) (y i) else neumannPiHeat t (x i) (y i) := by
  split_ifs
  · exact dirichletPiHeat_pos ht (hx i) (hy i)
  · exact neumannPiHeat_pos ht _ _

theorem kernel_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (active : Finset (Fin d))
    {x y : Fin d → ℝ} (hx : x ∈ interiorCube d) (hy : y ∈ interiorCube d) : 0 < kernel active t x y :=
  Finset.prod_pos (fun i _ => factor_pos ht active hx hy i)

theorem neumannKernel_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (x y : Fin d → ℝ) : 0 < neumannKernel t x y :=
  Finset.prod_pos (fun i _ => neumannPiHeat_pos ht (x i) (y i))

theorem kernel_le_neumann {d : ℕ} {t : ℝ} (ht : 0 < t) (active : Finset (Fin d))
    {x y : Fin d → ℝ} (hx : x ∈ interiorCube d) (hy : y ∈ interiorCube d) :
    kernel active t x y ≤ neumannKernel t x y := by
  apply Finset.prod_le_prod₀ (fun i _ => (factor_pos ht active hx hy i).le)
  intro i _
  split_ifs
  · exact (dirichletPiHeat_lt_neumann ht _ _).le
  · exact le_rfl

theorem kernel_lt_neumann {d : ℕ} {t : ℝ} (ht : 0 < t) (active : Finset (Fin d))
    (hactive : active.Nonempty) {x y : Fin d → ℝ}
    (hx : x ∈ interiorCube d) (hy : y ∈ interiorCube d) :
    kernel active t x y < neumannKernel t x y := by
  apply Finset.prod_lt_prod₀ (fun i _ => factor_pos ht active hx hy i)
  · intro i _
    split_ifs
    · exact (dirichletPiHeat_lt_neumann ht _ _).le
    · exact le_rfl
  · obtain ⟨i,hi⟩ := hactive
    exact ⟨i,Finset.mem_univ i,by rw [if_pos hi]; exact dirichletPiHeat_lt_neumann ht _ _⟩

theorem kernel_antitone_active {d : ℕ} {t : ℝ} (ht : 0 < t) {active larger : Finset (Fin d)}
    (hsub : active ⊆ larger) {x y : Fin d → ℝ} (hx : x ∈ interiorCube d) (hy : y ∈ interiorCube d) :
    kernel larger t x y ≤ kernel active t x y := by
  apply Finset.prod_le_prod₀ (fun i _ => (factor_pos ht larger hx hy i).le)
  intro i _
  by_cases hi : i ∈ active
  · rw [if_pos hi,if_pos (hsub hi)]
  · rw [if_neg hi]
    split_ifs
    · exact (dirichletPiHeat_lt_neumann ht _ _).le
    · exact le_rfl

#print axioms kernel_pos
#print axioms kernel_lt_neumann
end Legacy.BecknerOnofri.MixedBoundaryHeat
