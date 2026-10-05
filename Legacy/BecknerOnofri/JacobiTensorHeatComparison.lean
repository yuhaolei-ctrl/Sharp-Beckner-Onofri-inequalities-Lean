module

public import Legacy.BecknerOnofri.JacobiTensorHeatKernel
public import Legacy.BecknerOnofri.JacobiHeatNonnegative
public import Legacy.BecknerOnofri.JacobiCircleHeat
public import Legacy.BecknerOnofri.MixedBoundaryHeat

@[expose] public section

/-! Genuine positivity of the actual tensor heat kernel, including Neumann coordinates. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorHeatKernel
open JacobiTensor JacobiHeatBounds

theorem oneKernel_nonnegative (m : ℕ) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Icc 0 Real.pi) (hy : y ∈ Icc 0 Real.pi) :
    0 ≤ heatKernel m t x y := by
  by_cases hm : m = 0
  · subst m
    exact (heatKernel_zero_pos ht x y).le
  · exact JacobiHeatPositivity.heatKernel_nonnegative (Nat.pos_of_ne_zero hm) ht hx hy

theorem kernel_nonnegative {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t)
    {x y : Space d} (hx : ∀ i, x i ∈ Icc 0 Real.pi) (hy : ∀ i, y i ∈ Icc 0 Real.pi) :
    0 ≤ kernel a t x y :=
  Finset.prod_nonneg (fun i _ => oneKernel_nonnegative (a i) ht (hx i) (hy i))

theorem kernel_nonnegative_ae {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ z ∂(JacobiTensor.measure d).prod (JacobiTensor.measure d), 0 ≤ kernel a t z.1 z.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hx hy
  exact kernel_nonnegative a ht (fun i => ⟨(hx i).1.le,(hx i).2.le⟩)
    (fun i => ⟨(hy i).1.le,(hy i).2.le⟩)

theorem heatOperator_nonnegative {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t)
    (u : TensorL2 d) (hu : ∀ᵐ x ∂JacobiTensor.measure d, 0 ≤ u x) :
    ∀ᵐ x ∂JacobiTensor.measure d, 0 ≤ heatOperator a t u x := by
  filter_upwards [kernel_representation a ht u, ae_mem_box d] with x hx hxi
  rw [← hx.2]
  apply integral_nonneg_of_ae
  filter_upwards [hu, ae_mem_box d] with y hy hyi
  exact mul_nonneg (kernel_nonnegative a ht (fun i => ⟨(hxi i).1.le,(hxi i).2.le⟩)
    (fun i => ⟨(hyi i).1.le,(hyi i).2.le⟩)) hy

def boundaryIndex {d : ℕ} (active : Finset (Fin d)) : Index d := fun i => if i ∈ active then 1 else 0

theorem boundary_kernel {d : ℕ} (active : Finset (Fin d)) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    kernel (boundaryIndex active) t x y = MixedBoundaryHeat.kernel active t x y := by
  unfold kernel MixedBoundaryHeat.kernel boundaryIndex
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · exact heatKernel_one_eq_dirichlet ht _ _
  · exact heatKernel_zero_eq_neumann ht _ _

theorem kernel_zero_eq_neumann {d : ℕ} {t : ℝ} (ht : 0 < t) (x y : Space d) :
    kernel (0 : Index d) t x y = MixedBoundaryHeat.neumannKernel t x y := by
  have h0 : boundaryIndex (∅ : Finset (Fin d)) = 0 := by
    funext i
    simp [boundaryIndex]
  simpa only [h0, MixedBoundaryHeat.kernel_empty]
    using boundary_kernel (∅ : Finset (Fin d)) ht x y

theorem boundary_kernel_pos {d : ℕ} (active : Finset (Fin d)) {t : ℝ} (ht : 0 < t)
    {x y : Space d} (hx : x ∈ MixedBoundaryHeat.interiorCube d)
    (hy : y ∈ MixedBoundaryHeat.interiorCube d) : 0 < kernel (boundaryIndex active) t x y := by
  rw [boundary_kernel active ht]
  exact MixedBoundaryHeat.kernel_pos ht active hx hy

theorem boundary_kernel_lt_neumann {d : ℕ} (active : Finset (Fin d))
    (ha : active.Nonempty) {t : ℝ} (ht : 0 < t) {x y : Space d}
    (hx : x ∈ MixedBoundaryHeat.interiorCube d) (hy : y ∈ MixedBoundaryHeat.interiorCube d) :
    kernel (boundaryIndex active) t x y < kernel 0 t x y := by
  rw [boundary_kernel active ht, kernel_zero_eq_neumann ht]
  exact MixedBoundaryHeat.kernel_lt_neumann ht active ha hx hy

#print axioms kernel_nonnegative
#print axioms heatOperator_nonnegative
#print axioms boundary_kernel_lt_neumann
end Legacy.BecknerOnofri.JacobiTensorHeatKernel
