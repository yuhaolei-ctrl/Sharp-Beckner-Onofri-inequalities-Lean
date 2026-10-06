module

public import Legacy.BecknerOnofri.JacobiTensorHeatComparison
public import Legacy.BecknerOnofri.JacobiHeatStrictComparison

@[expose] public section

/-! Genuine product-kernel comparison with the single-active-coordinate baseline. -/
noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace Legacy.BecknerOnofri.JacobiTensorHeatKernel
open JacobiTensor JacobiHeatBounds JacobiHeatPositivity

theorem product_lt_of_right_positive {β : Type*} (F : Finset β) (f g : β→ℝ)
    (hf : ∀i∈F,0≤f i) (hg : ∀i∈F,0<g i) (hle : ∀i∈F,f i≤g i)
    (hlt : ∃i∈F,f i<g i) : ∏i∈F,f i < ∏i∈F,g i := by
  by_cases hp : ∀i∈F,0<f i
  · exact Finset.prod_lt_prod₀ hp hle hlt
  · push_neg at hp
    obtain ⟨i,hi,hfi⟩ := hp
    have hz : f i=0 := le_antisymm hfi (hf i hi)
    rw [Finset.prod_eq_zero hi hz]
    exact Finset.prod_pos hg

def activeCoordinates {d : ℕ} (a : Index d) : Finset (Fin d) := Finset.univ.filter (fun i => a i≠0)

@[simp] theorem mem_activeCoordinates {d : ℕ} (a : Index d) (i : Fin d) :
    i∈activeCoordinates a ↔ a i≠0 := by simp [activeCoordinates]

theorem activeCoordinates_nonempty {d : ℕ} (a : Index d) (ha : a≠0) :
    (activeCoordinates a).Nonempty := by
  obtain ⟨i,hi⟩ := not_forall.mp (show ¬∀i,a i=(0:Index d) i from fun h => ha (funext h))
  exact ⟨i,(mem_activeCoordinates a i).mpr hi⟩

/-- The baseline has Dirichlet in every active coordinate and Neumann elsewhere. -/
theorem kernel_le_boundary {d : ℕ} (a : Index d) {t : ℝ} (ht : 0<t)
    {x y : Space d} (hx : x∈MixedBoundaryHeat.interiorCube d) (hy : y∈MixedBoundaryHeat.interiorCube d) :
    kernel a t x y≤kernel (boundaryIndex (activeCoordinates a)) t x y := by
  apply Finset.prod_le_prod₀ (fun i _ => heatKernel_nonnegative_all (a i) ht (hx i) (hy i))
  intro i hi
  by_cases ha : a i=0
  · simp [boundaryIndex,mem_activeCoordinates,ha]
  · simpa [boundaryIndex,mem_activeCoordinates,ha] using
      heatKernel_le_dirichlet (Nat.pos_of_ne_zero ha) ht (hx i) (hy i)

/-- Every nonzero activity index is strictly below the all-Neumann actual tensor kernel. -/
theorem kernel_lt_all_neumann {d : ℕ} (a : Index d) (ha : a≠0) {t : ℝ} (ht : 0<t)
    {x y : Space d} (hx : x∈MixedBoundaryHeat.interiorCube d) (hy : y∈MixedBoundaryHeat.interiorCube d) :
    kernel a t x y<kernel (0:Index d) t x y :=
  (kernel_le_boundary a ht hx hy).trans_lt
    (boundary_kernel_lt_neumann _ (activeCoordinates_nonempty a ha) ht hx hy)

/-- Each factor of the single-coordinate baseline is genuinely strictly positive. -/
theorem single_factor_pos {d : ℕ} (i j : Fin d) {t : ℝ} (ht : 0<t)
    {x y : Space d} (hx : x∈MixedBoundaryHeat.interiorCube d) (hy : y∈MixedBoundaryHeat.interiorCube d) :
    0<heatKernel ((Pi.single i 1 : Index d) j) t (x j) (y j) := by
  by_cases hj : j=i
  · subst j
    simpa using heatKernel_one_pos ht (hx i) (hy i)
  · simpa [Pi.single_eq_of_ne hj] using heatKernel_zero_pos ht (x j) (y j)

theorem kernel_single_pos {d : ℕ} (i : Fin d) {t : ℝ} (ht : 0<t)
    {x y : Space d} (hx : x∈MixedBoundaryHeat.interiorCube d) (hy : y∈MixedBoundaryHeat.interiorCube d) :
    0<kernel (Pi.single i 1) t x y :=
  Finset.prod_pos (fun j _ => single_factor_pos i j ht hx hy)

/-- The actual tensor kernel for a higher mixed index is strictly below a first-index kernel.
A larger order in the selected coordinate or an additional active coordinate supplies the gap. -/
theorem kernel_lt_single {d : ℕ} (a : Index d) (i : Fin d) (hai : 1≤a i)
    (hne : a≠Pi.single i 1) {t : ℝ} (ht : 0<t)
    {x y : Space d} (hx : x∈MixedBoundaryHeat.interiorCube d) (hy : y∈MixedBoundaryHeat.interiorCube d) :
    kernel a t x y<kernel (Pi.single i 1) t x y := by
  unfold kernel
  apply product_lt_of_right_positive
  · intro j hj
    exact heatKernel_nonnegative_all (a j) ht (hx j) (hy j)
  · intro j hj
    exact single_factor_pos i j ht hx hy
  · intro j hj
    by_cases hji : j=i
    · subst j
      simpa using heatKernel_le_dirichlet (Nat.zero_lt_of_lt hai) ht (hx i) (hy i)
    · rw [Pi.single_eq_of_ne hji]
      by_cases haj : a j=0
      · rw [haj]
      · exact (heatKernel_lt_neumann (Nat.pos_of_ne_zero haj) ht (hx j) (hy j)).le
  · obtain ⟨j,hj⟩ := not_forall.mp
      (show ¬∀j,a j=(Pi.single i 1 : Index d) j from fun h => hne (funext h))
    refine ⟨j,Finset.mem_univ j,?_⟩
    by_cases hji : j=i
    · subst j
      have hm : 2≤a i := by simp only [Pi.single_eq_same] at hj; omega
      simpa using heatKernel_lt_dirichlet hm ht (hx i) (hy i)
    · rw [Pi.single_eq_of_ne hji] at hj ⊢
      exact heatKernel_lt_neumann (Nat.pos_of_ne_zero hj) ht (hx j) (hy j)

/-- The strict comparison holds almost everywhere for the genuine product Lebesgue measure. -/
theorem kernel_lt_single_ae {d : ℕ} (a : Index d) (i : Fin d) (hai : 1≤a i)
    (hne : a≠Pi.single i 1) {t : ℝ} (ht : 0<t) :
    ∀ᵐz∂(JacobiTensor.measure d).prod (JacobiTensor.measure d),
      kernel a t z.1 z.2<kernel (Pi.single i 1) t z.1 z.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_mem_box d),
    Measure.quasiMeasurePreserving_snd.ae (ae_mem_box d)] with z hx hy
  exact kernel_lt_single a i hai hne ht hx hy

#print axioms kernel_le_boundary
#print axioms kernel_lt_single
#print axioms kernel_lt_single_ae
end Legacy.BecknerOnofri.JacobiTensorHeatKernel
