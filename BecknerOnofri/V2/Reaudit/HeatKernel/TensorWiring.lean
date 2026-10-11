module

public import BecknerOnofri.V2.Reaudit.HeatKernel.KernelDomination
public import BecknerOnofri.GeneralEuler.CriticalComparison

@[expose] public section

/-! # Tensor, Mellin and weighted-operator layers on top of the new heat-kernel comparison
(U05/S015)

The legacy chain `heatKernel_nonnegative_all`, `heatKernel_le_dirichlet`, `heatKernel_lt_dirichlet`
→ tensor kernel comparison (`JacobiTensorHeatStrictComparison`) → Mellin kernel comparison
(`JacobiTensorMellinComparison`) → `GeneralEuler.CriticalComparison.higher_norm_lt_one` is
re-proved here with the same statements, the one-dimensional inputs being
`KernelDomination.heatKernel_nonneg_V2 / heatKernel_le_dirichlet_V2 / heatKernel_lt_dirichlet_V2`
(positive-operator/Schur-test route; no legacy maximum-principle declaration is used).
Statement identity with the legacy theorems is certified by `type_of%` equalities at the end.
-/

noncomputable section
open Set MeasureTheory Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiTensor Legacy.BecknerOnofri.JacobiHeatBounds
  Legacy.BecknerOnofri.JacobiHeatPositivity
open BecknerOnofri.V2.Reaudit.HeatKernel.Engine

/-! ### One coordinate -/

theorem oneKernel_nonnegative_V2 (m : ℕ) {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Icc 0 Real.pi) (hy : y ∈ Icc 0 Real.pi) : 0 ≤ heatKernel m t x y := by
  by_cases hm : m = 0
  · subst m
    exact (heatKernel_zero_pos ht x y).le
  · have hm' : 0 < m := Nat.pos_of_ne_zero hm
    by_cases hx0 : x = 0
    · subst hx0
      simp [heatKernel, JacobiEigenfunctions.normalizedFunction_zero hm']
    by_cases hxp : x = Real.pi
    · subst hxp
      simp [heatKernel, JacobiEigenfunctions.normalizedFunction_pi hm']
    by_cases hy0 : y = 0
    · subst hy0
      simp [heatKernel, JacobiEigenfunctions.normalizedFunction_zero hm']
    by_cases hyp : y = Real.pi
    · subst hyp
      simp [heatKernel, JacobiEigenfunctions.normalizedFunction_pi hm']
    exact heatKernel_nonneg_V2 hm' ht
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxp⟩
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hyp⟩

theorem heatKernel_lt_neumann_V2 {m : ℕ} (hm : 0 < m) {t x y : ℝ}
    (ht : 0 < t) (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    heatKernel m t x y < heatKernel 0 t x y :=
  (heatKernel_le_dirichlet_V2 hm ht hx hy).trans_lt (heatKernel_one_lt_zero ht x y)

/-! ### Tensor kernels -/

open Legacy.BecknerOnofri.JacobiTensorHeatKernel in
theorem kernel_nonnegative_V2 {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t)
    {x y : Space d} (hx : ∀ i, x i ∈ Icc 0 Real.pi) (hy : ∀ i, y i ∈ Icc 0 Real.pi) :
    0 ≤ kernel a t x y :=
  Finset.prod_nonneg (fun i _ => oneKernel_nonnegative_V2 (a i) ht (hx i) (hy i))

open Legacy.BecknerOnofri.JacobiTensorHeatKernel in
theorem kernel_le_boundary_V2 {d : ℕ} (a : Index d) {t : ℝ} (ht : 0 < t)
    {x y : Space d} (hx : x ∈ MixedBoundaryHeat.interiorCube d)
    (hy : y ∈ MixedBoundaryHeat.interiorCube d) :
    kernel a t x y ≤ kernel (boundaryIndex (activeCoordinates a)) t x y := by
  apply Finset.prod_le_prod₀ (fun i _ => oneKernel_nonnegative_V2 (a i) ht
    ⟨(hx i).1.le, (hx i).2.le⟩ ⟨(hy i).1.le, (hy i).2.le⟩)
  intro i hi
  by_cases ha : a i = 0
  · simp [boundaryIndex, mem_activeCoordinates, ha]
  · simpa [boundaryIndex, mem_activeCoordinates, ha] using
      heatKernel_le_dirichlet_V2 (Nat.pos_of_ne_zero ha) ht (hx i) (hy i)

open Legacy.BecknerOnofri.JacobiTensorHeatKernel in
theorem kernel_lt_single_V2 {d : ℕ} (a : Index d) (i : Fin d) (hai : 1 ≤ a i)
    (hne : a ≠ Pi.single i 1) {t : ℝ} (ht : 0 < t)
    {x y : Space d} (hx : x ∈ MixedBoundaryHeat.interiorCube d)
    (hy : y ∈ MixedBoundaryHeat.interiorCube d) :
    kernel a t x y < kernel (Pi.single i 1) t x y := by
  unfold kernel
  apply product_lt_of_right_positive
  · intro j hj
    exact oneKernel_nonnegative_V2 (a j) ht ⟨(hx j).1.le, (hx j).2.le⟩ ⟨(hy j).1.le, (hy j).2.le⟩
  · intro j hj
    exact single_factor_pos i j ht hx hy
  · intro j hj
    by_cases hji : j = i
    · subst j
      simpa using heatKernel_le_dirichlet_V2 (Nat.zero_lt_of_lt hai) ht (hx i) (hy i)
    · rw [Pi.single_eq_of_ne hji]
      by_cases haj : a j = 0
      · rw [haj]
      · exact (heatKernel_lt_neumann_V2 (Nat.pos_of_ne_zero haj) ht (hx j) (hy j)).le
  · obtain ⟨j, hj⟩ := not_forall.mp
      (show ¬∀ j, a j = (Pi.single i 1 : Index d) j from fun h => hne (funext h))
    refine ⟨j, Finset.mem_univ j, ?_⟩
    by_cases hji : j = i
    · subst j
      have hm : 2 ≤ a i := by simp only [Pi.single_eq_same] at hj; omega
      simpa using heatKernel_lt_dirichlet_V2 hm ht (hx i) (hy i)
    · rw [Pi.single_eq_of_ne hji] at hj ⊢
      exact heatKernel_lt_neumann_V2 (Nat.pos_of_ne_zero hj) ht (hx j) (hy j)

end BecknerOnofri.V2.Reaudit.HeatKernel.Wiring
