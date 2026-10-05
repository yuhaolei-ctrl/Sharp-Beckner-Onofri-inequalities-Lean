import Legacy.BecknerOnofri.FiniteDifferenceSmooth
import Mathlib.Analysis.Convex.Deriv

/-! Coordinate convexity from the actual nonnegative second partials on the
closed cube, including faces where other coordinates are on the boundary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff
namespace Legacy.BecknerOnofri.FiniteDifferences

theorem update_mem_closedCube {d : ℕ} {v : Space d} (hv : v ∈ closedCube d)
    (i : Fin d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : update v i t ∈ closedCube d := by
  constructor <;> intro j <;> by_cases hj : j = i
  · subst j; simpa using ht.1
  · simpa only [update_of_ne hj] using hv.1 j
  · subst j; simpa using ht.2
  · simpa only [update_of_ne hj] using hv.2 j

theorem coordinate_convex {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (i : Fin d)
    (h2 : ∀ y ∈ closedCube d, 0 ≤ mixedPartial [i,i] f y)
    {v : Space d} (hv : v ∈ closedCube d) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => f (update v i t)) := by
  have hmap : MapsTo (update v i) (Icc (0 : ℝ) 1) (closedCube d) :=
    fun t ht => update_mem_closedCube hv i ht
  have hc : Continuous (update v i) := by fun_prop
  have hd (g : Space d → ℝ) (hg : ContDiffOn ℝ ∞ g (closedCube d))
      (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (fun s => g (update v i s)) (coordinateDerivative i g (update v i t))
        (interior (Icc (0 : ℝ) 1)) t := by
    have h := hasDerivWithinAt_coordinate_of_contDiffOn hg i (hmap (interior_subset ht))
    simp only [update_idem, update_self] at h
    exact h.mono interior_subset
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (hf.continuousOn.comp hc.continuousOn hmap) (hd f hf)
    (hd (coordinateDerivative i f) (contDiffOn_coordinateDerivative hf i))
    (fun t ht => h2 _ (hmap (interior_subset ht)))

#print axioms coordinate_convex
end Legacy.BecknerOnofri.FiniteDifferences
