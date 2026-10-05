import BecknerOnofri.CosineShapeDefinitions
import Legacy.BecknerOnofri.FiniteDifferenceSmooth
import Mathlib.Analysis.Convex.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff
namespace BecknerOnofri.HighDim.CosineShape
open ConditionalEntropy

theorem uniqueDiffOn_cosineCube (d : ℕ) : UniqueDiffOn ℝ (cosineCube d) := by
  have hh := UniqueDiffOn.univ_pi (fun _ : Fin d => (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ)<1)))
  have he : cosineCube d = Set.pi Set.univ (fun _ : Fin d => Icc (-1 : ℝ) 1) := by
    ext x
    simp only [cosineCube, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [he]
  exact hh


theorem contDiffOn_cosinePartial {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cosineCube d)) (i : Fin d) :
    ContDiffOn ℝ ∞ (cosinePartial i f) (cosineCube d) := by
  have hd := hf.fderivWithin (uniqueDiffOn_cosineCube d) (m := ∞) (by simp)
  exact hd.clm_apply contDiffOn_const


theorem hasDerivWithinAt_coordinate_of_contDiffOn {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cosineCube d)) (i : Fin d) {x : (Fin d → ℝ)}
    (hx : x ∈ cosineCube d) :
    HasDerivWithinAt (fun t => f (Function.update x i t))
      (cosinePartial i f x) (Icc (-1 : ℝ) 1) (x i) := by
  have hd := (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hm : MapsTo (Function.update x i) (Icc (-1 : ℝ) 1) (cosineCube d) := by
    intro t ht
    constructor <;> intro k <;> by_cases hk : k = i
    · subst k; simpa using ht.1
    · simpa [Function.update_of_ne hk] using hx.1 k
    · subst k; simpa using ht.2
    · simpa [Function.update_of_ne hk] using hx.2 k
  have hc := hd.comp_hasDerivWithinAt_of_eq (x i)
    (hasDerivAt_update x i (x i)).hasDerivWithinAt hm (Function.update_eq_self i x).symm
  exact hc


theorem update_mem_cosineCube {d : ℕ} {v : (Fin d → ℝ)} (hv : v ∈ cosineCube d)
    (i : Fin d) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : update v i t ∈ cosineCube d := by
  constructor <;> intro j <;> by_cases hj : j = i
  · subst j; simpa using ht.1
  · simpa only [update_of_ne hj] using hv.1 j
  · subst j; simpa using ht.2
  · simpa only [update_of_ne hj] using hv.2 j

theorem coordinate_convex {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cosineCube d)) (i : Fin d)
    (h2 : ∀ y ∈ cosineCube d, 0 ≤ cosinePartial i (cosinePartial i f) y)
    {v : (Fin d → ℝ)} (hv : v ∈ cosineCube d) :
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t => f (update v i t)) := by
  have hmap : MapsTo (update v i) (Icc (-1 : ℝ) 1) (cosineCube d) :=
    fun t ht => update_mem_cosineCube hv i ht
  have hc : Continuous (update v i) := by fun_prop
  have hd (g : (Fin d → ℝ) → ℝ) (hg : ContDiffOn ℝ ∞ g (cosineCube d))
      (t : ℝ) (ht : t ∈ interior (Icc (-1 : ℝ) 1)) :
      HasDerivWithinAt (fun s => g (update v i s)) (cosinePartial i g (update v i t))
        (interior (Icc (-1 : ℝ) 1)) t := by
    have h := hasDerivWithinAt_coordinate_of_contDiffOn hg i (hmap (interior_subset ht))
    simp only [update_idem, update_self] at h
    exact h.mono interior_subset
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (hf.continuousOn.comp hc.continuousOn hmap) (hd f hf)
    (hd (cosinePartial i f) (contDiffOn_cosinePartial hf i))
    (fun t ht => h2 _ (hmap (interior_subset ht)))


theorem coordinate_monotone {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (cosineCube d)) (i : Fin d)
    (h1 : ∀ y∈cosineCube d,0≤cosinePartial i f y)
    {v : Fin d → ℝ} (hv : v∈cosineCube d) :
    MonotoneOn (fun t => f (update v i t)) (Icc (-1 : ℝ) 1) := by
  have hmap : MapsTo (update v i) (Icc (-1 : ℝ) 1) (cosineCube d) :=
    fun t ht => update_mem_cosineCube hv i ht
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (hf.continuousOn.comp (by fun_prop) hmap)
  · intro t ht
    have h := hasDerivWithinAt_coordinate_of_contDiffOn hf i (hmap (interior_subset ht))
    simp only [update_idem,update_self] at h
    exact h.mono interior_subset
  · intro t ht
    exact h1 _ (hmap (interior_subset ht))

#print axioms coordinate_convex
#print axioms coordinate_monotone
end BecknerOnofri.HighDim.CosineShape
