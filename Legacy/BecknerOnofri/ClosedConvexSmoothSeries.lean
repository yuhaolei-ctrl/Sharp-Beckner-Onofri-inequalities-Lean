module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-! Uniform derivative bounds on the closure of a convex open set give smooth
series on that closure, with genuine derivatives at boundary points. -/

open Set Filter
open scoped Topology ContDiff

namespace Legacy.BecknerOnofri.ClosedConvexSmoothSeries

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasFDerivWithinAt_tsum_closure {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u v : ι → ℝ}
    (hu : Summable u) (hv : Summable v)
    (hf : ∀ i x, HasFDerivAt (f i) (f' i x) x)
    (hcf' : ∀ i, ContinuousOn (f' i) (closure s))
    (hfu : ∀ i x, x ∈ closure s → ‖f i x‖ ≤ u i)
    (hfv : ∀ i x, x ∈ closure s → ‖f' i x‖ ≤ v i)
    {x : E} (hx : x ∈ closure s) :
    HasFDerivWithinAt (fun y => ∑' i, f i y) (∑' i, f' i x) (closure s) x := by
  have hd (y : E) (hy : y ∈ s) :
      HasFDerivAt (fun z => ∑' i, f i z) (∑' i, f' i y) y := by
    apply hasFDerivAt_tsum_of_isPreconnected hv hs hc.isPreconnected
      (fun i z _ => hf i z) (fun i z hz => hfv i z (subset_closure hz)) hy
    · exact hu.of_norm_bounded (fun i => hfu i y (subset_closure hy))
    · exact hy
  have hcontinuous : ContinuousOn (fun y => ∑' i, f i y) (closure s) :=
    continuousOn_tsum (fun i => (continuous_iff_continuousAt.mpr (fun y => (hf i y).continuousAt)).continuousOn) hu hfu
  have hcontinuous' : ContinuousOn (fun y => ∑' i, f' i y) (closure s) :=
    continuousOn_tsum hcf' hv hfv
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hc hs
    (fun y hy => (hcontinuous y hy).mono subset_closure)
  apply ((hcontinuous' x hx).mono subset_closure).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hd y hy).fderiv.symm

theorem contDiffOn_tsum_closure {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s)
    {f : ι → E → F} {u : ℕ → ι → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hu : ∀ m, Summable (u m))
    (hbound : ∀ m i x, x ∈ closure s → ‖iteratedFDeriv ℝ m (f i) x‖ ≤ u m i) :
    ContDiffOn ℝ ∞ (fun x => ∑' i, f i x) (closure s) := by
  let p (x : E) : FormalMultilinearSeries ℝ E F := fun m => ∑' i, iteratedFDeriv ℝ m (f i) x
  have hfinite (i : ι) (m : ℕ) : ContDiff ℝ (m : ℕ∞ω) (f i) :=
    (hf i).of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hcont (m : ℕ) (i : ι) : Continuous (iteratedFDeriv ℝ m (f i)) :=
    (hfinite i m).continuous_iteratedFDeriv le_rfl
  have hdiff (m : ℕ) (i : ι) : Differentiable ℝ (iteratedFDeriv ℝ m (f i)) :=
    (hfinite i (m+1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m)
  have hTaylor : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) (fun x => ∑' i, f i x) p (closure s) := by
    constructor
    · intro x _
      change (continuousMultilinearCurryFin0 ℝ E F) (∑' i, iteratedFDeriv ℝ 0 (f i) x) = _
      have hmap : (continuousMultilinearCurryFin0 ℝ E F) (∑' i, iteratedFDeriv ℝ 0 (f i) x) =
          ∑' i, (continuousMultilinearCurryFin0 ℝ E F) (iteratedFDeriv ℝ 0 (f i) x) :=
        (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum
      rw [hmap]
      apply tsum_congr
      intro i
      simp [continuousMultilinearCurryFin0_apply,
        iteratedFDeriv_zero_apply]
    · intro m _ x hx
      have ht := hasFDerivWithinAt_tsum_closure hs hc (hu m) (hu (m+1))
        (fun i y => (hdiff m i y).hasFDerivAt)
        (fun i => by
          rw [fderiv_iteratedFDeriv]
          exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).continuous.comp
            (hcont (m+1) i)).continuousOn)
        (hbound m) (fun i y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hbound (m+1) i y hy) hx
      change HasFDerivWithinAt (fun y => ∑' i, iteratedFDeriv ℝ m (f i) y)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F)
          (∑' i, iteratedFDeriv ℝ (m+1) (f i) x)) (closure s) x
      have hmap : (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F)
          (∑' i, iteratedFDeriv ℝ (m+1) (f i) x) =
          ∑' i, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F)
            (iteratedFDeriv ℝ (m+1) (f i) x) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).toContinuousLinearEquiv.map_tsum
      rw [hmap]
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using ht
    · intro m _
      exact continuousOn_tsum (fun i => (hcont m i).continuousOn) (hu m) (hbound m)
  exact hTaylor.contDiffOn

#print axioms hasFDerivWithinAt_tsum_closure
#print axioms contDiffOn_tsum_closure

end Legacy.BecknerOnofri.ClosedConvexSmoothSeries
