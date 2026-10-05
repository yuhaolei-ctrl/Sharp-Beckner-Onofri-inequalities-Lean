module

public import Legacy.BecknerOnofri.ClosedConvexSmoothSeries

@[expose] public section

/-! Termwise differentiation of a uniformly dominated series on a closed
interval, including its one-sided boundary derivatives. -/
namespace Legacy.BecknerOnofri.ClosedIntervalDerivativeSeries
open Set

theorem hasDerivWithinAt_tsum {ι : Type*} {f g : ι → ℝ → ℝ} {u v : ι → ℝ}
    (hu : Summable u) (hv : Summable v)
    (hf : ∀ i x, HasDerivAt (f i) (g i x) x)
    (hg : ∀ i, ContinuousOn (g i) (Icc (0 : ℝ) 1))
    (hfu : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖f i x‖ ≤ u i)
    (hgv : ∀ i x, x ∈ Icc (0 : ℝ) 1 → ‖g i x‖ ≤ v i)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun y => ∑' i, f i y) (∑' i, g i x) (Icc (0 : ℝ) 1) x := by
  have he : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo (by norm_num)
  have h := ClosedConvexSmoothSeries.hasFDerivWithinAt_tsum_closure isOpen_Ioo (convex_Ioo 0 1)
    hu hv (fun i y => (hf i y).hasFDerivAt)
    (fun i => by
      rw [he]
      exact ContinuousLinearMap.toSpanSingletonCLE.continuous.comp_continuousOn (hg i))
    (fun i y hy => hfu i y (he ▸ hy))
    (fun i y hy => by simpa using hgv i y (he ▸ hy)) (he ▸ hx)
  rw [he] at h
  have hm : ContinuousLinearMap.toSpanSingleton ℝ (∑' i, g i x) =
      ∑' i, ContinuousLinearMap.toSpanSingleton ℝ (g i x) :=
    ContinuousLinearMap.toSpanSingletonCLE.map_tsum
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, hm]
  exact h

#print axioms hasDerivWithinAt_tsum
end Legacy.BecknerOnofri.ClosedIntervalDerivativeSeries
