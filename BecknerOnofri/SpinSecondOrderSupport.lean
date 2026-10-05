import BecknerOnofri.SpinSegmentCalculus

/-! A scalar second-order support theorem with continuity at the boundary.
No differentiability of the far endpoint is required. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.Spin

theorem second_order_support {f f' f'' : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (h0 : HasDerivAt f (f' 0) 0)
    (h1 : ∀ t ∈ Ioo (0:ℝ) 1,HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Ioo (0:ℝ) 1,HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1,c≤f'' t) :
    f 0+f' 0+c/2≤f 1 := by
  let g : ℝ → ℝ := fun t => f t-(c/2)*t^2
  have hd (t : ℝ) : HasDerivAt (fun a : ℝ => (c/2)*a^2) (c*t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (c/2) using 1 <;> first | rfl | (norm_num; ring)
  have hc : ConvexOn ℝ (Icc 0 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f':=fun t => f' t-c*t)
      (f'':=fun t => f'' t-c) (convex_Icc 0 1)
    · exact hf.sub ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
    · intro t ht
      rw [interior_Icc] at ht
      exact ((h1 t ht).sub (hd t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      convert ((h2 t ht).sub ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt
        (s:=interior (Icc (0:ℝ) 1)) using 1 <;> first | rfl | simp
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonneg.mpr (hbound t ht)
  have hg0 : HasDerivAt g (f' 0) 0 := by
    convert h0.sub (hd 0) using 1 <;> first | rfl | simp [g]
  have h := hc.le_slope_of_hasDerivAt (x:=0) (y:=1) (by norm_num) (by norm_num) (by norm_num) hg0
  simp [slope,g] at h
  linarith

#print axioms second_order_support
end BecknerOnofri.HighDim.Spin
