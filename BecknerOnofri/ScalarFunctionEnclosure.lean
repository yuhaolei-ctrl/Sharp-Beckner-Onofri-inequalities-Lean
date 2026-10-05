import BecknerOnofri.ScalarRationalInterval
import BecknerOnofri.ScalarSlopeEnclosure

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

structure FunctionEnclosure (a b : ℝ) (f : ℝ → ℝ) where
  value : RationalInterval
  slope : RationalInterval
  value_mem : ∀ x ∈ Icc a b,value.Contains (f x)
  slope_bounds : SlopeBounds (Icc a b) f slope.lower slope.upper

noncomputable def FunctionEnclosure.const (a b : ℝ) (q : ℚ) :
    FunctionEnclosure a b (fun _ => (q : ℝ)) where
  value := ⟨q,q⟩
  slope := ⟨0,0⟩
  value_mem := fun _ _ => ⟨le_rfl,le_rfl⟩
  slope_bounds := by simpa only [Rat.cast_zero] using slopeBounds_const (Icc a b) (q : ℝ)

noncomputable def FunctionEnclosure.add {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => f x+g x) where
  value := ef.value.add eg.value
  slope := ef.slope.add eg.slope
  value_mem := fun x hx => RationalInterval.contains_add (ef.value_mem x hx) (eg.value_mem x hx)
  slope_bounds := by
    simpa only [RationalInterval.add,Rat.cast_add] using ef.slope_bounds.add eg.slope_bounds

noncomputable def FunctionEnclosure.neg {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) : FunctionEnclosure a b (fun x => -f x) where
  value := ef.value.neg
  slope := ef.slope.neg
  value_mem := fun x hx => RationalInterval.contains_neg (ef.value_mem x hx)
  slope_bounds := by
    simpa only [RationalInterval.neg,Rat.cast_neg] using ef.slope_bounds.neg

theorem FunctionEnclosure.secant_mem {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b)
    (hxy : x<y) : ef.slope.Contains ((f y-f x)/(y-x)) := by
  have h := ef.slope_bounds x hx y hy hxy.le
  exact ⟨(le_div_iff₀ (sub_pos.mpr hxy)).mpr h.1,
    (div_le_iff₀ (sub_pos.mpr hxy)).mpr h.2⟩

noncomputable def FunctionEnclosure.mul {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => f x*g x) where
  value := ef.value.mul eg.value
  slope := (ef.slope.mul eg.value).add (ef.value.mul eg.slope)
  value_mem := fun x hx => RationalInterval.contains_mul (ef.value_mem x hx) (eg.value_mem x hx)
  slope_bounds := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl|hxy
    · simp
    have hd := sub_pos.mpr hxy
    have h1 := RationalInterval.contains_mul (ef.secant_mem hx hy hxy) (eg.value_mem x hx)
    have h2 := RationalInterval.contains_mul (ef.value_mem y hy) (eg.secant_mem hx hy hxy)
    have h := RationalInterval.contains_add h1 h2
    have he : ((f y-f x)/(y-x))*g x+f y*((g y-g x)/(y-x))=
        (f y*g y-f x*g x)/(y-x) := by ring
    rw [he] at h
    exact ⟨(le_div_iff₀ hd).mp h.1,(div_le_iff₀ hd).mp h.2⟩

noncomputable def FunctionEnclosure.pointwiseMin {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => min (f x) (g x)) where
  value := ef.value.hull eg.value
  slope := ef.slope.hull eg.slope
  value_mem := by
    intro x hx
    by_cases h : f x≤g x
    · rw [min_eq_left h]
      exact RationalInterval.contains_hull_left (ef.value_mem x hx)
    · rw [min_eq_right (le_of_not_ge h)]
      exact RationalInterval.contains_hull_right (eg.value_mem x hx)
  slope_bounds := by
    simpa only [RationalInterval.hull,Rat.cast_min,Rat.cast_max] using
      ef.slope_bounds.pointwise_min eg.slope_bounds

noncomputable def FunctionEnclosure.pointwiseMax {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (eg : FunctionEnclosure a b g) :
    FunctionEnclosure a b (fun x => max (f x) (g x)) where
  value := ef.value.hull eg.value
  slope := ef.slope.hull eg.slope
  value_mem := by
    intro x hx
    by_cases h : f x≤g x
    · rw [max_eq_right h]
      exact RationalInterval.contains_hull_right (eg.value_mem x hx)
    · rw [max_eq_left (le_of_not_ge h)]
      exact RationalInterval.contains_hull_left (ef.value_mem x hx)
  slope_bounds := by
    simpa only [RationalInterval.hull,Rat.cast_min,Rat.cast_max] using
      ef.slope_bounds.pointwise_max eg.slope_bounds

#print axioms FunctionEnclosure.mul
#print axioms FunctionEnclosure.pointwiseMin
end BecknerOnofri.HighDim.ScalarCertificate
