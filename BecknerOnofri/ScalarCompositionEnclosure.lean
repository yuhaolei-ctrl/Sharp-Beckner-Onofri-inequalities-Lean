module

public import BecknerOnofri.ScalarReciprocalEnclosure
public import BecknerOnofri.EntropyCheckedLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set EntropyLogCertificate

/-- The secant bound holds in either order of its two arguments. -/
theorem FunctionEnclosure.secant_mem_ne {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) {x y : ℝ} (hx : x∈Icc a b) (hy : y∈Icc a b)
    (hxy : x≠y) : ef.slope.Contains ((f y-f x)/(y-x)) := by
  rcases lt_or_gt_of_ne hxy with h|h
  · exact ef.secant_mem hx hy h
  · have he : (f y-f x)/(y-x)=(f x-f y)/(x-y) := by
      rw [← neg_sub (f y), ← neg_sub y, neg_div_neg_eq]
    rw [he]
    exact ef.secant_mem hy hx h

noncomputable def FunctionEnclosure.comp {a b : ℝ} {f g : ℝ → ℝ}
    (ef : FunctionEnclosure a b f)
    (eg : FunctionEnclosure ef.value.lower ef.value.upper g)
    (hs : eg.slope.lower≤eg.slope.upper) :
    FunctionEnclosure a b (fun x => g (f x)) where
  value := eg.value
  slope := eg.slope.mul ef.slope
  value_mem := fun x hx => eg.value_mem (f x) (ef.value_mem x hx)
  slope_bounds := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl|hxy
    · simp
    have hd := sub_pos.mpr hxy
    by_cases heq : f x=f y
    · have hzero : ef.slope.Contains (0 : ℝ) := by
        have h := ef.secant_mem hx hy hxy
        simpa only [heq,sub_self,zero_div] using h
      have hnonempty : (eg.slope.lower : ℝ)≤eg.slope.upper := by exact_mod_cast hs
      have hout : eg.slope.Contains (eg.slope.lower : ℝ) := ⟨le_rfl,hnonempty⟩
      have h := RationalInterval.contains_mul hout hzero
      simpa only [heq,sub_self,mul_zero,zero_mul] using
        And.intro (mul_le_mul_of_nonneg_right h.1 hd.le) (mul_le_mul_of_nonneg_right h.2 hd.le)
    · have h := RationalInterval.contains_mul
        (eg.secant_mem_ne (ef.value_mem x hx) (ef.value_mem y hy) heq)
        (ef.secant_mem hx hy hxy)
      have he : ((g (f y)-g (f x))/(f y-f x))*((f y-f x)/(y-x))=
          (g (f y)-g (f x))/(y-x) := by
        field_simp [sub_ne_zero.mpr (Ne.symm heq)]
      rw [he] at h
      exact ⟨(le_div_iff₀ hd).mp h.1,(div_le_iff₀ hd).mp h.2⟩

noncomputable def logFunctionEnclosure (l u : CheckedLog) (hl : 0<l.value) :
    FunctionEnclosure l.value u.value Real.log where
  value := ⟨l.lower,u.upper⟩
  slope := ⟨u.value⁻¹,l.value⁻¹⟩
  value_mem := by
    intro x hx
    have hl0 : (0 : ℝ)<l.value := by exact_mod_cast hl
    have hx0 := hl0.trans_le hx.1
    exact ⟨l.sound.1.trans (Real.log_le_log hl0 hx.1),
      (Real.log_le_log hx0 hx.2).trans u.sound.2⟩
  slope_bounds := by
    have hl0 : (0 : ℝ)<l.value := by exact_mod_cast hl
    apply slopeBounds_of_hasDerivAt
      (fun x hx => (Real.hasDerivAt_log (hl0.trans_le hx.1).ne').continuousAt.continuousWithinAt)
      (fun x hx => Real.hasDerivAt_log (hl0.trans hx.1).ne')
    intro x hx
    have hx0 := hl0.trans hx.1
    have hu0 := hx0.trans hx.2
    simp only [Rat.cast_inv]
    exact ⟨(inv_le_inv₀ hu0 hx0).mpr hx.2.le,(inv_le_inv₀ hx0 hl0).mpr hx.1.le⟩

#print axioms FunctionEnclosure.comp
#print axioms logFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
