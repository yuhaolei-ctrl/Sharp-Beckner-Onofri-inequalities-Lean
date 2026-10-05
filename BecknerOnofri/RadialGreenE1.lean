module

public import BecknerOnofri.RadialE1
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-! Exact reciprocal substitution in the actual E1 improper integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.RadialGreenE1

theorem image_reciprocal {A : ℝ} (hA : 0<A) :
    (fun t : ℝ => A/t) '' Ioo (0:ℝ) 1=Ioi A := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact (lt_div_iff₀ ht.1).mpr (by nlinarith [ht.2])
  · intro hy
    have hyp : 0<y := hA.trans hy
    refine ⟨A/y,⟨div_pos hA hyp,(div_lt_one hyp).mpr hy⟩,?_⟩
    field_simp

theorem reciprocal_integral {A : ℝ} (hA : 0<A) :
    (∫ t in Ioo (0:ℝ) 1,Real.exp (-A/t)/t)=RadialE1.E1 A := by
  have hd (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
      HasDerivWithinAt (fun s : ℝ => A/s) (-A/t^2) (Ioo (0:ℝ) 1) t := by
    convert! ((hasDerivAt_const t A).div (hasDerivAt_id t) ht.1.ne').hasDerivWithinAt using 1 <;> simp
  have hinj : InjOn (fun t : ℝ => A/t) (Ioo (0:ℝ) 1) := by
    intro s hs t ht he
    have hh := (div_eq_div_iff hs.1.ne' ht.1.ne').mp he
    exact (mul_left_cancel₀ hA.ne' hh).symm
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
    (fun t : ℝ => Real.exp (-t)/t)
  rw [image_reciprocal hA] at hh
  rw [RadialE1.E1,hh]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hA) (sq_pos_of_pos ht.1))]
  simp only [smul_eq_mul,neg_div,neg_neg]
  field_simp [hA.ne',ht.1.ne']

#print axioms reciprocal_integral
end BecknerOnofri.HighDim.RadialGreenE1
