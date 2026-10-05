import BecknerOnofri.ScalarFunctionEnclosure

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

def RationalInterval.inv (a : RationalInterval) : RationalInterval := ⟨a.upper⁻¹,a.lower⁻¹⟩

theorem RationalInterval.contains_inv {a : RationalInterval} {x : ℝ}
    (ha : 0<a.lower) (hx : a.Contains x) : a.inv.Contains x⁻¹ := by
  have hl : (0 : ℝ)<a.lower := by exact_mod_cast ha
  have hp : 0<x := hl.trans_le hx.1
  have hu : (0 : ℝ)<a.upper := hp.trans_le hx.2
  simp only [Contains,inv,Rat.cast_inv]
  exact ⟨(inv_le_inv₀ hu hp).mpr hx.2,(inv_le_inv₀ hp hl).mpr hx.1⟩

noncomputable def FunctionEnclosure.inv {a b : ℝ} {f : ℝ → ℝ}
    (ef : FunctionEnclosure a b f) (hpos : 0<ef.value.lower) :
    FunctionEnclosure a b (fun x => (f x)⁻¹) where
  value := ef.value.inv
  slope := (ef.slope.mul (ef.value.inv.mul ef.value.inv)).neg
  value_mem := fun x hx => RationalInterval.contains_inv hpos (ef.value_mem x hx)
  slope_bounds := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl|hxy
    · simp
    have hd := sub_pos.mpr hxy
    have hpx : 0<f x := (show (0 : ℝ)<ef.value.lower by exact_mod_cast hpos).trans_le (ef.value_mem x hx).1
    have hpy : 0<f y := (show (0 : ℝ)<ef.value.lower by exact_mod_cast hpos).trans_le (ef.value_mem y hy).1
    have hxinv := RationalInterval.contains_inv hpos (ef.value_mem x hx)
    have hyinv := RationalInterval.contains_inv hpos (ef.value_mem y hy)
    have hm := RationalInterval.contains_mul (ef.secant_mem hx hy hxy)
      (RationalInterval.contains_mul hxinv hyinv)
    have h := RationalInterval.contains_neg hm
    have he : -(((f y-f x)/(y-x))*((f x)⁻¹*(f y)⁻¹))=
        ((f y)⁻¹-(f x)⁻¹)/(y-x) := by
      field_simp
      <;> ring
    rw [he] at h
    exact ⟨(le_div_iff₀ hd).mp h.1,(div_le_iff₀ hd).mp h.2⟩

#print axioms FunctionEnclosure.inv
end BecknerOnofri.HighDim.ScalarCertificate
