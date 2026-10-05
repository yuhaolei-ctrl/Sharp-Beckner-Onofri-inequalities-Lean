import BecknerOnofri.CircleWeightClosedForm
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar
open Set Filter
open scoped Topology

theorem weight_one_formula (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    weight 1 t=(-Real.log (1-t^2)-t^2)/t^4 := by
  simpa using weight_closed_form 1 t ht ht1

theorem weight_two_formula (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    weight 2 t=(-Real.log (1-t^2)-t^2-t^4/2)/t^6 := by
  have he := weight_closed_form 2 t ht ht1
  norm_num [Finset.sum_range_succ] at he
  rw [he]
  ring

theorem weight_one_derivative (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    HasDerivAt (weight 1) (2/(t*(1-t^2))-4*weight 1 t/t) t := by
  have hne : 1-t^2≠0 := by nlinarith
  have hd := (((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).log hne).neg).sub
    ((hasDerivAt_id t).pow 2)).div ((hasDerivAt_id t).pow 4) (pow_ne_zero _ ht.ne')
  have he : weight 1 =ᶠ[𝓝 t] (fun x : ℝ => (-Real.log (1-x^2)-x^2)/x^4) := by
    filter_upwards [Ioo_mem_nhds ht ht1] with x hx
    exact weight_one_formula x hx.1 hx.2
  have hd' := hd.congr_of_eventuallyEq he
  apply hd'.congr_deriv
  rw [weight_one_formula t ht ht1]
  dsimp
  field_simp [ht.ne',hne]
  <;> ring

theorem weight_two_derivative (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    HasDerivAt (weight 2) (2/(t*(1-t^2))-6*weight 2 t/t) t := by
  have hne : 1-t^2≠0 := by nlinarith
  have hd := ((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).log hne).neg).sub
    ((hasDerivAt_id t).pow 2)).sub (((hasDerivAt_id t).pow 4).div_const 2)).div
      ((hasDerivAt_id t).pow 6) (pow_ne_zero _ ht.ne')
  have he : weight 2 =ᶠ[𝓝 t] (fun x : ℝ => (-Real.log (1-x^2)-x^2-x^4/2)/x^6) := by
    filter_upwards [Ioo_mem_nhds ht ht1] with x hx
    exact weight_two_formula x hx.1 hx.2
  have hd' := hd.congr_of_eventuallyEq he
  apply hd'.congr_deriv
  rw [weight_two_formula t ht ht1]
  dsimp
  field_simp [ht.ne',hne]
  <;> ring

#print axioms weight_one_derivative
#print axioms weight_two_derivative
end BecknerOnofri.HighDim.CircleScalar
