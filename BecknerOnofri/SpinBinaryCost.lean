import BecknerOnofri.SpinProductDefinitions
import BecknerOnofri.SpinSecondOrderSupport

/-! The binary entropy cost and its sharp quadratic/quartic lower bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.Spin

def binaryCostSlope (t : ℝ) : ℝ := (Real.log (1+t)-Real.log (1-t))/2
def binaryCostHessian (t : ℝ) : ℝ := 1/(1-t^2)

theorem binaryCost_continuous : Continuous binaryCost := by
  unfold binaryCost
  exact ((Real.continuous_mul_log.comp (by fun_prop)).add
    (Real.continuous_mul_log.comp (by fun_prop))).div_const 2

theorem binaryCost_derivative (t : ℝ) (ht : -1<t) (ht1 : t<1) :
    HasDerivAt binaryCost (binaryCostSlope t) t := by
  have hp : 1+t≠0 := ne_of_gt (by linarith)
  have hm : 1-t≠0 := ne_of_gt (by linarith)
  have h := (((Real.hasDerivAt_mul_log hp).comp t ((hasDerivAt_id t).const_add 1)).add
    ((Real.hasDerivAt_mul_log hm).comp t ((hasDerivAt_id t).const_sub 1))).div_const 2
  convert h using 1 <;> try rfl
  simp only [binaryCostSlope]
  ring

theorem binaryCost_second_derivative (t : ℝ) (ht : -1<t) (ht1 : t<1) :
    HasDerivAt binaryCostSlope (binaryCostHessian t) t := by
  have hp : 1+t≠0 := ne_of_gt (by linarith)
  have hm : 1-t≠0 := ne_of_gt (by linarith)
  have hd : 1-t^2≠0 := by
    have hh := mul_pos (show 0<1+t by linarith) (show 0<1-t by linarith)
    nlinarith
  have h := (((Real.hasDerivAt_log hp).comp t ((hasDerivAt_id t).const_add 1)).sub
    ((Real.hasDerivAt_log hm).comp t ((hasDerivAt_id t).const_sub 1))).div_const 2
  convert h using 1 <;> try rfl
  unfold binaryCostHessian
  field_simp [hp,hm,hd]
  ring

/-- The lower bound used for F(p^(t)) in the small-mean argument. -/
theorem binaryCost_quartic_lower {a : ℝ} (ha : 0≤a) (ha1 : a≤1) :
    a^2/2+a^4/12≤binaryCost a := by
  let f : ℝ → ℝ := fun t => binaryCost (a*t)-a^2*t^2/2-a^4*t^4/12
  let f' : ℝ → ℝ := fun t => a*binaryCostSlope (a*t)-a^2*t-(a^4/3)*t^3
  let f'' : ℝ → ℝ := fun t => a^2*binaryCostHessian (a*t)-a^2-a^4*t^2
  have hd (t : ℝ) (ht : -1<a*t) (ht1 : a*t<1) : HasDerivAt f (f' t) t := by
    have h := (((binaryCost_derivative (a*t) ht ht1).comp t
      ((hasDerivAt_id t).const_mul a)).sub
      ((((hasDerivAt_id t).pow 2).const_mul (a^2)).div_const 2)).sub
      ((((hasDerivAt_id t).pow 4).const_mul (a^4)).div_const 12)
    convert h using 1 <;> try rfl
    dsimp [f']
    ring
  have hdd (t : ℝ) (ht : -1<a*t) (ht1 : a*t<1) : HasDerivAt f' (f'' t) t := by
    have h := ((((binaryCost_second_derivative (a*t) ht ht1).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul a).sub
      ((hasDerivAt_id t).const_mul (a^2))).sub
      (((hasDerivAt_id t).pow 3).const_mul (a^4/3))
    convert h using 1 <;> try rfl
    dsimp [f'']
    ring
  have hi (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0≤a*t ∧ a*t<1 := by
    constructor
    · exact mul_nonneg ha ht.1.le
    · calc
        a*t≤1*t := mul_le_mul_of_nonneg_right ha1 ht.1.le
        _ < 1 := by simpa using ht.2
  have hb (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0≤f'' t := by
    have hi' := hi t ht
    have hd' : 0<1-(a*t)^2 := by nlinarith
    have hne : 1-a^2*t^2≠0 := by simpa [mul_pow] using hd'.ne'
    have he : f'' t=a^6*t^4/(1-(a*t)^2) := by
      dsimp [f'',binaryCostHessian]
      field_simp [hd'.ne',hne]
      ring
    rw [he]
    positivity
  have hcont : Continuous f := by
    dsimp [f]
    exact ((binaryCost_continuous.comp (by fun_prop)).sub (by fun_prop)).sub (by fun_prop)
  have h := second_order_support hcont.continuousOn (hd 0 (by simp) (by simp))
    (fun t ht => hd t (by linarith [(hi t ht).1]) (hi t ht).2)
    (fun t ht => hdd t (by linarith [(hi t ht).1]) (hi t ht).2) hb
  norm_num [f,f',binaryCost,binaryCostSlope] at h ⊢
  linarith

#print axioms binaryCost_quartic_lower
end BecknerOnofri.HighDim.Spin
