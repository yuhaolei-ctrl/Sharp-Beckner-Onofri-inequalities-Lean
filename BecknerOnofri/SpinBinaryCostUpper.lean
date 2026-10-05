module

public import BecknerOnofri.SpinBinaryCost

@[expose] public section

/-! The binary-entropy remainder bound used by the scalar small-mean
minorant construction. Proved from the actual second derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace BecknerOnofri.HighDim.Spin

theorem binaryCost_quartic_upper {a : ℝ} (ha : 0≤a) (ha1 : a<1) :
    2*binaryCost a≤a^2+a^4/(6*(1-a^2)) := by
  have hden : 0<1-a^2 := by nlinarith
  let f : ℝ → ℝ := fun t => a^2*t^2+a^4*t^4/(6*(1-a^2))-2*binaryCost (a*t)
  let f' : ℝ → ℝ := fun t => 2*a^2*t+(2*a^4/(3*(1-a^2)))*t^3-2*a*binaryCostSlope (a*t)
  let f'' : ℝ → ℝ := fun t => 2*a^2+(2*a^4/(1-a^2))*t^2-2*a^2*binaryCostHessian (a*t)
  have hd (t : ℝ) (ht : -1<a*t) (ht1 : a*t<1) : HasDerivAt f (f' t) t := by
    have h := ((((hasDerivAt_id t).pow 2).const_mul (a^2)).add
      ((((hasDerivAt_id t).pow 4).const_mul (a^4)).div_const (6*(1-a^2)))).sub
      (((binaryCost_derivative (a*t) ht ht1).comp t ((hasDerivAt_id t).const_mul a)).const_mul 2)
    convert h using 1 <;> try rfl
    dsimp [f']
    field_simp [hden.ne']
    <;> ring
  have hdd (t : ℝ) (ht : -1<a*t) (ht1 : a*t<1) : HasDerivAt f' (f'' t) t := by
    have h := (((hasDerivAt_id t).const_mul (2*a^2)).add
      (((hasDerivAt_id t).pow 3).const_mul (2*a^4/(3*(1-a^2))))).sub
      (((binaryCost_second_derivative (a*t) ht ht1).comp t
        ((hasDerivAt_id t).const_mul a)).const_mul (2*a))
    convert h using 1 <;> try rfl
    dsimp [f'']
    field_simp [hden.ne']
    <;> ring
  have hi (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0≤a*t ∧ a*t<1 := by
    constructor
    · exact mul_nonneg ha ht.1.le
    · have : a*t≤a := by nlinarith [ht.2]
      linarith
  have hb (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : 0≤f'' t := by
    have hi' := hi t ht
    have hd' : 0<1-(a*t)^2 := by nlinarith
    have hne : 1-a^2*t^2≠0 := by simpa [mul_pow] using hd'.ne'
    have he : f'' t=2*a^6*t^2*(1-t^2)/((1-a^2)*(1-(a*t)^2)) := by
      dsimp [f'',binaryCostHessian]
      field_simp [hden.ne',hd'.ne',hne]
      ring
    rw [he]
    have ht2 : 0≤1-t^2 := by nlinarith [ht.1,ht.2]
    positivity
  have hcont : Continuous f := by
    dsimp [f]
    exact (by fun_prop : Continuous (fun t : ℝ => a^2*t^2+a^4*t^4/(6*(1-a^2)))).sub
      ((binaryCost_continuous.comp (by fun_prop)).const_mul 2)
  have h := second_order_support hcont.continuousOn (hd 0 (by simp) (by simp))
    (fun t ht => hd t (by linarith [(hi t ht).1]) (hi t ht).2)
    (fun t ht => hdd t (by linarith [(hi t ht).1]) (hi t ht).2) hb
  norm_num [f,f',binaryCost,binaryCostSlope] at h ⊢
  linarith

#print axioms binaryCost_quartic_upper
end BecknerOnofri.HighDim.Spin
