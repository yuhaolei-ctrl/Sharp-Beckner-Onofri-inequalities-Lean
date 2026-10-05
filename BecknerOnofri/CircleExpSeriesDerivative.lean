import BecknerOnofri.CircleSeriesDerivative

/-! The logarithmic derivative identity for an actual exponential Fourier series. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.CircleRegularity

theorem exponential_series_derivative (a b : ℤ → ℂ)
    (ha₀ : Summable (fun n => ‖a n‖))
    (ha₁ : Summable (fun n : ℤ => |(n:ℝ)| * ‖a n‖))
    (hb₀ : Summable (fun n => ‖b n‖))
    (hb₁ : Summable (fun n : ℤ => |(n:ℝ)| * ‖b n‖))
    (he : ∀ x : UnitAddCircle,(∑' n : ℤ,b n*fourier n x)=
      Complex.exp (∑' n : ℤ,a n*fourier n x)) (x : UnitAddCircle) :
    (∑' n : ℤ,(n:ℂ)*b n*fourier n x)=
      Complex.exp (∑' n : ℤ,a n*fourier n x)*(∑' n : ℤ,(n:ℂ)*a n*fourier n x) := by
  induction x using QuotientAddGroup.induction_on
  rename_i x
  have ha := (hasDerivAt_series a ha₀ ha₁ x).cexp
  have hb := hasDerivAt_series b hb₀ hb₁ x
  have he' : (fun y : ℝ => ∑' n : ℤ,b n*fourier n (y:UnitAddCircle))=
      (fun y : ℝ => Complex.exp (∑' n : ℤ,a n*fourier n (y:UnitAddCircle))) :=
    funext (fun y => he y)
  rw [he'] at hb
  have h := hb.unique ha
  have hn : 2*(Real.pi:ℂ)*Complex.I≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  apply mul_left_cancel₀ hn
  calc
    _ = Complex.exp (∑' n : ℤ,a n*fourier n (x:UnitAddCircle))*
        (2*(Real.pi:ℂ)*Complex.I*(∑' n : ℤ,(n:ℂ)*a n*fourier n (x:UnitAddCircle))) := h
    _ = _ := by ring

#print axioms exponential_series_derivative
end BecknerOnofri.HighDim.CircleRegularity
