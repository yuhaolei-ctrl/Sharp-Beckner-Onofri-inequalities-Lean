module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Tactic

@[expose] public section

/-! Differentiation of actual absolutely convergent circle Fourier series.
The first weighted absolute moment controls the derivative uniformly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.CircleRegularity

theorem hasDerivAt_series (a : ℤ → ℂ)
    (h₀ : Summable (fun n => ‖a n‖))
    (h₁ : Summable (fun n : ℤ => |(n:ℝ)| *‖a n‖)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∑' n : ℤ,a n*fourier n (y:UnitAddCircle))
      (2*(Real.pi:ℂ)*Complex.I*(∑' n : ℤ,(n:ℂ)*a n*fourier n (x:UnitAddCircle))) x := by
  let g : ℤ → ℝ → ℂ := fun n y => a n*fourier n (y:UnitAddCircle)
  let g' : ℤ → ℝ → ℂ := fun n y => a n*(2*(Real.pi:ℂ)*Complex.I*n*fourier n (y:UnitAddCircle))
  have hd (n : ℤ) (y : ℝ) : HasDerivAt (g n) (g' n y) y := by
    simpa only [Complex.ofReal_one,div_one,g,g'] using (hasDerivAt_fourier 1 n y).const_mul (a n)
  have hb (n : ℤ) (y : ℝ) : ‖g' n y‖≤(2*Real.pi)*(|(n:ℝ)| *‖a n‖) := by
    dsimp only [g']
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,Complex.norm_intCast,
      fourier_apply,Circle.norm_coe,mul_one]
    exact le_of_eq (by ring)
  have hs : Summable (fun n => g n 0) := by
    apply Summable.of_norm_bounded h₀
    intro n
    dsimp only [g]
    simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,le_refl]
  have h := hasDerivAt_tsum (h₁.mul_left (2*Real.pi)) hd hb hs x
  have he : 2*(Real.pi:ℂ)*Complex.I*(∑' n : ℤ,(n:ℂ)*a n*fourier n (x:UnitAddCircle))=
      ∑' n : ℤ,g' n x := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [g']
    ring
  rw [he]
  exact h

#print axioms hasDerivAt_series
end BecknerOnofri.HighDim.CircleRegularity
