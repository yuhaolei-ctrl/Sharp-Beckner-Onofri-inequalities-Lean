module

public import BecknerOnofri.CircleSeriesDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.CircleRegularity

theorem contDiff_series (N : ℕ) (a : ℤ → ℂ)
    (hw : ∀ m : ℕ,m≤N → Summable (fun n : ℤ => |(n:ℝ)|^m*‖a n‖)) :
    ContDiff ℝ N (fun x : ℝ => ∑' n : ℤ,a n*fourier n (x:UnitAddCircle)) := by
  induction N generalizing a with
  | zero =>
    apply contDiff_zero.mpr
    have h₀ : Summable (fun n => ‖a n‖) := by simpa only [pow_zero,one_mul] using hw 0 (by omega)
    apply continuous_tsum (fun n => continuous_const.mul (continuous_iff_continuousAt.mpr (fun x : ℝ => (hasDerivAt_fourier 1 n x).continuousAt))) h₀
    intro n x
    change ‖a n*fourier n (x:UnitAddCircle)‖≤‖a n‖
    simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,le_refl]
  | succ N ih =>
    have h₀ : Summable (fun n => ‖a n‖) := by simpa only [pow_zero,one_mul] using hw 0 (by omega)
    have h₁ : Summable (fun n : ℤ => |(n:ℝ)| *‖a n‖) := by simpa only [pow_one] using hw 1 (by omega)
    let b : ℤ → ℂ := fun n => (n:ℂ)*a n
    have hb : ∀ m : ℕ,m≤N → Summable (fun n : ℤ => |(n:ℝ)|^m*‖b n‖) := by
      intro m hm
      simpa only [b,norm_mul,Complex.norm_intCast,pow_succ,mul_assoc] using hw (m+1) (by omega)
    have hd (x : ℝ) := hasDerivAt_series a h₀ h₁ x
    have hderiv : deriv (fun x : ℝ => ∑' n : ℤ,a n*fourier n (x:UnitAddCircle))=
        fun x : ℝ => 2*(Real.pi:ℂ)*Complex.I*(∑' n : ℤ,b n*fourier n (x:UnitAddCircle)) := by
      funext x
      exact (hd x).deriv
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd x).differentiableAt,by simp,?_⟩
    rw [hderiv]
    exact contDiff_const.mul (ih b hb)

#print axioms contDiff_series
end BecknerOnofri.HighDim.CircleRegularity
