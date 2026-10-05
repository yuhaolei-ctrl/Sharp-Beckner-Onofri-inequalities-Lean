module

public import BecknerOnofri.Friedrichs.PeriodicWeakEquation

@[expose] public section

/-! All real trigonometric modes on the full circle, including the odd sector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs

def periodicMode (odd : Bool) (n : ℕ) (t : ℝ) : ℝ :=
  if odd then Real.sin ((n:ℝ)*t) else Real.cos ((n:ℝ)*t)

lemma periodicMode_smooth (odd : Bool) (n : ℕ) : ContDiff ℝ ∞ (periodicMode odd n) := by
  cases odd <;> unfold periodicMode <;> dsimp <;> fun_prop

lemma periodicMode_periodic (odd : Bool) (n : ℕ) :
    Function.Periodic (periodicMode odd n) (2*Real.pi) := by
  intro t
  cases odd
  · simpa only [periodicMode,Bool.false_eq_true,if_false,mul_add] using Real.cos_periodic.nat_mul n ((n:ℝ)*t)
  · simpa only [periodicMode,if_true,mul_add] using Real.sin_periodic.nat_mul n ((n:ℝ)*t)

lemma periodicMode_eigen (odd : Bool) (n : ℕ) (t : ℝ) :
    -(deriv (deriv (periodicMode odd n)) t)=(n:ℝ)^2*periodicMode odd n t := by
  have hs (t : ℝ) : HasDerivAt (fun s : ℝ => Real.sin ((n:ℝ)*s)) (Real.cos ((n:ℝ)*t)*(n:ℝ)) t :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul (n:ℝ)).sin
  have hc (t : ℝ) : HasDerivAt (fun s : ℝ => Real.cos ((n:ℝ)*s)) (-Real.sin ((n:ℝ)*t)*(n:ℝ)) t :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul (n:ℝ)).cos
  cases odd
  · change -(deriv (deriv (fun s : ℝ => Real.cos ((n:ℝ)*s))) t)=_
    have hh : deriv (fun s : ℝ => -Real.sin ((n:ℝ)*s)*(n:ℝ)) t=
        -(Real.cos ((n:ℝ)*t)*(n:ℝ))*(n:ℝ) := ((hs t).neg.mul_const (n:ℝ)).deriv
    rw [funext (fun s => (hc s).deriv),hh]
    simp only [periodicMode,Bool.false_eq_true,if_false]
    ring
  · change -(deriv (deriv (fun s : ℝ => Real.sin ((n:ℝ)*s))) t)=_
    rw [funext (fun s => (hs s).deriv), ((hc t).mul_const (n:ℝ)).deriv]
    simp only [periodicMode,if_true]
    ring

theorem periodicMode_weak (odd : Bool) (n : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hp : φ (2*Real.pi)=φ 0) :
    (∫ t in Ioc 0 (2*Real.pi),deriv (periodicMode odd n) t*deriv φ t)=
      ∫ t in Ioc 0 (2*Real.pi),(n:ℝ)^2*periodicMode odd n t*φ t := by
  simpa only [periodicMode_eigen] using periodic_weak_equation (periodicMode_smooth odd n)
    hφ (periodicMode_periodic odd n) hp

#print axioms periodicMode_weak
end BecknerOnofri.Friedrichs
