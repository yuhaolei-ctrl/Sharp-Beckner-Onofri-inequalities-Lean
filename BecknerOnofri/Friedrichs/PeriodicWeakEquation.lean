import BecknerOnofri.Friedrichs.PeriodicAngularWeak
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Periodic integration by parts for arbitrary smooth profiles, including
odd modes. This does not use an evenness or endpoint-derivative-zero premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs

lemma periodic_derivative {F : ℝ → ℝ} {T : ℝ} (hF : Function.Periodic F T) :
    Function.Periodic (deriv F) T := by
  intro x
  have he : (fun t => F (t+T))=F := funext hF
  rw [← deriv_comp_add_const F T x,he]

theorem periodic_weak_equation {F φ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hφ : ContDiff ℝ ∞ φ) (hp : Function.Periodic F (2*Real.pi))
    (hφp : φ (2*Real.pi)=φ 0) :
    (∫ t in Ioc 0 (2*Real.pi),deriv F t*deriv φ t)=
      ∫ t in Ioc 0 (2*Real.pi),-(deriv (deriv F) t)*φ t := by
  have hd := (contDiff_infty_iff_deriv.mp hF).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := 2*Real.pi)
    (fun t _ => (hd.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt)
    (hdd.continuous.intervalIntegrable 0 (2*Real.pi))
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.intervalIntegrable 0 (2*Real.pi))
  have hb : deriv F (2*Real.pi)=deriv F 0 := by simpa only [zero_add] using periodic_derivative hp 0
  simp only [hb,hφp,sub_self,zero_sub,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at he
  simpa only [neg_mul,integral_neg] using he

#print axioms periodic_weak_equation
end BecknerOnofri.Friedrichs
