module

public import BecknerOnofri.Friedrichs.AngularWeakEquation
public import BecknerOnofri.Friedrichs.MixedSpatialDefinitions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs
open Legacy.BecknerOnofri.JacobiAngular

lemma angular_zero_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    deriv (angular 0 f) t=deriv f (Real.cos t)*(-Real.sin t) := by
  have h := ((hf.differentiable (by simp) (Real.cos t)).hasDerivAt).comp t (Real.hasDerivAt_cos t)
  have he : angular 0 f=(fun x => f (Real.cos x)) := by
    funext x
    simp [angular]
  rw [he]
  exact h.deriv

lemma angular_zero_image {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    -deriv (deriv (angular 0 f)) t=angularImage 0 f t := by
  have he : deriv (angular 0 f)=(fun t => deriv f (Real.cos t)*(-Real.sin t)) :=
    funext (angular_zero_deriv hf)
  have hfd := (contDiff_infty_iff_deriv.mp hf).2
  have hd := (((hfd.differentiable (by simp) (Real.cos t)).hasDerivAt).comp t
    (Real.hasDerivAt_cos t)).mul (Real.hasDerivAt_sin t).neg
  have hde : deriv (fun t => deriv f (Real.cos t)*(-Real.sin t)) t =
      deriv (deriv f) (Real.cos t)*(-Real.sin t)*(-Real.sin t)+
        deriv f (Real.cos t)*(-Real.cos t) := hd.deriv
  rw [he,hde]
  dsimp [angularImage,jacobi]
  have hs : (Real.sin t)^2=1-(Real.cos t)^2 := by nlinarith [Real.sin_sq_add_cos_sq t]
  have hh : deriv (deriv f) (Real.cos t)*(-Real.sin t)*(-Real.sin t)=
      (1-(Real.cos t)^2)*deriv (deriv f) (Real.cos t) := by
    calc
      _ = (Real.sin t)^2*deriv (deriv f) (Real.cos t) := by ring
      _ = _ := by rw [hs]
  rw [hh]
  ring

theorem periodic_angular_weak {f φ : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) :
    (∫ t in Ioc 0 (2*Real.pi),deriv (angular 0 f) t*deriv φ t)=
      ∫ t in Ioc 0 (2*Real.pi),angularImage 0 f t*φ t := by
  have hh := angular_smooth 0 hf
  have hd := (contDiff_infty_iff_deriv.mp hh).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hb : deriv (angular 0 f) (2*Real.pi)=0 := by simp [angular_zero_deriv hf]
  have ha : deriv (angular 0 f) 0=0 := by simp [angular_zero_deriv hf]
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := 2*Real.pi)
    (fun t _ => (hd.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt)
    (hdd.continuous.intervalIntegrable 0 (2*Real.pi))
    ((contDiff_infty_iff_deriv.mp hφ).2.continuous.intervalIntegrable 0 (2*Real.pi))
  simp only [ha,hb,zero_mul,sub_self,zero_sub,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at hip
  have he : (fun t => angularImage 0 f t*φ t)=(fun t => -(deriv (deriv (angular 0 f)) t*φ t)) := by
    funext t
    rw [← angular_zero_image hf t]
    ring
  rw [he,integral_neg]
  exact hip

#print axioms periodic_angular_weak
end BecknerOnofri.Friedrichs
