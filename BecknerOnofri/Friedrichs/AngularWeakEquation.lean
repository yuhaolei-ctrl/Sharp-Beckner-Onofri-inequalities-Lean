module

public import BecknerOnofri.Friedrichs.AngularCutoffApproximation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! The angular conjugation identity holds against actual spatial test
functions after integration by parts. No spectral-domain premise is used. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs
open Legacy.BecknerOnofri.JacobiAngular

def angularImage (m : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sin t^m*(jacobi m f (Real.cos t)+(m:ℝ)^2*f (Real.cos t))

lemma angularImage_continuous (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (angularImage m f) := by
  have hfd := (contDiff_infty_iff_deriv.mp hf).2
  have hfdd := (contDiff_infty_iff_deriv.mp hfd).2
  unfold angularImage jacobi
  have h0 := hf.continuous
  have h1 := hfd.continuous
  have h2 := hfdd.continuous
  fun_prop

lemma compact_test_endpoints {φ : ℝ → ℝ} (hφ : tsupport φ ⊆ Ioo 0 Real.pi) :
    φ 0=0 ∧ φ Real.pi=0 := by
  constructor
  · by_contra hn
    have hh := hφ (subset_closure (show 0∈Function.support φ from hn))
    exact lt_irrefl _ hh.1
  · by_contra hn
    have hh := hφ (subset_closure (show Real.pi∈Function.support φ from hn))
    exact lt_irrefl _ hh.2

theorem angular_weak_conjugation (m : ℕ) {f φ : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : φ 0=0) (hφπ : φ Real.pi=0) :
    (∫ t in Ioo 0 Real.pi,
      deriv (angular m f) t*deriv φ t+
        ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*angular m f t*φ t) =
      ∫ t in Ioo 0 Real.pi,angularImage m f t*φ t := by
  let h := angular m f
  have hh := angular_smooth m hf
  have hd := (contDiff_infty_iff_deriv.mp hh).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a:=(0:ℝ)) (b:=Real.pi)
    (fun t _ => (hd.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hφ.differentiable (by simp) t).hasDerivAt)
    (hdd.continuous.intervalIntegrable 0 Real.pi) (hφd.continuous.intervalIntegrable 0 Real.pi)
  simp only [hφ0,hφπ,mul_zero,sub_self,zero_sub,
    intervalIntegral.integral_of_le Real.pi_pos.le,integral_Ioc_eq_integral_Ioo] at hip
  have hip' : (∫ t in Ioo 0 Real.pi,deriv h t*deriv φ t) =
      -(∫ t in Ioo 0 Real.pi,deriv (deriv h) t*φ t) := hip
  have hiF : IntegrableOn (fun t => angularImage m f t*φ t) (Ioo 0 Real.pi) :=
    ((angularImage_continuous m hf).mul hφ.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiD : IntegrableOn (fun t => deriv (deriv h) t*φ t) (Ioo 0 Real.pi) :=
    (hdd.continuous.mul hφ.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiG : IntegrableOn (fun t => deriv h t*deriv φ t) (Ioo 0 Real.pi) :=
    (hd.continuous.mul hφd.continuous).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have he : (fun t => ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*h t*φ t) =ᵐ[volume.restrict (Ioo 0 Real.pi)]
      (fun t => angularImage m f t*φ t+deriv (deriv h) t*φ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hc := angular_conjugation m hf (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    change -deriv (deriv h) t+((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*h t=angularImage m f t at hc
    linear_combination (φ t)*hc
  have hiP : IntegrableOn (fun t => ((m:ℝ)*((m:ℝ)-1)/(Real.sin t)^2)*h t*φ t)
      (Ioo 0 Real.pi) := (hiF.add hiD).congr he.symm
  rw [integral_add hiG hiP,integral_congr_ae he,integral_add hiF hiD,hip']
  ring

#print axioms angular_weak_conjugation
end BecknerOnofri.Friedrichs
