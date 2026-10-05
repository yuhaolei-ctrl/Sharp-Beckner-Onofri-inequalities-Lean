import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.Friedrichs

abbrev PeriodicComplexL2 := Lp ℂ 2 (volume.restrict (Ioc 0 (2*Real.pi)))

lemma periodic_coefficients_total (f : PeriodicComplexL2)
    (h : ∀ n : ℤ,fourierCoeffOn (by positivity : (0:ℝ)<2*Real.pi) f n=0) : f=0 := by
  have hp := tsum_sq_fourierCoeffOn (by positivity : (0:ℝ)<2*Real.pi) (Lp.memLp f)
  simp only [h,norm_zero,zero_pow (by decide : (2:ℕ)≠0),tsum_zero,sub_zero,smul_eq_mul] at hp
  have hi : (∫ x in Ioc 0 (2*Real.pi),‖f x‖^2)=0 := by
    rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)] at hp
    exact (mul_eq_zero.mp hp.symm).resolve_left (by positivity)
  have hInt : Integrable (fun x => ‖f x‖^2) (volume.restrict (Ioc 0 (2*Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hInt).mp hi
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 (2*Real.pi)))] with x hx hz
  have hf : f x=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  exact hf.trans hz.symm

#print axioms periodic_coefficients_total
end BecknerOnofri.Friedrichs
