import BecknerOnofri.Friedrichs.MixedOpenBox
import BecknerOnofri.Friedrichs.MixedCoordinateWeak
import BecknerOnofri.Friedrichs.MixedFiberIntegral
import BecknerOnofri.Friedrichs.MixedCompactBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma coordinate_test_integration (m : ℕ) {F ψ : ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (h0 : ψ 0=0) (hL : ψ (coordinateLength m)=0) :
    (∫ t,deriv F t*ψ t ∂coordinateMeasure m)=
      ∫ t,-(F t*deriv ψ t) ∂coordinateMeasure m := by
  have hdF := (contDiff_infty_iff_deriv.mp hF).2
  have hdψ := (contDiff_infty_iff_deriv.mp hψ).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0:ℝ)) (b := coordinateLength m)
    (fun t _ => (hF.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hψ.differentiable (by simp) t).hasDerivAt)
    (hdF.continuous.intervalIntegrable 0 (coordinateLength m))
    (hdψ.continuous.intervalIntegrable 0 (coordinateLength m))
  simp only [h0,hL,mul_zero,sub_self,zero_sub,
    intervalIntegral.integral_of_le (coordinateLength_pos m).le,integral_Ioc_eq_integral_Ioo] at he
  rw [coordinateMeasure_open,integral_neg]
  linarith

lemma mixed_test_integration {d : ℕ} (α : MultiIndex d) {F ψ : Space d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ openBox α) (i : Fin d) :
    (∫ x,partialDerivative i F x*ψ x ∂spatialMeasure α)=
      -(∫ x,F x*partialDerivative i ψ x ∂spatialMeasure α) := by
  rw [← integral_neg]
  apply integral_eq_of_fiber_eq α i
    ((continuous_memLp α ((partialDerivative_continuous hF i).mul hψ.continuous)).integrable (by norm_num))
    ((continuous_memLp α (hF.continuous.mul (partialDerivative_continuous hψ i)).neg).integrable (by norm_num))
  intro x
  have he := coordinate_test_integration (α i) (fiber_smooth hF x i) (fiber_smooth hψ x i)
    (supported_fiber_endpoints hs x i).1 (supported_fiber_endpoints hs x i).2
  simpa only [fiber_deriv hF x i,fiber_deriv hψ x i,Pi.neg_apply,Pi.mul_apply] using he

#print axioms mixed_test_integration
end BecknerOnofri.Friedrichs.MixedSpatial
