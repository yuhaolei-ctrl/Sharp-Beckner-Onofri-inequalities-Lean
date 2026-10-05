import Legacy.BecknerOnofri.GreenHeatPointwise

/-! The zero Poisson image gives a lower bound for the actual heat-Mellin
integrand with the exact logarithmic coefficient. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri ShiftedGaussianBound GreenHeatPointwise HeatDensityApproximation

theorem heatKernel_first_image_le {d : ℕ} {t : ℝ} (ht : 0<t) (x : Fin d → ℝ) :
    t^(-(d : ℝ)/2)*Real.exp (-Real.pi/t*coordinateRadiusSq x)≤
      heatKernel t (fun i => (x i : UnitAddCircle)) := by
  rw [heatKernel_eq_shiftedGaussian ht x]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos ht _).le
  have h := (summable_shiftedGaussian ht x).le_tsum (0 : Frequency d)
    (fun k _ => (Real.exp_pos _).le)
  simpa only [shiftedGaussian,shiftedRadiusSq,coordinateRadiusSq,Pi.zero_apply,Int.cast_zero,
    zero_sub,neg_sq] using h

theorem heatMellin_first_image_lower {d : ℕ} {t : ℝ} (ht : 0<t) (x : Fin d → ℝ) :
    LogGaussianIntegral.integrand (Real.pi*coordinateRadiusSq x) t-t^((d : ℝ)/2-1)≤
      GreenHeatPointwise.heatMellin (fun i => (x i : UnitAddCircle)) t := by
  have h := mul_le_mul_of_nonneg_left (heatKernel_first_image_le ht x)
    (Real.rpow_pos_of_pos ht ((d : ℝ)/2-1)).le
  rw [← mul_assoc,rpow_mellin_cancel ht] at h
  have he : LogGaussianIntegral.integrand (Real.pi*coordinateRadiusSq x) t=
      t⁻¹*Real.exp (-Real.pi/t*coordinateRadiusSq x) := by
    unfold LogGaussianIntegral.integrand
    rw [show -(Real.pi*coordinateRadiusSq x)/t= -Real.pi/t*coordinateRadiusSq x by ring]
    ring
  rw [he]
  unfold GreenHeatPointwise.heatMellin
  linarith

#print axioms heatMellin_first_image_lower
end BecknerOnofri.AdamsEndpoint
