module

public import Legacy.BecknerOnofri.ThetaDecayAllDimensions

@[expose] public section

/-! Integrability of the actual dimension-twelve theta integral. No finite
truncation is used in this lemma. -/
noncomputable section
open MeasureTheory Set
open Legacy.BecknerOnofri.ThetaDomination
namespace BecknerOnofri.HighDim.Twelve

theorem theta_integrand_le_decay {r : ℝ} (hr : 1 ≤ r) :
    thetaIntegrand realTheta 12 r ≤ thetaDecayConstant 12 *
      ((r ^ (5 : ℝ) + 1) * Real.exp (-Real.pi * r)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hp := realTheta_pow_sub_one_le 12 (show Real.pi ≤ Real.pi*r by nlinarith [Real.pi_pos])
  have hz : 0 ≤ realTheta (Real.pi*r)^12 - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (one_le_realTheta (mul_pos Real.pi_pos hr0)))
  have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr
  unfold thetaIntegrand
  norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2-1 = 5 by norm_num]
  calc
    _ ≤ (r ^ (5 : ℝ)+1) * (realTheta (Real.pi*r)^12-1) :=
      mul_le_mul_of_nonneg_right (add_le_add_right hi _) hz
    _ ≤ (r ^ (5 : ℝ)+1) * (thetaDecayConstant 12 * Real.exp (-(Real.pi*r))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [neg_mul]; ring

theorem theta_decay_integrable :
    IntegrableOn (fun r : ℝ => thetaDecayConstant 12 *
      ((r ^ (5 : ℝ) + 1) * Real.exp (-Real.pi * r))) (Ici (1 : ℝ)) := by
  have hp : IntegrableOn (fun r : ℝ => r^(5 : ℝ)*Real.exp (-Real.pi*r)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 5) (by norm_num : (0 : ℝ) < 1) Real.pi_pos
    simpa only [Real.rpow_one] using h
  have he : IntegrableOn (fun r : ℝ => Real.exp (-Real.pi*r)) (Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) Real.pi_pos
    simpa only [Real.rpow_one, Real.rpow_zero, one_mul] using h
  have h := (hp.add he).const_mul (thetaDecayConstant 12)
  apply (IntegrableOn.mono_set h
    (show Ici (1 : ℝ) ⊆ Ioi (0 : ℝ) from fun r hr =>
      (show (0 : ℝ) < r from lt_of_lt_of_le zero_lt_one hr))).congr_fun
      ?_ measurableSet_Ici
  intro r _
  dsimp
  ring

theorem theta_integrable :
    IntegrableOn (thetaIntegrand realTheta 12) (Ici (1 : ℝ)) := by
  refine theta_decay_integrable.mono'
    (aestronglyMeasurable_thetaIntegrand measurable_realTheta 12) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
  have ht := one_le_realTheta (mul_pos Real.pi_pos (zero_lt_one.trans_le hr))
  rw [Real.norm_eq_abs, abs_of_nonneg (thetaIntegrand_nonneg hr ht)]
  exact theta_integrand_le_decay hr

end BecknerOnofri.HighDim.Twelve
