import Legacy.BecknerOnofri.ThetaIntegrability
import Legacy.BecknerOnofri.ThetaJacobi
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set

namespace Legacy.BecknerOnofri.GaussianHeatSplit

open ThetaDomination

theorem reciprocal_image {c : ℝ} (hc : 0 < c) :
    (fun r : ℝ => c/r) '' Ioi 1 = Ioo 0 c := by
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    change 1 < r at hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    refine ⟨div_pos hc hr0, (div_lt_iff₀ hr0).2 ?_⟩
    nlinarith
  · intro ht
    refine ⟨c/t, (lt_div_iff₀ ht.1).2 (by simpa using ht.2), ?_⟩
    exact div_div_cancel₀ hc.ne'

theorem reciprocal_injOn {c : ℝ} (hc : 0 < c) :
    InjOn (fun r : ℝ => c/r) (Ioi 1) := by
  intro r hr u hu h
  have hh := congrArg (fun z : ℝ => c/z) h
  simpa only [div_div_cancel₀ hc.ne'] using hh

theorem reciprocal_hasDeriv {c r : ℝ} (hr : r ∈ Ioi (1 : ℝ)) :
    HasDerivWithinAt (fun u : ℝ => c/u) (-c/r^2) (Ioi 1) r := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  convert! ((hasDerivAt_const r c).fun_div (hasDerivAt_id r) hr0).hasDerivWithinAt using 1 <;> simp

theorem reciprocal_abs_deriv {c r : ℝ} (hc : 0 < c) (hr : r ∈ Ioi (1 : ℝ)) :
    |-c/r^2| = c/r^2 := by
  rw [neg_div, abs_neg, abs_of_pos]
  exact div_pos hc (sq_pos_of_pos (lt_trans zero_lt_one hr))

/-- The reciprocal change of variables on an entire open interval. -/
theorem integral_reciprocal (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioo 0 c, f t) = ∫ r in Ioi (1 : ℝ), (c/r^2) * f (c/r) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r hr => reciprocal_hasDeriv (c := c) hr) (reciprocal_injOn hc) f
  rw [reciprocal_image hc] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [reciprocal_abs_deriv hc hr, smul_eq_mul]

theorem integrableOn_reciprocal_iff (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn f (Ioo 0 c) ↔
      IntegrableOn (fun r : ℝ => (c/r^2) * f (c/r)) (Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun r hr => reciprocal_hasDeriv (c := c) hr) (reciprocal_injOn hc) f
  rw [reciprocal_image hc] at h
  rw [h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro r hr
  dsimp only
  rw [reciprocal_abs_deriv hc hr, smul_eq_mul]

noncomputable def radialTheta (d : ℕ) (r : ℝ) : ℝ :=
  r^((d : ℝ)/2-1) * (realTheta (Real.pi*r)^d-1)

noncomputable def inverseTheta (d : ℕ) (r : ℝ) : ℝ :=
  r⁻¹ * (realTheta (Real.pi*r)^d-1)

theorem thetaIntegrand_eq_add (d : ℕ) (r : ℝ) :
    thetaIntegrand realTheta d r = radialTheta d r + inverseTheta d r := by
  unfold thetaIntegrand radialTheta inverseTheta
  ring

theorem theta_defect_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ realTheta t^d-1 :=
  sub_nonneg.mpr (one_le_pow₀ (one_le_realTheta ht))

theorem radialTheta_nonneg (d : ℕ) {r : ℝ} (hr : 1 < r) : 0 ≤ radialTheta d r := by
  unfold radialTheta
  exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
    (theta_defect_nonneg d (mul_pos Real.pi_pos (by linarith)))

theorem inverseTheta_nonneg (d : ℕ) {r : ℝ} (hr : 1 < r) : 0 ≤ inverseTheta d r := by
  unfold inverseTheta
  exact mul_nonneg (inv_nonneg.mpr (by linarith))
    (theta_defect_nonneg d (mul_pos Real.pi_pos (by linarith)))

theorem integrable_radialTheta {d : ℕ} (hd : d ≤ 10) :
    IntegrableOn (radialTheta d) (Ioi (1 : ℝ)) := by
  have hi := (integrableOn_realThetaIntegrand hd).mono_set (Ioi_subset_Ici_self)
  have hc : ContinuousOn (fun r : ℝ => r^((d : ℝ)/2-1)) (Ioi 1) :=
    continuousOn_id.rpow_const (fun r hr => Or.inl (ne_of_gt (lt_trans zero_lt_one hr)))
  have hm : AEStronglyMeasurable (radialTheta d) (volume.restrict (Ioi 1)) :=
    (hc.aestronglyMeasurable measurableSet_Ioi).mul
      (((measurable_realTheta.comp (measurable_const.mul measurable_id)).pow_const d).sub
        measurable_const).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (radialTheta_nonneg d hr), thetaIntegrand_eq_add]
  linarith [inverseTheta_nonneg d hr]

theorem integrable_inverseTheta {d : ℕ} (hd : d ≤ 10) :
    IntegrableOn (inverseTheta d) (Ioi (1 : ℝ)) := by
  have hi := (integrableOn_realThetaIntegrand hd).mono_set (Ioi_subset_Ici_self)
  have hm : AEStronglyMeasurable (inverseTheta d) (volume.restrict (Ioi 1)) :=
    measurable_inv.aestronglyMeasurable.mul
      (((measurable_realTheta.comp (measurable_const.mul measurable_id)).pow_const d).sub
        measurable_const).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (inverseTheta_nonneg d hr), thetaIntegrand_eq_add]
  linarith [radialTheta_nonneg d hr]

theorem thetaIntegral_split {d : ℕ} (hd : d ≤ 10) :
    thetaIntegral realTheta d = (∫ r in Ioi (1 : ℝ), radialTheta d r) +
      ∫ r in Ioi (1 : ℝ), inverseTheta d r := by
  unfold thetaIntegral
  rw [integral_Ici_eq_integral_Ioi]
  simp_rw [thetaIntegrand_eq_add]
  exact integral_add (integrable_radialTheta hd) (integrable_inverseTheta hd)

noncomputable def imageMajorant (d : ℕ) (t : ℝ) : ℝ :=
  t⁻¹ * (realTheta (Real.pi^2/t)^d-1)

theorem imageMajorant_pullback (d : ℕ) {r : ℝ} (hr : 1 < r) :
    (Real.pi/r^2) * imageMajorant d (Real.pi/r) = inverseTheta d r := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have ha : Real.pi^2/(Real.pi/r) = Real.pi*r := by field_simp
  unfold imageMajorant inverseTheta
  rw [ha]
  field_simp

theorem integrable_imageMajorant {d : ℕ} (hd : d ≤ 10) :
    IntegrableOn (imageMajorant d) (Ioo 0 Real.pi) := by
  rw [integrableOn_reciprocal_iff _ Real.pi_pos]
  apply (integrable_inverseTheta hd).congr_fun _ measurableSet_Ioi
  intro r hr
  exact (imageMajorant_pullback d hr).symm

theorem imageMajorant_integral (d : ℕ) :
    (∫ t in Ioo 0 Real.pi, imageMajorant d t) =
      ∫ r in Ioi (1 : ℝ), inverseTheta d r := by
  rw [integral_reciprocal _ Real.pi_pos]
  exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => imageMajorant_pullback d hr)

noncomputable def largeMajorant (d : ℕ) (t : ℝ) : ℝ :=
  t^((d : ℝ)/2-1) * (realTheta t^d-1)

theorem largeMajorant_pullback (d : ℕ) {r : ℝ} (hr : 1 < r) :
    largeMajorant d (Real.pi*r) = Real.pi^((d : ℝ)/2-1) * radialTheta d r := by
  unfold largeMajorant radialTheta
  rw [Real.mul_rpow Real.pi_pos.le (by linarith : 0 ≤ r)]
  ring

theorem integrable_largeMajorant {d : ℕ} (hd : d ≤ 10) :
    IntegrableOn (largeMajorant d) (Ioi Real.pi) := by
  have h : IntegrableOn (fun r : ℝ => Real.pi^((d : ℝ)/2-1) * radialTheta d r) (Ioi 1) :=
    (integrable_radialTheta hd).const_mul (Real.pi^((d : ℝ)/2-1))
  have hc : IntegrableOn (fun r : ℝ => largeMajorant d (Real.pi*r)) (Ioi 1) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    exact (largeMajorant_pullback d hr).symm
  have ht := (integrableOn_Ioi_comp_mul_left_iff (largeMajorant d) 1 Real.pi_pos).mp hc
  simpa only [mul_one] using ht

theorem largeMajorant_integral (d : ℕ) :
    (∫ t in Ioi Real.pi, largeMajorant d t) =
      Real.pi^((d : ℝ)/2) * ∫ r in Ioi (1 : ℝ), radialTheta d r := by
  have h := integral_comp_mul_left_Ioi (largeMajorant d) 1 Real.pi_pos
  simp only [mul_one, smul_eq_mul] at h
  have he : (∫ r in Ioi (1 : ℝ), largeMajorant d (Real.pi*r)) =
      Real.pi^((d : ℝ)/2-1) * ∫ r in Ioi (1 : ℝ), radialTheta d r := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => largeMajorant_pullback d hr)
  rw [he] at h
  have hp : Real.pi * Real.pi^((d : ℝ)/2-1) = Real.pi^((d : ℝ)/2) := by
    calc
      _ = Real.pi^(1 : ℝ) * Real.pi^((d : ℝ)/2-1) := by rw [Real.rpow_one]
      _ = Real.pi^(1 + ((d : ℝ)/2-1)) := (Real.rpow_add Real.pi_pos _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = Real.pi * (Real.pi⁻¹ * ∫ t in Ioi Real.pi, largeMajorant d t) := by
      rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    _ = Real.pi * (Real.pi^((d : ℝ)/2-1) * ∫ r in Ioi (1 : ℝ), radialTheta d r) := by rw [← h]
    _ = _ := by rw [← mul_assoc, hp]

end Legacy.BecknerOnofri.GaussianHeatSplit
