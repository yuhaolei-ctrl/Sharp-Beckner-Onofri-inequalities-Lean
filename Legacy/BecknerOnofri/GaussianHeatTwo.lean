import Legacy.BecknerOnofri.GaussianHeatSplit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The boundary exponent s = 1 in the actual Gaussian heat splitting. -/
noncomputable section
open MeasureTheory Set
namespace Legacy.BecknerOnofri.GaussianHeatTwo
open GaussianLattice GaussianHeatSplit ThetaDomination

/-- The central function has an elementary logarithmic value at the boundary exponent. -/
theorem central_one {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    GaussianCentral.central 1 x = -Real.log x - 1 + x := by
  unfold GaussianCentral.central
  norm_num only [sub_self, Real.rpow_zero, Real.rpow_one, div_one]
  have hi : (∫ z in Ioo 0 (1-x), (1 : ℝ)/(1-z)) = -Real.log x := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1-x),
      intervalIntegral.integral_comp_sub_left]
    simp only [sub_sub_cancel, sub_zero]
    rw [integral_one_div_of_pos hx (by norm_num)]
    simp
  rw [hi]
  ring

theorem centralIntegrand_one (a t : ℝ) : centralIntegrand 1 a t = Real.pi/t-1 := by
  norm_num [centralIntegrand]

theorem centralIntegrand_one_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (centralIntegrand 1 a) (Ioo a Real.pi) := by
  have hc : ContinuousOn (fun t : ℝ => Real.pi/t-1) (Icc a Real.pi) :=
    (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (ha.trans_le ht.1))).sub continuousOn_const
  have hi : IntegrableOn (fun t : ℝ => Real.pi/t-1) (Ioo a Real.pi) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  exact hi.congr_fun (fun t _ => (centralIntegrand_one a t).symm) measurableSet_Ioo

theorem rawCentral_one {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    rawCentral 1 a = Real.pi * (Real.log Real.pi - Real.log a - 1) + a := by
  have hi : IntervalIntegrable (fun t : ℝ => (1 : ℝ)/t) volume a Real.pi := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hap.le]
    exact continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (ha.trans_le ht.1))
  unfold rawCentral
  simp_rw [centralIntegrand_one]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hap.le]
  have he : (fun t : ℝ => Real.pi/t-1) = fun t => Real.pi*(1/t)-1 := by
    funext t
    ring
  rw [he, intervalIntegral.integral_sub (hi.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_one_div_of_pos ha Real.pi_pos]
  rw [Real.log_div Real.pi_ne_zero ha.ne']
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem rawCentral_one_eq_central {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    rawCentral 1 a = Real.pi * GaussianCentral.central 1 (a/Real.pi) := by
  rw [rawCentral_one ha hap, central_one (div_pos ha Real.pi_pos)
    ((div_lt_one Real.pi_pos).mpr hap), Real.log_div ha.ne' Real.pi_ne_zero]
  field_simp
  ring

theorem smallImage_two (a t : ℝ) : smallImage 2 a t = Real.pi * imageMajorant 2 t := by
  norm_num [smallImage, imageMajorant, div_eq_mul_inv]
  ring

theorem smallImage_two_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (smallImage 2 a) (Ioo a Real.pi) := by
  have hi : IntegrableOn (fun t => Real.pi * imageMajorant 2 t) (Ioo a Real.pi) :=
    ((integrable_imageMajorant (d := 2) (by decide)).mono_set
      (show Ioo a Real.pi ⊆ Ioo 0 Real.pi from fun _ ht => ⟨ha.trans ht.1, ht.2⟩)).const_mul Real.pi
  exact hi.congr_fun (fun t _ => (smallImage_two a t).symm) measurableSet_Ioo

theorem smallImage_two_integral_le {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioo a Real.pi, smallImage 2 a t) ≤
      Real.pi * ∫ r in Ioi (1 : ℝ), inverseTheta 2 r := by
  simp_rw [smallImage_two]
  rw [integral_const_mul, ← imageMajorant_integral]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply setIntegral_mono_set (integrable_imageMajorant (by decide : 2 ≤ 10)) _
    (show Ioo a Real.pi ⊆ Ioo 0 Real.pi from fun _ ht => ⟨ha.trans ht.1, ht.2⟩).eventuallyLE
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact imageMajorant_nonneg 2 ht.1

theorem large_mellin_two (a t : ℝ) : mellinIntegrand 2 a t = largeMajorant 2 t := by
  norm_num [mellinIntegrand, largeMajorant]

/-- The complete s=1 Mellin integral is bounded by the actual J_2 integral. -/
theorem mellin_integral_two_le {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    (∫ t in Ioi a, mellinIntegrand 2 a t) ≤
      rawCentral 1 a + Real.pi * thetaIntegral realTheta 2 := by
  have he : (∫ t in Ioo a Real.pi, mellinIntegrand 2 a t) =
      rawCentral 1 a + ∫ t in Ioo a Real.pi, smallImage 2 a t := by
    calc
      _ = ∫ t in Ioo a Real.pi, centralIntegrand 1 a t + smallImage 2 a t := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        simpa using mellin_small_eq 2 a t (ha.trans ht.1)
      _ = _ := integral_add (centralIntegrand_one_integrable ha) (smallImage_two_integrable ha)
  rw [mellin_integral_split (by decide : 0 < 2) ha hap, he]
  have hl : (∫ t in Ioi Real.pi, mellinIntegrand 2 a t) =
      Real.pi * ∫ r in Ioi (1 : ℝ), radialTheta 2 r := by
    simp_rw [large_mellin_two]
    simpa using largeMajorant_integral 2
  rw [hl, thetaIntegral_split (by decide : 2 ≤ 10)]
  have h := smallImage_two_integral_le ha
  linarith

/-- No differentiability, summability or heat bound remains as a hypothesis. -/
theorem gaussianEnergy_two_le {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    gaussianEnergy 2 a ≤
      Real.pi * (Real.log Real.pi - Real.log a - 1 + thetaIntegral realTheta 2) + a := by
  rw [gaussianEnergy_mellin (by decide : 0 < 2) ha]
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.Gamma_one,
    div_one, one_mul]
  have h := mellin_integral_two_le ha hap
  rw [rawCentral_one ha hap] at h
  nlinarith only [h]

#print axioms central_one
#print axioms gaussianEnergy_two_le
end Legacy.BecknerOnofri.GaussianHeatTwo
