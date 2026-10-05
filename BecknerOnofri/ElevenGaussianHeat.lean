import BecknerOnofri.ElevenThetaIntegrability
import Legacy.BecknerOnofri.GaussianHeatSplit

/-! The same Gaussian/Mellin splitting as Section 3, now applied to d=11.
The old d≤10 integrability assumptions are discharged here by the actual
infinite-series integrability proof in ElevenThetaIntegrability. -/
noncomputable section
open MeasureTheory Set
open Legacy.BecknerOnofri Legacy.BecknerOnofri.GaussianHeatSplit
open Legacy.BecknerOnofri.GaussianLattice Legacy.BecknerOnofri.ThetaDomination
namespace BecknerOnofri.HighDim.Eleven.Heat

theorem integrable_radialTheta {d : ℕ} (hd : d = 11) :
    IntegrableOn (radialTheta d) (Ioi (1 : ℝ)) := by
  have hi := (show IntegrableOn (thetaIntegrand realTheta d) (Ici (1 : ℝ)) from by simpa [hd] using theta_integrable).mono_set (Ioi_subset_Ici_self)
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

theorem integrable_inverseTheta {d : ℕ} (hd : d = 11) :
    IntegrableOn (inverseTheta d) (Ioi (1 : ℝ)) := by
  have hi := (show IntegrableOn (thetaIntegrand realTheta d) (Ici (1 : ℝ)) from by simpa [hd] using theta_integrable).mono_set (Ioi_subset_Ici_self)
  have hm : AEStronglyMeasurable (inverseTheta d) (volume.restrict (Ioi 1)) :=
    measurable_inv.aestronglyMeasurable.mul
      (((measurable_realTheta.comp (measurable_const.mul measurable_id)).pow_const d).sub
        measurable_const).aestronglyMeasurable
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (inverseTheta_nonneg d hr), thetaIntegrand_eq_add]
  linarith [radialTheta_nonneg d hr]

theorem thetaIntegral_split {d : ℕ} (hd : d = 11) :
    thetaIntegral realTheta d = (∫ r in Ioi (1 : ℝ), radialTheta d r) +
      ∫ r in Ioi (1 : ℝ), inverseTheta d r := by
  unfold thetaIntegral
  rw [integral_Ici_eq_integral_Ioi]
  simp_rw [thetaIntegrand_eq_add]
  exact integral_add (integrable_radialTheta hd) (integrable_inverseTheta hd)

theorem integrable_imageMajorant {d : ℕ} (hd : d = 11) :
    IntegrableOn (imageMajorant d) (Ioo 0 Real.pi) := by
  rw [integrableOn_reciprocal_iff _ Real.pi_pos]
  apply (integrable_inverseTheta hd).congr_fun _ measurableSet_Ioi
  intro r hr
  exact (imageMajorant_pullback d hr).symm

theorem integrable_largeMajorant {d : ℕ} (hd : d = 11) :
    IntegrableOn (largeMajorant d) (Ioi Real.pi) := by
  have h : IntegrableOn (fun r : ℝ => Real.pi^((d : ℝ)/2-1) * radialTheta d r) (Ioi 1) :=
    (integrable_radialTheta hd).const_mul (Real.pi^((d : ℝ)/2-1))
  have hc : IntegrableOn (fun r : ℝ => largeMajorant d (Real.pi*r)) (Ioi 1) := by
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    exact (largeMajorant_pullback d hr).symm
  have ht := (integrableOn_Ioi_comp_mul_left_iff (largeMajorant d) 1 Real.pi_pos).mp hc
  simpa only [mul_one] using ht

theorem smallImage_integral_le {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d = 11)
    {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioo a Real.pi, smallImage d a t) ≤
      Real.pi^((d : ℝ)/2) * ∫ r in Ioi (1 : ℝ), inverseTheta d r := by
  have hsub : Ioo a Real.pi ⊆ Ioo 0 Real.pi := fun _ ht => ⟨lt_trans ha ht.1, ht.2⟩
  have him := (integrable_imageMajorant hd10).mono_set hsub
  have hfirst : (∫ t in Ioo a Real.pi, smallImage d a t) ≤
      Real.pi^((d : ℝ)/2) * ∫ t in Ioo a Real.pi, imageMajorant d t := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (smallImage_integrable hd3 ha) (him.const_mul _) measurableSet_Ioo
      (fun t ht => smallImage_le hd3 ha ht.1)
  have hmono : (∫ t in Ioo a Real.pi, imageMajorant d t) ≤
      ∫ t in Ioo 0 Real.pi, imageMajorant d t := by
    apply setIntegral_mono_set (integrable_imageMajorant hd10) _ hsub.eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact imageMajorant_nonneg d ht.1
  calc
    _ ≤ Real.pi^((d : ℝ)/2) * ∫ t in Ioo a Real.pi, imageMajorant d t := hfirst
    _ ≤ Real.pi^((d : ℝ)/2) * ∫ t in Ioo 0 Real.pi, imageMajorant d t :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg Real.pi_pos.le _)
    _ = _ := by rw [imageMajorant_integral]

theorem large_mellin_integral_le {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d = 11)
    {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    (∫ t in Ioi Real.pi, mellinIntegrand d a t) ≤
      Real.pi^((d : ℝ)/2) * ∫ r in Ioi (1 : ℝ), radialTheta d r := by
  have hm : IntegrableOn (mellinIntegrand d a) (Ioi Real.pi) :=
    (integrable_mellinIntegrand (by omega : 0 < d) ha).mono_set (fun _ ht => lt_trans hap ht)
  calc
    _ ≤ ∫ t in Ioi Real.pi, largeMajorant d t :=
      setIntegral_mono_on hm (integrable_largeMajorant hd10) measurableSet_Ioi
        (fun t ht => large_mellin_le hd3 ha (lt_trans hap ht))
    _ = _ := largeMajorant_integral d

theorem mellin_integral_le_raw {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d = 11)
    {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    (∫ t in Ioi a, mellinIntegrand d a t) ≤
      rawCentral ((d : ℝ)/2) a + Real.pi^((d : ℝ)/2) * thetaIntegral realTheta d := by
  have he : (∫ t in Ioo a Real.pi, mellinIntegrand d a t) =
      rawCentral ((d : ℝ)/2) a + ∫ t in Ioo a Real.pi, smallImage d a t := by
    calc
      _ = ∫ t in Ioo a Real.pi, centralIntegrand ((d : ℝ)/2) a t + smallImage d a t :=
        setIntegral_congr_fun measurableSet_Ioo (fun t ht => mellin_small_eq d a t (lt_trans ha ht.1))
      _ = _ := integral_add
        (centralIntegrand_integrable _ _ (half_dimension_gt_one hd3) ha) (smallImage_integrable hd3 ha)
  rw [mellin_integral_split (by omega : 0 < d) ha hap, he]
  calc
    _ ≤ rawCentral ((d : ℝ)/2) a +
        Real.pi^((d : ℝ)/2) * (∫ r in Ioi (1 : ℝ), inverseTheta d r) +
        Real.pi^((d : ℝ)/2) * (∫ r in Ioi (1 : ℝ), radialTheta d r) :=
      add_le_add (add_le_add (le_refl _) (smallImage_integral_le hd3 hd10 ha))
        (large_mellin_integral_le hd3 hd10 ha hap)
    _ = _ := by rw [thetaIntegral_split hd10]; ring

theorem gaussianEnergy_le_raw {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d = 11)
    {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    gaussianEnergy d a ≤ (1 / Real.Gamma ((d : ℝ)/2)) *
      (rawCentral ((d : ℝ)/2) a + Real.pi^((d : ℝ)/2) * thetaIntegral realTheta d) := by
  rw [gaussianEnergy_mellin (by omega : 0 < d) ha]
  apply mul_le_mul_of_nonneg_left (mellin_integral_le_raw hd3 hd10 ha hap)
  exact (one_div_pos.mpr (Real.Gamma_pos_of_pos (by linarith [half_dimension_gt_one hd3]))).le

/-- Gaussian heat splitting with the central contribution expressed on `(0,1-a/pi)`. -/

theorem gaussianEnergy_le_central {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d = 11)
    {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    gaussianEnergy d a ≤ (Real.pi^((d : ℝ)/2) / Real.Gamma ((d : ℝ)/2)) *
      (GaussianCentral.central ((d : ℝ)/2) (a/Real.pi) + thetaIntegral realTheta d) := by
  have hc : rawCentral ((d : ℝ)/2) a = Real.pi^((d : ℝ)/2) *
      GaussianCentral.central ((d : ℝ)/2) (a/Real.pi) :=
    GaussianCentral.rawCentral_eq _ a (half_dimension_gt_one hd3) ha hap
  calc
    _ ≤ (1 / Real.Gamma ((d : ℝ)/2)) *
        (rawCentral ((d : ℝ)/2) a + Real.pi^((d : ℝ)/2) * thetaIntegral realTheta d) :=
      gaussianEnergy_le_raw hd3 hd10 ha hap
    _ = _ := by rw [hc]; ring

#print axioms gaussianEnergy_le_central
end BecknerOnofri.HighDim.Eleven.Heat
