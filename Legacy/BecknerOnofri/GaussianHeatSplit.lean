import Legacy.BecknerOnofri.GaussianHeatChanges
import Legacy.BecknerOnofri.GaussianMellin
import Legacy.BecknerOnofri.GaussianCentralSubstitution

/-!
# Splitting the actual shifted Mellin integral at pi

The small-time theta image and the large-time theta contribution are bounded
by the two integrable pieces of J_d. Every power has real exponent d/2, and
the reciprocal and scaling changes of variables are proved in GaussianHeatChanges.
-/

open MeasureTheory Set

namespace Legacy.BecknerOnofri.GaussianHeatSplit

open GaussianLattice ThetaDomination

noncomputable def centralIntegrand (s a t : ℝ) : ℝ :=
  (t-a)^(s-1) * ((Real.pi/t)^s-1)

noncomputable def rawCentral (s a : ℝ) : ℝ :=
  ∫ t in Ioo a Real.pi, centralIntegrand s a t

noncomputable def smallImage (d : ℕ) (a t : ℝ) : ℝ :=
  (t-a)^((d : ℝ)/2-1) * (Real.pi/t)^((d : ℝ)/2) *
    (realTheta (Real.pi^2/t)^d-1)

theorem half_dimension_gt_one {d : ℕ} (hd : 3 ≤ d) : 1 < (d : ℝ)/2 := by
  have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem centralIntegrand_integrable (s a : ℝ) (hs : 1 < s) (ha : 0 < a) :
    IntegrableOn (centralIntegrand s a) (Ioo a Real.pi) := by
  have hpow : Continuous (fun t : ℝ => (t-a)^(s-1)) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  have hdiv : ContinuousOn (fun t : ℝ => Real.pi/t) (Icc a Real.pi) :=
    continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))
  have hp := hdiv.rpow_const (p := s) (fun _ _ => Or.inr (by linarith : 0 ≤ s))
  have hc : ContinuousOn (centralIntegrand s a) (Icc a Real.pi) :=
    hpow.continuousOn.mul (hp.sub continuousOn_const)
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem mellin_small_eq (d : ℕ) (a t : ℝ) (ht : 0 < t) :
    mellinIntegrand d a t = centralIntegrand ((d : ℝ)/2) a t + smallImage d a t := by
  unfold mellinIntegrand centralIntegrand smallImage
  rw [realTheta_pow_jacobi ht d]
  ring

theorem smallImage_integrable {d : ℕ} (hd : 3 ≤ d) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (smallImage d a) (Ioo a Real.pi) := by
  have hm : IntegrableOn (mellinIntegrand d a) (Ioo a Real.pi) :=
    (integrable_mellinIntegrand (by omega : 0 < d) ha).mono_set (fun _ ht => ht.1)
  have hc := centralIntegrand_integrable ((d : ℝ)/2) a (half_dimension_gt_one hd) ha
  have hi : IntegrableOn (fun t => mellinIntegrand d a t - centralIntegrand ((d : ℝ)/2) a t)
      (Ioo a Real.pi) := hm.sub hc
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  dsimp only
  rw [mellin_small_eq d a t (lt_trans ha ht.1)]
  ring

theorem imageMajorant_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ imageMajorant d t := by
  exact mul_nonneg (inv_nonneg.mpr ht.le)
    (theta_defect_nonneg d (div_pos (sq_pos_of_pos Real.pi_pos) ht))

theorem radial_jacobi_factor (s t : ℝ) (ht : 0 < t) :
    t^(s-1) * (Real.pi/t)^s = Real.pi^s/t := by
  rw [Real.rpow_sub ht, Real.rpow_one, Real.div_rpow Real.pi_pos.le ht.le]
  field_simp [(Real.rpow_pos_of_pos ht s).ne']

theorem smallImage_le {d : ℕ} (hd : 3 ≤ d) {a t : ℝ} (ha : 0 < a) (ht : a < t) :
    smallImage d a t ≤ Real.pi^((d : ℝ)/2) * imageMajorant d t := by
  have ht0 := lt_trans ha ht
  have hs := half_dimension_gt_one hd
  have hp : (t-a)^((d : ℝ)/2-1) ≤ t^((d : ℝ)/2-1) :=
    Real.rpow_le_rpow (sub_pos.mpr ht).le (by linarith) (by linarith)
  have hz := theta_defect_nonneg d (div_pos (sq_pos_of_pos Real.pi_pos) ht0)
  unfold smallImage imageMajorant
  calc
    _ ≤ t^((d : ℝ)/2-1) * (Real.pi/t)^((d : ℝ)/2) *
        (realTheta (Real.pi^2/t)^d-1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (div_pos Real.pi_pos ht0).le _)) hz
    _ = _ := by rw [radial_jacobi_factor _ _ ht0]; ring

theorem large_mellin_le {d : ℕ} (hd : 3 ≤ d) {a t : ℝ} (ha : 0 < a) (ht : a < t) :
    mellinIntegrand d a t ≤ largeMajorant d t := by
  have hs := half_dimension_gt_one hd
  apply mul_le_mul_of_nonneg_right _ (theta_defect_nonneg d (lt_trans ha ht))
  exact Real.rpow_le_rpow (sub_pos.mpr ht).le (by linarith) (by linarith)

theorem smallImage_integral_le {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
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

theorem large_mellin_integral_le {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
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

theorem mellin_integral_split {d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 < a) (hap : a < Real.pi) :
    (∫ t in Ioi a, mellinIntegrand d a t) =
      (∫ t in Ioo a Real.pi, mellinIntegrand d a t) +
      ∫ t in Ioi Real.pi, mellinIntegrand d a t := by
  have hm := integrable_mellinIntegrand hd ha
  have hsmall : IntegrableOn (mellinIntegrand d a) (Ioo a Real.pi) :=
    hm.mono_set (fun _ ht => ht.1)
  have hlarge : IntegrableOn (mellinIntegrand d a) (Ici Real.pi) :=
    hm.mono_set (fun _ ht => lt_of_lt_of_le hap ht)
  have hset : Ioo a Real.pi ∪ Ici Real.pi = Ioi a := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact lt_of_lt_of_le hap ht
    · intro ht
      by_cases hp : t < Real.pi
      · exact Or.inl ⟨ht, hp⟩
      · exact Or.inr (le_of_not_gt hp)
  have hdis : Disjoint (Ioo a Real.pi) (Ici Real.pi) :=
    disjoint_left.mpr (fun _ ht hu => (not_lt_of_ge hu) ht.2)
  rw [← hset, setIntegral_union hdis measurableSet_Ici hsmall hlarge,
    integral_Ici_eq_integral_Ioi]

/-- The actual Mellin integral is bounded by its central contribution plus
pi^s J_d. All image and large-time integrability has already been proved. -/
theorem mellin_integral_le_raw {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
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

theorem gaussianEnergy_le_raw {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    {a : ℝ} (ha : 0 < a) (hap : a < Real.pi) :
    gaussianEnergy d a ≤ (1 / Real.Gamma ((d : ℝ)/2)) *
      (rawCentral ((d : ℝ)/2) a + Real.pi^((d : ℝ)/2) * thetaIntegral realTheta d) := by
  rw [gaussianEnergy_mellin (by omega : 0 < d) ha]
  apply mul_le_mul_of_nonneg_left (mellin_integral_le_raw hd3 hd10 ha hap)
  exact (one_div_pos.mpr (Real.Gamma_pos_of_pos (by linarith [half_dimension_gt_one hd3]))).le

/-- Gaussian heat splitting with the central contribution expressed on `(0,1-a/pi)`. -/
theorem gaussianEnergy_le_central {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
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

end Legacy.BecknerOnofri.GaussianHeatSplit

#print axioms Legacy.BecknerOnofri.GaussianHeatSplit.mellin_integral_le_raw
#print axioms Legacy.BecknerOnofri.GaussianHeatSplit.gaussianEnergy_le_raw
#print axioms Legacy.BecknerOnofri.GaussianHeatSplit.gaussianEnergy_le_central
