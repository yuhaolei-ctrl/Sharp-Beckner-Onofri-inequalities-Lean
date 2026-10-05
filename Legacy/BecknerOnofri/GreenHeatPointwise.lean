module

public import Legacy.BecknerOnofri.GreenHeatBounds

@[expose] public section

/-! An actual heat-Mellin Green candidate, its pointwise integrability and logarithmic bound. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.GreenHeatPointwise
open HeatDensityApproximation ThetaDomination LogGaussianIntegral

def coordinateRadiusSq {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, (x i)^2

def smallMajorant {d : ℕ} (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  integrand (Real.pi*coordinateRadiusSq x) t + (thetaDecayConstant d) * integrand (Real.pi/4) t

theorem coordinateRadiusSq_pos {d : ℕ} {x : Fin d → ℝ} (hx : x ≠ 0) :
    0 < coordinateRadiusSq x := by
  have hn : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  obtain ⟨i, hi⟩ := hn
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

theorem coordinateRadiusSq_le {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ 1/2) :
    coordinateRadiusSq x ≤ (d : ℝ)/4 := by
  calc
    coordinateRadiusSq x ≤ ∑ _ : Fin d, (1/4 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hx i
      nlinarith [sq_abs (x i), mul_self_le_mul_self (abs_nonneg (x i)) hi]
    _ = _ := by simp; ring

theorem rpow_mellin_cancel {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t^((d : ℝ)/2-1)*t^(-(d : ℝ)/2) = t⁻¹ := by
  rw [← Real.rpow_add ht]
  convert! Real.rpow_neg_one t using 1
  congr 1
  ring

theorem weighted_heatKernel_le_small {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) {t : ℝ} (ht : t ∈ Ioo 0 (1/4)) :
    t^((d : ℝ)/2-1)*heatKernel t (fun i => (x i : UnitAddCircle)) ≤ smallMajorant x t := by
  have hk := ShiftedGaussianBound.heatKernel_le ht.1 x hx
  have hi := theta_image_bound (d := d) ht.1 ht.2.le
  have hp := mul_le_mul_of_nonneg_left hk (Real.rpow_pos_of_pos ht.1 ((d : ℝ)/2-1)).le
  rw [← mul_assoc, rpow_mellin_cancel ht.1] at hp
  have htinv : 0 ≤ t⁻¹ := (inv_pos.mpr ht.1).le
  have hbound := mul_le_mul_of_nonneg_left hi htinv
  have he : smallMajorant x t = t⁻¹ * (Real.exp (-Real.pi/t * coordinateRadiusSq x) +
      (thetaDecayConstant d) * Real.exp (-(Real.pi/4)/t)) := by
    unfold smallMajorant integrand
    rw [show -(Real.pi*coordinateRadiusSq x)/t = -Real.pi/t*coordinateRadiusSq x by ring]
    ring
  rw [he]
  change t^((d : ℝ)/2-1)*heatKernel t (fun i => (x i : UnitAddCircle)) ≤ _
  change t⁻¹ * (Real.exp (-Real.pi/t*coordinateRadiusSq x) +
    realTheta (Real.pi/(4*t))^d-1) ≥ _ at hp
  nlinarith only [hp, hbound]

theorem heatMellin_abs_le_small {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ 1/2) {t : ℝ} (ht : t ∈ Ioo 0 (1/4)) :
    |heatMellin (fun i => (x i : UnitAddCircle)) t| ≤ smallMajorant x t + t^((d : ℝ)/2-1) := by
  have hp := (Real.rpow_pos_of_pos ht.1 ((d : ℝ)/2-1)).le
  have hk := (heatKernel_pos ht.1 (fun i => (x i : UnitAddCircle))).le
  have habs : |heatKernel t (fun i => (x i : UnitAddCircle))-1| ≤
      heatKernel t (fun i => (x i : UnitAddCircle))+1 := by
    rw [abs_le]
    constructor <;> linarith
  unfold heatMellin
  rw [abs_mul, abs_of_nonneg hp]
  have hh := mul_le_mul_of_nonneg_left habs hp
  have hb := weighted_heatKernel_le_small x hx ht
  nlinarith only [hh, hb]

theorem integrable_smallMajorant {d : ℕ} (x : Fin d → ℝ) (hx : x ≠ 0) :
    IntegrableOn (smallMajorant x) (Ioo 0 (1/4)) :=
  (LogGaussianIntegral.integrable (mul_pos Real.pi_pos (coordinateRadiusSq_pos hx)) (by norm_num)).add
    ((LogGaussianIntegral.integrable (by positivity : 0 < Real.pi/4) (by norm_num)).const_mul _)

theorem integrable_smallPower {d : ℕ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => t^((d : ℝ)/2-1)) (Ioo 0 (1/4)) := by
  apply (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1/4)).2
  have : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

theorem integrable_heatMellin_small {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    IntegrableOn (heatMellin (fun i => (x i : UnitAddCircle))) (Ioo 0 (1/4)) := by
  apply ((integrable_smallMajorant x hx0).add (integrable_smallPower hd)).mono'
    ((aestronglyMeasurable_heatMellin _).mono_set (fun t ht => ht.1))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [Real.norm_eq_abs] using! heatMellin_abs_le_small x hx ht

theorem time_partition : Ioo (0 : ℝ) (1/4) ∪ Ici (1/4) = Ioi 0 := by
  ext t
  constructor
  · rintro (ht | ht)
    · exact ht.1
    · change 1/4 ≤ t at ht
      change 0 < t
      linarith
  · intro ht
    by_cases h : t < 1/4
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (le_of_not_gt h)

theorem integrable_heatMellin {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    IntegrableOn (heatMellin (fun i => (x i : UnitAddCircle))) (Ioi 0) := by
  rw [← time_partition, integrableOn_union]
  exact ⟨integrable_heatMellin_small hd x hx hx0, integrable_heatMellin_tail hd _⟩

def heatGreen {d : ℕ} (x : Torus d) : ℝ := (1/2) * ∫ t in Ioi 0, heatMellin x t

def imageConstant (d : ℕ) : ℝ := (thetaDecayConstant d) * (Real.log (Real.pi/4+1/4)-Real.log (Real.pi/4))
def tailIntegral (d : ℕ) : ℝ := ∫ t in Ici (1/4), tailMajorant d t

def upperConstant (d : ℕ) : ℝ :=
  (Real.log (Real.pi*((d : ℝ)/4)+1/4)-Real.log Real.pi)/2 + (imageConstant d+tailIntegral d)/2

def lowerConstant (d : ℕ) : ℝ :=
  ((∫ t in Ioo 0 (1/4), t^((d : ℝ)/2-1))+tailIntegral d)/2

theorem heatMellin_integral_split {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    (∫ t in Ioi 0, heatMellin (fun i => (x i : UnitAddCircle)) t) =
      (∫ t in Ioo 0 (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t)+
      ∫ t in Ici (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t := by
  rw [← time_partition, setIntegral_union]
  · exact disjoint_left.mpr (fun t ht hu => (not_lt_of_ge hu) ht.2)
  · exact measurableSet_Ici
  · exact integrable_heatMellin_small hd x hx hx0
  · exact integrable_heatMellin_tail hd _

theorem small_integral_le {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    (∫ t in Ioo 0 (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t) ≤
      (∫ t in Ioo 0 (1/4), integrand (Real.pi*coordinateRadiusSq x) t) + imageConstant d := by
  have hb : (∫ t in Ioo 0 (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t) ≤
      ∫ t in Ioo 0 (1/4), smallMajorant x t := by
    apply integral_mono_ae (integrable_heatMellin_small hd x hx hx0) (integrable_smallMajorant x hx0)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hh := weighted_heatKernel_le_small x hx ht
    have hp := (Real.rpow_pos_of_pos ht.1 ((d : ℝ)/2-1)).le
    unfold heatMellin
    nlinarith only [hh, hp]
  unfold smallMajorant at hb
  rw [integral_add, integral_const_mul] at hb
  · have hg := mul_le_mul_of_nonneg_left
      (integral_le_log (by positivity : 0 < Real.pi/4) (by norm_num : (0 : ℝ) ≤ 1/4))
      (thetaDecayConstant_nonneg d)
    unfold imageConstant
    linarith
  · exact LogGaussianIntegral.integrable (mul_pos Real.pi_pos (coordinateRadiusSq_pos hx0)) (by norm_num)
  · exact (LogGaussianIntegral.integrable (by positivity : 0 < Real.pi/4) (by norm_num)).const_mul _

theorem tail_integral_abs_le {d : ℕ} (hd : 0 < d) (x : Torus d) :
    |∫ t in Ici (1/4), heatMellin x t| ≤ tailIntegral d := by
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (integrable_heatMellin_tail hd x).abs
    ((integrable_tailMajorant hd).mono_set (fun t ht => by change 1/4 ≤ t at ht; change 0 < t; linarith))
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact heatMellin_abs_le_tail x ht

theorem heatGreen_le_log {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    heatGreen (fun i => (x i : UnitAddCircle)) ≤ -Real.log (Real.sqrt (coordinateRadiusSq x))+upperConstant d := by
  have hs := small_integral_le hd x hx hx0
  have hl := half_integral_le_neg_log_sqrt (coordinateRadiusSq_pos hx0) (coordinateRadiusSq_le hx)
    (by norm_num : (0 : ℝ) ≤ 1/4)
  have ht := (le_abs_self _).trans (tail_integral_abs_le hd (fun i => (x i : UnitAddCircle)))
  unfold heatGreen upperConstant
  rw [heatMellin_integral_split hd x hx hx0]
  linarith

theorem heatGreen_lower {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, |x i| ≤ 1/2) (hx0 : x ≠ 0) :
    -lowerConstant d ≤ heatGreen (fun i => (x i : UnitAddCircle)) := by
  have hs : -(∫ t in Ioo 0 (1/4), t^((d : ℝ)/2-1)) ≤
      ∫ t in Ioo 0 (1/4), heatMellin (fun i => (x i : UnitAddCircle)) t := by
    rw [← integral_neg]
    apply integral_mono_ae (integrable_smallPower hd).neg (integrable_heatMellin_small hd x hx hx0)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hk := (heatKernel_pos ht.1 (fun i => (x i : UnitAddCircle))).le
    have hp := (Real.rpow_pos_of_pos ht.1 ((d : ℝ)/2-1)).le
    unfold heatMellin
    change -t^((d : ℝ)/2-1) ≤ _
    nlinarith [mul_nonneg hp hk]
  have ht := (abs_le.mp (tail_integral_abs_le hd (fun i => (x i : UnitAddCircle)))).1
  unfold heatGreen lowerConstant
  rw [heatMellin_integral_split hd x hx hx0]
  linarith

#print axioms integrable_heatMellin
#print axioms heatGreen_le_log
#print axioms heatGreen_lower
end Legacy.BecknerOnofri.GreenHeatPointwise
