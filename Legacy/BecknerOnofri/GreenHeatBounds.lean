import Legacy.BecknerOnofri.ShiftedGaussianBound
import Legacy.BecknerOnofri.LogGaussianIntegral
import Legacy.BecknerOnofri.ThetaDecayAllDimensions

/-! Time measurability and integrable pointwise majorants for the actual heat kernel. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint Legacy.TorusEndpoint.GreenMultiplierSummability
open scoped BigOperators
namespace Legacy.BecknerOnofri.GreenHeatPointwise
open HeatDensityApproximation TorusHeatPositivity TorusHeatBounds ThetaDomination

def heatTailConstant (d : ℕ) (T : ℝ) : ℝ :=
  ∑' k : Frequency d, nonzeroHeatWeight (T/2) k

theorem heatTailConstant_nonneg (d : ℕ) (T : ℝ) : 0 ≤ heatTailConstant d T :=
  tsum_nonneg (nonzeroHeatWeight_nonneg (T/2))

theorem heatWeight_time_bound {d : ℕ} {T t : ℝ} (hT : 0 < T) (ht : T ≤ t)
    {k : Frequency d} (hk : k ≠ 0) :
    heatWeight t k ≤ heatWeight (T/2) k * Real.exp (-Real.pi*t/2) := by
  have hr := radiusSq_one_le hk
  have hprod := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hr)
  have htr : t/2+(T/2)*radiusSq k ≤ t*radiusSq k := by nlinarith
  have hp := mul_le_mul_of_nonneg_left htr Real.pi_pos.le
  unfold heatWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem heatKernel_sub_one_abs_le {d : ℕ} {T t : ℝ} (hT : 0 < T) (ht : T ≤ t)
    (x : Torus d) : |heatKernel t x-1| ≤ heatTailConstant d T * Real.exp (-Real.pi*t/2) := by
  have hc : ‖torusTheta t x-1‖ ≤ heatTailConstant d T * Real.exp (-Real.pi*t/2) := by
    rw [torusTheta_sub_one (lt_of_lt_of_le hT ht)]
    apply tsum_of_norm_bounded
      ((nonzeroHeatWeight_summable (by positivity : 0 < T/2)).hasSum.mul_right
        (Real.exp (-Real.pi*t/2)))
    intro k
    simp only [norm_mul, mFourier_norm_apply, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (nonzeroHeatWeight_nonneg t k)]
    by_cases hk : k = 0
    · simp [nonzeroHeatWeight, hk]
    · simpa only [nonzeroHeatWeight, if_neg hk] using heatWeight_time_bound hT ht hk
  have hh : |heatKernel t x-1| ≤ ‖torusTheta t x-1‖ := by
    simpa [heatKernel] using Complex.abs_re_le_norm (torusTheta t x-1)
  exact hh.trans hc

theorem measurable_heatKernel_time {d : ℕ} (x : Torus d) :
    Measurable (fun t : ℝ => heatKernel t x) := by
  unfold heatKernel torusTheta
  apply Complex.measurable_re.comp
  apply Measurable.tsum
  intro k
  apply Measurable.mul _ measurable_const
  apply Complex.measurable_ofReal.comp
  exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).mul continuous_const)).measurable

def heatMellin {d : ℕ} (x : Torus d) (t : ℝ) : ℝ :=
  t^((d : ℝ)/2-1) * (heatKernel t x-1)

def tailMajorant (d : ℕ) (t : ℝ) : ℝ :=
  heatTailConstant d (1/4) * (t^((d : ℝ)/2-1) * Real.exp (-Real.pi*t/2))

theorem aestronglyMeasurable_heatMellin {d : ℕ} (x : Torus d) :
    AEStronglyMeasurable (heatMellin x) (volume.restrict (Ioi 0)) := by
  have hp : ContinuousOn (fun t : ℝ => t^((d : ℝ)/2-1)) (Ioi 0) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
  exact (hp.aestronglyMeasurable measurableSet_Ioi).mul
    ((measurable_heatKernel_time x).sub measurable_const).aestronglyMeasurable

theorem integrable_tailMajorant {d : ℕ} (hd : 0 < d) :
    IntegrableOn (tailMajorant d) (Ioi 0) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith : (-1 : ℝ) < (d : ℝ)/2-1)
    (by norm_num : (1 : ℝ) ≤ 1) (by positivity : 0 < Real.pi/2)
  have he : (fun t : ℝ => t^((d : ℝ)/2-1)*Real.exp (-(Real.pi/2)*t^(1:ℝ))) =
      (fun t : ℝ => t^((d : ℝ)/2-1)*Real.exp (-Real.pi*t/2)) := by
    ext t
    rw [Real.rpow_one]
    congr 2
    ring
  rw [he] at hi
  exact hi.const_mul _

theorem heatMellin_abs_le_tail {d : ℕ} (x : Torus d) {t : ℝ} (ht : 1/4 ≤ t) :
    |heatMellin x t| ≤ tailMajorant d t := by
  have ht0 : 0 < t := by linarith
  unfold heatMellin tailMajorant
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hh := mul_le_mul_of_nonneg_left
    (heatKernel_sub_one_abs_le (by norm_num : (0 : ℝ)<1/4) ht x)
    (Real.rpow_pos_of_pos ht0 ((d : ℝ)/2-1)).le
  nlinarith only [hh]

theorem integrable_heatMellin_tail {d : ℕ} (hd : 0 < d) (x : Torus d) :
    IntegrableOn (heatMellin x) (Ici (1/4)) := by
  have hs : Ici (1/4 : ℝ) ⊆ Ioi 0 := fun t ht => by change 1/4 ≤ t at ht; change 0 < t; linarith
  apply ((integrable_tailMajorant hd).mono_set hs).mono'
    ((aestronglyMeasurable_heatMellin x).mono_set hs)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  simpa only [Real.norm_eq_abs] using heatMellin_abs_le_tail x ht

theorem theta_image_bound {d : ℕ} {t : ℝ} (ht : 0 < t) (htT : t ≤ 1/4) :
    realTheta (Real.pi/(4*t))^d-1 ≤ thetaDecayConstant d * Real.exp (-(Real.pi/4)/t) := by
  have hp : Real.pi ≤ Real.pi/(4*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*t)).2
    nlinarith [Real.pi_pos]
  have hb := realTheta_pow_sub_one_le d hp
  have he : -(Real.pi/(4*t)) = -(Real.pi/4)/t := by ring
  rwa [he] at hb

#print axioms heatKernel_sub_one_abs_le
#print axioms integrable_heatMellin_tail
end Legacy.BecknerOnofri.GreenHeatPointwise
