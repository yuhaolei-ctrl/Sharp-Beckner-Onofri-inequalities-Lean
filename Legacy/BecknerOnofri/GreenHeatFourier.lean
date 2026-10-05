module

public import Legacy.BecknerOnofri.GreenHeatMeasurable
public import Legacy.TorusEndpoint.GreenMellinMultiplier

@[expose] public section

/-! Fubini for the actual heat-Mellin integral and exact Green Fourier multipliers. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace Legacy.BecknerOnofri.GreenHeatPointwise
open HeatDensityApproximation TorusHeatPositivity TorusHeatBounds GreenMultiplierSummability
  GreenMellinMultiplier

theorem integrable_heatMellin_space {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Torus d => heatMellin x t) (torusMeasure d) :=
  ((heatKernel_integrable ht).sub (integrable_const 1)).const_mul _

def spatialNorm (d : ℕ) (t : ℝ) : ℝ := ∫ x, ‖heatMellin x t‖ ∂torusMeasure d

theorem measurable_spatialNorm (d : ℕ) : Measurable (spatialNorm d) :=
  ((measurable_heatMellin_joint d).norm.stronglyMeasurable.integral_prod_left).measurable

theorem spatialNorm_nonneg (d : ℕ) (t : ℝ) : 0 ≤ spatialNorm d t := integral_nonneg (fun _ => norm_nonneg _)

theorem spatialNorm_le_small {d : ℕ} {t : ℝ} (ht : 0 < t) :
    spatialNorm d t ≤ 2*t^((d : ℝ)/2-1) := by
  have hi : Integrable (fun x : Torus d => t^((d : ℝ)/2-1)*(heatKernel t x+1)) (torusMeasure d) :=
    ((heatKernel_integrable ht).add (integrable_const 1)).const_mul _
  have hh : spatialNorm d t ≤ ∫ x, t^((d : ℝ)/2-1)*(heatKernel t x+1) ∂torusMeasure d := by
    apply integral_mono_ae (integrable_heatMellin_space ht).norm hi
    filter_upwards with x
    have hpos := (heatKernel_pos ht x).le
    have habs : |heatKernel t x-1| ≤ heatKernel t x+1 := by rw [abs_le]; constructor <;> linarith
    simpa only [heatMellin, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _)] using
      mul_le_mul_of_nonneg_left habs (Real.rpow_pos_of_pos ht ((d : ℝ)/2-1)).le
  rw [integral_const_mul, integral_add (heatKernel_integrable ht) (integrable_const 1), heatKernel_mass ht] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  linarith only [hh]

theorem spatialNorm_le_tail {d : ℕ} {t : ℝ} (ht : 1/4 ≤ t) :
    spatialNorm d t ≤ tailMajorant d t := by
  have ht0 : 0 < t := by linarith
  have h := integral_mono_ae (integrable_heatMellin_space (d := d) ht0).norm
    (integrable_const (tailMajorant d t)) (by
      filter_upwards with x
      simpa only [Real.norm_eq_abs] using heatMellin_abs_le_tail x ht)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using! h

theorem integrable_spatialNorm {d : ℕ} (hd : 0 < d) : IntegrableOn (spatialNorm d) (Ioi 0) := by
  rw [← time_partition, integrableOn_union]
  constructor
  · apply ((integrable_smallPower hd).const_mul 2).mono' (measurable_spatialNorm d).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (spatialNorm_nonneg d t)]
    exact spatialNorm_le_small ht.1
  · have hs : Ici (1/4 : ℝ) ⊆ Ioi 0 := fun t ht => by change 1/4 ≤ t at ht; change 0 < t; linarith
    apply ((integrable_tailMajorant hd).mono_set hs).mono' (measurable_spatialNorm d).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (spatialNorm_nonneg d t)]
    exact spatialNorm_le_tail ht

/-- Joint absolute integrability; no pointwise bound at the singular spatial origin is assumed. -/
theorem integrable_heatMellin_product {d : ℕ} (hd : 0 < d) :
    Integrable (fun p : Torus d × ℝ => heatMellin p.1 p.2)
      ((torusMeasure d).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff' (measurable_heatMellin_joint d).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrable_heatMellin_space ht
  · exact integrable_spatialNorm hd

theorem integrable_heatGreen {d : ℕ} (hd : 0 < d) :
    Integrable (heatGreen (d := d)) (torusMeasure d) :=
  (integrable_heatMellin_product hd).integral_prod_left.const_mul _

def fourierMellin {d : ℕ} (k : Frequency d) (x : Torus d) (t : ℝ) : ℂ :=
  UnitAddTorus.mFourier (-k) x * (heatMellin x t : ℂ)

theorem integrable_fourierMellin_product {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    Integrable (Function.uncurry (fourierMellin k))
      ((torusMeasure d).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_heatMellin_product hd).ofReal.bdd_mul
    (((UnitAddTorus.mFourier (-k)).continuous.comp continuous_fst).measurable.aestronglyMeasurable)
  filter_upwards with p
  exact le_of_eq (mFourier_norm_apply (-k) p.1)

theorem heatKernel_sub_one_fourier {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    densityFourier (fun x : Torus d => heatKernel t x-1) k = (nonzeroHeatWeight t k : ℂ) := by
  have he : (fun x : Torus d => ((heatKernel t x-1 : ℝ) : ℂ)) =
      absoluteFourierSeries (fun k => (nonzeroHeatWeight t k : ℂ)) := by
    funext x
    have hh : ((heatKernel t x-1 : ℝ) : ℂ) = torusTheta t x-1 := by
      apply Complex.ext
      · simp [heatKernel]
      · simp [torusTheta_im_zero ht]
    rw [hh, torusTheta_sub_one ht x]
    rfl
  change UnitAddTorus.mFourierCoeff (fun x : Torus d => ((heatKernel t x-1 : ℝ) : ℂ)) k = _
  rw [he]
  apply absoluteFourierSeries_coefficient
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (nonzeroHeatWeight_nonneg t _)] using
    (nonzeroHeatWeight_summable ht : Summable (nonzeroHeatWeight t : Frequency d → ℝ))

theorem fourierMellin_integral_space {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    (∫ x, fourierMellin k x t ∂torusMeasure d) =
      ((t^((d : ℝ)/2-1)*nonzeroHeatWeight t k : ℝ) : ℂ) := by
  have he (x : Torus d) : fourierMellin k x t =
      (t^((d : ℝ)/2-1) : ℝ) *
        (UnitAddTorus.mFourier (-k) x * ((heatKernel t x-1 : ℝ) : ℂ)) := by
    unfold fourierMellin heatMellin
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul]
  change (t^((d : ℝ)/2-1) : ℝ) * densityFourier (fun x => heatKernel t x-1) k = _
  rw [heatKernel_sub_one_fourier ht]
  push_cast
  rfl

theorem heatGreen_fourier {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    densityFourier (heatGreen (d := d)) k = (greenMultiplier d k : ℂ) := by
  have hp (x : Torus d) : UnitAddTorus.mFourier (-k) x * (heatGreen x : ℂ) =
      (1/2 : ℂ) * ∫ t in Ioi 0, fourierMellin k x t := by
    unfold heatGreen fourierMellin
    push_cast
    rw [← integral_complex_ofReal, integral_const_mul]
    ring
  unfold densityFourier
  simp_rw [hp]
  rw [integral_const_mul, integral_integral_swap (integrable_fourierMellin_product hd k)]
  have he : (∫ t in Ioi 0, ∫ x, fourierMellin k x t ∂torusMeasure d) =
      ((∫ t in Ioi 0, t^((d : ℝ)/2-1)*nonzeroHeatWeight t k : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fourierMellin_integral_space ht k
  rw [he, nonzeroHeatWeight_mellin_integral hd k]
  push_cast
  ring

#print axioms integrable_heatMellin_product
#print axioms heatGreen_fourier
end Legacy.BecknerOnofri.GreenHeatPointwise
