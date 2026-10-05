import BecknerOnofri.CircleRadialSuperlevels
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! The extended-nonnegative layer-cake representative of the circle
rearrangement. Infinite values at null exceptional radii are allowed. -/
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open DistributionLimit

def superlevelMeasure (f : Torus 1 → ℝ) (t : ℝ) : ℝ≥0∞ := torusMeasure 1 {x | t<f x}

theorem superlevelMeasure_antitone (f : Torus 1 → ℝ) : Antitone (superlevelMeasure f) := by
  intro s t hst
  exact measure_mono (fun x hx => hst.trans_lt hx)

def layerRearrangement (f : Torus 1 → ℝ) (x : Torus 1) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ),if ENNReal.ofReal (circleRank x)<superlevelMeasure f t then 1 else 0

theorem layerRearrangement_mono {f g : Torus 1 → ℝ} (hfg : f≤ᵐ[torusMeasure 1] g) :
    ∀ x,layerRearrangement f x≤layerRearrangement g x := by
  have hm (t : ℝ) : superlevelMeasure f t≤superlevelMeasure g t := by
    apply measure_mono_ae
    filter_upwards [hfg] with x hx
    exact fun ht => ht.trans_le hx
  intro x
  apply lintegral_mono
  intro t
  by_cases h : ENNReal.ofReal (circleRank x)<superlevelMeasure f t
  · simp only [if_pos h,if_pos (h.trans_le (hm t)),le_refl]
  · simp only [if_neg h]
    exact bot_le

theorem layerRearrangement_radial (f : Torus 1 → ℝ) {x y : Torus 1}
    (hxy : ‖x 0‖≤‖y 0‖) : layerRearrangement f y≤layerRearrangement f x := by
  have hr : ENNReal.ofReal (circleRank x)≤ENNReal.ofReal (circleRank y) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hxy (by norm_num))
  apply lintegral_mono
  intro t
  by_cases h : ENNReal.ofReal (circleRank y)<superlevelMeasure f t
  · simp only [if_pos h,if_pos (hr.trans_lt h),le_refl]
  · simp only [if_neg h]
    exact bot_le

theorem AntitoneRadiusAE.congr {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r f g : α → ℝ} (hf : AntitoneRadiusAE μ r f) (he : f=ᵐ[μ] g) : AntitoneRadiusAE μ r g := by
  obtain ⟨s,hs,hfs⟩ := hf
  refine ⟨{x | x∈s ∧ f x=g x},hs.and he,?_⟩
  intro x hx y hy hxy
  rw [← hx.2,← hy.2]
  exact hfs x hx.1 y hy.1 hxy

lemma layerRearrangement_eq_ofReal_of_measurable {f F : Torus 1 → ℝ}
    (hF : Measurable F) (hD : IdentDistrib F f (torusMeasure 1) (torusMeasure 1))
    (hR : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F) :
    layerRearrangement f=ᵐ[torusMeasure 1] (fun x => ENNReal.ofReal (F x)) := by
  have hlevels (t : ℝ) : ∀ᵐ x ∂torusMeasure 1,
      (t<F x ↔ ENNReal.ofReal (circleRank x)<superlevelMeasure f t) := by
    have he := radial_superlevel_ae_rank_ball hF.aemeasurable hR t
    have hm := hD.measure_mem_eq (s := Ioi t) measurableSet_Ioi
    change torusMeasure 1 {x | t<F x}=torusMeasure 1 {x | t<f x} at hm
    filter_upwards [he] with x hx
    have hh : (t<F x ↔ circleRank x<(superlevelMeasure f t).toReal) := by
      have hiff : (t<F x ↔ circleRank x<(torusMeasure 1 {y | t<F y}).toReal) := Iff.of_eq hx
      rw [hm] at hiff
      exact hiff
    exact hh.trans (ENNReal.ofReal_lt_iff_lt_toReal (circleRank_nonneg x) (measure_ne_top _ _)).symm
  have hmeas : MeasurableSet {p : ℝ × Torus 1 |
      (p.1<F p.2 ↔ ENNReal.ofReal (circleRank p.2)<superlevelMeasure f p.1)} := by
    apply MeasurableSet.iff
    · exact measurableSet_lt measurable_fst (hF.comp measurable_snd)
    · exact measurableSet_lt (ENNReal.measurable_ofReal.comp
        (circleRank_continuous.measurable.comp measurable_snd))
        ((superlevelMeasure_antitone f).measurable.comp measurable_fst)
  have hxt : ∀ᵐ x ∂torusMeasure 1,∀ᵐ t : ℝ ∂volume,
      (t<F x ↔ ENNReal.ofReal (circleRank x)<superlevelMeasure f t) :=
    (Measure.ae_ae_comm hmeas).mp (Filter.Eventually.of_forall hlevels)
  filter_upwards [hxt] with x hx
  unfold layerRearrangement
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ),if t<F x then (1 : ℝ≥0∞) else 0 := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hx] with t ht
      simp only [ht]
    _ = ENNReal.ofReal (F x) := by
      have he : (fun t : ℝ => if t<F x then (1 : ℝ≥0∞) else 0)=
          (Iio (F x)).indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext t
        simp only [Set.indicator,mem_Iio]
      rw [he,lintegral_indicator measurableSet_Iio,lintegral_one,Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iio]
      simp only [Iio_inter_Ioi,Real.volume_Ioo,sub_zero]

#print axioms layerRearrangement_mono
#print axioms layerRearrangement_eq_ofReal_of_measurable
end BecknerOnofri.PolarizationL1
