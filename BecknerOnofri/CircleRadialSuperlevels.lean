import BecknerOnofri.CircleRadiusDistribution
import BecknerOnofri.DistributionAERadialUniqueness

/-! Superlevel sets of radial decreasing representatives are centered balls,
up to Haar null sets, with the radius fixed by their measure. -/
noncomputable section
open scoped ENNReal
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1
open DistributionLimit

theorem radial_superlevel_ae_rank_ball {F : Torus 1 → ℝ}
    (hF : AEMeasurable F (torusMeasure 1))
    (hR : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F) (t : ℝ) :
    {x | t<F x}=ᵐ[torusMeasure 1]
      {x | circleRank x<(torusMeasure 1 {y | t<F y}).toReal} := by
  let m := torusMeasure 1 {x | t<F x}
  have hm1 : m≤1 := by
    simpa only [measure_univ] using (measure_mono (μ := torusMeasure 1) (subset_univ {x | t<F x}))
  have hmfin : m≠∞ := measure_ne_top _ _
  have hb : torusMeasure 1 {x | circleRank x<m.toReal}=m := by
    rw [circleRank_sublevel_measure ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hm1)),ENNReal.ofReal_toReal hmfin]
  have hsm : NullMeasurableSet {x | t<F x} (torusMeasure 1) := hF.nullMeasurable measurableSet_Ioi
  have hbm : MeasurableSet {x : Torus 1 | circleRank x<m.toReal} :=
    isOpen_lt circleRank_continuous continuous_const |>.measurableSet
  obtain ⟨s,hs,hFs⟩ := hR
  by_cases hsub : ∀ x∈s,t<F x → circleRank x<m.toReal
  · have ha : {x | t<F x}≤ᵐ[torusMeasure 1] {x | circleRank x<m.toReal} := by
      filter_upwards [hs] with x hx
      exact hsub x hx
    exact ae_eq_of_ae_subset_of_measure_ge ha hb.le hsm (measure_ne_top _ _)
  · push_neg at hsub
    obtain ⟨x,hxs,hxt,hxr⟩ := hsub
    have ha : {x | circleRank x<m.toReal}≤ᵐ[torusMeasure 1] {x | t<F x} := by
      filter_upwards [hs] with y hys
      intro hyr
      have hxy : ‖y 0‖≤‖x 0‖ := by
        change 2*‖x 0‖≥m.toReal at hxr
        change 2*‖y 0‖<m.toReal at hyr
        linarith
      exact hxt.trans_le (hFs y hys x hxs hxy)
    exact (ae_eq_of_ae_subset_of_measure_ge ha hb.ge hbm.nullMeasurableSet (measure_ne_top _ _)).symm

#print axioms radial_superlevel_ae_rank_ball
end BecknerOnofri.PolarizationL1
