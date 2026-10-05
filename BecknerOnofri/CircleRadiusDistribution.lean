import BecknerOnofri.PolarizationMetricGeometry
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi

/-! The normalized radius rank on the actual circle is uniformly distributed. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1

def circleRank (x : Torus 1) : ℝ := 2*‖x 0‖

lemma circleRank_nonneg (x : Torus 1) : 0≤circleRank x := by
  exact mul_nonneg (by norm_num) (norm_nonneg _)

lemma circleRank_le_one (x : Torus 1) : circleRank x≤1 := by
  have h := AddCircle.norm_le_half_period 1 (x := x 0) (by norm_num)
  norm_num at h
  dsimp [circleRank]
  linarith

theorem circleRank_continuous : Continuous circleRank := by
  unfold circleRank
  fun_prop

theorem circleRank_sublevel_measure {a : ℝ} (ha0 : 0≤a) (ha1 : a≤1) :
    torusMeasure 1 {x | circleRank x<a}=ENNReal.ofReal a := by
  have hmp : MeasurePreserving (fun x : Torus 1 => x 0) (torusMeasure 1)
      (AddCircle.haarAddCircle (T := 1)) :=
    measurePreserving_eval (fun _ : Fin 1 => AddCircle.haarAddCircle (T := 1)) 0
  have he : {x : Torus 1 | circleRank x<a}=
      (fun x : Torus 1 => x 0) ⁻¹' Metric.ball (0 : UnitAddCircle) (a/2) := by
    ext x
    simp only [mem_setOf_eq,mem_preimage,Metric.mem_ball,dist_zero_right,circleRank]
    constructor <;> intro h <;> linarith
  rw [he,hmp.measure_preimage measurableSet_ball.nullMeasurableSet]
  have hv : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle (T := 1) := by
    simpa using AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  rw [← hv,← measure_congr (AddCircle.closedBall_ae_eq_ball (x := (0 : UnitAddCircle)) (ε := a/2)),
    AddCircle.volume_closedBall]
  congr 1
  rw [show 2*(a/2)=a by ring,min_eq_right ha1]

#print axioms circleRank_sublevel_measure
end BecknerOnofri.PolarizationL1
