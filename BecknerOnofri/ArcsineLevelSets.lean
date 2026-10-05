import BecknerOnofri.ArcsineProductBins
import Mathlib.MeasureTheory.Measure.Prod

/-! Atomlessness of the actual radial coordinate on every positive-dimensional torus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ArcsineCircle

theorem sineSquare_le_iff {a : ℝ} (ha : a∈Icc (0:ℝ) 1) (x : UnitAddCircle) :
    sineSquare x≤a ↔ ‖x‖≤radius a := by
  have hx := angle_mem x
  have hs : 0≤Real.sin (Real.pi*‖x‖) := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [Real.pi_pos,hx.2])
  have hroot : Real.sqrt a∈Icc (-1:ℝ) 1 :=
    ⟨by linarith [Real.sqrt_nonneg a],Real.sqrt_le_one.mpr ha.2⟩
  unfold sineSquare radius
  nth_rw 1 [← Real.sq_sqrt ha.1]
  rw [sq_le_sq₀ hs (Real.sqrt_nonneg a)]
  rw [← Real.strictMonoOn_arcsin.le_iff_le (Real.sin_mem_Icc _) hroot,
    Real.arcsin_sin (by linarith [Real.pi_pos,hx.1,hx.2]) hx.2]
  exact (le_div_iff₀' Real.pi_pos).symm

theorem sineSquare_level_null (a : ℝ) :
    (AddCircle.haarAddCircle (T:=1)) {x : UnitAddCircle | sineSquare x=a}=0 := by
  by_cases ha : a∈Icc (0:ℝ) 1
  · rw [uniform_eq_volume]
    apply measure_mono_null (t := Metric.closedBall (0:UnitAddCircle) (radius a) \
        Metric.ball 0 (radius a))
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,dist_zero_right,not_lt]
      exact ⟨(sineSquare_le_iff ha x).mp hx.le,
        le_of_not_gt (fun h => ((sineSquare_lt_iff ha x).mpr h).ne hx)⟩
    · exact (ae_le_set.mp AddCircle.closedBall_ae_eq_ball.le)
  · rw [show {x : UnitAddCircle | sineSquare x=a}=∅ by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      intro hx
      exact ha (hx ▸ sineSquare_mem x),measure_empty]

theorem sineSquare_ne_ae (a : ℝ) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T:=1), sineSquare x≠a := by
  exact ae_iff.mpr (by simpa using sineSquare_level_null a)

end BecknerOnofri.HighDim.ArcsineCircle

namespace BecknerOnofri.HighDim.ArcsineProductBins
open ArcsineCircle

theorem radialSum_level_null {d : ℕ} (hd : 0<d) (a : ℝ) :
    torusMeasure d {x | radialSum x=a}=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hp : ∀ᵐ z ∂(AddCircle.haarAddCircle (T:=1)).prod (torusMeasure n),
      sineSquare z.1+radialSum z.2≠a := by
    rw [ae_prod_iff_ae_ae]
    · rw [ae_ae_comm]
      · apply Filter.Eventually.of_forall
        intro y
        filter_upwards [sineSquare_ne_ae (a-radialSum y)] with x hx
        intro he
        apply hx
        linarith
      · exact (measurableSet_eq_fun
          ((sineSquare_continuous.comp continuous_fst).add
            ((radialSum_continuous n).comp continuous_snd)).measurable measurable_const).compl
    · exact (measurableSet_eq_fun
        ((sineSquare_continuous.comp continuous_fst).add
          ((radialSum_continuous n).comp continuous_snd)).measurable measurable_const).compl
  have hm := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => AddCircle.haarAddCircle (T:=1)) 0).quasiMeasurePreserving.ae hp
  have hn : ∀ᵐ x ∂torusMeasure (n+1),radialSum x≠a := by
    filter_upwards [hm] with x hx
    simpa [radialSum,MeasurableEquiv.piFinSuccAbove_apply,Fin.sum_univ_succ] using hx
  simpa using ae_iff.mp hn

#print axioms sineSquare_level_null
#print axioms radialSum_level_null
end BecknerOnofri.HighDim.ArcsineProductBins
