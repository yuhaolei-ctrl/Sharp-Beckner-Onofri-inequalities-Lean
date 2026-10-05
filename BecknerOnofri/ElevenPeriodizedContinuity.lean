module

public import BecknerOnofri.ElevenPeriodizedMass
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-! Continuity of the exact representative-based periodization, including
across the boundary of the fundamental cube. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven

lemma periodizedProfile_lift (x : Fin 11 → ℝ) :
    periodizedProfile (fun i => (x i:UnitAddCircle)) =
      ∑' n : Frequency 11, euclideanProfile (fun i => x i+(n i:ℝ)) := by
  have hm (i : Fin 11) : ∃ n : ℤ, x i = representative (x i:UnitAddCircle)+(n:ℝ) := by
    have he : ((representative (x i:UnitAddCircle):ℝ):UnitAddCircle) = (x i:UnitAddCircle) :=
      AddCircle.coe_equivIco
    have hz : ((x i-representative (x i:UnitAddCircle):ℝ):UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, he, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
    simp only [zsmul_eq_mul, mul_one] at hn
    exact ⟨n, by linarith⟩
  choose n hn using hm
  unfold periodizedProfile
  rw [← (Equiv.addLeft n).tsum_eq (fun m : Frequency 11 =>
    euclideanProfile (fun i => representative (x i:UnitAddCircle)+(m i:ℝ)))]
  apply tsum_congr
  intro m
  congr 1
  funext i
  change representative (x i:UnitAddCircle)+((n i+m i:ℤ):ℝ) = x i+(m i:ℝ)
  rw [Int.cast_add, ← add_assoc, ← hn i]

lemma profile_sum_continuous :
    Continuous (fun x : Fin 11 → ℝ => ∑' n : Frequency 11,
      euclideanProfile (fun i => x i+(n i:ℝ))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let R : ℝ := ‖x‖+1
  let b : Frequency 11 → ℝ := fun n =>
    ((5:ℝ)^11*(122880/Real.pi^6)*(2+22*R^2)^11)*
      Legacy.TorusEndpoint.GreenMultiplierSummability.productMajorant n
  have hs : Summable b :=
    (Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant 11).mul_left _
  have hc : ContinuousOn (fun y : Fin 11 → ℝ => ∑' n : Frequency 11,
      euclideanProfile (fun i => y i+(n i:ℝ))) (Metric.ball x 1) := by
    apply continuousOn_tsum (u := b)
    · intro n
      exact (euclideanProfile_continuous.comp (by fun_prop)).continuousOn
    · exact hs
    · intro n y hy
      rw [Real.norm_eq_abs, abs_of_pos (euclideanProfile_pos _)]
      apply translated_profile_majorant y n (by dsimp [R]; positivity)
      intro i
      have hy' : ‖y-x‖ < 1 := hy
      have hn := norm_le_norm_sub_add y x
      have hi := norm_le_pi_norm y i
      rw [Real.norm_eq_abs] at hi
      dsimp [R]
      linarith
  exact hc.continuousAt (Metric.ball_mem_nhds x (by norm_num))

lemma periodizedProfile_continuous : Continuous periodizedProfile := by
  have hq : IsOpenQuotientMap (fun x : Fin 11 → ℝ => fun i => (x i:UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ : Fin 11 => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, periodizedProfile_lift] using profile_sum_continuous

#print axioms periodizedProfile_continuous
end BecknerOnofri.HighDim.Eleven
