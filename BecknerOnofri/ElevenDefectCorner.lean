module

public import BecknerOnofri.ElevenPressureCorner
public import BecknerOnofri.ElevenDefectFinite

@[expose] public section

/-! The nonzero transition optimizer supplies the second affine support of
the actual defect, with strictly negative slope given by its physical energy. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

lemma exists_negative_defect_support : ∃ s : ℝ, s < 0 ∧
    ∀ A : ℝ, (((A-zeroDefectCoefficient)*s:ℝ):EReal) ≤ coefficientDefect 11 A := by
  obtain ⟨U,hU,hUnz,hM⟩ := exists_nonzero_limit_optimizer
  obtain ⟨u,huL,hu,hm,_,_,hmax⟩ := continuous_optimizer_of_L2 (by norm_num) transition_pos U hU hM
  have hvalue : functional (spectralThreshold 11/(2*globalTransition)) U = 0 := by
    have h := pressure_eq_dual (by norm_num) transition_pos u hu hmax
    rw [pressure_at_transition, dualFunctional_eq_toL2 (by norm_num) _ u hu hm, huL] at h
    exact_mod_cast h.symm
  have hepos : 0 < criticalEnergy U := by
    have hh := coefficient_norm_sq_le_energy (fourierIsometry 11 U) hU.2.1 hU.2.2
    rw [(fourierIsometry 11).norm_map] at hh
    exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hUnz)) hh
  let E := (2*Real.pi)^11*criticalEnergy U
  have hE : 0 < E := mul_pos (by positivity) hepos
  have hcoef : zeroDefectCoefficient*(2*Real.pi)^11 = spectralThreshold 11/(2*globalTransition) := by
    unfold zeroDefectCoefficient
    have hp := Real.pi_ne_zero
    have hb := transition_pos.ne'
    field_simp
  refine ⟨-E, neg_neg_of_pos hE, fun A => ?_⟩
  have hh : RawAttainment.rawFunctional A (RawAttainment.realValue U) ≤ coefficientDefect 11 A :=
    le_iSup_of_le (RawAttainment.realValue U)
      (le_iSup_of_le (RawAttainment.realValue_sobolev U hU) le_rfl)
  rw [RawAttainment.rawFunctional_realValue (by norm_num) A U hU] at hh
  have he : functional (A*(2*Real.pi)^11) U = (A-zeroDefectCoefficient)*(-E) := by
    unfold functional at hvalue ⊢
    rw [← hcoef] at hvalue
    dsimp [E]
    nlinarith
  rwa [he] at hh

theorem defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < zeroDefectCoefficient ∧
      ∀ A : ℝ, |A-zeroDefectCoefficient| < ε →
        coefficientDefect 11 A = (defectReal A:EReal)) ∧
    ¬ DifferentiableAt ℝ defectReal zeroDefectCoefficient := by
  refine ⟨defect_finite_neighborhood, ?_⟩
  obtain ⟨s,hs,hline⟩ := exists_negative_defect_support
  apply not_differentiable_of_two_supports hs.ne defectReal_at_transition
  · filter_upwards [defect_finite_eventually] with A hA
    have h := coefficientDefect_nonneg 11 A
    rw [hA] at h
    exact_mod_cast h
  · filter_upwards [defect_finite_eventually] with A hA
    have h := hline A
    rw [hA] at h
    exact_mod_cast h

#print axioms defect_corner
end BecknerOnofri.HighDim.Eleven
