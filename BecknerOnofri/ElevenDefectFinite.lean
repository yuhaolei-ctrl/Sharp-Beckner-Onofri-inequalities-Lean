import BecknerOnofri.ElevenTransitionZeroSet

/-! A real neighborhood of the transition coefficient has finite actual
defect, by the exact coefficient-pressure involution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven

def couplingOf (A : ℝ) : ℝ := spectralThreshold 11/(2*A*(2*Real.pi)^11)

lemma zeroDefectCoefficient_pos : 0 < zeroDefectCoefficient := by
  unfold zeroDefectCoefficient
  exact div_pos (spectralThreshold_pos (by norm_num)) (by positivity [transition_pos])

lemma couplingOf_pos {A : ℝ} (hA : 0 < A) : 0 < couplingOf A := by
  unfold couplingOf
  exact div_pos (spectralThreshold_pos (by norm_num)) (by positivity)

lemma couplingOf_involutive {A : ℝ} (hA : A ≠ 0) : couplingOf (couplingOf A) = A := by
  have hs := (spectralThreshold_pos (d := 11) (by norm_num)).ne'
  have hp := Real.pi_ne_zero
  unfold couplingOf
  field_simp

lemma couplingOf_transition : couplingOf zeroDefectCoefficient = globalTransition :=
  couplingOf_involutive transition_pos.ne'

lemma defect_pressure {A : ℝ} (hA : 0 < A) : coefficientDefect 11 A = pressure 11 (couplingOf A) := by
  have h := pressure_eq_coefficientDefect (d := 11) (by norm_num) (couplingOf_pos hA)
  change pressure 11 (couplingOf A) = coefficientDefect 11 (couplingOf (couplingOf A)) at h
  rw [couplingOf_involutive hA.ne'] at h
  exact h.symm

lemma defect_at_transition : coefficientDefect 11 zeroDefectCoefficient = 0 := by
  rw [defect_pressure zeroDefectCoefficient_pos, couplingOf_transition, pressure_at_transition]

lemma defectReal_at_transition : defectReal zeroDefectCoefficient = 0 := by
  simp only [defectReal, defect_at_transition, EReal.toReal_zero]

lemma defect_finite_eventually : ∀ᶠ A in 𝓝 zeroDefectCoefficient,
    coefficientDefect 11 A = (defectReal A:EReal) := by
  have hcont : ContinuousAt couplingOf zeroDefectCoefficient := by
    unfold couplingOf
    fun_prop (disch := positivity [zeroDefectCoefficient_pos])
  have hlim : Tendsto couplingOf (𝓝 zeroDefectCoefficient) (𝓝 globalTransition) := by
    simpa only [couplingOf_transition] using hcont.tendsto
  have hJ : Ioo (0:ℝ) 22 ∈ 𝓝 globalTransition := isOpen_Ioo.mem_nhds
    ⟨transition_pos, transition_upper.trans (by norm_num)⟩
  filter_upwards [hlim.eventually hJ, isOpen_Ioi.mem_nhds zeroDefectCoefficient_pos] with A hb hA
  have h := pressure_eq_real hb.1.le hb.2
  rw [← defect_pressure hA] at h
  exact (EReal.coe_toReal (by rw [h]; exact EReal.coe_ne_top _)
    (by rw [h]; exact EReal.coe_ne_bot _)).symm

lemma defect_finite_neighborhood : ∃ ε : ℝ, 0 < ε ∧ ε < zeroDefectCoefficient ∧
    ∀ A : ℝ, |A-zeroDefectCoefficient| < ε → coefficientDefect 11 A = (defectReal A:EReal) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp defect_finite_eventually
  refine ⟨min δ (zeroDefectCoefficient/2), lt_min hδ (by positivity [zeroDefectCoefficient_pos]),
    lt_of_le_of_lt (min_le_right _ _) (by linarith [zeroDefectCoefficient_pos]), ?_⟩
  intro A hA
  exact hball (show A ∈ Metric.ball zeroDefectCoefficient δ from
    lt_of_lt_of_le hA (min_le_left _ _))

#print axioms defect_finite_neighborhood
end BecknerOnofri.HighDim.Eleven
