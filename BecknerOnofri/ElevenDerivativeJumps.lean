import BecknerOnofri.ElevenDefectCorner
import BecknerOnofri.VariationalCurveConvexity

/-! Explicit one-sided derivative jumps in the coexistence proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven

lemma pressureReal_convex : ConvexOn ℝ (Ioo 0 22) pressureReal :=
  pressure_toReal_convexOn (by norm_num) (convex_Ioo _ _)
    (fun β hβ => pressure_eq_real hβ.1.le hβ.2)

lemma transition_interior : globalTransition ∈ interior (Ioo (0:ℝ) 22) := by
  rw [isOpen_Ioo.interior_eq]
  exact ⟨transition_pos, transition_upper.trans (by norm_num)⟩

lemma pressure_left_derivative :
    HasDerivWithinAt pressureReal 0 (Iio globalTransition) globalTransition := by
  have hbnear : ∀ᶠ β : ℝ in 𝓝 globalTransition, 0 < β :=
    isOpen_Ioi.mem_nhds transition_pos
  apply (hasDerivWithinAt_const globalTransition (Iio globalTransition) (0:ℝ)).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      hbnear.filter_mono nhdsWithin_le_nhds] with β hβ hb
    change (pressure 11 β).toReal = 0
    rw [(pressure_zero_iff hb.le).mpr hβ.le, EReal.toReal_zero]
  · exact pressureReal_at_transition

lemma pressure_right_derivative_positive : ∃ s : ℝ, 0 < s ∧
    s ≤ derivWithin pressureReal (Ioi globalTransition) globalTransition := by
  obtain ⟨s,hs,hline⟩ := exists_positive_support
  refine ⟨s,hs,?_⟩
  rw [pressureReal_convex.rightDeriv_eq_sInf_slope_of_mem_interior transition_interior]
  apply le_csInf
  · obtain ⟨y,hy,h22⟩ := exists_between (transition_upper.trans (show (2063:ℝ)/100 < 22 by norm_num))
    exact ⟨slope pressureReal globalTransition y, y, ⟨⟨transition_pos.trans hy,h22⟩,hy⟩,rfl⟩
  · rintro z ⟨y,⟨hy,hyb⟩,rfl⟩
    rw [slope_def_field, pressureReal_at_transition, sub_zero]
    exact (le_div_iff₀ (sub_pos.mpr hyb)).mpr (by simpa only [mul_comm] using hline y hy.1.le hy.2)

lemma defect_zero_above {A : ℝ} (hA : zeroDefectCoefficient ≤ A) : coefficientDefect 11 A = 0 := by
  have hpos := zeroDefectCoefficient_pos.trans_le hA
  rw [defect_pressure hpos]
  apply (pressure_zero_iff (couplingOf_pos hpos).le).mpr
  rw [← couplingOf_transition]
  unfold couplingOf
  apply div_le_div_of_nonneg_left (spectralThreshold_pos (d := 11) (by norm_num)).le
    (by positivity [zeroDefectCoefficient_pos])
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (by positivity)

lemma defect_right_derivative :
    HasDerivWithinAt defectReal 0 (Ioi zeroDefectCoefficient) zeroDefectCoefficient := by
  apply (hasDerivWithinAt_const zeroDefectCoefficient (Ioi zeroDefectCoefficient) (0:ℝ)).congr
  · intro A hA
    change (coefficientDefect 11 A).toReal = 0
    rw [defect_zero_above hA.le, EReal.toReal_zero]
  · exact defectReal_at_transition

lemma defect_convex_neighborhood : ∃ ε : ℝ, 0 < ε ∧
    ConvexOn ℝ (Ioo (zeroDefectCoefficient-ε) (zeroDefectCoefficient+ε)) defectReal := by
  obtain ⟨ε,hε,_,hfin⟩ := defect_finite_neighborhood
  refine ⟨ε,hε,defect_toReal_convexOn (by norm_num) (convex_Ioo _ _) (fun A hA => ?_)⟩
  exact hfin A (abs_lt.mpr ⟨by linarith [hA.1],by linarith [hA.2]⟩)

lemma defect_left_derivative_negative : ∃ s : ℝ, s < 0 ∧
    derivWithin defectReal (Iio zeroDefectCoefficient) zeroDefectCoefficient ≤ s := by
  obtain ⟨ε,hε,hconv⟩ := defect_convex_neighborhood
  have hint : zeroDefectCoefficient ∈ interior
      (Ioo (zeroDefectCoefficient-ε) (zeroDefectCoefficient+ε)) := by
    rw [isOpen_Ioo.interior_eq]
    constructor <;> linarith
  have hder := hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show zeroDefectCoefficient ∉
    Iio zeroDefectCoefficient by simp)).mp hder
  obtain ⟨s,hs,hline⟩ := exists_negative_defect_support
  refine ⟨s,hs,le_of_tendsto hlim ?_⟩
  filter_upwards [self_mem_nhdsWithin,
      defect_finite_eventually.filter_mono nhdsWithin_le_nhds] with A hA hf
  have h := hline A
  rw [hf] at h
  have hr := EReal.coe_le_coe_iff.mp h
  rw [slope_def_field, defectReal_at_transition, sub_zero]
  exact (div_le_iff_of_neg (sub_neg.mpr hA)).mpr (by simpa only [mul_comm] using hr)

/-- Both actual one-sided derivatives exist and have the asserted strict jump. -/
theorem pressure_derivative_jump : ∃ p : ℝ, 0 < p ∧
    HasDerivWithinAt pressureReal 0 (Iio globalTransition) globalTransition ∧
    HasDerivWithinAt pressureReal p (Ioi globalTransition) globalTransition := by
  obtain ⟨s,hs,hsp⟩ := pressure_right_derivative_positive
  exact ⟨_,hs.trans_le hsp,pressure_left_derivative,
    pressureReal_convex.hasDerivWithinAt_rightDeriv_of_mem_interior transition_interior⟩

theorem defect_derivative_jump : ∃ q : ℝ, q < 0 ∧
    HasDerivWithinAt defectReal q (Iio zeroDefectCoefficient) zeroDefectCoefficient ∧
    HasDerivWithinAt defectReal 0 (Ioi zeroDefectCoefficient) zeroDefectCoefficient := by
  obtain ⟨s,hs,hqs⟩ := defect_left_derivative_negative
  obtain ⟨ε,hε,hconv⟩ := defect_convex_neighborhood
  have hint : zeroDefectCoefficient ∈ interior
      (Ioo (zeroDefectCoefficient-ε) (zeroDefectCoefficient+ε)) := by
    rw [isOpen_Ioo.interior_eq]
    constructor <;> linarith
  exact ⟨_,hqs.trans_lt hs,hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint,
    defect_right_derivative⟩

#print axioms pressure_derivative_jump
#print axioms defect_derivative_jump
#print axioms pressure_left_derivative
#print axioms pressure_right_derivative_positive
#print axioms defect_right_derivative
#print axioms defect_left_derivative_negative
end BecknerOnofri.HighDim.Eleven
