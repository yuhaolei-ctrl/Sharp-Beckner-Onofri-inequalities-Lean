module

public import BecknerOnofri.V2.Reaudit.Compactness.Coexistence
public import BecknerOnofri.ElevenDefectFinite
public import BecknerOnofri.VariationalCurveConvexity
public import BecknerOnofri.ElevenUniformHessian
public import BecknerOnofri.SupportingLineCorner
public import BecknerOnofri.Entropy

@[expose] public section

/-! # Proposition 4.9: Hessian, corners, derivative jumps, on top of the new coexistence argument

The supporting-line arguments of the printed proof (`eq:section4-pressure-supporting-line`,
`eq:section4-pressure-derivative-jump`, `eq:section4-defect-affine-functions`,
`eq:section4-defect-derivative-jump`) are the existing legacy ones; the legacy statements, however, take
their two states from the old theorems `coexistence` / `exists_nonzero_limit_optimizer`.  Here the
same proofs are repeated with the two states supplied by the new compactness argument
(`Compactness.coexistence`, `Compactness.transition_limit`).  The Hessian (`eq:section4-uniform-strict-hessian`)
and the pure convexity/zero-set facts do not involve the old coexistence theorem and are reused. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.Compactness
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment (Admissible functional)

/-! ## Small generic facts (copies of lemmas of the legacy corner modules, which cannot be imported
because those modules import the old `ElevenCoexistence`) -/

theorem minimizer_pressureValue_zero (ρ : ProbabilityDensity 11)
    (hρ : IsGlobalMinimizer Eleven.globalTransition ρ) : pressureValue Eleven.globalTransition ρ = 0 := by
  apply le_antisymm
  · simpa only [Eleven.pressure_at_transition] using
      Eleven.pressureValue_le_pressure Eleven.globalTransition ρ hρ.1
  · simpa only [pressureValue, uniformDensity_spectralEnergy, EReal.coe_ennreal_zero,
      mul_zero, uniformDensity_entropy, EReal.coe_zero, sub_zero] using
        hρ.2 (uniformDensity 11) (uniformDensity_finiteEntropy 11)

theorem pressure_left_derivative :
    HasDerivWithinAt Eleven.pressureReal 0 (Iio Eleven.globalTransition) Eleven.globalTransition := by
  have hbnear : ∀ᶠ β : ℝ in 𝓝 Eleven.globalTransition, 0 < β :=
    isOpen_Ioi.mem_nhds Eleven.transition_pos
  apply (hasDerivWithinAt_const Eleven.globalTransition (Iio Eleven.globalTransition)
    (0 : ℝ)).congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      hbnear.filter_mono nhdsWithin_le_nhds] with β hβ hb
    change (pressure 11 β).toReal = 0
    rw [(Eleven.pressure_zero_iff hb.le).mpr hβ.le, EReal.toReal_zero]
  · exact pressureReal_at_transition

theorem transition_interior : Eleven.globalTransition ∈ interior (Ioo (0 : ℝ) 22) := by
  rw [isOpen_Ioo.interior_eq]
  exact transition_mem_Ioo

theorem defect_zero_above {A : ℝ} (hA : Eleven.zeroDefectCoefficient ≤ A) :
    coefficientDefect 11 A = 0 := by
  have hpos := Eleven.zeroDefectCoefficient_pos.trans_le hA
  rw [Eleven.defect_pressure hpos]
  apply (Eleven.pressure_zero_iff (Eleven.couplingOf_pos hpos).le).mpr
  rw [← Eleven.couplingOf_transition]
  unfold Eleven.couplingOf
  apply div_le_div_of_nonneg_left (spectralThreshold_pos (d := 11) (by norm_num)).le
    (by positivity [Eleven.zeroDefectCoefficient_pos])
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (by positivity)

theorem defect_right_derivative :
    HasDerivWithinAt Eleven.defectReal 0 (Ioi Eleven.zeroDefectCoefficient)
      Eleven.zeroDefectCoefficient := by
  apply (hasDerivWithinAt_const Eleven.zeroDefectCoefficient (Ioi Eleven.zeroDefectCoefficient)
    (0 : ℝ)).congr
  · intro A hA
    change (coefficientDefect 11 A).toReal = 0
    rw [defect_zero_above hA.le, EReal.toReal_zero]
  · exact Eleven.defectReal_at_transition

theorem defect_convex_neighborhood : ∃ ε : ℝ, 0 < ε ∧
    ConvexOn ℝ (Ioo (Eleven.zeroDefectCoefficient - ε) (Eleven.zeroDefectCoefficient + ε))
      Eleven.defectReal := by
  obtain ⟨ε, hε, -, hfin⟩ := Eleven.defect_finite_neighborhood
  refine ⟨ε, hε, defect_toReal_convexOn (by norm_num) (convex_Ioo _ _) (fun A hA => ?_)⟩
  exact hfin A (abs_lt.mpr ⟨by linarith [hA.1], by linarith [hA.2]⟩)

/-! ## The pressure: supporting line at `ρ_tr` -/

theorem exists_positive_support : ∃ s : ℝ, 0 < s ∧
    ∀ β : ℝ, 0 ≤ β → β < 22 → (β - Eleven.globalTransition) * s ≤ Eleven.pressureReal β := by
  obtain ⟨ρ, hρ, -, -, hnon⟩ := coexistence.2
  let Q := ∑' k, spectralTerm ρ k
  let s := Q / (2 * spectralThreshold 11)
  have he : Eleven.globalTransition * s = entropy ρ := by
    have h := minimizer_pressureValue_zero ρ hρ
    rw [Eleven.pressureValue_eq_real Eleven.globalTransition ρ hρ.1] at h
    have hr : Eleven.globalTransition / (2 * spectralThreshold 11) * Q - entropy ρ = 0 := by
      exact_mod_cast h
    calc
      _ = Eleven.globalTransition / (2 * spectralThreshold 11) * Q := by dsimp [s]; ring
      _ = _ := sub_eq_zero.mp hr
  have hEnt : 0 < entropy ρ := lt_of_le_of_ne (entropy_nonneg ρ hρ.1)
    (fun h => hnon ((entropy_eq_zero_iff ρ hρ.1).mp h.symm))
  have hs : 0 < s := by nlinarith [Eleven.transition_pos]
  refine ⟨s, hs, fun β hβ hb => ?_⟩
  have hv := Eleven.pressureValue_le_pressure β ρ hρ.1
  rw [Eleven.pressureValue_eq_real β ρ hρ.1, Eleven.pressure_eq_real hβ hb] at hv
  have hr : β / (2 * spectralThreshold 11) * Q - entropy ρ ≤ Eleven.pressureReal β := by
    exact_mod_cast hv
  have hm : β / (2 * spectralThreshold 11) * Q = β * s := by dsimp [s]; ring
  rw [hm, ← he] at hr
  nlinarith

/-- `eq:section4-pressure-supporting-line` and the corner of `P_11` at `β_gm`. -/
theorem pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (Eleven.pressureReal β : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.pressureReal Eleven.globalTransition := by
  refine ⟨fun β hβ hb => Eleven.pressure_eq_real hβ.le hb, ?_⟩
  obtain ⟨s, hs, hline⟩ := exists_positive_support
  have hJ : Ioo (0 : ℝ) 22 ∈ 𝓝 Eleven.globalTransition := isOpen_Ioo.mem_nhds transition_mem_Ioo
  apply not_differentiable_of_two_supports hs.ne' pressureReal_at_transition
  · filter_upwards [hJ] with β hβ
    have hh := pressure_nonneg 11 β
    rw [Eleven.pressure_eq_real hβ.1.le hβ.2] at hh
    exact_mod_cast hh
  · filter_upwards [hJ] with β hβ
    exact hline β hβ.1.le hβ.2

theorem pressure_right_derivative_positive : ∃ s : ℝ, 0 < s ∧
    s ≤ derivWithin Eleven.pressureReal (Ioi Eleven.globalTransition) Eleven.globalTransition := by
  obtain ⟨s, hs, hline⟩ := exists_positive_support
  refine ⟨s, hs, ?_⟩
  rw [pressureReal_convex.rightDeriv_eq_sInf_slope_of_mem_interior transition_interior]
  apply le_csInf
  · obtain ⟨y, hy, h22⟩ := exists_between (Eleven.transition_upper.trans
      (show (2063 : ℝ) / 100 < 22 by norm_num))
    exact ⟨slope Eleven.pressureReal Eleven.globalTransition y, y,
      ⟨⟨Eleven.transition_pos.trans hy, h22⟩, hy⟩, rfl⟩
  · rintro z ⟨y, ⟨hy, hyb⟩, rfl⟩
    rw [slope_def_field, pressureReal_at_transition, sub_zero]
    exact (le_div_iff₀ (sub_pos.mpr hyb)).mpr (by simpa only [mul_comm] using hline y hy.1.le hy.2)

/-- `eq:section4-pressure-derivative-jump`. -/
theorem pressure_derivative_jump : ∃ p : ℝ, 0 < p ∧
    HasDerivWithinAt Eleven.pressureReal 0 (Iio Eleven.globalTransition) Eleven.globalTransition ∧
    HasDerivWithinAt Eleven.pressureReal p (Ioi Eleven.globalTransition) Eleven.globalTransition := by
  obtain ⟨s, hs, hsp⟩ := pressure_right_derivative_positive
  exact ⟨_, hs.trans_le hsp, pressure_left_derivative,
    pressureReal_convex.hasDerivWithinAt_rightDeriv_of_mem_interior transition_interior⟩

/-! ## The defect: affine lower bound from `u_0` -/

theorem exists_negative_defect_support : ∃ s : ℝ, s < 0 ∧
    ∀ A : ℝ, (((A - Eleven.zeroDefectCoefficient) * s : ℝ) : EReal) ≤ coefficientDefect 11 A := by
  obtain ⟨-, -, U, -, -, -, -, -, -, hU, hUnz, hM, -, -⟩ := transition_limit
  obtain ⟨u, huL, hu, hm, -, -, hmax⟩ :=
    continuous_optimizer_of_L2 (by norm_num) Eleven.transition_pos U hU hM
  have hvalue : functional (spectralThreshold 11 / (2 * Eleven.globalTransition)) U = 0 := by
    have h := pressure_eq_dual (by norm_num) Eleven.transition_pos u hu hmax
    rw [Eleven.pressure_at_transition, dualFunctional_eq_toL2 (by norm_num) _ u hu hm, huL] at h
    exact_mod_cast h.symm
  have hepos : 0 < criticalEnergy U := by
    have hh := coefficient_norm_sq_le_energy (fourierIsometry 11 U) hU.2.1 hU.2.2
    rw [(fourierIsometry 11).norm_map] at hh
    exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hUnz)) hh
  let E := (2 * Real.pi) ^ 11 * criticalEnergy U
  have hE : 0 < E := mul_pos (by positivity) hepos
  have hcoef : Eleven.zeroDefectCoefficient * (2 * Real.pi) ^ 11 =
      spectralThreshold 11 / (2 * Eleven.globalTransition) := by
    unfold Eleven.zeroDefectCoefficient
    have hp := Real.pi_ne_zero
    have hb := Eleven.transition_pos.ne'
    field_simp
  refine ⟨-E, neg_neg_of_pos hE, fun A => ?_⟩
  have hh : RawAttainment.rawFunctional A (RawAttainment.realValue U) ≤ coefficientDefect 11 A :=
    le_iSup_of_le (RawAttainment.realValue U)
      (le_iSup_of_le (RawAttainment.realValue_sobolev U hU) le_rfl)
  rw [RawAttainment.rawFunctional_realValue (by norm_num) A U hU] at hh
  have he : functional (A * (2 * Real.pi) ^ 11) U = (A - Eleven.zeroDefectCoefficient) * (-E) := by
    unfold functional at hvalue ⊢
    rw [← hcoef] at hvalue
    dsimp [E]
    nlinarith
  rwa [he] at hh

/-- `eq:section4-defect-affine-functions` and the corner of `C_11` at `A_gm`. -/
theorem defect_corner :
    (∃ ε : ℝ, 0 < ε ∧ ε < Eleven.zeroDefectCoefficient ∧
      ∀ A : ℝ, |A - Eleven.zeroDefectCoefficient| < ε →
        coefficientDefect 11 A = (Eleven.defectReal A : EReal)) ∧
    ¬ DifferentiableAt ℝ Eleven.defectReal Eleven.zeroDefectCoefficient := by
  refine ⟨Eleven.defect_finite_neighborhood, ?_⟩
  obtain ⟨s, hs, hline⟩ := exists_negative_defect_support
  apply not_differentiable_of_two_supports hs.ne Eleven.defectReal_at_transition
  · filter_upwards [Eleven.defect_finite_eventually] with A hA
    have h := coefficientDefect_nonneg 11 A
    rw [hA] at h
    exact_mod_cast h
  · filter_upwards [Eleven.defect_finite_eventually] with A hA
    have h := hline A
    rw [hA] at h
    exact_mod_cast h

theorem defect_left_derivative_negative : ∃ s : ℝ, s < 0 ∧
    derivWithin Eleven.defectReal (Iio Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient ≤ s := by
  obtain ⟨ε, hε, hconv⟩ := defect_convex_neighborhood
  have hint : Eleven.zeroDefectCoefficient ∈ interior
      (Ioo (Eleven.zeroDefectCoefficient - ε) (Eleven.zeroDefectCoefficient + ε)) := by
    rw [isOpen_Ioo.interior_eq]
    constructor <;> linarith
  have hder := hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show Eleven.zeroDefectCoefficient ∉
    Iio Eleven.zeroDefectCoefficient by simp)).mp hder
  obtain ⟨s, hs, hline⟩ := exists_negative_defect_support
  refine ⟨s, hs, le_of_tendsto hlim ?_⟩
  filter_upwards [self_mem_nhdsWithin,
      Eleven.defect_finite_eventually.filter_mono nhdsWithin_le_nhds] with A hA hf
  have h := hline A
  rw [hf] at h
  have hr := EReal.coe_le_coe_iff.mp h
  rw [slope_def_field, Eleven.defectReal_at_transition, sub_zero]
  exact (div_le_iff_of_neg (sub_neg.mpr hA)).mpr (by simpa only [mul_comm] using hr)

/-- `eq:section4-defect-derivative-jump`. -/
theorem defect_derivative_jump : ∃ q : ℝ, q < 0 ∧
    HasDerivWithinAt Eleven.defectReal q (Iio Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient ∧
    HasDerivWithinAt Eleven.defectReal 0 (Ioi Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient := by
  obtain ⟨s, hs, hqs⟩ := defect_left_derivative_negative
  obtain ⟨ε, hε, hconv⟩ := defect_convex_neighborhood
  have hint : Eleven.zeroDefectCoefficient ∈ interior
      (Ioo (Eleven.zeroDefectCoefficient - ε) (Eleven.zeroDefectCoefficient + ε)) := by
    rw [isOpen_Ioo.interior_eq]
    constructor <;> linarith
  exact ⟨_, hqs.trans_lt hs, hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint,
    defect_right_derivative⟩

/-! ## Proposition 4.9 assembled -/

/-- **Proposition 4.9 (`prop:section4-first-order-coexistence`)**, all components, in the vocabulary of
`BecknerOnofri.HighDim.Eleven`, with the compactness/coexistence argument of this package in place of
the legacy `Eleven.coexistence`. -/
theorem prop49_manuscript :
    (IsGlobalMinimizer Eleven.globalTransition (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer Eleven.globalTransition ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ ρ.value =ᵐ[torusMeasure 11] fun _ => 1) ∧
    (0 < 1 - Eleven.globalTransition / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - Eleven.globalTransition / spectralThreshold 11) * ∫ x, h x ^ 2 ∂torusMeasure 11 ≤
          Eleven.uniformHessian Eleven.globalTransition h) ∧
    ((∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (Eleven.pressureReal β : EReal)) ∧
      ¬ DifferentiableAt ℝ Eleven.pressureReal Eleven.globalTransition) ∧
    ((∃ ε : ℝ, 0 < ε ∧ ε < Eleven.zeroDefectCoefficient ∧
        ∀ A : ℝ, |A - Eleven.zeroDefectCoefficient| < ε →
          coefficientDefect 11 A = (Eleven.defectReal A : EReal)) ∧
      ¬ DifferentiableAt ℝ Eleven.defectReal Eleven.zeroDefectCoefficient) ∧
    (∃ p : ℝ, 0 < p ∧
      HasDerivWithinAt Eleven.pressureReal 0 (Iio Eleven.globalTransition) Eleven.globalTransition ∧
      HasDerivWithinAt Eleven.pressureReal p (Ioi Eleven.globalTransition) Eleven.globalTransition) ∧
    (∃ q : ℝ, q < 0 ∧
      HasDerivWithinAt Eleven.defectReal q (Iio Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient ∧
      HasDerivWithinAt Eleven.defectReal 0 (Ioi Eleven.zeroDefectCoefficient) Eleven.zeroDefectCoefficient) :=
  ⟨coexistence, Eleven.uniform_hessian, pressure_corner, defect_corner, pressure_derivative_jump,
    defect_derivative_jump⟩

end BecknerOnofri.V2.Reaudit.Compactness
