module

public import BecknerOnofri.CurveThresholdDefinitions
public import BecknerOnofri.VariationalTransitionQuotient
public import BecknerOnofri.ConcentrationDivergence
public import BecknerOnofri.LowDimensionConsequences
public import BecknerOnofri.ElevenTransitionZeroSet
public import BecknerOnofri.EntropyMainTheorems

@[expose] public section

/-! The common pressure/defect thresholds in every positive dimension.
Positivity uses the previously proved dimension-specific endpoint estimates;
the quotient formula itself was proved independently of those estimates. -/
noncomputable section
namespace BecknerOnofri.HighDim.VariationalCurves

lemma transition_positive {d : ℕ} (hd : 0 < d) : 0 < globalTransition d := by
  by_cases hlow : d ≤ 10
  · have hz : pressure d (2*(d:ℝ)) = 0 := by
      rw [LowDimension.pressure_formula (by omega) hlow]
      simp
    exact (mul_pos (by norm_num) (Nat.cast_pos.mpr hd)).trans_le
      ((pressure_zero_iff hd _).mp hz)
  · by_cases heleven : d = 11
    · subst d
      exact Eleven.transition_pos
    · have hhigh : 12 ≤ d := by omega
      exact (spectralThreshold_pos hd).trans_le
        ((pressure_zero_iff hd _).mp (BecknerOnofri.Target.pressure_threshold d hhigh).1.2)

lemma transition_upper_bounds {d : ℕ} (hd : 0 < d) :
    globalTransition d ≤ min (2*(d:ℝ)) (spectralThreshold d) := by
  refine le_min ?_ (transition_le_spectral hd)
  by_contra hn
  have h := HighDim.pressure_above_collapse hd (lt_of_not_ge hn)
  rw [(pressure_zero_iff hd _).mpr le_rfl] at h
  exact (by simp : (0:EReal) ≠ ⊤) h

lemma zeroDefectCoefficient_positive {d : ℕ} (hd : 0 < d) : 0 < zeroDefectCoefficient d := by
  unfold zeroDefectCoefficient
  positivity [spectralThreshold_pos hd,transition_positive hd]

lemma coefficient_zero_iff {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    coefficientDefect d A = 0 ↔ zeroDefectCoefficient d ≤ A := by
  have hσ := spectralThreshold_pos hd
  have hT := transition_positive hd
  have hp : 0 < (2*Real.pi)^d := by positivity
  let β := spectralThreshold d/(2*A*(2*Real.pi)^d)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hc : spectralThreshold d/(2*β*(2*Real.pi)^d) = A := by dsimp [β]; field_simp
  rw [← hc,← pressure_eq_coefficientDefect hd hβ,pressure_zero_iff hd]
  rw [hc]
  change spectralThreshold d/(2*A*(2*Real.pi)^d) ≤ globalTransition d ↔
    spectralThreshold d/(2*globalTransition d*(2*Real.pi)^d) ≤ A
  rw [div_le_iff₀ (by positivity : 0 < 2*A*(2*Real.pi)^d),
    div_le_iff₀ (by positivity : 0 < 2*globalTransition d*(2*Real.pi)^d)]
  constructor <;> intro h <;> nlinarith

lemma coefficient_lower_bounds {d : ℕ} (hd : 0 < d) :
    max (collapseCoefficient d) (spectralCoefficient d) ≤ zeroDefectCoefficient d := by
  have hσ := spectralThreshold_pos hd
  have hT := transition_positive hd
  have hp : 0 < (2*Real.pi)^d := by positivity
  have hb := transition_upper_bounds hd
  have hc := hb.trans (min_le_left _ _)
  have hs := hb.trans (min_le_right _ _)
  apply max_le
  · unfold collapseCoefficient zeroDefectCoefficient
    apply div_le_div_of_nonneg_left hσ.le (by positivity)
    nlinarith
  · have he : spectralCoefficient d = spectralThreshold d/(2*spectralThreshold d*(2*Real.pi)^d) := by
      unfold spectralCoefficient
      field_simp
    rw [he]
    unfold zeroDefectCoefficient
    apply div_le_div_of_nonneg_left hσ.le (by positivity)
    nlinarith

#print axioms transition_positive
#print axioms transition_upper_bounds
#print axioms coefficient_zero_iff
#print axioms coefficient_lower_bounds
end BecknerOnofri.HighDim.VariationalCurves
