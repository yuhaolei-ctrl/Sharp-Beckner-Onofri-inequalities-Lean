module

public import BecknerOnofri.ElevenConstants
public import BecknerOnofri.PressureRegularity
public import BecknerOnofri.PressureDuality

@[expose] public section

/-! Variational consequences used in Section 4. The competitor's analytic
bounds are explicit premises here, until its periodization and Fourier
identities have been proved. None of these premises is an axiom or a field
of the trusted density definition. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim.Eleven

theorem pressure_eq_real {β : ℝ} (hβ : 0 ≤ β) (hb : β < 22) :
    pressure 11 β = (pressureReal β : EReal) := by
  have hf := pressure_finite (d := 11) (by norm_num) hβ (by norm_num; exact hb)
  exact (EReal.coe_toReal hf.2 hf.1).symm

theorem pressure_zero : pressure 11 0 = 0 := by
  apply le_antisymm ?_ (pressure_nonneg _ _)
  unfold pressure
  refine iSup_le fun ρ => iSup_le fun hρ => ?_
  rw [spectralEnergy_coe_eq_tsum (by norm_num) ρ hρ]
  norm_num only [zero_div, EReal.coe_zero, zero_mul, zero_sub]
  exact_mod_cast neg_nonpos.mpr (entropy_nonneg ρ hρ)

theorem pressureValue_le_pressure (β : ℝ) (ρ : ProbabilityDensity 11)
    (hρ : ρ.FiniteEntropy) : pressureValue β ρ ≤ pressure 11 β :=
  le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)

theorem energy_eq_ofReal (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (∑' k, spectralTerm ρ k) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => by unfold spectralTerm frequencyLength; positivity)
    (finiteEntropy_spectralTerm_summable (by norm_num) ρ hρ)).symm

theorem pressureValue_eq_real (β : ℝ) (ρ : ProbabilityDensity 11)
    (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ =
      ((β / (2 * spectralThreshold 11) * (∑' k, spectralTerm ρ k) - entropy ρ : ℝ) : EReal) := by
  unfold pressureValue
  rw [spectralEnergy_coe_eq_tsum (by norm_num) ρ hρ]
  push_cast
  rfl

/-- The numerical competitor gap implies the actual supremum lower bound. -/
theorem spectral_pressure_of_competitor (ρ : ProbabilityDensity 11)
    (hρ : ρ.FiniteEntropy) (he : entropy ρ < (18011 : ℝ)/1250)
    (hq : ENNReal.ofReal (2*((14475384292906 : ℝ)/10^12)) < spectralEnergy ρ) :
    (1/30 : EReal) < pressure 11 (spectralThreshold 11) := by
  rw [energy_eq_ofReal ρ hρ] at hq
  have hq' := (ENNReal.ofReal_lt_ofReal_iff'.mp hq).1
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  have hr : (1 : ℝ)/30 < spectralThreshold 11 / (2 * spectralThreshold 11) *
      (∑' k, spectralTerm ρ k) - entropy ρ := by
    rw [show spectralThreshold 11 / (2 * spectralThreshold 11) = (1 : ℝ)/2 by
      field_simp]
    linarith [competitor_gap_rational]
  apply lt_of_lt_of_le ?_ (pressureValue_le_pressure _ ρ hρ)
  rw [pressureValue_eq_real _ ρ hρ]
  change (((1 : ℝ)/30 : ℝ) : EReal) < _
  exact_mod_cast hr

theorem defect_at_spectral :
    coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) := by
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  have h := pressure_eq_coefficientDefect (d := 11) (by norm_num) hs
  have hc : spectralThreshold 11 / (2 * spectralThreshold 11 * (2 * Real.pi)^11) =
      spectralCoefficient 11 := by
    unfold spectralCoefficient
    field_simp
  rw [hc] at h
  exact h.symm

/-- Every zero-pressure parameter is bounded by any positive-energy trial
quotient. This uses the genuine full supremum, not a restricted trial pressure. -/
theorem transition_le_trial_quotient (ρ : ProbabilityDensity 11)
    (hρ : ρ.FiniteEntropy) (hq : 0 < ∑' k, spectralTerm ρ k) :
    globalTransition ≤ 2 * spectralThreshold 11 * entropy ρ / (∑' k, spectralTerm ρ k) := by
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  apply csSup_le
  · exact ⟨0, le_rfl, pressure_zero⟩
  · intro β hβ
    have hv := pressureValue_le_pressure β ρ hρ
    rw [hβ.2, pressureValue_eq_real β ρ hρ] at hv
    have hv' : β / (2 * spectralThreshold 11) * (∑' k, spectralTerm ρ k) ≤ entropy ρ := by
      have : β / (2 * spectralThreshold 11) * (∑' k, spectralTerm ρ k) - entropy ρ ≤ 0 := by
        exact_mod_cast hv
      linarith
    apply (le_div_iff₀ hq).mpr
    have hm := mul_le_mul_of_nonneg_left hv' (by positivity : 0 ≤ 2 * spectralThreshold 11)
    field_simp at hm
    nlinarith

/-- The finer entropy estimate in Section 4 gives the strict upper endpoint
20.630, using the same explicitly certified trial quotient as the paper. -/
theorem transition_lt_of_competitor (ρ : ProbabilityDensity 11)
    (hρ : ρ.FiniteEntropy)
    (he : entropy ρ < (7305164 : ℝ)/10^6 + 17897/2520 + 1/625)
    (hq : ENNReal.ofReal (2*((14475384292906 : ℝ)/10^12)) < spectralEnergy ρ) :
    globalTransition < (2063 : ℝ)/100 := by
  rw [energy_eq_ofReal ρ hρ] at hq
  have hq' := (ENNReal.ofReal_lt_ofReal_iff'.mp hq).1
  have hQ : 0 < ∑' k, spectralTerm ρ k := by linarith
  apply (transition_le_trial_quotient ρ hρ hQ).trans_lt
  apply (div_lt_iff₀ hQ).mpr
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  have hpi : Real.pi^5 < ((104348 : ℝ)/33215)^5 := by
    gcongr
    exact pi_fine_bounds.2
  have hsig : spectralThreshold 11 < (64 : ℝ)/945 * (104348/33215)^5 := by
    rw [spectralThreshold_eleven]
    nlinarith
  have hm := mul_lt_mul_of_pos_left he (by positivity : 0 < 2 * spectralThreshold 11)
  have hm' := mul_lt_mul_of_pos_right hsig
    (by norm_num : (0 : ℝ) < 2 * (7305164/10^6 + 17897/2520 + 1/625))
  have hc : (2 : ℝ) * ((64 : ℝ)/945 * (104348/33215)^5) *
      (7305164/10^6 + 17897/2520 + 1/625) <
      (2063/100) * (2 * (14475384292906/10^12)) := by norm_num
  nlinarith

theorem hessian_gap_of_transition_upper (hb : globalTransition < (2063 : ℝ)/100) :
    0 < 1 - globalTransition / spectralThreshold 11 := by
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  have hb' := hb.trans spectralThreshold_bounds.1
  have hdiv : globalTransition / spectralThreshold 11 < 1 :=
    (div_lt_one hs).mpr hb'
  linarith

#print axioms spectral_pressure_of_competitor
#print axioms transition_le_trial_quotient
#print axioms transition_lt_of_competitor
end BecknerOnofri.HighDim.Eleven
