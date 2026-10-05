module

public import BecknerOnofri.ElevenTrialConsequences
public import BecknerOnofri.ElevenUniform

@[expose] public section

/-! The genuine pressure has a closed initial zero interval. In particular,
uniform density is a global minimizer at the supremum defining the transition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven

lemma pressure_monotone : Monotone (pressure 11) := by
  intro a b hab
  apply iSup_le fun ρ => iSup_le fun hρ => ?_
  apply le_trans ?_ (pressureValue_le_pressure b ρ hρ)
  change pressureValue a ρ ≤ pressureValue b ρ
  rw [pressureValue_eq_real a ρ hρ, pressureValue_eq_real b ρ hρ]
  apply EReal.coe_le_coe_iff.mpr
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hab (by positivity [spectralThreshold_pos (d := 11) (by norm_num)]))
    (scalar_energy_nonneg ρ)) _

lemma zero_parameters_bounded : BddAbove {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0} := by
  refine ⟨spectralThreshold 11, fun β hβ => ?_⟩
  by_contra hn
  have h := pressure_monotone (le_of_not_ge hn)
  rw [hβ.2] at h
  have hp := spectral_pressure
  have : (0:EReal) < pressure 11 (spectralThreshold 11) :=
    lt_trans (by change ((0:ℝ):EReal) < ((1/30:ℝ):EReal); exact EReal.coe_lt_coe_iff.mpr (by norm_num)) hp
  exact this.not_ge h

lemma transition_lower : (3543:ℝ)/200 ≤ globalTransition :=
  le_csSup zero_parameters_bounded ⟨by norm_num, pressure_zero_below le_rfl⟩

lemma transition_pos : 0 < globalTransition := lt_of_lt_of_le (by norm_num) transition_lower

lemma pressure_eq_zero_iff_nonpos (β : ℝ) :
    pressure 11 β = 0 ↔ ∀ (ρ : ProbabilityDensity 11), ρ.FiniteEntropy →
      β/(2*spectralThreshold 11)*(∑' k, spectralTerm ρ k)-entropy ρ ≤ 0 := by
  constructor
  · intro hz ρ hρ
    have h := pressureValue_le_pressure β ρ hρ
    rw [hz, pressureValue_eq_real β ρ hρ] at h
    exact_mod_cast h
  · intro h
    apply le_antisymm (iSup_le fun ρ => iSup_le fun hρ => ?_) (pressure_nonneg _ _)
    change pressureValue β ρ ≤ 0
    rw [pressureValue_eq_real β ρ hρ]
    exact_mod_cast h ρ hρ

lemma zero_parameters_closed : IsClosed {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0} := by
  have he : {β : ℝ | 0 ≤ β ∧ pressure 11 β = 0} =
      Ici 0 ∩ ⋂ (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy),
      {β : ℝ | β/(2*spectralThreshold 11)*(∑' k, spectralTerm ρ k)-entropy ρ ≤ 0} := by
    ext β
    simp only [mem_setOf_eq, mem_inter_iff, mem_Ici, mem_iInter, pressure_eq_zero_iff_nonpos]
  rw [he]
  apply isClosed_Ici.inter
  apply isClosed_iInter
  intro ρ
  apply isClosed_iInter
  intro hρ
  exact isClosed_le (by fun_prop) continuous_const

lemma pressure_at_transition : pressure 11 globalTransition = 0 :=
  (zero_parameters_closed.csSup_mem ⟨0, le_rfl, pressure_zero⟩ zero_parameters_bounded).2

lemma pressure_zero_iff {β : ℝ} (hβ : 0 ≤ β) :
    pressure 11 β = 0 ↔ β ≤ globalTransition := by
  constructor
  · intro hz
    exact le_csSup zero_parameters_bounded ⟨hβ, hz⟩
  · intro hb
    apply le_antisymm ?_ (pressure_nonneg _ _)
    simpa only [pressure_at_transition] using pressure_monotone hb

lemma uniform_at_transition : IsGlobalMinimizer globalTransition (uniformDensity 11) := by
  refine ⟨uniformDensity_finiteEntropy 11, fun ρ hρ => ?_⟩
  have h := pressureValue_le_pressure globalTransition ρ hρ
  rw [pressure_at_transition] at h
  simpa only [pressureValue, uniformDensity_spectralEnergy, EReal.coe_ennreal_zero,
    mul_zero, uniformDensity_entropy, EReal.coe_zero, sub_zero] using h

#print axioms transition_lower
#print axioms uniform_at_transition
end BecknerOnofri.HighDim.Eleven
