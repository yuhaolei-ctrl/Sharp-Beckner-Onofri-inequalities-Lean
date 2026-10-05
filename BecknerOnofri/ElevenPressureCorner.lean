module

public import BecknerOnofri.ElevenCoexistence
public import BecknerOnofri.SupportingLineCorner
public import BecknerOnofri.Entropy

@[expose] public section

/-! The two coexisting states give distinct active affine supporting lines
of the actual finite pressure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.Eleven

lemma pressureReal_at_transition : pressureReal globalTransition = 0 := by
  simp only [pressureReal, pressure_at_transition, EReal.toReal_zero]

lemma minimizer_pressureValue_zero (ρ : ProbabilityDensity 11)
    (hρ : IsGlobalMinimizer globalTransition ρ) : pressureValue globalTransition ρ = 0 := by
  apply le_antisymm
  · simpa only [pressure_at_transition] using pressureValue_le_pressure globalTransition ρ hρ.1
  · simpa only [pressureValue, uniformDensity_spectralEnergy, EReal.coe_ennreal_zero,
      mul_zero, uniformDensity_entropy, EReal.coe_zero, sub_zero] using
        hρ.2 (uniformDensity 11) (uniformDensity_finiteEntropy 11)

lemma exists_positive_support : ∃ s : ℝ, 0 < s ∧
    ∀ β : ℝ, 0 ≤ β → β < 22 → (β-globalTransition)*s ≤ pressureReal β := by
  obtain ⟨ρ,hρ,_,_,hnon⟩ := coexistence.2
  let Q := ∑' k, spectralTerm ρ k
  let s := Q/(2*spectralThreshold 11)
  have he : globalTransition*s = entropy ρ := by
    have h := minimizer_pressureValue_zero ρ hρ
    rw [pressureValue_eq_real globalTransition ρ hρ.1] at h
    have hr : globalTransition/(2*spectralThreshold 11)*Q-entropy ρ = 0 := by exact_mod_cast h
    calc
      _ = globalTransition/(2*spectralThreshold 11)*Q := by dsimp [s]; ring
      _ = _ := sub_eq_zero.mp hr
  have hEnt : 0 < entropy ρ := lt_of_le_of_ne (entropy_nonneg ρ hρ.1)
    (fun h => hnon ((entropy_eq_zero_iff ρ hρ.1).mp h.symm))
  have hs : 0 < s := by nlinarith [transition_pos]
  refine ⟨s,hs,fun β hβ hb => ?_⟩
  have hv := pressureValue_le_pressure β ρ hρ.1
  rw [pressureValue_eq_real β ρ hρ.1, pressure_eq_real hβ hb] at hv
  have hr : β/(2*spectralThreshold 11)*Q-entropy ρ ≤ pressureReal β := by exact_mod_cast hv
  have hm : β/(2*spectralThreshold 11)*Q = β*s := by dsimp [s]; ring
  rw [hm, ← he] at hr
  nlinarith

theorem pressure_corner :
    (∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = (pressureReal β:EReal)) ∧
    ¬ DifferentiableAt ℝ pressureReal globalTransition := by
  refine ⟨fun β hβ hb => pressure_eq_real hβ.le hb, ?_⟩
  obtain ⟨s,hs,hline⟩ := exists_positive_support
  have hb : globalTransition < 22 := transition_upper.trans (by norm_num)
  have hJ : Ioo (0:ℝ) 22 ∈ 𝓝 globalTransition := isOpen_Ioo.mem_nhds ⟨transition_pos,hb⟩
  apply not_differentiable_of_two_supports hs.ne' pressureReal_at_transition
  · filter_upwards [hJ] with β hβ
    have hh := pressure_nonneg 11 β
    rw [pressure_eq_real hβ.1.le hβ.2] at hh
    exact_mod_cast hh
  · filter_upwards [hJ] with β hβ
    exact hline β hβ.1.le hβ.2

#print axioms pressure_corner
end BecknerOnofri.HighDim.Eleven
