import BecknerOnofri.VariationalCurveDefinitions
import BecknerOnofri.SpectralEnergyPositive
import BecknerOnofri.PressureDuality
import BecknerOnofri.FiniteEntropyPhysical

/-! The all-dimension variational quotient formula and the complete initial
zero interval, derived from the actual affine competitors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
namespace BecknerOnofri.HighDim.VariationalCurves

lemma interaction_nonneg {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) : 0 ≤ interaction ρ :=
  div_nonneg (scalar_spectral_energy_nonneg ρ) (by positivity [spectralThreshold_pos hd])

lemma interaction_pos_iff {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    0 < interaction ρ ↔ ¬ (ρ.value =ᵐ[torusMeasure d] (fun _ => 1)) := by
  rw [interaction,div_pos_iff_of_pos_right (by positivity [spectralThreshold_pos hd]),
    scalar_spectral_energy_pos_iff hd ρ hρ]

lemma pressureValue_eq {d : ℕ} (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : pressureValue β ρ = ((β*interaction ρ-entropy ρ:ℝ):EReal) := by
  unfold pressureValue
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ,← EReal.coe_mul,← EReal.coe_sub]
  congr 1
  unfold interaction
  ring

lemma pressure_zero_iff_competitors {d : ℕ} (hd : 0 < d) (β : ℝ) :
    pressure d β = 0 ↔ ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → β*interaction ρ ≤ entropy ρ := by
  constructor
  · intro hz ρ hρ
    have h : pressureValue β ρ ≤ pressure d β := le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
    rw [hz,pressureValue_eq hd β ρ hρ] at h
    have hr : β*interaction ρ-entropy ρ ≤ 0 := by exact_mod_cast h
    linarith
  · intro h
    apply le_antisymm ?_ (pressure_nonneg _ _)
    apply iSup_le fun ρ => iSup_le fun hρ => ?_
    change pressureValue β ρ ≤ 0
    rw [pressureValue_eq hd β ρ hρ]
    exact_mod_cast sub_nonpos.mpr (h ρ hρ)

lemma pressure_zero {d : ℕ} (hd : 0 < d) : pressure d 0 = 0 := by
  apply (pressure_zero_iff_competitors hd 0).mpr
  intro ρ hρ
  simpa using entropy_nonneg ρ hρ

lemma quotient_set_bddBelow {d : ℕ} (hd : 0 < d) : BddBelow (entropyInteractionQuotients d) := by
  refine ⟨0,?_⟩
  rintro q ⟨ρ,hρ,hn,rfl⟩
  exact div_nonneg (entropy_nonneg ρ hρ) (interaction_nonneg hd ρ)

lemma quotient_set_nonempty {d : ℕ} (hd : 0 < d) : (entropyInteractionQuotients d).Nonempty := by
  by_contra hnone
  have hz : pressure d (spectralThreshold d+1) = 0 := by
    apply (pressure_zero_iff_competitors hd _).mpr
    intro ρ hρ
    have hQ : interaction ρ = 0 := by
      by_contra hQ
      have hp := lt_of_le_of_ne (interaction_nonneg hd ρ) (Ne.symm hQ)
      have hn := (interaction_pos_iff hd ρ hρ).mp hp
      exact hnone ⟨entropy ρ/interaction ρ,ρ,hρ,hn,rfl⟩
    simp only [hQ,mul_zero]
    exact entropy_nonneg ρ hρ
  have hp := pressure_pos_of_spectral_lt hd (by linarith : spectralThreshold d < spectralThreshold d+1)
  rw [hz] at hp
  exact lt_irrefl _ hp

lemma pressure_zero_iff_le_all_quotients {d : ℕ} (hd : 0 < d) (β : ℝ) :
    pressure d β = 0 ↔ ∀ q ∈ entropyInteractionQuotients d, β ≤ q := by
  rw [pressure_zero_iff_competitors hd]
  constructor
  · intro h q hq
    rcases hq with ⟨ρ,hρ,hn,rfl⟩
    exact (le_div_iff₀ ((interaction_pos_iff hd ρ hρ).mpr hn)).mpr (h ρ hρ)
  · intro h ρ hρ
    by_cases hp : 0 < interaction ρ
    · exact (le_div_iff₀ hp).mp
        (h _ ⟨ρ,hρ,(interaction_pos_iff hd ρ hρ).mp hp,rfl⟩)
    · have hz : interaction ρ = 0 := le_antisymm (le_of_not_gt hp) (interaction_nonneg hd ρ)
      simpa only [hz,mul_zero] using entropy_nonneg ρ hρ

lemma pressure_zero_iff_le_inf {d : ℕ} (hd : 0 < d) (β : ℝ) :
    pressure d β = 0 ↔ β ≤ sInf (entropyInteractionQuotients d) := by
  rw [pressure_zero_iff_le_all_quotients hd]
  constructor
  · exact fun h => le_csInf (quotient_set_nonempty hd) h
  · exact fun h q hq => h.trans (csInf_le (quotient_set_bddBelow hd) hq)

lemma quotient_inf_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ sInf (entropyInteractionQuotients d) :=
  (pressure_zero_iff_le_inf hd 0).mp (pressure_zero hd)

lemma transition_quotient {d : ℕ} (hd : 0 < d) :
    globalTransition d = sInf (entropyInteractionQuotients d) := by
  apply le_antisymm
  · exact csSup_le ⟨0,le_rfl,pressure_zero hd⟩
      (fun β hβ => (pressure_zero_iff_le_inf hd β).mp hβ.2)
  · apply le_csSup
    · exact ⟨sInf (entropyInteractionQuotients d),fun β hβ =>
        (pressure_zero_iff_le_inf hd β).mp hβ.2⟩
    · exact ⟨quotient_inf_nonneg hd,(pressure_zero_iff_le_inf hd _).mpr le_rfl⟩

lemma pressure_zero_iff {d : ℕ} (hd : 0 < d) (β : ℝ) :
    pressure d β = 0 ↔ β ≤ globalTransition d := by
  rw [transition_quotient hd]
  exact pressure_zero_iff_le_inf hd β

lemma transition_le_spectral {d : ℕ} (hd : 0 < d) : globalTransition d ≤ spectralThreshold d := by
  by_contra hn
  have hp := pressure_pos_of_spectral_lt hd (lt_of_not_ge hn)
  rw [(pressure_zero_iff hd _).mpr le_rfl] at hp
  exact lt_irrefl _ hp

lemma interaction_eq_physical {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    interaction ρ = (1/2:ℝ)*(∫ x,∫ y,Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
      ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d) := by
  have he := FiniteEntropyPhysical.physical_eq_spectral hd (Bridge.density ρ) hρ
  rw [Legacy.BecknerOnofri.normalized_energy] at he
  have hQ : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [hQ] at he
  change (∫ x,∫ y,Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y)*
    ρ.value x*ρ.value y ∂torusMeasure d ∂torusMeasure d) = (∑' k,spectralTerm ρ k)/spectralThreshold d at he
  rw [he]
  unfold interaction
  ring

#print axioms transition_quotient
#print axioms pressure_zero_iff
#print axioms interaction_eq_physical
end BecknerOnofri.HighDim.VariationalCurves
