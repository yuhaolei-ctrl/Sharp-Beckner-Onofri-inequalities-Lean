module

public import BecknerOnofri.ElevenEndpoint
public import BecknerOnofri.OptimizerDuality

@[expose] public section

/-! The raw full finite-entropy statement at every coupling 0 ≤ beta ≤ 17.715. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Eleven

lemma scalar_energy_nonneg (ρ : ProbabilityDensity 11) : 0 ≤ ∑' k, spectralTerm ρ k := by
  apply tsum_nonneg
  intro k
  unfold spectralTerm frequencyLength
  positivity

lemma full_density_bound (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    ((3543:ℝ)/200)/(2*spectralThreshold 11) * (∑' k, spectralTerm ρ k) ≤ entropy ρ := by
  have h := (Legacy.BecknerOnofri.ElevenMixture.full_endpoint (Bridge.density ρ) hρ).2
  have he : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [he] at h
  exact h

lemma full_density_rigidity (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy)
    (he : ((3543:ℝ)/200)/(2*spectralThreshold 11) * (∑' k, spectralTerm ρ k) = entropy ρ) :
    ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  apply Legacy.BecknerOnofri.ElevenMixture.full_rigidity (Bridge.density ρ) hρ
  have hterms : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [hterms]
  exact he

lemma pressureValue_nonpos {β : ℝ} (hβ₀ : β ≤ 3543/200)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) : pressureValue β ρ ≤ 0 := by
  rw [pressureValue_eq_real β ρ hρ]
  have hs := spectralThreshold_pos (d := 11) (by norm_num)
  have hc : β/(2*spectralThreshold 11) ≤ ((3543:ℝ)/200)/(2*spectralThreshold 11) :=
    div_le_div_of_nonneg_right hβ₀ (by positivity)
  have h := (mul_le_mul_of_nonneg_right hc (scalar_energy_nonneg ρ)).trans (full_density_bound ρ hρ)
  have hh : β/(2*spectralThreshold 11) * (∑' k, spectralTerm ρ k) - entropy ρ ≤ 0 := by linarith
  exact_mod_cast hh

theorem pressure_zero_below {β : ℝ} (hβ₀ : β ≤ 3543/200) : pressure 11 β = 0 := by
  apply le_antisymm ?_ (pressure_nonneg _ _)
  exact iSup_le fun ρ => iSup_le fun hρ => pressureValue_nonpos hβ₀ ρ hρ

theorem uniform_unique (β : ℝ) (hβ : 0 ≤ β) (hβ₀ : β ≤ 3543/200)
    (ρ : ProbabilityDensity 11) (hρ : ρ.FiniteEntropy) :
    IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] (fun _ => 1) := by
  constructor
  · intro hm
    have hz : 0 ≤ pressureValue β ρ := by
      simpa [pressureValue] using hm.2 (uniformDensity 11) (uniformDensity_finiteEntropy 11)
    rw [pressureValue_eq_real β ρ hρ] at hz
    have hzR : 0 ≤ β/(2*spectralThreshold 11) * (∑' k, spectralTerm ρ k) - entropy ρ := by
      exact_mod_cast hz
    have hs := spectralThreshold_pos (d := 11) (by norm_num)
    have hc : β/(2*spectralThreshold 11) ≤ ((3543:ℝ)/200)/(2*spectralThreshold 11) :=
      div_le_div_of_nonneg_right hβ₀ (by positivity)
    have he := mul_le_mul_of_nonneg_right hc (scalar_energy_nonneg ρ)
    apply full_density_rigidity ρ hρ
    linarith [full_density_bound ρ hρ]
  · intro he
    refine ⟨hρ, fun η hη => ?_⟩
    have he' : ρ.value =ᵐ[torusMeasure 11] (uniformDensity 11).value := he
    rw [OptimizerDuality.pressureValue_congr_ae he']
    simpa [pressureValue] using pressureValue_nonpos hβ₀ η hη

#print axioms uniform_unique
#print axioms pressure_zero_below
end BecknerOnofri.HighDim.Eleven
