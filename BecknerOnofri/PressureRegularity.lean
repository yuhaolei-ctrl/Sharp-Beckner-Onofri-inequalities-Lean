import BecknerOnofri.FiniteEntropyEnergy
import BecknerOnofri.SubcriticalGap
import BecknerOnofri.Uniform

/-! Finiteness of the actual full finite-entropy pressure in the subcritical interval. -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace BecknerOnofri.HighDim

theorem pressure_nonneg (d : ℕ) (β : ℝ) : 0 ≤ pressure d β := by
  have h := le_iSup_of_le (uniformDensity d)
    (le_iSup_of_le (uniformDensity_finiteEntropy d) le_rfl)
      (f := fun ρ : ProbabilityDensity d => ⨆ (_ : ρ.FiniteEntropy),
        (β / (2 * spectralThreshold d) : ℝ) * (spectralEnergy ρ).toEReal -
          (entropy ρ : EReal))
  simpa [pressure] using h

theorem pressure_bounded_above {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 ≤ β) (hβd : β < 2 * (d : ℝ)) : ∃ M : ℝ, pressure d β ≤ (M : EReal) := by
  let α := β / (2 * spectralThreshold d)
  let C := Legacy.BecknerOnofri.endpointConstant d
  have hσ := spectralThreshold_pos hd
  have hα : 0 ≤ α := div_nonneg hβ (by positivity)
  have hαC : α < C := by
    change β / (2 * spectralThreshold d) < (d : ℝ) / spectralThreshold d
    apply (div_lt_iff₀ (by positivity : 0 < 2 * spectralThreshold d)).mpr
    have he : (d : ℝ) / spectralThreshold d * (2 * spectralThreshold d) = 2 * (d : ℝ) := by
      field_simp
    rw [he]
    exact hβd
  obtain ⟨b, hαb, hbC⟩ := exists_between hαC
  have hb : 0 < b := hα.trans_lt hαb
  let M := Real.log (Legacy.BecknerOnofri.GreenRoughEnergy.partition d b)
  refine ⟨M, ?_⟩
  unfold pressure
  refine iSup_le (fun ρ => iSup_le (fun hρ => ?_))
  have hrough := (legacy_rough_finite_entropy hd (Bridge.density ρ) hρ hb hbC).2
  have hterms : Legacy.BecknerOnofri.fourierEnergy (Bridge.density ρ) = ∑' k, spectralTerm ρ k := by
    unfold Legacy.BecknerOnofri.fourierEnergy
    exact tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  rw [hterms] at hrough
  change b * (∑' k, spectralTerm ρ k) ≤ entropy ρ + M at hrough
  have hn : 0 ≤ ∑' k, spectralTerm ρ k := by
    apply tsum_nonneg
    intro k
    unfold spectralTerm frequencyLength
    positivity
  have hr : α * (∑' k, spectralTerm ρ k) - entropy ρ ≤ M := by
    have hm := mul_le_mul_of_nonneg_right hαb.le hn
    linarith
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ]
  exact_mod_cast hr

theorem pressure_finite {d : ℕ} (hd : 0 < d) {β : ℝ}
    (hβ : 0 ≤ β) (hβd : β < 2 * (d : ℝ)) :
    pressure d β ≠ ⊥ ∧ pressure d β ≠ ⊤ := by
  obtain ⟨M, hM⟩ := pressure_bounded_above hd hβ hβd
  constructor
  · exact ne_of_gt ((by simp : (⊥ : EReal) < 0).trans_le (pressure_nonneg d β))
  · exact ne_of_lt (hM.trans_lt (by simp))

#print axioms pressure_finite
end BecknerOnofri.HighDim
