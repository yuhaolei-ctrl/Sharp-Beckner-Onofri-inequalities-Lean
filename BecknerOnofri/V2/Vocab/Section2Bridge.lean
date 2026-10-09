module

public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import BecknerOnofri.V2.Vocab.Normalization
public import BecknerOnofri.FiniteEntropyPhysical
public import BecknerOnofri.VariationalTransitionQuotient
public import BecknerOnofri.GapDefinitions

@[expose] public section

/-! # Section 2 interface bridges stated with the manuscript normalization (G02)

`lem:section2-finite-entropy-energy`, estimate `eq:section2-finite-entropy-energy-bound`:
for `Ent(ρ) < ∞` and `a ∈ (0,d)`,
`0 ≤ c_d ‖ρ‖² ≤ (2/a) Ent(ρ) + (1/a) log ∬ exp(a g(x-y))`,
with `c_d ‖ρ‖² = kernelConstant d * (negSobolevEnergy ρ.value).toReal` and `Ent = torusEntropy`.
The proof reuses the repository's physical-space bound `FiniteEntropyPhysical.interaction_bound`
(Donsker--Varadhan route) and converts with the G01 normalization identity. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

/-- The real Green double integral is `c_d ‖ρ‖²` (finite-entropy densities). -/
theorem green_interaction_eq_kernelConstant_mul {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) * ρ.value x * ρ.value y
        ∂torusMeasure d ∂torusMeasure d) =
      kernelConstant d * (negSobolevEnergy ρ.value).toReal := by
  have h1 := VariationalCurves.interaction_eq_physical hd ρ hρ
  unfold VariationalCurves.interaction at h1
  have hfin : spectralEnergy ρ ≠ ∞ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
  have h2 : (spectralEnergy ρ).toReal = ∑' k, spectralTerm ρ k := by
    have := spectralEnergy_coe_eq_tsum hd ρ hρ
    rw [← EReal.coe_ennreal_toReal hfin] at this
    exact EReal.coe_eq_coe_iff.mp this
  rw [kernelConstant_mul_negSobolevEnergy_toReal hd ρ, h2]
  have hβ : spectralThreshold d ≠ 0 := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    unfold spectralThreshold
    have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
    positivity
  field_simp at h1 ⊢
  linarith

/-- `eq:section2-finite-entropy-energy-bound` in the manuscript normalization. -/
theorem finite_entropy_energy_bound {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) {a : ℝ} (ha : 0 < a) (had : a < (d : ℝ)) :
    negSobolevEnergy ρ.value ≠ ∞ ∧
      0 ≤ kernelConstant d * (negSobolevEnergy ρ.value).toReal ∧
      kernelConstant d * (negSobolevEnergy ρ.value).toReal ≤
        2 / a * (torusEntropy ρ.value).toReal + 1 / a * Real.log
          (∫ x, ∫ y, Real.exp (a * Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y))
            ∂torusMeasure d ∂torusMeasure d) := by
  obtain ⟨h0, hle⟩ := FiniteEntropyPhysical.interaction_bound hd (Bridge.density ρ) hρ a ha had
  have hint := FiniteEntropyPhysical.physical_eq_spectral hd (Bridge.density ρ) hρ
  have hG := green_interaction_eq_kernelConstant_mul hd ρ hρ
  refine ⟨(negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ),
    ?_, ?_⟩
  · rw [← hG]
    exact h0
  · rw [← hG, ← entropy_eq_toReal_torusEntropy ρ hρ]
    exact hle


section Duality

/-- `β_s(d) > 0` for `d > 0`. -/
lemma spectralThreshold_pos' {d : ℕ} (hd : 0 < d) : 0 < spectralThreshold d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold spectralThreshold
  have := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)
  positivity

/-- `A_crit(d) = 1 / (4 d c_d)` (`eq:intro-A-landmarks`). -/
theorem collapseCoefficient_eq {d : ℕ} (hd : 0 < d) :
    collapseCoefficient d = 1 / (4 * (d : ℝ) * kernelConstant d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := kernelConstant_pos hd
  have h := kernelConstant_mul_spectralThreshold hd
  have hβ := spectralThreshold_pos' hd
  unfold collapseCoefficient
  rw [← h]
  field_simp

/-- `A_s(d) = 1 / (2 (2π)^d)` (`eq:intro-A-landmarks`); this is the repository definition. -/
theorem spectralCoefficient_eq (d : ℕ) : spectralCoefficient d = 1 / (2 * (2 * Real.pi) ^ d) := rfl

/-- `A = (2 β c_d)⁻¹` is the repository's `Gap.coefficient d β = β_s / (2 β (2π)^d)`. -/
theorem gapCoefficient_eq {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β) :
    Gap.coefficient d β = (2 * β * kernelConstant d)⁻¹ := by
  have hc := kernelConstant_pos hd
  have h := kernelConstant_mul_spectralThreshold hd
  have hs := spectralThreshold_pos' hd
  unfold Gap.coefficient
  rw [← h]
  field_simp

/-- `A_0(d) = 1 / (2 c_d β_gm(d))` (`eq:intro-A-landmarks`) whenever `β_gm(d) ≠ 0`. -/
theorem zeroDefectCoefficient_eq {d : ℕ} (hd : 0 < d) :
    VariationalCurves.zeroDefectCoefficient d =
      1 / (2 * kernelConstant d * VariationalCurves.globalTransition d) := by
  have hc := kernelConstant_pos hd
  have h := kernelConstant_mul_spectralThreshold hd
  have hs := spectralThreshold_pos' hd
  unfold VariationalCurves.zeroDefectCoefficient
  rw [← h]
  by_cases hg : VariationalCurves.globalTransition d = 0
  · simp [hg]
  · field_simp

/-- `prop:section2-coefficient-pressure-duality` in the manuscript's direction:
for `A > 0` and `β = (2 A c_d)⁻¹`, `C_d(A) = P_d(β)` in `EReal` (both sides may be `⊤`). -/
theorem coefficient_pressure_duality {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    coefficientDefect d A = pressure d (2 * A * kernelConstant d)⁻¹ := by
  have hc := kernelConstant_pos hd
  have hβ : 0 < (2 * A * kernelConstant d)⁻¹ := by positivity
  rw [pressure_eq_coefficientDefect hd hβ]
  congr 1
  have h := kernelConstant_mul_spectralThreshold hd
  have hs := spectralThreshold_pos' hd
  rw [← h]
  field_simp

/-- The repository's pressure integrand is the manuscript's free-energy term
`(β c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}} - Ent(ρ)` for finite-entropy densities. -/
theorem pressureValue_eq_manuscript {d : ℕ} (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ =
      ((β * kernelConstant d / 2 : ℝ) : EReal) * (negSobolevEnergy ρ.value).toEReal -
        (torusEntropy ρ.value).toEReal := by
  have hfin : spectralEnergy ρ ≠ ∞ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
  have hN : negSobolevEnergy ρ.value ≠ ∞ := (negSobolevEnergy_ne_top_iff ρ).2 hfin
  have hent : torusEntropy ρ.value ≠ ∞ := (torusEntropy_density_ne_top_iff ρ).2 hρ
  have key := kernelConstant_mul_negSobolevEnergy_toReal hd ρ
  have hs := spectralThreshold_pos' hd
  unfold pressureValue
  rw [← EReal.coe_ennreal_toReal hfin, ← EReal.coe_ennreal_toReal hN,
    ← EReal.coe_ennreal_toReal hent, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub,
    ← EReal.coe_sub, ← entropy_eq_toReal_torusEntropy ρ hρ]
  congr 1
  have : (spectralEnergy ρ).toReal = spectralThreshold d * (kernelConstant d *
      (negSobolevEnergy ρ.value).toReal) := by
    rw [key]; field_simp
  rw [this]
  field_simp

end Duality

/-- The repository's `Gap.densityValue β ρ` (physical Green double integral minus `∫ ρ log ρ`) is the
manuscript's free energy term `(β c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}} - Ent(ρ)` for finite-entropy densities. -/
theorem densityValue_eq_manuscript {d : ℕ} (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    Gap.densityValue β ρ.value =
      β * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal -
        (torusEntropy ρ.value).toReal := by
  unfold Gap.densityValue
  rw [green_interaction_eq_kernelConstant_mul hd ρ hρ, ← entropy_eq_toReal_torusEntropy ρ hρ]
  unfold entropy
  ring

section Quotient

/-- Finite-entropy densities: `interaction ρ = c_d ‖ρ‖² / 2`. -/
theorem interaction_eq_kernelConstant_mul {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    VariationalCurves.interaction ρ = kernelConstant d * (negSobolevEnergy ρ.value).toReal / 2 := by
  rw [VariationalCurves.interaction_eq_physical hd ρ hρ,
    green_interaction_eq_kernelConstant_mul hd ρ hρ]
  ring

/-- `0 < Ent(ρ) < ∞` is exactly: finite entropy and not a.e. equal to `1`. -/
theorem pos_entropy_iff {d : ℕ} (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    0 < (torusEntropy ρ.value).toReal ↔ ¬ ρ.value =ᵐ[torusMeasure d] fun _ => 1 := by
  rw [← entropy_eq_toReal_torusEntropy ρ hρ, ← entropy_eq_zero_iff ρ hρ]
  exact ⟨fun h h0 => h.ne' h0, fun h => lt_of_le_of_ne (entropy_nonneg ρ hρ) (Ne.symm h)⟩

/-- `eq:section2-beta-gm-quotient`: the repository's quotient set is the manuscript's set
`{2 Ent(ρ) / (c_d ‖ρ‖²) : 0 < Ent(ρ) < ∞}`. -/
theorem entropyInteractionQuotients_eq {d : ℕ} (hd : 0 < d) :
    VariationalCurves.entropyInteractionQuotients d =
      {q | ∃ ρ : ProbabilityDensity d, ρ.FiniteEntropy ∧ 0 < (torusEntropy ρ.value).toReal ∧
        q = 2 * (torusEntropy ρ.value).toReal /
          (kernelConstant d * (negSobolevEnergy ρ.value).toReal)} := by
  ext q
  constructor
  · rintro ⟨ρ, hρ, hne, rfl⟩
    refine ⟨ρ, hρ, (pos_entropy_iff ρ hρ).2 hne, ?_⟩
    rw [interaction_eq_kernelConstant_mul hd ρ hρ, ← entropy_eq_toReal_torusEntropy ρ hρ,
      div_div_eq_mul_div, mul_comm (entropy ρ)]
  · rintro ⟨ρ, hρ, hpos, rfl⟩
    refine ⟨ρ, hρ, (pos_entropy_iff ρ hρ).1 hpos, ?_⟩
    rw [interaction_eq_kernelConstant_mul hd ρ hρ, ← entropy_eq_toReal_torusEntropy ρ hρ,
      div_div_eq_mul_div, mul_comm (entropy ρ)]

/-- `eq:section2-beta-gm-quotient`: `β_gm(d) = inf 2 Ent(ρ) / (c_d ‖ρ‖²_{Ḣ^{-d/2}})`. -/
theorem globalTransition_eq_manuscript_quotient {d : ℕ} (hd : 0 < d) :
    VariationalCurves.globalTransition d =
      sInf {q | ∃ ρ : ProbabilityDensity d, ρ.FiniteEntropy ∧ 0 < (torusEntropy ρ.value).toReal ∧
        q = 2 * (torusEntropy ρ.value).toReal /
          (kernelConstant d * (negSobolevEnergy ρ.value).toReal)} := by
  rw [VariationalCurves.transition_quotient hd, entropyInteractionQuotients_eq hd]

end Quotient

end BecknerOnofri.V2.Vocab
