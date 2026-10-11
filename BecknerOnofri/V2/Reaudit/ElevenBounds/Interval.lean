module

public import BecknerOnofri.V2.Reaudit.ElevenBounds.Quantitative
public import BecknerOnofri.V2.Eleven.Estimates
public import BecknerOnofri.ElevenCoexistence

@[expose] public section

/-! # S024, steps 4-5: `d11:thm:interval` in the printed order (strict lower bound only after coexistence)

The printed proof of `d11:thm:interval` runs in this order, which this file and `Quantitative.lean` follow:

1. `d11:eq:mixture-gap` (the quantitative latent-mass gap, `LatentGap.mixture_gap_eleven`):
   `E_{β_0}(ρ) ≥ (1/44000) ∑_i P(L_i ≥ 1)`.  **No coexistence.**
2. a nonuniform mixture has some `P(L_i ≥ 1) > 0`, so `E_{β_0}(ρ) > 0`
   (`exists_pos_latentProb`, `efree_pos_of_nonuniform_mixture`).  **No coexistence.**
3. uniqueness of the uniform minimizer for `0 ≤ β ≤ β_0` and the *non-strict* bound `β_0 ≤ β_gm`
   (`uniform_unique_quantitative`, `beta0_le_globalTransition_quantitative`): `V2.Eleven.uniform_unique_of_gap`,
   `beta0_le_globalTransition`, fed with the hypothesis `SmoothMixtureGap11` proved from steps 1-2.
   **No coexistence.**  Steps 1-3 are in `Quantitative.lean` (which does not import `ElevenCoexistence`);
   `HighDim.Eleven.transition_lower` is proved from them.
4. the upper bound `β_gm < 2063/100` (`V2.Eleven.transition_upper`, from `Estimates.lean`).
5. **Only now** coexistence (`HighDim.Eleven.coexistence`, existing) is used, to exclude `β_gm = β_0`:
   `strict_lower_quantitative`.

The existing `V2.Eleven.smoothMixtureGap11` is not used. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.ElevenBounds
open BecknerOnofri.HighDim BecknerOnofri.V2.Section3
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg sum_latentWeight)
open Legacy.BecknerOnofri

variable {d : ℕ}

/-! ## The strict lower bound, only after coexistence -/

/-- **The strict lower bound** `3543/200 < β_gm(11)`.  Order of the printed proof: the non-strict
bound and the uniqueness on `[0, β_0]` (both above, without coexistence), then the existing
`HighDim.Eleven.coexistence` (a nonuniform global minimizer at `β_gm`) excludes `β_gm = β_0`. -/
theorem strict_lower_quantitative : Eleven.beta0 < VariationalCurves.globalTransition 11 := by
  refine lt_of_le_of_ne beta0_le_globalTransition_quantitative fun heq => ?_
  obtain ⟨-, ρ, hmin, -, -, hnon⟩ := HighDim.Eleven.coexistence
  have hβ0 : (0 : ℝ) ≤ VariationalCurves.globalTransition 11 := by
    rw [← heq]; unfold Eleven.beta0; norm_num
  exact hnon ((uniform_unique_quantitative _ hβ0 heq.ge ρ hmin.1).1 hmin)

/-- **`d11:thm:interval`** (Proposition 4.1), assembled in the printed order through the quantitative
gap: the interval `17.715 < β_gm < 20.630`, uniqueness of the uniform minimizer for `0 ≤ β ≤ 17.715`,
and the energy bound for `ρ_*`. -/
theorem interval_quantitative :
    (3543 / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100) ∧
    (∀ β : ℝ, 0 ≤ β → β ≤ 3543 / 200 → ∀ ρ : ProbabilityDensity 11, ρ.FiniteEntropy →
      (IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] fun _ => 1)) ∧
    (∀ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile →
      (14475384292906 : ℝ) / 10 ^ 12 <
        (2 * Real.pi) ^ 11 / 2 * (Vocab.negSobolevEnergy ρ.value).toReal) := by
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile :=
    ⟨HighDim.Eleven.competitorDensity, rfl⟩
  exact ⟨⟨strict_lower_quantitative, Eleven.transition_upper ρ₀ hρ₀⟩,
    fun β hβ hβ0 ρ hρ => uniform_unique_quantitative β hβ hβ0 ρ hρ,
    fun ρ h => Eleven.periodized_energy_bound ρ h⟩

end BecknerOnofri.V2.Reaudit.ElevenBounds
