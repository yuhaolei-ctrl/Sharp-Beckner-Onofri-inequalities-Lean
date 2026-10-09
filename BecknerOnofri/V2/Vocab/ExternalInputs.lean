module

public import BecknerOnofri.V2.Vocab.Section2Gibbs

@[expose] public section

/-! # Named external inputs of Section 2 (stated, NOT proved here)

The manuscript uses three analytic inputs from the literature.  In the repository they are only
available through the old low-dimensional endpoint chain
(`Legacy.BecknerOnofri.physical_green_endpoint`, `d ≤ 10`, and the `d ≥ 12` endpoint theorems), which
the v2 proof path must not import.  Here each is a **named `Prop`** with exactly the manuscript's
content, in the manuscript normalization (`c_d`, `‖·‖²_{Ḣ^{-d/2}}`, `‖·‖²_{Ḣ^{d/2}}`, `Ent`), so that a
v2 theorem can take it as a labelled hypothesis.  Nothing stronger is stated or assumed.

* `PositiveThresholdInput d` — `eq:section2-positive-threshold-input` (CdCRS2025 Thm 3 via
  tensorization for `d ≥ 2`; Lebedev–Milin with `β₀ = 2` for `d = 1`):
  there is `β₀ > 0` with `Ent(ρ) ≥ (β₀ c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}}` for all finite-entropy densities.
* `CriticalAdamsInput d` — `eq:section2-critical-adams`: there is `B` with
  `log ∫ e^{u-ū} ≤ A_crit ‖u‖²_{Ḣ^{d/2}} + B` for all `u ∈ H^{d/2}`, `A_crit = 1/(4 d c_d)`.
* `CircleLebedevMilinInput` — the `d = 1` entropy/energy inequality `c_1 ‖ρ‖²_{Ḣ^{-1/2}} ≤ Ent(ρ)`
  (Lebedev–Milin / Beckner, the case `β = 2d = 2` of the free energy), the repository's
  `circle_heatInteraction_entropy` (obtained there only from the `d ≤ 10` endpoint theorem). -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

/-- `eq:section2-positive-threshold-input`: `Ent(ρ) ≥ (β₀ c_d/2) ‖ρ‖²_{Ḣ^{-d/2}}` for some
`β₀ > 0` and all finite-entropy probability densities on `𝕋^d`. -/
def PositiveThresholdInput (d : ℕ) : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
    β₀ * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal ≤ (torusEntropy ρ.value).toReal

/-- `eq:section2-critical-adams`: `log ∫ e^{u-ū} ≤ (1/(4 d c_d)) ‖u‖²_{Ḣ^{d/2}} + B`
for all `u ∈ H^{d/2}(𝕋^d)`. -/
def CriticalAdamsInput (d : ℕ) : Prop :=
  ∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
    logPartition u ≤
      (((1 / (4 * (d : ℝ) * kernelConstant d)) * (sobolevEnergyPos u).toReal + B : ℝ) : EReal)

/-- The circle case of the critical entropy/energy inequality (Lebedev–Milin):
`c_1 ‖ρ‖²_{Ḣ^{-1/2}} ≤ Ent(ρ)` for every finite-entropy density on `𝕋¹`. -/
def CircleLebedevMilinInput : Prop :=
  ∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
    kernelConstant 1 * (negSobolevEnergy ρ.value).toReal ≤ (torusEntropy ρ.value).toReal

/-- `CriticalAdamsInput d` is literally the repository's shape of `critical_adams_bound`
(`A_crit` is `collapseCoefficient d`, `‖u‖²_{Ḣ^{d/2}}` is `potentialEnergy u`).  Stated for the
Prop only; no endpoint declaration is involved. -/
theorem criticalAdamsInput_iff {d : ℕ} (hd : 0 < d) :
    CriticalAdamsInput d ↔
      ∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal) := by
  unfold CriticalAdamsInput
  refine exists_congr fun B => forall_congr' fun u => imp_congr_right fun hu => ?_
  rw [collapseCoefficient_eq hd, potentialEnergy_eq_toReal_sobolevEnergyPos hu]

/-- `CircleLebedevMilinInput` in physical space: the real Green double integral on `𝕋¹` is at most
the real entropy `∫ ρ log ρ` (the repository's `physical_green_endpoint` at `d = 1`, second clause). -/
theorem circleLebedevMilinInput_iff_physical :
    CircleLebedevMilinInput ↔
      ∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
        (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen 1 (x - y) * ρ.value x *
          ρ.value y ∂torusMeasure 1 ∂torusMeasure 1) ≤ entropy ρ := by
  unfold CircleLebedevMilinInput
  refine forall_congr' fun ρ => imp_congr_right fun hρ => ?_
  rw [green_interaction_eq_kernelConstant_mul one_pos ρ hρ, entropy_eq_toReal_torusEntropy ρ hρ]

/-- Consequence used downstream: `PositiveThresholdInput d` gives `0 < β_gm(d)` (the infimum of the
nonempty set of quotients is at least `β₀`). -/
theorem globalTransition_pos_of_input {d : ℕ} (hd : 0 < d) (h : PositiveThresholdInput d) :
    0 < VariationalCurves.globalTransition d := by
  obtain ⟨β₀, hβ₀, hin⟩ := h
  rw [VariationalCurves.transition_quotient hd]
  refine lt_of_lt_of_le hβ₀ (le_csInf (VariationalCurves.quotient_set_nonempty hd) ?_)
  rintro q ⟨ρ, hρ, hne, rfl⟩
  have hpos : 0 < VariationalCurves.interaction ρ :=
    (VariationalCurves.interaction_pos_iff hd ρ hρ).2 hne
  rw [le_div_iff₀ hpos, interaction_eq_kernelConstant_mul hd ρ hρ,
    entropy_eq_toReal_torusEntropy ρ hρ]
  have := hin ρ hρ
  linarith

end BecknerOnofri.V2.Vocab
