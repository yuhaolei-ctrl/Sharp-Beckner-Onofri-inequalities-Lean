module

public import BecknerOnofri.V2.Reaudit.Final.Section4

@[expose] public section

/-! # Exact manuscript statements (Reaudit, Final)

Statements in the form printed in the manuscript (SHA-256 1a3b8bdb...), added next to, not in place of,
the Challenge-shaped regression targets.  `Challenge.eleven_competitor` states the repository's sharper
entropy bound `14.4088 = 18011/1250` and the energy bound `ofReal (2 * (144753/10000)) < spectralEnergy`;
the manuscript prints (eq:intro-d11-certificate)
`Ent(ρ_*) < 8653/600` and `(2π)^11/2 ‖ρ_*‖²_{Ḣ^{-11/2}} > 14475384292906/10^12`.
Both printed constants are stated here, exactly. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.Final
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-- **Theorem 1.2, (eq:intro-d11-certificate), exactly as printed**: both printed constants
`8653/600` (entropy) and `14475384292906/10^12` (energy in the form `(2π)^11/2 ‖ρ_*‖²`). -/
theorem eleven_competitor_printed :
    ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile ∧
      SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧ ρ.FiniteEntropy ∧
      entropy ρ < (8653 : ℝ) / 600 ∧
      (14475384292906 : ℝ) / 10 ^ 12 <
        (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal := by
  have h := theorem_1_2_route.1
  refine ⟨V2.Eleven.rhoStar, V2.Eleven.rhoStar_value, h.2.2.1, h.2.2.2.1, h.2.1, ?_, h.2.2.2.2.2⟩
  rw [entropy_eq_toReal_torusEntropy _ h.2.1]
  exact h.2.2.2.2.1

#print axioms eleven_competitor_printed

end BecknerOnofri.V2.Reaudit.Final
