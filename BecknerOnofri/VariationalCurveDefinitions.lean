import BecknerOnofri.Definitions

/-! Definitions only: the genuine zero-pressure threshold and the interaction
in the manuscript normalization. The identification with the physical Green
integral is proved separately on the full finite-entropy domain. -/
noncomputable section
namespace BecknerOnofri.HighDim.VariationalCurves

def globalTransition (d : ℕ) : ℝ := sSup {β : ℝ | 0 ≤ β ∧ pressure d β = 0}

def interaction {d : ℕ} (ρ : ProbabilityDensity d) : ℝ :=
  (∑' k, spectralTerm ρ k)/(2*spectralThreshold d)

def entropyInteractionQuotients (d : ℕ) : Set ℝ :=
  {q | ∃ ρ : ProbabilityDensity d, ρ.FiniteEntropy ∧
    ¬ (ρ.value =ᵐ[torusMeasure d] (fun _ => 1)) ∧ q = entropy ρ/interaction ρ}

end BecknerOnofri.HighDim.VariationalCurves
