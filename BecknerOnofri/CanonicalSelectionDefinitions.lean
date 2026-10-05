module

public import BecknerOnofri.CoordinateRearrangementDefinitions
public import BecknerOnofri.PrescribedSelectionDefinitions

@[expose] public section

/-! Canonical finite successive Steiner selection on the entire finite-entropy
domain. The rearrangements are the literal circle layer-cake construction,
applied in coordinate order and interpreted on almost-everywhere classes. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim.PrescribedSelection

def CanonicalSelection (d : ℕ) : Prop :=
  ∀ β : ℝ, 0 < β → β < 2*(d:ℝ) →
  ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
  ∃ η : ProbabilityDensity d, ∃ u : Torus d → ℝ,
    CoordinateRearrangementStatement.AESuccessiveSteiner ρ.value η.value ∧
    IsGlobalMinimizer β η ∧
    ProbabilityTheory.IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) ∧
    entropy η = entropy ρ ∧ pressureValue β η = pressureValue β ρ ∧
    η.value = normalizedGibbs u ∧ SmoothOnTorus η.value ∧ (∀ x, 0 < η.value x) ∧
    SmoothOnTorus u ∧ InCriticalSobolev u ∧ (∀ s : ℝ, InSobolev s u) ∧ MeanZero u ∧
    u =ᵐ[torusMeasure d] Gap.densityPotential β η.value ∧
    CoordinateSteiner η.value ∧ CoordinateSteiner u ∧
    IsCountableCosineMixture η ∧
    (∀ k : Frequency d, 0 ≤ (fourierCoeff η.value k).re ∧ (fourierCoeff η.value k).im=0 ∧
      0 ≤ (fourierCoeff u k).re ∧ (fourierCoeff u k).im=0) ∧
    (¬ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) →
      ¬ η.value =ᵐ[torusMeasure d] (fun _ => 1))

end BecknerOnofri.HighDim.PrescribedSelection
