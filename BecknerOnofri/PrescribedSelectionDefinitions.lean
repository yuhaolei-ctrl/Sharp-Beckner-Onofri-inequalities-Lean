import BecknerOnofri.BranchDefinitions
import BecknerOnofri.GapDefinitions
import BecknerOnofri.CosineMixtureStatementDefinitions
import Mathlib.Probability.IdentDistrib

/-! Trusted physical statement for equimeasurable selection. It deliberately
does not assert identification with successive canonical fiber rearrangements. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.PrescribedSelection

def CoordinateSteiner {d : ℕ} (f : Torus d → ℝ) : Prop :=
  (∀ (i : Fin d) (x : Torus d), f (Function.update x i (-x i)) = f x) ∧
  ∀ (x : Torus d) (i : Fin d),
    AntitoneOn (fun t : ℝ => f (Function.update x i (t : UnitAddCircle))) (Icc 0 (1/2))

/-- Actual full finite-entropy minimizers, with the distribution of the
specified input retained, rather than merely its optimum value. -/
def EquimeasurableSelection (d : ℕ) : Prop :=
  ∀ β : ℝ, 0 < β → β < 2*(d:ℝ) →
  ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
  ∃ η : ProbabilityDensity d, ∃ u : Torus d → ℝ,
    IsGlobalMinimizer β η ∧
    ProbabilityTheory.IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) ∧
    entropy η = entropy ρ ∧ pressureValue β η = pressureValue β ρ ∧
    η.value = normalizedGibbs u ∧ SmoothOnTorus η.value ∧ (∀ x, 0 < η.value x) ∧
    SmoothOnTorus u ∧ InCriticalSobolev u ∧ (∀ s : ℝ, InSobolev s u) ∧ MeanZero u ∧
    u =ᵐ[torusMeasure d] Gap.densityPotential β η.value ∧
    CoordinateSteiner η.value ∧ CoordinateSteiner u ∧
    IsCountableCosineMixture η ∧
    (¬ ρ.value =ᵐ[torusMeasure d] (fun _ => 1) →
      ¬ η.value =ᵐ[torusMeasure d] (fun _ => 1))

end BecknerOnofri.HighDim.PrescribedSelection
