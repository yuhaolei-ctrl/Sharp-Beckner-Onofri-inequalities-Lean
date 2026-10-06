module

public import BecknerOnofri.EntropyMinorantCompletion
public import BecknerOnofri.TwelveNumericalInputs

@[expose] public section

/-! Theorem 1.3 for `d ≥ 12`, from Lemma 5.17 and Lemma 5.19 (`TwelveNumericalInputs`). -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators ContDiff
namespace BecknerOnofri.Target
open HighDim

theorem density_endpoint (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := 
  EntropyMinorantCompletion.density_endpoint psi_le_gamma pressureScalar_gt hd ρ hρ

theorem density_rigidity (d : ℕ) (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) := 
  EntropyMinorantCompletion.density_rigidity psi_le_gamma pressureScalar_gt hd ρ hρ

theorem potential_endpoint (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) := 
  EntropyMinorantCompletion.potential_endpoint psi_le_gamma pressureScalar_gt hd u hu

theorem potential_rigidity (d : ℕ) (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) := 
  EntropyMinorantCompletion.potential_rigidity psi_le_gamma pressureScalar_gt hd u hu

theorem pressure_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) := 
  EntropyMinorantCompletion.pressure_threshold psi_le_gamma pressureScalar_gt hd

theorem coefficient_threshold (d : ℕ) (hd : 12 ≤ d) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := 
  EntropyMinorantCompletion.coefficient_threshold psi_le_gamma pressureScalar_gt hd

theorem full_branch_onset (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d := 
  EntropyMinorantCompletion.full_branch_onset psi_le_gamma pressureScalar_gt hd

theorem pressure_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := 
  EntropyMinorantCompletion.pressure_onset psi_le_gamma pressureScalar_gt hd

theorem coefficient_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 := 
  EntropyMinorantCompletion.coefficient_onset psi_le_gamma pressureScalar_gt hd

#print axioms density_endpoint
#print axioms density_rigidity
#print axioms potential_endpoint
#print axioms potential_rigidity
#print axioms pressure_threshold
#print axioms coefficient_threshold
#print axioms full_branch_onset
#print axioms pressure_onset
#print axioms coefficient_onset
end BecknerOnofri.Target
