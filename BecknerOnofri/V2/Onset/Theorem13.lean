module

public import BecknerOnofri.V2.Onset.Assembly
public import BecknerOnofri.V2.Onset.PressureOnset
public import BecknerOnofri.OnsetTransfer

@[expose] public section

/-! # Theorem 1.3 onset assertions, conditional only on `OnsetEndpointInputs d`

The three onset statements of `Challenge.lean` (`high_dim_onset_branch`, `high_dim_pressure_onset`,
`high_dim_defect_onset`), stated verbatim in the `Challenge` vocabulary, with `hd : 12 ≤ d` and
the single extra hypothesis `OnsetEndpointInputs d` (the spectral inequality of Corollary 5.8 and the
forward direction of its equality case). -/

noncomputable section

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

theorem high_dim_onset_branch_of_inputs (d : ℕ) (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    FullBranchOnset d := full_branch_onset_of_inputs hd E

theorem high_dim_pressure_onset_of_inputs (d : ℕ) (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 := pressure_onset_of_inputs hd E

theorem high_dim_defect_onset_of_inputs (d : ℕ) (hd : 12 ≤ d) (E : OnsetEndpointInputs d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  coefficient_onset_of_pressure (by omega) (pressure_onset_of_inputs hd E)

#print axioms high_dim_onset_branch_of_inputs
#print axioms high_dim_pressure_onset_of_inputs
#print axioms high_dim_defect_onset_of_inputs

end BecknerOnofri.V2.Onset
