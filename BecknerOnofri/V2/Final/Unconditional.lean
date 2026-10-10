module

public import BecknerOnofri.V2.Final.Endpoint
public import BecknerOnofri.V2.IntervalKernel.Cells1
public import BecknerOnofri.V2.IntervalKernel.Cells2
public import BecknerOnofri.V2.IntervalKernel.Cells3

@[expose] public section

/-!
# The dimension-twelve endpoint and Theorem 1.3 with the finite checks discharged

Each declaration is the corresponding declaration of `Endpoint.lean` with the three hypotheses
`hc1 hc2 hc3` (the finite cell checks `Row.checkCell k = true` for all cells of the three rows of the
scalar certificate) supplied by `V2.IntervalKernel.hc1`, `hc2`, `hc3`, which are proved by the
kernel (`decide +kernel` on each cell, through `fastCheck_sound`).  The statements are the
statements of `Challenge.lean` with no additional hypotheses.
-/

noncomputable section

namespace BecknerOnofri.V2.Final.Unconditional
open MeasureTheory BecknerOnofri.HighDim BecknerOnofri.V2.IntervalKernel

theorem scalarBounds : BecknerOnofri.V2.Assembly.ScalarBounds :=
  BecknerOnofri.V2.Final.scalarBounds_of_checks hc1 hc2 hc3

theorem onsetEndpointInputs {d : ℕ} (hd : 12 ≤ d) : Onset.OnsetEndpointInputs d :=
  BecknerOnofri.V2.Final.onsetEndpointInputs_of_checks hc1 hc2 hc3 hd

theorem high_endpoint (d : ℕ) (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
    VariationalCurves.globalTransition d = spectralThreshold d ∧
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) :=
  BecknerOnofri.V2.Final.high_endpoint_of_checks (d := d) hd hc1 hc2 hc3

theorem high_dim_entropy_inequality (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ :=
  BecknerOnofri.V2.Final.high_dim_entropy_inequality d hd hc1 hc2 hc3 ρ

theorem high_dim_entropy_eq_iff (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  BecknerOnofri.V2.Final.high_dim_entropy_eq_iff d hd hc1 hc2 hc3 ρ hρ

theorem high_dim_beckner_onofri (d : ℕ) (hd : 12 ≤ d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  BecknerOnofri.V2.Final.high_dim_beckner_onofri d hd hc1 hc2 hc3 u hu

theorem high_dim_beckner_onofri_eq_iff (d : ℕ) (hd : 12 ≤ d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  BecknerOnofri.V2.Final.high_dim_beckner_onofri_eq_iff d hd hc1 hc2 hc3 u hu

theorem high_dim_thresholds (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d :=
  BecknerOnofri.V2.Final.high_dim_thresholds d hd hc1 hc2 hc3

theorem high_dim_onset_branch (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d :=
  BecknerOnofri.V2.Final.high_dim_onset_branch d hd hc1 hc2 hc3

theorem high_dim_pressure_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 :=
  BecknerOnofri.V2.Final.high_dim_pressure_onset d hd hc1 hc2 hc3

theorem high_dim_defect_onset (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  BecknerOnofri.V2.Final.high_dim_defect_onset d hd hc1 hc2 hc3

end BecknerOnofri.V2.Final.Unconditional
