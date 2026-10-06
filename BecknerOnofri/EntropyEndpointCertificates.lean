module

public import BecknerOnofri.EntropyEndpointClosure

@[expose] public section

/-! Endpoint consequences of the two numerical inputs in the manuscript's
entropy proof. These are conditional helper theorems, not replacements for
the unconditional Challenge declarations. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyEndpointCertificates
open SelectedNumericalModel EntropyEndpointClosure
open Legacy.BecknerOnofri.TorusSobolev

variable
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))

include hscalar ψ hc hcv hminor hspin
theorem selected_zero {u : TorusL2 12} (hu : Selected u) : u=0 :=
  selected_zero_of_entropy_certificates hscalar ψ hc hcv hminor hspin hu

theorem density_endpoint {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2*entropy ρ) :=
  density_endpoint_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin) hd ρ hρ

theorem density_rigidity {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2*entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  density_rigidity_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin) hd ρ hρ

theorem potential_endpoint {d : ℕ} (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d*potentialEnergy u : ℝ) : EReal) :=
  potential_endpoint_from_twelve
    (twelve_mixture_endpoint_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin)) hd u hu

theorem potential_rigidity {d : ℕ} (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d*potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) :=
  potential_rigidity_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin) hd u hu

theorem pressure_threshold {d : ℕ} (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β=0} (spectralThreshold d) :=
  pressure_threshold_from_twelve
    (twelve_mixture_endpoint_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin)) hd

theorem coefficient_threshold {d : ℕ} (hd : 12 ≤ d) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A=0} (spectralCoefficient d) :=
  coefficient_threshold_from_twelve
    (twelve_mixture_endpoint_of_selected_zero (selected_zero hscalar ψ hc hcv hminor hspin)) hd

#print axioms density_endpoint
#print axioms density_rigidity
#print axioms potential_endpoint
#print axioms potential_rigidity
#print axioms pressure_threshold
#print axioms coefficient_threshold
end BecknerOnofri.HighDim.EntropyEndpointCertificates
