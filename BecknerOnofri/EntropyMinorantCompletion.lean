module

public import BecknerOnofri.SelectedEntropyAssembly
public import BecknerOnofri.NumericalBranchReduction
public import BecknerOnofri.EntropyEndpointClosure
public import BecknerOnofri.EndpointPackage

@[expose] public section

/-! The high-dimensional results of Theorem 1.3, conditional on Lemma 5.17 (`ψ ≤ γ`) and the
numerical part of Lemma 5.19 (`𝓑(t) > t⁴/200` on `[1/16, 0.99]`). The unconditional versions
are in `EntropyMainTheorems`. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyMinorantCompletion
open EntropyEndpointClosure
open Legacy.BecknerOnofri.TorusSobolev

variable (hminor : ∀ t ∈ Ico (0 : ℝ) 1, Spin.psi t ≤ CircleScalar.gamma t)
  (hB : ∀ t ∈ Icc (1 / 16 : ℝ) (99 / 100), t ^ 4 / 200 < Spin.pressureScalar t)
include hminor hB

theorem selected_zero {u : TorusL2 12} (hu : SelectedNumericalModel.Selected u) : u=0 :=
  SelectedNumericalModel.selected_zero hminor hB hu

theorem legacy_endpoint {d : ℕ} (hd : 12≤d) :
    BecknerOnofri.EndpointRigidity.CoefficientEndpoint d (1/2) :=
  CosineMixtureTransfer.finite_entropy_endpoint_from_mixture hd
    (CosineMixtureTransfer.mixture_endpoint_from_twelve
      (twelve_mixture_endpoint_of_selected_zero (selected_zero hminor hB)) hd)

theorem legacy_rigidity {d : ℕ} (hd : 12≤d) : BecknerOnofri.OnsetCompactness.DensityRigidity d :=
  EndpointRigidity.uniform_from_twelve
    (twelve_mixture_endpoint_of_selected_zero (selected_zero hminor hB))
    (twelve_mixture_rigidity_of_selected_zero (selected_zero hminor hB)) hd

theorem density_endpoint {d : ℕ} (hd : 12≤d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ≤ENNReal.ofReal (2*entropy ρ) :=
  density_endpoint_of_selected_zero (selected_zero hminor hB) hd ρ hρ

theorem density_rigidity {d : ℕ} (hd : 12≤d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ=ENNReal.ofReal (2*entropy ρ) ↔ ρ.value=ᵐ[torusMeasure d] (fun _ => 1) :=
  density_rigidity_of_selected_zero (selected_zero hminor hB) hd ρ hρ

theorem potential_endpoint {d : ℕ} (hd : 12≤d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u≤((spectralCoefficient d*potentialEnergy u : ℝ) : EReal) :=
  potential_endpoint_from_twelve (twelve_mixture_endpoint_of_selected_zero (selected_zero hminor hB)) hd u hu

theorem potential_rigidity {d : ℕ} (hd : 12≤d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u=((spectralCoefficient d*potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ,u=ᵐ[torusMeasure d] (fun _ => c) :=
  potential_rigidity_of_selected_zero (selected_zero hminor hB) hd u hu

theorem pressure_threshold {d : ℕ} (hd : 12≤d) :
    IsGreatest {β : ℝ | 0≤β ∧ pressure d β=0} (spectralThreshold d) :=
  pressure_threshold_from_twelve (twelve_mixture_endpoint_of_selected_zero (selected_zero hminor hB)) hd

theorem coefficient_threshold {d : ℕ} (hd : 12≤d) :
    IsLeast {A : ℝ | 0<A ∧ coefficientDefect d A=0} (spectralCoefficient d) :=
  coefficient_threshold_from_twelve (twelve_mixture_endpoint_of_selected_zero (selected_zero hminor hB)) hd

theorem full_branch_onset {d : ℕ} (hd : 12≤d) : FullBranchOnset d :=
  full_branch_onset_of_endpoint hd (legacy_endpoint hminor hB hd) (legacy_rigidity hminor hB hd)

theorem pressure_onset {d : ℕ} (hd : 12≤d) :
    ∃ ε C : ℝ,0<ε ∧ 0≤C ∧ ∀ β : ℝ,spectralThreshold d<β → β<spectralThreshold d+ε →
      ∃ p : ℝ,pressure d β=(p : EReal) ∧
        |p-(d : ℝ)/(2*kappa d)*(1-spectralThreshold d/β)^2|≤C*(β-spectralThreshold d)^3 :=
  GlobalPressureOnset.pressure_onset_of_endpoint hd (legacy_endpoint hminor hB hd) (legacy_rigidity hminor hB hd)

theorem coefficient_onset {d : ℕ} (hd : 12≤d) :
    ∃ ε C : ℝ,0<ε ∧ ε<spectralCoefficient d ∧ 0≤C ∧
      ∀ A : ℝ,spectralCoefficient d-ε<A → A<spectralCoefficient d →
        ∃ c : ℝ,coefficientDefect d A=(c : EReal) ∧
          |c-(d : ℝ)/(2*kappa d)*(1-A/spectralCoefficient d)^2|≤C*(1-A/spectralCoefficient d)^3 :=
  coefficient_onset_of_pressure (by omega) (pressure_onset hminor hB hd)

#print axioms density_endpoint
#print axioms full_branch_onset
#print axioms pressure_onset
#print axioms coefficient_onset
end BecknerOnofri.HighDim.EntropyMinorantCompletion
