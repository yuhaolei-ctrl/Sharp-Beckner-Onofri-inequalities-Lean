import BecknerOnofri.EndpointRigidity.RawDensity
import BecknerOnofri.PotentialRigidity

/-! All endpoint assertions of Theorem 1.3, reduced to the two exact d=12
mixture base statements. These premises are deliberately visible; this is not
an unconditional proof of the Challenge targets. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.HighDim
open CosineMixtureTransfer EndpointRigidity

theorem potential_endpoint_from_twelve (h12 : MixtureEndpoint 12)
    {d : ℕ} (hd : 12 ≤ d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  potential_endpoint_of_density (by omega) (density_endpoint_from_twelve h12 hd) u hu

theorem potential_rigidity_from_twelve (h12 : MixtureEndpoint 12)
    (hRig12 : MixtureRigidity 12) {d : ℕ} (hd : 12 ≤ d)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) :=
  potential_rigidity_of_density (by omega) (density_endpoint_from_twelve h12 hd)
    (fun ρ hρ => (density_rigidity_from_twelve h12 hRig12 hd ρ hρ).mp) u hu

theorem pressure_threshold_from_twelve (h12 : MixtureEndpoint 12)
    {d : ℕ} (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) :=
  pressure_threshold_of_density (by omega) (density_endpoint_from_twelve h12 hd)

theorem coefficient_threshold_from_twelve (h12 : MixtureEndpoint 12)
    {d : ℕ} (hd : 12 ≤ d) :
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) :=
  coefficient_threshold_of_density (by omega) (density_endpoint_from_twelve h12 hd)

#print axioms potential_rigidity_from_twelve
#print axioms pressure_threshold_from_twelve
#print axioms coefficient_threshold_from_twelve
end BecknerOnofri.HighDim
