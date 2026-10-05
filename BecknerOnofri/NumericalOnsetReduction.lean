import BecknerOnofri.TwelveExitReduction
import BecknerOnofri.GlobalPressureOnset
import BecknerOnofri.OnsetTransfer

/-! Both exact scalar-onset assertions reduce to the same explicit d=12
numerical-neighborhood obligation as the endpoint. The obligation remains
an ordinary visible hypothesis; this is not a solution of the main targets. -/
noncomputable section
namespace BecknerOnofri.HighDim
open CosineMixtureTransfer EndpointRigidity

theorem legacy_endpoint_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) : CoefficientEndpoint d (1/2) :=
  finite_entropy_endpoint_from_mixture hd
    (mixture_endpoint_from_twelve (twelve_mixture_endpoint_of_neighborhood hnum) hd)

theorem legacy_rigidity_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) : BecknerOnofri.OnsetCompactness.DensityRigidity d :=
  uniform_from_twelve (twelve_mixture_endpoint_of_neighborhood hnum)
    (twelve_mixture_rigidity_of_neighborhood hnum) hd

theorem pressure_onset_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d+ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p-(d:ℝ)/(2*kappa d)*(1-spectralThreshold d/β)^2| ≤
            C*(β-spectralThreshold d)^3 :=
  GlobalPressureOnset.pressure_onset_of_endpoint hd
    (legacy_endpoint_of_twelve_neighborhood hnum hd)
    (legacy_rigidity_of_twelve_neighborhood hnum hd)

theorem coefficient_onset_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d-ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c-(d:ℝ)/(2*kappa d)*(1-A/spectralCoefficient d)^2| ≤
            C*(1-A/spectralCoefficient d)^3 :=
  coefficient_onset_of_pressure (by omega) (pressure_onset_of_twelve_neighborhood hnum hd)

#print axioms pressure_onset_of_twelve_neighborhood
#print axioms coefficient_onset_of_twelve_neighborhood
end BecknerOnofri.HighDim
