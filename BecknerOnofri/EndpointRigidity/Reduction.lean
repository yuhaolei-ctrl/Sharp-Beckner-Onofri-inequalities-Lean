import BecknerOnofri.EndpointRigidity.DensityGibbs
import BecknerOnofri.EndpointRigidity.Selection
import BecknerOnofri.GenericCosineRepresentation

/-! Full finite-entropy rigidity reduces to rigidity of genuine positive cosine
mixtures. The passage uses the actual Gibbs identity and entropy-preserving
Steiner selection, so no equality-preserving heat limit is presumed. -/

noncomputable section
open MeasureTheory
namespace BecknerOnofri.EndpointRigidity
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier

/-- The precise remaining rigidity input concerns actual continuous positive
probability densities with genuine nonnegative countable cosine expansions. -/
def PositiveMixtureRigidity (d : ℕ) (C : ℝ) : Prop :=
  ∀ r : ProbabilityDensity d, Continuous r.value → (∀ x, 0 < r.value x) →
    GenericCosineRepresentation.HasPositiveCosineMixture r.value →
    C * fourierEnergy r = densityEntropy r.value →
    ∀ x, r.value x = 1

/-- The original equality density need only have finite entropy. Square
integrability and an entropy-preserving smooth positive representative in the
selected class are proved along the way. -/
theorem uniform_of_equality {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 0 < C)
    (hEndpoint : CoefficientEndpoint d C) (hMixture : PositiveMixtureRigidity d C)
    (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (he : C * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  have hL2 := DensityGibbs.memLp_two_of_equality hd hC hEndpoint r hr he
  have hR := AnalyticEndpoint.rough_of_endpoint hd hC hEndpoint
  have hA := AnalyticEndpoint.coefficient_pos hC
  have hCoeff : 1 / (4 * AnalyticEndpoint.coefficient C) = C := by
    unfold AnalyticEndpoint.coefficient
    field_simp
  obtain ⟨u, hu, hmax, hStR, hStU, hEnt⟩ :=
    Selection.exists_steiner_equality hd hEndpoint hC hR hA hCoeff r hL2 he.symm
  have hs := maximizer_fourier_summable hd hR hA hu hmax
  let q := smoothGibbsDensity hR hu hs
  have hQ : fourierEnergy q = fourierEnergy (gibbsDensity hR hu) := by
    unfold fourierEnergy
    apply tsum_congr
    intro k
    unfold densitySpectralTerm
    rw [smoothGibbsDensity_fourier hR hu hs]
    rfl
  have hz := MaximizerLevel.maximizer_functional_zero hd hEndpoint hR hA hCoeff hu hmax
  rw [maximizer_functional_eq_density hd hR hA hu hmax, hCoeff] at hz
  have heq : C * fourierEnergy q = densityEntropy q.value := by
    rw [hQ, smoothGibbsDensity_entropy hR hu hs]
    exact sub_eq_zero.mp hz
  have hq := hMixture q (smoothGibbsValue_continuous u hs)
    (smoothGibbsValue_pos hR hu)
    (GenericCosineRepresentation.steiner_maximizer_mixture hd hA hu hmax hStR hStU) heq
  have hzero : densityEntropy (smoothGibbsValue u) = 0 := by
    change densityEntropy q.value = 0
    simp only [densityEntropy, hq, Real.log_one, mul_zero, integral_zero]
  exact (EntropyVariationalEquality.entropy_eq_zero_iff r hr).mp (hEnt.symm.trans hzero)

#print axioms uniform_of_equality
end BecknerOnofri.EndpointRigidity
