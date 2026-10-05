module

public import Legacy.BecknerOnofri.GaussianScalarTwo
public import Legacy.BecknerOnofri.PositivePolynomialEndpoint
public import Legacy.BecknerOnofri.BernsteinPositiveCoefficients

@[expose] public section

/-! The actual mixture and positive-profile density endpoints in every dimension 2 through 10.
The old dimension-three interfaces are preserved in their original modules.
This module contains no unproved scalar or positive-series premise in its final smooth-profile theorem.
-/
noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint Filter
open scoped Topology ContDiff
namespace Legacy.BecknerOnofri.LowDimensionMixtureEndpoint
open CosineMixtureEnergy GaussianScalarTail CosineMixtureApproximation PositivePolynomialLimit

theorem scalar_bound {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (n : ℕ) :
    (2 * endpointConstant d) * GaussianLattice.binomialEnergy d n ≤
      (d : ℝ) * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  by_cases hd : d = 2
  · subst d
    exact GaussianScalarTwo.all_indices_lattice_bound n
  · exact GaussianScalarTail.all_indices_lattice_bound (by omega) hd10 n

theorem component_bound {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (N : Fin d → ℕ) :
    (2 * endpointConstant d) * componentEnergy N ≤
      ∑ i, (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  calc
    _ ≤ (2 * endpointConstant d) * ((1/(d:ℝ)) *
        ∑ i, GaussianLattice.binomialEnergy d (N i)) :=
      mul_le_mul_of_nonneg_left (MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 N)
        (coefficient_nonneg hd0)
    _ = (1/(d:ℝ)) * ∑ i, (2 * endpointConstant d) *
        GaussianLattice.binomialEnergy d (N i) := by rw [← mul_sum]; ring
    _ ≤ (1/(d:ℝ)) * ∑ i, (d:ℝ) * (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => scalar_bound hd2 hd10 (N i))
    _ = _ := by rw [← mul_sum]; field_simp

theorem finite_mixture_endpoint {α : Type*} {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (hpos : ∀ x, 0 < CosineMixture.mixture s w N x) :
    Summable (densitySpectralTerm (CosineMixture.density s w N hw hm)) ∧
      endpointConstant d * fourierEnergy (CosineMixture.density s w N hw hm) ≤
        densityEntropy (CosineMixture.density s w N hw hm).value := by
  refine ⟨spectral_summable s w N hw hm, ?_⟩
  have he : (2 * endpointConstant d) *
      fourierEnergy (CosineMixture.density s w N hw hm) ≤
        ∑ a ∈ s, ∑ b ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a),
          w a * w b * Legacy.D10.latentWeight (N a) (N b) L *
            ∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ) := by
    rw [fourierEnergy_eq_latent]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum
    intro L hL
    have hnon := Legacy.D10.correlated_latent_nonneg w w N N a b L (hw a ha) (hw b hb)
    simpa only [Finset.mul_sum, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left (component_bound hd2 hd10 L) hnon
  have haxis := (TorusMarginals.axis_entropy_bound (by omega : 0 < d)
    (CosineMixture.density s w N hw hm) (CosineMixture.mixture_continuous s w N) hpos).2
  rw [CosineMixtureAxis.density_axis_sum_eq] at haxis
  linarith


theorem countable_mixture_endpoint {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    Summable (densitySpectralTerm (probabilityDensity w N hw hm hSup)) ∧
      endpointConstant d * fourierEnergy (probabilityDensity w N hw hm hSup) ≤
        densityEntropy (probabilityDensity w N hw hm hSup).value := by
  apply EndpointClosure.endpoint_of_L1_entropy_limit (by omega : 0 < d)
    (approximatingDensity w N hw hm) (probabilityDensity w N hw hm hSup)
    _ (density_L1_tendsto w N hw hm hSup) (density_entropy_tendsto w N hw hm hSup)
  intro m
  exact finite_mixture_endpoint hd2 hd10
    (Finset.range (m+1)) (finiteWeight w m) (finiteIndex N m)
    (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)
    (approximatingDensity_pos w N hw hm m)

theorem positive_monomial_series_endpoint {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (heq : ∀ x, r.value x = ∑' n, c n * PositiveCosineRepresentation.monomial (N n) x) :
    Summable (densitySpectralTerm r) ∧
      endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  let w := PositiveCosineRepresentation.weights c N
  have hw := PositiveCosineRepresentation.weights_nonneg c N hc
  have hm := PositiveCosineRepresentation.weights_hasSum_one r c N hc hs heq
  have hSup := PositiveCosineRepresentation.weights_majorant_summable c N hs
  have h := countable_mixture_endpoint hd2 hd10 w N hw hm hSup
  have hv : (probabilityDensity w N hw hm hSup).value = r.value :=
    (PositiveCosineRepresentation.density_eq_countable_mixture r c N heq).symm
  have ht : densitySpectralTerm (probabilityDensity w N hw hm hSup) = densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, hv]
  simpa only [fourierEnergy, ht, hv] using h


theorem positive_cube_series_endpoint {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : Index d → ℝ) (hc : ∀ a, 0 ≤ c a) (hs : Summable c)
    (hr : ∀ x, r.value x = ∑' a, c a * monomialValue a (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  letI : Countable (Index d) :=
    (Finsupp.equivFunOnFinite : Index d ≃ (Fin d → ℕ)).injective.countable
  let e : ℕ ≃ Index d := Classical.choice (inferInstance : Nonempty (ℕ ≃ Index d))
  apply positive_monomial_series_endpoint hd2 hd10 r
    (fun n => c (e n)) (fun n i => (e n) i) (fun n => hc (e n)) (e.summable_iff.mpr hs)
  intro x
  rw [hr]
  exact (e.tsum_eq (fun a => c a * monomialValue a (PositiveCosineRepresentation.cube x))).symm

theorem positive_polynomial_limit_endpoint {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1 : ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i : ℝ)) (P m)) atTop (𝓝 (f y)))
    (hr : ∀ x, r.value x = f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  apply positive_cube_series_endpoint hd2 hd10 r c (limit_coefficient_nonneg hP hlim)
    (limit_coefficient_summable hP hmass hlim)
  intro x
  rw [hr]
  exact representation hP hmass hlim hfc hf _


open BernsteinPositiveCoefficients in
/-- Actual smooth absolute monotonicity implies the endpoint, including d=2.
The positive series is constructed from the genuine derivatives, not assumed. -/
theorem absolutely_monotone_endpoint {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {f : FiniteDifferences.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d))
    (hpos : NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = restriction f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧
      endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  apply positive_cube_series_endpoint hd2 hd10 r
    (taylorCoefficient f) (taylorCoefficient_nonneg hpos) (positiveTaylor_mass hf hpos).summable
  intro x
  rw [hr]
  exact (positiveTaylor_hasSum hf hpos _).tsum_eq.symm

#print axioms scalar_bound
#print axioms finite_mixture_endpoint
#print axioms countable_mixture_endpoint
#print axioms positive_cube_series_endpoint
#print axioms positive_polynomial_limit_endpoint
#print axioms absolutely_monotone_endpoint
end Legacy.BecknerOnofri.LowDimensionMixtureEndpoint
