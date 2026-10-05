module

public import Legacy.BecknerOnofri.StrictCountableMixture

@[expose] public section

/-! Equality forces the actual density to be uniform for summable positive
cosine series, and hence for smooth absolutely monotone closed-cube profiles.
No rearrangement or regularity of an arbitrary endpoint equality case is assumed here. -/
noncomputable section
open Legacy.TorusEndpoint Filter
open scoped Topology ContDiff
namespace Legacy.BecknerOnofri.StrictMixture
open CosineMixtureApproximation PositivePolynomialLimit

theorem positive_monomial_series_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (hr : ∀ x, r.value x = ∑' n, c n * PositiveCosineRepresentation.monomial (N n) x)
    (heq : endpointConstant d * fourierEnergy r = densityEntropy r.value) :
    ∀ x, r.value x = 1 := by
  let w := PositiveCosineRepresentation.weights c N
  have hw := PositiveCosineRepresentation.weights_nonneg c N hc
  have hm := PositiveCosineRepresentation.weights_hasSum_one r c N hc hs hr
  have hSup := PositiveCosineRepresentation.weights_majorant_summable c N hs
  have hv : (probabilityDensity w N hw hm hSup).value = r.value :=
    (PositiveCosineRepresentation.density_eq_countable_mixture r c N hr).symm
  have ht : densitySpectralTerm (probabilityDensity w N hw hm hSup) = densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, hv]
  have h := countable_mixture_uniform_of_equality hd2 hd10 w N hw hm hSup
    (by simpa only [fourierEnergy, ht, hv] using heq)
  intro x
  rw [← hv]
  exact h x

theorem positive_cube_series_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : Index d → ℝ) (hc : ∀ a, 0 ≤ c a) (hs : Summable c)
    (hr : ∀ x, r.value x = ∑' a, c a * monomialValue a (PositiveCosineRepresentation.cube x))
    (heq : endpointConstant d * fourierEnergy r = densityEntropy r.value) :
    ∀ x, r.value x = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  letI : Countable (Index d) :=
    (Finsupp.equivFunOnFinite : Index d ≃ (Fin d → ℕ)).injective.countable
  let e : ℕ ≃ Index d := Classical.choice (inferInstance : Nonempty (ℕ ≃ Index d))
  apply positive_monomial_series_uniform_of_equality hd2 hd10 r
    (fun n => c (e n)) (fun n i => (e n) i) (fun n => hc (e n)) (e.summable_iff.mpr hs) _ heq
  intro x
  rw [hr]
  exact (e.tsum_eq (fun a => c a * monomialValue a (PositiveCosineRepresentation.cube x))).symm

theorem positive_polynomial_limit_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1 : ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i : ℝ)) (P m)) atTop (𝓝 (f y)))
    (hr : ∀ x, r.value x = f (PositiveCosineRepresentation.cube x))
    (heq : endpointConstant d * fourierEnergy r = densityEntropy r.value) :
    ∀ x, r.value x = 1 := by
  apply positive_cube_series_uniform_of_equality hd2 hd10 r c
    (limit_coefficient_nonneg hP hlim) (limit_coefficient_summable hP hmass hlim) _ heq
  intro x
  rw [hr]
  exact representation hP hmass hlim hfc hf _

open BernsteinPositiveCoefficients in
theorem absolutely_monotone_uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {f : FiniteDifferences.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d))
    (hpos : NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = restriction f (PositiveCosineRepresentation.cube x))
    (heq : endpointConstant d * fourierEnergy r = densityEntropy r.value) :
    ∀ x, r.value x = 1 := by
  apply positive_cube_series_uniform_of_equality hd2 hd10 r
    (taylorCoefficient f) (taylorCoefficient_nonneg hpos) (positiveTaylor_mass hf hpos).summable _ heq
  intro x
  rw [hr]
  exact (positiveTaylor_hasSum hf hpos _).tsum_eq.symm

open BernsteinPositiveCoefficients in
theorem absolutely_monotone_strict {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {f : FiniteDifferences.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d))
    (hpos : NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = restriction f (PositiveCosineRepresentation.cube x))
    (hnon : ∃ x, r.value x ≠ 1) :
    endpointConstant d * fourierEnergy r < densityEntropy r.value := by
  apply lt_of_le_of_ne (LowDimensionMixtureEndpoint.absolutely_monotone_endpoint hd2 hd10 r hf hpos hr).2
  intro heq
  have h := absolutely_monotone_uniform_of_equality hd2 hd10 r hf hpos hr heq
  obtain ⟨x, hx⟩ := hnon
  exact hx (h x)

#print axioms positive_cube_series_uniform_of_equality
#print axioms absolutely_monotone_uniform_of_equality
#print axioms absolutely_monotone_strict
end Legacy.BecknerOnofri.StrictMixture
