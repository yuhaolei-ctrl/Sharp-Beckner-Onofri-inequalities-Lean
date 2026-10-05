import BecknerOnofri.GenericAttainment
import Legacy.BecknerOnofri.EulerCriticalComparison
import Legacy.BecknerOnofri.EulerHigherPartialSigns
import Legacy.BecknerOnofri.NormalizedExponentialPartials
import Legacy.BecknerOnofri.PositiveCosineRepresentation

/-!
Dimension-independent positive cosine-mixture representation for actual Steiner
Euler maximizers. The derivative signs come from actual Jacobi heat kernels,
Mellin inverse operators, and strict weighted-kernel comparison. The positive
series comes from the proved Bernstein/Taylor theorem. No endpoint inequality,
rough estimate, sign assumption, or mixture representation is assumed here.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators ContDiff

namespace BecknerOnofri.GenericCosineRepresentation
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier SteinerSelection FiniteDifferences
open AngularMixedTerms JacobiTensorSpectrum

/-- Actual nonnegative probability weights and a summable uniform majorant. -/
def HasPositiveCosineMixture {d : ℕ} (f : Torus d → ℝ) : Prop :=
  ∃ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ),
    (∀ n, 0 ≤ w n) ∧ HasSum w 1 ∧
    Summable (fun n => w n * CosineMixture.tensor (N n) 0) ∧
    f = CosineMixtureApproximation.rho w N

private theorem default_rough {d : ℕ} (hd : 0 < d) :
    RoughExponentialBound d (endpointConstant d / 2)
      (GreenRoughEnergy.partition d (endpointConstant d / 2)) := by
  have hC : 0 < endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact GenericAttainment.rough_bound hd (by positivity) (by linarith)

/-- Every nonempty actual mixed partial of the selected potential is nonnegative
on the entire closed unit cube, including its boundary. -/
theorem steiner_maximizer_mixedPartials {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 0 < A) {u : TorusL2 d} (hu : SubcriticalAttainment.Admissible u)
    (hmax : ∀ v : TorusL2 d, SubcriticalAttainment.Admissible v → functional A v ≤ functional A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (EulerUnitProfiles.potential u) y :=
  EulerHigherPartialSigns.mixedPartials_nonnegative hd (default_rough hd) hA hu hmax hStR hStU
    (fun js hjs => EulerCriticalComparison.criticalInverse_positive (countIndex js)
      (AngularSpectralIntertwining.countIndex_ne_zero js hjs))
    (EulerCriticalComparison.higher_norm_lt_one hd (default_rough hd) hA hu hmax hStR hStU) is his

/-- Actual smooth positive profiles yield normalized countable cosine mixtures. -/
theorem positive_profile_mixture {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    {f : FiniteDifferences.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d))
    (hpos : BernsteinPositiveCoefficients.NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = BernsteinPositiveCoefficients.restriction f
      (PositiveCosineRepresentation.cube x)) : HasPositiveCosineMixture r.value := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Countable (PositivePolynomialLimit.Index d) :=
    (Finsupp.equivFunOnFinite : PositivePolynomialLimit.Index d ≃ (Fin d → ℕ)).injective.countable
  let e : ℕ ≃ PositivePolynomialLimit.Index d := Classical.choice inferInstance
  let c : ℕ → ℝ := fun n => BernsteinPositiveCoefficients.taylorCoefficient f (e n)
  let N : ℕ → Fin d → ℕ := fun n i => (e n) i
  have hc : ∀ n, 0 ≤ c n := fun n =>
    BernsteinPositiveCoefficients.taylorCoefficient_nonneg hpos (e n)
  have hs : Summable c :=
    e.summable_iff.mpr (BernsteinPositiveCoefficients.positiveTaylor_mass hf hpos).summable
  have heq : ∀ x, r.value x = ∑' n, c n * PositiveCosineRepresentation.monomial (N n) x := by
    intro x
    rw [hr x, ← (BernsteinPositiveCoefficients.positiveTaylor_hasSum hf hpos _).tsum_eq]
    exact (e.tsum_eq (fun a => BernsteinPositiveCoefficients.taylorCoefficient f a *
      PositivePolynomialLimit.monomialValue a (PositiveCosineRepresentation.cube x))).symm
  refine ⟨PositiveCosineRepresentation.weights c N, N,
    PositiveCosineRepresentation.weights_nonneg c N hc,
    PositiveCosineRepresentation.weights_hasSum_one r c N hc hs heq,
    PositiveCosineRepresentation.weights_majorant_summable c N hs, ?_⟩
  exact PositiveCosineRepresentation.density_eq_countable_mixture r c N heq

/-- The genuine smooth Gibbs density of every Steiner maximizer has a positive
cosine mixture; no derivative positivity or series representation is a premise. -/
theorem steiner_maximizer_mixture {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 0 < A) {u : TorusL2 d} (hu : SubcriticalAttainment.Admissible u)
    (hmax : ∀ v : TorusL2 d, SubcriticalAttainment.Admissible v → functional A v ≤ functional A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re)) :
    HasPositiveCosineMixture (smoothGibbsValue u) := by
  have hR := default_rough hd
  have hs := maximizer_fourier_summable hd hR hA hu hmax
  have hnon : BernsteinPositiveCoefficients.NonnegativeMixedPartials (EulerUnitProfiles.density u) :=
    NormalizedExponentialPartials.normalized_exp_nonnegative_mixed (partition_pos hR hu)
      (EulerUnitProfiles.potential_contDiffOn hd hR hA hu hmax hStU)
      (fun _ hx => EulerUnitProfiles.density_eq_exp hd hR hA hu hmax hStU hStR hx)
      (steiner_maximizer_mixedPartials hd hA hu hmax hStR hStU)
  exact positive_profile_mixture hd (smoothGibbsDensity hR hu hs)
    (EulerUnitProfiles.density_contDiffOn hd hR hA hu hmax hStR) hnon
    (EulerUnitProfiles.density_representation hd hR hA hu hmax hStR)

/-- Unconditional subcritical selection, smoothness, and actual mixture
representation in every positive dimension. -/
theorem exists_steiner_optimizer_mixture {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1 / (4 * endpointConstant d) < A) :
    ∃ u : TorusL2 d, SubcriticalAttainment.Admissible u ∧
      (∀ v : TorusL2 d, SubcriticalAttainment.Admissible v → functional A v ≤ functional A u) ∧
      Steiner (smoothGibbsValue u) ∧
      Steiner (fun x => (representative u x).re) ∧
      ContDiff ℝ ∞ (fun x : Fin d → ℝ => smoothGibbsValue u (quotient x)) ∧
      HasPositiveCosineMixture (smoothGibbsValue u) := by
  obtain ⟨u, hu, hmax, hStR, hStU⟩ := GenericAttainment.exists_steiner_optimizer hd hA
  have hC : 0 < endpointConstant d :=
    div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1 / (4 * endpointConstant d)).trans hA
  exact ⟨u, hu, hmax, hStR, hStU,
    maximizer_gibbs_contDiff_lift hd (default_rough hd) hA0 hu hmax,
    steiner_maximizer_mixture hd hA0 hu hmax hStR hStU⟩

#print axioms steiner_maximizer_mixedPartials
#print axioms positive_profile_mixture
#print axioms steiner_maximizer_mixture
#print axioms exists_steiner_optimizer_mixture

end BecknerOnofri.GenericCosineRepresentation
