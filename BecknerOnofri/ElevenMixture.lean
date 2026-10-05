import BecknerOnofri.ElevenScalarTail
import Legacy.BecknerOnofri.LowDimensionMixtureEndpoint

/-! Transfer of the actual eleven-dimensional scalar bound to positive cosine
mixtures, by the same hypergeometric representation as the manuscript. -/
noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint Filter
open scoped Topology ContDiff
namespace Legacy.BecknerOnofri.ElevenMixture
open _root_.BecknerOnofri.HighDim.Eleven
open CosineMixtureEnergy CosineMixtureApproximation PositivePolynomialLimit

/-- The coefficient beta0/(2 sigma11) in the free energy. -/
def coupling : ℝ := (3543/200) / (2 * _root_.BecknerOnofri.HighDim.spectralThreshold 11)

lemma coupling_pos : 0 < coupling := by
  unfold coupling
  have h := spectralThreshold_bounds.1
  positivity

lemma twice_coupling : 2 * coupling = (3543/200) / _root_.BecknerOnofri.HighDim.spectralThreshold 11 := by
  unfold coupling
  ring

lemma scalar_indicator_bound (n : ℕ) :
    (2 * coupling) * GaussianLattice.binomialEnergy 11 n +
      (if n = 0 then 0 else (1/2000 : ℝ)) ≤
        11 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [GaussianScalarTail.binomialEnergy_zero, Legacy.D10.FiniteScalar.harmonic]
  · have h := ScalarTail.all_scalar_gap (show 1 ≤ n by omega)
    rw [ScalarFinite.scalarEnergy_eq_legacy, ← ScalarFinite.harmonic_eq] at h
    rw [if_neg hn, twice_coupling]
    linarith

lemma scalar_bound (n : ℕ) :
    (2 * coupling) * GaussianLattice.binomialEnergy 11 n ≤
      11 * (Legacy.D10.FiniteScalar.harmonic n : ℝ) := by
  have h := scalar_indicator_bound n
  split_ifs at h <;> linarith

theorem component_bound  (N : Fin 11 → ℕ) :
    (2 * coupling) * componentEnergy N ≤
      ∑ i, (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
  have hd0 : 0 < 11 := by omega
  have hdR : (0 : ℝ) < 11 := Nat.cast_pos.mpr hd0
  calc
    _ ≤ (2 * coupling) * ((1/(11:ℝ)) *
        ∑ i, GaussianLattice.binomialEnergy 11 (N i)) :=
      mul_le_mul_of_nonneg_left (MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 N)
        (mul_nonneg (by norm_num) coupling_pos.le)
    _ = (1/(11:ℝ)) * ∑ i, (2 * coupling) *
        GaussianLattice.binomialEnergy 11 (N i) := by rw [← mul_sum]; ring
    _ ≤ (1/(11:ℝ)) * ∑ i, (11:ℝ) * (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => scalar_bound  (N i))
    _ = _ := by rw [← mul_sum]; field_simp

theorem finite_mixture_endpoint {α : Type*} 
    (s : Finset α) (w : α → ℝ) (N : α → Fin 11 → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (hpos : ∀ x, 0 < CosineMixture.mixture s w N x) :
    Summable (densitySpectralTerm (CosineMixture.density s w N hw hm)) ∧
      coupling * fourierEnergy (CosineMixture.density s w N hw hm) ≤
        densityEntropy (CosineMixture.density s w N hw hm).value := by
  refine ⟨spectral_summable s w N hw hm, ?_⟩
  have he : (2 * coupling) *
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
      mul_le_mul_of_nonneg_left (component_bound  L) hnon
  have haxis := (TorusMarginals.axis_entropy_bound (by omega : 0 < 11)
    (CosineMixture.density s w N hw hm) (CosineMixture.mixture_continuous s w N) hpos).2
  rw [CosineMixtureAxis.density_axis_sum_eq] at haxis
  linarith


theorem countable_mixture_endpoint 
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    Summable (densitySpectralTerm (probabilityDensity w N hw hm hSup)) ∧
      coupling * fourierEnergy (probabilityDensity w N hw hm hSup) ≤
        densityEntropy (probabilityDensity w N hw hm hSup).value := by
  apply EndpointClosure.spectral_bound_of_limits coupling coupling_pos
    (approximatingDensity w N hw hm) (probabilityDensity w N hw hm hSup)
    _ (EndpointClosure.fourier_tendsto_of_L1 _ _ (density_L1_tendsto w N hw hm hSup))
    (density_entropy_tendsto w N hw hm hSup)
  intro m
  exact finite_mixture_endpoint 
    (Finset.range (m+1)) (finiteWeight w m) (finiteIndex N m)
    (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)
    (approximatingDensity_pos w N hw hm m)

theorem positive_monomial_series_endpoint 
    (r : ProbabilityDensity 11) (c : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (heq : ∀ x, r.value x = ∑' n, c n * PositiveCosineRepresentation.monomial (N n) x) :
    Summable (densitySpectralTerm r) ∧
      coupling * fourierEnergy r ≤ densityEntropy r.value := by
  let w := PositiveCosineRepresentation.weights c N
  have hw := PositiveCosineRepresentation.weights_nonneg c N hc
  have hm := PositiveCosineRepresentation.weights_hasSum_one r c N hc hs heq
  have hSup := PositiveCosineRepresentation.weights_majorant_summable c N hs
  have h := countable_mixture_endpoint  w N hw hm hSup
  have hv : (probabilityDensity w N hw hm hSup).value = r.value :=
    (PositiveCosineRepresentation.density_eq_countable_mixture r c N heq).symm
  have ht : densitySpectralTerm (probabilityDensity w N hw hm hSup) = densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, hv]
  simpa only [fourierEnergy, ht, hv] using h


theorem positive_cube_series_endpoint 
    (r : ProbabilityDensity 11) (c : Index 11 → ℝ) (hc : ∀ a, 0 ≤ c a) (hs : Summable c)
    (hr : ∀ x, r.value x = ∑' a, c a * monomialValue a (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ coupling * fourierEnergy r ≤ densityEntropy r.value := by
  letI : Nonempty (Fin 11) := ⟨⟨0, by omega⟩⟩
  letI : Countable (Index 11) :=
    (Finsupp.equivFunOnFinite : Index 11 ≃ (Fin 11 → ℕ)).injective.countable
  let e : ℕ ≃ Index 11 := Classical.choice (inferInstance : Nonempty (ℕ ≃ Index 11))
  apply positive_monomial_series_endpoint  r
    (fun n => c (e n)) (fun n i => (e n) i) (fun n => hc (e n)) (e.summable_iff.mpr hs)
  intro x
  rw [hr]
  exact (e.tsum_eq (fun a => c a * monomialValue a (PositiveCosineRepresentation.cube x))).symm

theorem positive_polynomial_limit_endpoint 
    (r : ProbabilityDensity 11) {P : ℕ → MvPolynomial (Fin 11) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1 : ℝ)) (P m) = M)
    {c : Index 11 → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube 11 → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i : ℝ)) (P m)) atTop (𝓝 (f y)))
    (hr : ∀ x, r.value x = f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ coupling * fourierEnergy r ≤ densityEntropy r.value := by
  apply positive_cube_series_endpoint  r c (limit_coefficient_nonneg hP hlim)
    (limit_coefficient_summable hP hmass hlim)
  intro x
  rw [hr]
  exact representation hP hmass hlim hfc hf _


open BernsteinPositiveCoefficients in
/-- Actual smooth absolute monotonicity implies the endpoint, including 11=2.
The positive series is constructed from the genuine derivatives, not assumed. -/
theorem absolutely_monotone_endpoint 
    (r : ProbabilityDensity 11) {f : FiniteDifferences.Space 11 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube 11))
    (hpos : NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = restriction f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧
      coupling * fourierEnergy r ≤ densityEntropy r.value := by
  apply positive_cube_series_endpoint  r
    (taylorCoefficient f) (taylorCoefficient_nonneg hpos) (positiveTaylor_mass hf hpos).summable
  intro x
  rw [hr]
  exact (positiveTaylor_hasSum hf hpos _).tsum_eq.symm


#print axioms absolutely_monotone_endpoint
end Legacy.BecknerOnofri.ElevenMixture
