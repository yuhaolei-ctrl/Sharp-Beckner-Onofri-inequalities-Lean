import BecknerOnofri.LocalFourierExit
import BecknerOnofri.GenericCosineRepresentation
import BecknerOnofri.CountableMixtureTransfer
import BecknerOnofri.EndpointPackage

/-! The exact remaining numerical neighborhood obligation in dimension twelve.
This file proves consequences of that obligation; it does not assert or certify it.
The coefficient signs, summability, optimizer selection, and local exit theorem
are all proved independently from the actual torus analytic definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier SteinerSelection

private theorem twelve_rough :
    RoughExponentialBound 12 (endpointConstant 12 / 2)
      (GreenRoughEnergy.partition 12 (endpointConstant 12 / 2)) := by
  have hC : 0 < endpointConstant 12 := div_pos (by norm_num) (endpointSigma_pos (by norm_num))
  exact GenericAttainment.rough_bound (by norm_num) (by positivity) (by linarith)

/-- The two exact numerical output bounds required from the dimension-twelve
certified iteration, for every selected actual endpoint maximizer. -/
def TwelveNumericalNeighborhood : Prop :=
  ∀ (u : TorusL2 12), Admissible u →
    (∀ v : TorusL2 12, Admissible v → functional (1 / 2) v ≤ functional (1 / 2) u) →
    Steiner (smoothGibbsValue u) → Steiner (fun x => (WienerFourier.representative u x).re) →
    (∀ i : Fin 12, (fourierIsometry 12 u (axisFrequency i)).re ≤ 1 / 14) ∧
    (∑' k : HigherFrequency 12, (fourierIsometry 12 u k.val).re) ≤ (1 / 30 : ℝ)

/-- Nonnegative real coefficients follow from the actual cosine mixture and
Fourier Euler equation, independently of the numerical neighborhood bounds. -/
theorem twelve_selected_fourier_nonnegative (u : TorusL2 12) (hu : Admissible u)
    (hmax : ∀ v : TorusL2 12, Admissible v → functional (1 / 2) v ≤ functional (1 / 2) u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (WienerFourier.representative u x).re))
    (k : Frequency 12) :
    fourierIsometry 12 u k = ((fourierIsometry 12 u k).re : ℂ) ∧
      0 ≤ (fourierIsometry 12 u k).re := by
  by_cases hk : k = 0
  · subst k
    simp [hu.2.1]
  obtain ⟨w, N, hw, hm, hSup, heq⟩ :=
    GenericCosineRepresentation.steiner_maximizer_mixture (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
      hu hmax hStR hStU
  have hs := maximizer_fourier_summable (by norm_num) twelve_rough
    (by norm_num : (0 : ℝ) < 1 / 2) hu hmax
  let a : ℝ := ∑' n, w n * RandomRectangles.componentCoeff (N n) k
  have ha : 0 ≤ a := tsum_nonneg (fun n => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  have hρ : densityFourier (gibbsValue u) k = (a : ℂ) := by
    rw [← smoothGibbsDensity_fourier twelve_rough hu hs k]
    change densityFourier (smoothGibbsValue u) k = _
    rw [heq, CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  rw [maximizer_fourier_formula twelve_rough (by norm_num : (0 : ℝ) < 1 / 2) hu hmax hk, hρ]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  constructor
  · trivial
  · positivity

/-- A selected actual maximizer inside the certified neighborhood must vanish. -/
theorem twelve_selected_maximizer_zero (hnum : TwelveNumericalNeighborhood)
    (u : TorusL2 12) (hu : Admissible u)
    (hmax : ∀ v : TorusL2 12, Admissible v → functional (1 / 2) v ≤ functional (1 / 2) u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (WienerFourier.representative u x).re)) : u = 0 := by
  by_contra hne
  let t : Fin 12 → ℝ := fun i => (fourierIsometry 12 u (axisFrequency i)).re
  have hc := twelve_selected_fourier_nonnegative u hu hmax hStR hStU
  obtain ⟨hfirst, htail⟩ := hnum u hu hmax hStR hStU
  have hs := maximizer_fourier_summable (by norm_num) twelve_rough
    (by norm_num : (0 : ℝ) < 1 / 2) hu hmax
  have hn (k : Frequency 12) : ‖fourierIsometry 12 u k‖ = (fourierIsometry 12 u k).re := by
    calc
      _ = ‖((fourierIsometry 12 u k).re : ℂ)‖ := congrArg norm (hc k).1
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc k).2]
  have hlt := local_fourier_exit u hu t (fun i => (hc _).1) (fun i => (hc _).2)
    hfirst (hs.subtype _) (by simpa only [hn] using htail) hne
  rw [spectral_dual_eq_raw (by norm_num),
    RawAttainment.rawFunctional_realValue (by norm_num) _ u hu] at hlt
  have he : spectralCoefficient 12 * (2 * Real.pi) ^ 12 = (1 / 2 : ℝ) := by
    unfold spectralCoefficient
    field_simp
  rw [he] at hlt
  have hnon : (0 : ℝ) ≤ functional (1 / 2) u := by
    simpa using hmax 0 (admissible_zero 12)
  have hlt' : functional (1 / 2) u < (0 : ℝ) := by exact_mod_cast hlt
  linarith

/-- The exact dimension-twelve Sobolev endpoint follows from the numerical
neighborhood obligation and already-proved analytic selection and exit. -/
theorem twelve_primal_endpoint_of_neighborhood (hnum : TwelveNumericalNeighborhood)
    (v : TorusL2 12) (hv : Admissible v) : functional (1 / 2) v ≤ 0 := by
  obtain ⟨u, hu, hmax, hStR, hStU⟩ := GenericAttainment.exists_steiner_optimizer
    (by norm_num : 0 < 12) (CosineMixtureTransfer.half_strictly_subcritical (by norm_num : 12 ≤ 12))
  have hz := twelve_selected_maximizer_zero hnum u hu hmax hStR hStU
  have h := hmax v hv
  simpa [hz] using h

theorem twelve_legacy_l2_endpoint_of_neighborhood (hnum : TwelveNumericalNeighborhood)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12)
    (hr : MemLp r.value 2 (torusMeasure 12)) :
    Summable (densitySpectralTerm r) ∧ (1 / 2 : ℝ) * fourierEnergy r ≤ densityEntropy r.value := by
  refine ⟨(PhysicalGreenL2.physicalGreenEnergy_eq_spectral (by norm_num) r hr).1, ?_⟩
  have h := SubcriticalPrimalDual.density_le_dual (by norm_num) twelve_rough
    (by norm_num : (0 : ℝ) < 1 / 2) r hr
  have hp := twelve_primal_endpoint_of_neighborhood hnum
    (SubcriticalPrimalDual.dualPotential (1 / 2) r hr)
    (SubcriticalPrimalDual.dualPotential_admissible (by norm_num) (1 / 2) r hr)
  unfold SubcriticalPrimalDual.densityFunctional at h
  norm_num at h
  linarith

theorem twelve_legacy_entropy_endpoint_of_neighborhood (hnum : TwelveNumericalNeighborhood)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12) (hr : r.FiniteEntropy) :
    Summable (densitySpectralTerm r) ∧ (1 / 2 : ℝ) * fourierEnergy r ≤ densityEntropy r.value := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let rs : ℕ → Legacy.TorusEndpoint.ProbabilityDensity 12 :=
    fun n => HeatDensityApproximation.heatDensity r (ht n)
  apply EndpointClosure.spectral_bound_of_fourier_limits_entropy_le (1 / 2) (by norm_num) rs r
  · intro n
    exact twelve_legacy_l2_endpoint_of_neighborhood hnum (rs n)
      ((HeatDensityApproximation.heatValue_continuous r (ht n)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact HeatDensityApproximation.heatDensity_fourier_tendsto r t ht
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact HeatDensityApproximation.heatDensity_entropy_le r hr (ht n)

/-- The exact trusted d=12 finite-entropy density endpoint follows from the
numerical neighborhood obligation, including spectral-energy finiteness. -/
theorem twelve_density_endpoint_of_neighborhood (hnum : TwelveNumericalNeighborhood)
    (r : ProbabilityDensity 12) (hr : r.FiniteEntropy) :
    spectralEnergy r ≤ ENNReal.ofReal (2 * entropy r) := by
  have h := twelve_legacy_entropy_endpoint_of_neighborhood hnum (Bridge.density r) hr
  have he : Bridge.rawDensity (Bridge.density r) = r := by cases r; rfl
  rw [← he, Bridge.rawDensity_spectralEnergy _ h.1]
  apply ENNReal.ofReal_le_ofReal
  change fourierEnergy (Bridge.density r) ≤ 2 * entropy r
  have hb := h.2
  change (1 / 2 : ℝ) * fourierEnergy (Bridge.density r) ≤ entropy r at hb
  linarith

/-- All dimensions d≥12 are reduced to exactly the stated d=12 numerical
neighborhood obligation. No certificate assertion is part of this theorem. -/
theorem density_endpoint_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    spectralEnergy r ≤ ENNReal.ofReal (2 * entropy r) :=
  CosineMixtureTransfer.density_endpoint_of_twelve_density
    (twelve_density_endpoint_of_neighborhood hnum) hd r hr

lemma smoothGibbsValue_zero (x : Torus 12) : smoothGibbsValue (0 : TorusL2 12) x = 1 := by
  simp [smoothGibbsValue, WienerFourier.representative, Legacy.TorusEndpoint.absoluteFourierSeries]

/-- Entropy-preserving endpoint Steiner selection transfers the local exit to
rigidity for every finite-entropy equality density in dimension twelve. -/
theorem twelve_legacy_uniform_of_neighborhood (hnum : TwelveNumericalNeighborhood)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12) (hr : r.FiniteEntropy)
    (he : (1 / 2 : ℝ) * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure 12] (fun _ => 1) := by
  have hEndpoint : EndpointRigidity.CoefficientEndpoint 12 (1 / 2) :=
    twelve_legacy_entropy_endpoint_of_neighborhood hnum
  have hL2 := EndpointRigidity.DensityGibbs.memLp_two_of_equality (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 2) hEndpoint r hr he
  have hC : 0 < endpointConstant 12 := div_pos (by norm_num) (endpointSigma_pos (by norm_num))
  obtain ⟨u, hu, hmax, hStR, hStU, hEnt⟩ := EndpointRigidity.Selection.exists_steiner_equality
    (by norm_num) hEndpoint (by positivity : 0 < endpointConstant 12 / 2) twelve_rough
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : 1 / (4 * (1 / 2 : ℝ)) = 1 / 2)
    r hL2 he.symm
  have hz := twelve_selected_maximizer_zero hnum u hu hmax hStR hStU
  have hzero : densityEntropy (smoothGibbsValue u) = 0 := by
    rw [hz]
    simp [densityEntropy, smoothGibbsValue_zero]
  exact (EntropyVariationalEquality.entropy_eq_zero_iff r hr).mp (hEnt.symm.trans hzero)

/-- The d=12 rigidity base used in dimension induction follows from the same
numerical neighborhood obligation as the endpoint inequality. -/
theorem twelve_mixture_rigidity_of_neighborhood (hnum : TwelveNumericalNeighborhood) :
    EndpointRigidity.MixtureRigidity 12 :=
  EndpointRigidity.mixtureRigidity_of_densityRigidity (by norm_num)
    (twelve_legacy_uniform_of_neighborhood hnum)

theorem twelve_mixture_endpoint_of_neighborhood (hnum : TwelveNumericalNeighborhood) :
    CosineMixtureTransfer.MixtureEndpoint 12 :=
  CosineMixtureTransfer.mixture_endpoint_of_density (by norm_num)
    (twelve_density_endpoint_of_neighborhood hnum)

/-- The exact trusted density equality characterization in every d≥12 needs
only the same single numerical-neighborhood obligation. -/
theorem density_rigidity_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    spectralEnergy r = ENNReal.ofReal (2 * entropy r) ↔
      r.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  density_rigidity_from_twelve (twelve_mixture_endpoint_of_neighborhood hnum)
    (twelve_mixture_rigidity_of_neighborhood hnum) hd r hr

theorem potential_rigidity_of_twelve_neighborhood (hnum : TwelveNumericalNeighborhood)
    {d : ℕ} (hd : 12 ≤ d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) :=
  potential_rigidity_from_twelve (twelve_mixture_endpoint_of_neighborhood hnum)
    (twelve_mixture_rigidity_of_neighborhood hnum) hd u hu

#print axioms density_rigidity_of_twelve_neighborhood
#print axioms potential_rigidity_of_twelve_neighborhood

#print axioms density_endpoint_of_twelve_neighborhood

#print axioms twelve_selected_fourier_nonnegative
#print axioms twelve_selected_maximizer_zero
#print axioms twelve_primal_endpoint_of_neighborhood
end BecknerOnofri.HighDim
