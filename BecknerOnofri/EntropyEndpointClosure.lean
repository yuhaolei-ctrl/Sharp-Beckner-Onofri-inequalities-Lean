module

public import BecknerOnofri.SelectedEntropyRigidity

@[expose] public section

/-! Analytic closure of the latest entropy route, from the vanishing of actual
selected maximizers. Heat approximation preserves the finite-entropy domain;
the dimension induction and equality selection preserve the exact endpoints.
No numerical neighborhood or radial-iteration estimate is an input here. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyEndpointClosure
open Legacy.BecknerOnofri Legacy.TorusEndpoint
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier SteinerSelection
open SelectedNumericalModel

theorem twelve_primal_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    (v : TorusL2 12) (hv : Admissible v) : functional (1 / 2) v ≤ 0 := by
  obtain ⟨u, hu, hmax, hStR, hStU⟩ := GenericAttainment.exists_steiner_optimizer
    (by norm_num : 0 < 12) (CosineMixtureTransfer.half_strictly_subcritical (by norm_num : 12 ≤ 12))
  have hz := hzero ⟨hu,hmax,hStR,hStU⟩
  have h := hmax v hv
  simpa [hz] using h

theorem twelve_legacy_l2_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12)
    (hr : MemLp r.value 2 (torusMeasure 12)) :
    Summable (densitySpectralTerm r) ∧ (1 / 2 : ℝ) * fourierEnergy r ≤ densityEntropy r.value := by
  refine ⟨(PhysicalGreenL2.physicalGreenEnergy_eq_spectral (by norm_num) r hr).1, ?_⟩
  have h := SubcriticalPrimalDual.density_le_dual (by norm_num) rough
    (by norm_num : (0 : ℝ) < 1 / 2) r hr
  have hp := twelve_primal_endpoint_of_selected_zero hzero
    (SubcriticalPrimalDual.dualPotential (1 / 2) r hr)
    (SubcriticalPrimalDual.dualPotential_admissible (by norm_num) (1 / 2) r hr)
  unfold SubcriticalPrimalDual.densityFunctional at h
  norm_num at h
  linarith

theorem twelve_legacy_entropy_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12) (hr : r.FiniteEntropy) :
    Summable (densitySpectralTerm r) ∧ (1 / 2 : ℝ) * fourierEnergy r ≤ densityEntropy r.value := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let rs : ℕ → Legacy.TorusEndpoint.ProbabilityDensity 12 :=
    fun n => HeatDensityApproximation.heatDensity r (ht n)
  apply EndpointClosure.spectral_bound_of_fourier_limits_entropy_le (1 / 2) (by norm_num) rs r
  · intro n
    exact twelve_legacy_l2_endpoint_of_selected_zero hzero (rs n)
      ((HeatDensityApproximation.heatValue_continuous r (ht n)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact HeatDensityApproximation.heatDensity_fourier_tendsto r t ht
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact HeatDensityApproximation.heatDensity_entropy_le r hr (ht n)

/-- The exact trusted d=12 finite-entropy density endpoint follows from the
vanishing of selected maximizers, including spectral-energy finiteness. -/
theorem twelve_density_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    (r : ProbabilityDensity 12) (hr : r.FiniteEntropy) :
    spectralEnergy r ≤ ENNReal.ofReal (2 * entropy r) := by
  have h := twelve_legacy_entropy_endpoint_of_selected_zero hzero (Bridge.density r) hr
  have he : Bridge.rawDensity (Bridge.density r) = r := by cases r; rfl
  rw [← he, Bridge.rawDensity_spectralEnergy _ h.1]
  apply ENNReal.ofReal_le_ofReal
  change fourierEnergy (Bridge.density r) ≤ 2 * entropy r
  have hb := h.2
  change (1 / 2 : ℝ) * fourierEnergy (Bridge.density r) ≤ entropy r at hb
  linarith

/-- All dimensions d≥12 are reduced to exactly the stated d=12 vanishing of selected maximizers. No
certificate assertion is part of this theorem. -/
theorem density_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    {d : ℕ} (hd : 12 ≤ d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    spectralEnergy r ≤ ENNReal.ofReal (2 * entropy r) :=
  CosineMixtureTransfer.density_endpoint_of_twelve_density
    (twelve_density_endpoint_of_selected_zero hzero) hd r hr

lemma smoothGibbsValue_zero (x : Torus 12) : smoothGibbsValue (0 : TorusL2 12) x = 1 := by
  simp [smoothGibbsValue, WienerFourier.representative, Legacy.TorusEndpoint.absoluteFourierSeries]

/-- Entropy-preserving endpoint Steiner selection transfers the entropy rigidity to
rigidity for every finite-entropy equality density in dimension twelve. -/
theorem twelve_legacy_uniform_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    (r : Legacy.TorusEndpoint.ProbabilityDensity 12) (hr : r.FiniteEntropy)
    (he : (1 / 2 : ℝ) * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure 12] (fun _ => 1) := by
  have hEndpoint : EndpointRigidity.CoefficientEndpoint 12 (1 / 2) :=
    twelve_legacy_entropy_endpoint_of_selected_zero hzero
  have hL2 := EndpointRigidity.DensityGibbs.memLp_two_of_equality (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 2) hEndpoint r hr he
  have hC : 0 < endpointConstant 12 := div_pos (by norm_num) (endpointSigma_pos (by norm_num))
  obtain ⟨u, hu, hmax, hStR, hStU, hEnt⟩ := EndpointRigidity.Selection.exists_steiner_equality
    (by norm_num) hEndpoint (by positivity : 0 < endpointConstant 12 / 2) rough
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : 1 / (4 * (1 / 2 : ℝ)) = 1 / 2)
    r hL2 he.symm
  have hz := hzero ⟨hu,hmax,hStR,hStU⟩
  have hzero : densityEntropy (smoothGibbsValue u) = 0 := by
    rw [hz]
    simp [densityEntropy, smoothGibbsValue_zero]
  exact (EntropyVariationalEquality.entropy_eq_zero_iff r hr).mp (hEnt.symm.trans hzero)

/-- The d=12 rigidity base used in dimension induction follows from the same
vanishing of selected maximizers as the endpoint inequality. -/
theorem twelve_mixture_rigidity_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0) :
    EndpointRigidity.MixtureRigidity 12 :=
  EndpointRigidity.mixtureRigidity_of_densityRigidity (by norm_num)
    (twelve_legacy_uniform_of_selected_zero hzero)

theorem twelve_mixture_endpoint_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0) :
    CosineMixtureTransfer.MixtureEndpoint 12 :=
  CosineMixtureTransfer.mixture_endpoint_of_density (by norm_num)
    (twelve_density_endpoint_of_selected_zero hzero)

/-- The exact trusted density equality characterization in every d≥12 needs
only the same single selected-maximizer vanishing. -/
theorem density_rigidity_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    {d : ℕ} (hd : 12 ≤ d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    spectralEnergy r = ENNReal.ofReal (2 * entropy r) ↔
      r.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  density_rigidity_from_twelve (twelve_mixture_endpoint_of_selected_zero hzero)
    (twelve_mixture_rigidity_of_selected_zero hzero) hd r hr

theorem potential_rigidity_of_selected_zero (hzero : ∀ {u : TorusL2 12}, Selected u → u=0)
    {d : ℕ} (hd : 12 ≤ d) (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] (fun _ => c) :=
  potential_rigidity_from_twelve (twelve_mixture_endpoint_of_selected_zero hzero)
    (twelve_mixture_rigidity_of_selected_zero hzero) hd u hu

#print axioms density_endpoint_of_selected_zero
#print axioms density_rigidity_of_selected_zero
#print axioms potential_rigidity_of_selected_zero
end BecknerOnofri.HighDim.EntropyEndpointClosure
