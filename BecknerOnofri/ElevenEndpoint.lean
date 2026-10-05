module

public import BecknerOnofri.ElevenStrictMixture
public import BecknerOnofri.GenericCosineRepresentation
public import BecknerOnofri.EndpointRigidity.Reduction
public import BecknerOnofri.ElevenVariational

@[expose] public section

/-! Section 4: the full finite-entropy inequality at beta0. The proof selects
an actual Steiner optimizer, uses its positive cosine mixture, and transfers
back to the original full density class. Equality uses entropy-preserving
selection, as in the manuscript. -/
noncomputable section
open MeasureTheory
namespace Legacy.BecknerOnofri.ElevenMixture
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier
open _root_.BecknerOnofri

lemma coupling_lt_collapse : coupling < endpointConstant 11 := by
  have hs : 0 < _root_.BecknerOnofri.HighDim.spectralThreshold 11 :=
    _root_.BecknerOnofri.HighDim.spectralThreshold_pos (by norm_num)
  change (3543/200) / (2 * _root_.BecknerOnofri.HighDim.spectralThreshold 11) <
    11 / _root_.BecknerOnofri.HighDim.spectralThreshold 11
  apply (div_lt_div_iff₀ (by positivity) hs).2
  nlinarith

lemma dual_coefficient_subcritical : 1/(4*endpointConstant 11) < 1/(4*coupling) := by
  have hC := coupling_pos
  have hE : 0 < endpointConstant 11 := hC.trans coupling_lt_collapse
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [coupling_lt_collapse]

lemma default_rough : RoughExponentialBound 11 (endpointConstant 11/2)
    (GreenRoughEnergy.partition 11 (endpointConstant 11/2)) := by
  have hC : 0 < endpointConstant 11 := coupling_pos.trans coupling_lt_collapse
  exact GenericAttainment.rough_bound (by norm_num) (by positivity) (by linarith)

lemma mixture_endpoint (r : ProbabilityDensity 11)
    (hmix : GenericCosineRepresentation.HasPositiveCosineMixture r.value) :
    coupling * fourierEnergy r ≤ densityEntropy r.value := by
  obtain ⟨w, N, hw, hm, hSup, hv⟩ := hmix
  have h := (countable_mixture_endpoint w N hw hm hSup).2
  have he : (CosineMixtureApproximation.probabilityDensity w N hw hm hSup).value = r.value := hv.symm
  have ht : densitySpectralTerm (CosineMixtureApproximation.probabilityDensity w N hw hm hSup) =
      densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, he]
  simpa only [fourierEnergy, ht, he] using h

lemma primal_nonpos (v : TorusL2 11) (hv : Admissible v) :
    functional (1/(4*coupling)) v ≤ 0 := by
  obtain ⟨u, hu, hmax, hStR, hStU⟩ := GenericAttainment.exists_steiner_optimizer
    (by norm_num : 0 < 11) dual_coefficient_subcritical
  have hA : 0 < 1/(4*coupling) := by have := coupling_pos; positivity
  have hs := maximizer_fourier_summable (by norm_num) default_rough hA hu hmax
  have he := mixture_endpoint (smoothGibbsDensity default_rough hu hs)
    (GenericCosineRepresentation.steiner_maximizer_mixture (by norm_num) hA hu hmax hStR hStU)
  have hQ : fourierEnergy (smoothGibbsDensity default_rough hu hs) =
      fourierEnergy (gibbsDensity default_rough hu) := by
    apply tsum_congr
    intro k
    simp only [densitySpectralTerm, smoothGibbsDensity_fourier]
    rfl
  rw [hQ, smoothGibbsDensity_entropy] at he
  have hcoef : 1/(4*(1/(4*coupling))) = coupling := by field_simp
  have hn : functional (1/(4*coupling)) u ≤ 0 := by
    rw [maximizer_functional_eq_density (by norm_num) default_rough hA hu hmax, hcoef]
    exact sub_nonpos.mpr he
  exact (hmax v hv).trans hn

lemma l2_endpoint (r : ProbabilityDensity 11) (hr : MemLp r.value 2 (torusMeasure 11)) :
    Summable (densitySpectralTerm r) ∧ coupling * fourierEnergy r ≤ densityEntropy r.value := by
  refine ⟨(PhysicalGreenL2.physicalGreenEnergy_eq_spectral (by norm_num) r hr).1, ?_⟩
  have hA : 0 < 1/(4*coupling) := by have := coupling_pos; positivity
  have h := SubcriticalPrimalDual.density_le_dual (by norm_num) default_rough hA r hr
  have hp := primal_nonpos (SubcriticalPrimalDual.dualPotential (1/(4*coupling)) r hr)
    (SubcriticalPrimalDual.dualPotential_admissible (by norm_num) (1/(4*coupling)) r hr)
  have hcoef : 1/(4*(1/(4*coupling))) = coupling := by field_simp
  unfold SubcriticalPrimalDual.densityFunctional at h
  rw [hcoef] at h
  linarith

theorem full_endpoint : EndpointRigidity.CoefficientEndpoint 11 coupling := by
  intro r hr
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let rs := fun n => HeatDensityApproximation.heatDensity r (ht n)
  apply EndpointClosure.spectral_bound_of_fourier_limits_entropy_le coupling coupling_pos rs r
  · intro n
    exact l2_endpoint (rs n)
      ((HeatDensityApproximation.heatValue_continuous r (ht n)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · exact HeatDensityApproximation.heatDensity_fourier_tendsto r t ht
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    exact HeatDensityApproximation.heatDensity_entropy_le r hr (ht n)

lemma mixture_rigidity : EndpointRigidity.PositiveMixtureRigidity 11 coupling := by
  intro r _ _ hmix heq
  obtain ⟨w, N, hw, hm, hSup, hv⟩ := hmix
  have he : (CosineMixtureApproximation.probabilityDensity w N hw hm hSup).value = r.value := hv.symm
  have ht : densitySpectralTerm (CosineMixtureApproximation.probabilityDensity w N hw hm hSup) =
      densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, he]
  have h := countable_mixture_uniform_of_equality w N hw hm hSup
    (by simpa only [fourierEnergy, ht, he] using heq)
  intro x
  rw [hv]
  exact h x

theorem full_rigidity (r : ProbabilityDensity 11) (hr : r.FiniteEntropy)
    (he : coupling * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure 11] (fun _ => 1) :=
  EndpointRigidity.uniform_of_equality (by norm_num) coupling_pos full_endpoint mixture_rigidity r hr he

#print axioms full_endpoint
#print axioms full_rigidity
end Legacy.BecknerOnofri.ElevenMixture
