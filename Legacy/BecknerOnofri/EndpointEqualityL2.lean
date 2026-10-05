module

public import Legacy.BecknerOnofri.EndpointEqualitySelection
public import Legacy.BecknerOnofri.StrictPositiveProfile
public import Legacy.BecknerOnofri.EndpointPotential

@[expose] public section

/-! Endpoint rigidity for every actual L2 density in dimensions two through
ten. Compact selection preserves entropy and produces an actual absolutely
monotone profile, where the strict scalar gap forces uniformity. -/
noncomputable section
namespace Legacy.BecknerOnofri.EndpointEqualityL2
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open SmoothFourier WienerFourier SteinerSelection FiniteDifferences
open EndpointMaximizerLevel EndpointEqualitySelection

theorem steiner_density_uniform {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab) (hA : 0 < A)
    (hCoeff : 1/(4*A) = endpointConstant d) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re)) :
    ∀ x, smoothGibbsValue u x = 1 := by
  have hd : 0 < d := by omega
  have hs := maximizer_fourier_summable hd hR hA hu hmax
  have hpos := steiner_maximizer_mixedPartials hd hR hA hu hmax hStR hStU
  have hnon : BernsteinPositiveCoefficients.NonnegativeMixedPartials (EulerUnitProfiles.density u) :=
    NormalizedExponentialPartials.normalized_exp_nonnegative_mixed (partition_pos hR hu)
      (EulerUnitProfiles.potential_contDiffOn hd hR hA hu hmax hStU)
      (fun _ hx => EulerUnitProfiles.density_eq_exp hd hR hA hu hmax hStU hStR hx) hpos
  have hQ : fourierEnergy (smoothGibbsDensity hR hu hs) = fourierEnergy (gibbsDensity hR hu) := by
    apply tsum_congr
    intro k
    simp only [densitySpectralTerm, smoothGibbsDensity_fourier]
    rfl
  have hz := maximizer_functional_zero hd (endpoint_through_ten d (by omega) hd10)
    hR hA hCoeff hu hmax
  rw [maximizer_functional_eq_density hd hR hA hu hmax, hCoeff] at hz
  have he : endpointConstant d * fourierEnergy (smoothGibbsDensity hR hu hs) =
      densityEntropy (smoothGibbsDensity hR hu hs).value := by
    rw [hQ, smoothGibbsDensity_entropy]
    exact sub_eq_zero.mp hz
  exact StrictMixture.absolutely_monotone_uniform_of_equality hd2 hd10
    (smoothGibbsDensity hR hu hs) (EulerUnitProfiles.density_contDiffOn hd hR hA hu hmax hStR)
    hnon (EulerUnitProfiles.density_representation hd hR hA hu hmax hStR) he

/-- Every L2 endpoint equality density is actually uniform almost everywhere. -/
theorem uniform_of_equality {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (he : endpointConstant d * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure d] (fun _ => 1) := by
  have hd : 0 < d := by omega
  have hEndpoint := endpoint_through_ten d (by omega) hd10
  have hb := EndpointPotential.endpointConstant_pos hd
  have hR := EndpointPotential.rough_of_endpoint hd hEndpoint
  have hA := EndpointPotential.coefficient_pos hd
  have hCoeff : 1/(4*EndpointPotential.coefficient d) = endpointConstant d := by
    unfold EndpointPotential.coefficient
    field_simp
  obtain ⟨u, hu, hmax, hStR, hStU, hEnt⟩ :=
    exists_steiner_equality hd hEndpoint hb hR hA hCoeff r hr he.symm
  have huni := steiner_density_uniform hd2 hd10 hR hA hCoeff hu hmax hStR hStU
  have hzero : densityEntropy (smoothGibbsValue u) = 0 := by
    unfold densityEntropy
    simp only [huni, Real.log_one, mul_zero, integral_zero]
  exact (EntropyVariationalEquality.entropy_eq_zero_iff r
    (PhysicalGreenL2.finiteEntropy_of_memLp r hr)).mp (hEnt.symm.trans hzero)

/-- A nonuniform actual L2 density has a strictly positive endpoint deficit. -/
theorem strict_of_nonuniform {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (hne : ¬r.value =ᵐ[torusMeasure d] (fun _ => 1)) :
    endpointConstant d * fourierEnergy r < densityEntropy r.value := by
  apply lt_of_le_of_ne (endpoint_through_ten d (by omega) hd10 r
    (PhysicalGreenL2.finiteEntropy_of_memLp r hr)).2
  exact fun he => hne (uniform_of_equality hd2 hd10 r hr he)

#print axioms steiner_density_uniform
#print axioms uniform_of_equality
#print axioms strict_of_nonuniform
end Legacy.BecknerOnofri.EndpointEqualityL2
