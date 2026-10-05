import Legacy.BecknerOnofri.EulerUnitProfiles
import Legacy.BecknerOnofri.NormalizedExponentialPartials
import Legacy.BecknerOnofri.SubcriticalEulerEnergy
import Legacy.BecknerOnofri.HeatEndpointReduction
import Legacy.BecknerOnofri.LowDimensionMixtureEndpoint

/-! The endpoint consequence of the remaining higher-Jacobi derivative sign
statement. Selection, smoothness, profile identification, Bell expansion,
positive series, scalar bounds, and the passage to finite entropy are proved.
The higher-derivative sign is an explicit premise here. -/
noncomputable section
namespace Legacy.BecknerOnofri.SteinerEndpointReduction
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open SmoothFourier WienerFourier SteinerSelection FiniteDifferences
open scoped ContDiff

theorem energy_nonneg {d : ℕ} (r : ProbabilityDensity d) : 0 ≤ fourierEnergy r := by
  apply tsum_nonneg
  intro k
  unfold densitySpectralTerm
  exact div_nonneg (sq_nonneg _) (pow_nonneg (frequencyRadius_nonneg _) _)

theorem maximizer_functional_nonpos_of_partials {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    (hA : 1/(4*endpointConstant d) < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re))
    (hpos : ∀ is : List (Fin d), is ≠ [] → ∀ x ∈ closedCube d,
      0 ≤ mixedPartial is (EulerUnitProfiles.potential u) x) : functional A u ≤ 0 := by
  have hd : 0 < d := by omega
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hs := maximizer_fourier_summable hd hR hA0 hu hmax
  have hnon : BernsteinPositiveCoefficients.NonnegativeMixedPartials (EulerUnitProfiles.density u) :=
    NormalizedExponentialPartials.normalized_exp_nonnegative_mixed (partition_pos hR hu)
      (EulerUnitProfiles.potential_contDiffOn hd hR hA0 hu hmax hStU)
      (fun _ hx => EulerUnitProfiles.density_eq_exp hd hR hA0 hu hmax hStU hStR hx) hpos
  have he := (LowDimensionMixtureEndpoint.absolutely_monotone_endpoint hd2 hd10
    (smoothGibbsDensity hR hu hs) (EulerUnitProfiles.density_contDiffOn hd hR hA0 hu hmax hStR)
    hnon (EulerUnitProfiles.density_representation hd hR hA0 hu hmax hStR)).2
  have hQ : fourierEnergy (smoothGibbsDensity hR hu hs) = fourierEnergy (gibbsDensity hR hu) := by
    apply tsum_congr
    intro k
    simp only [densitySpectralTerm, smoothGibbsDensity_fourier]
    rfl
  rw [hQ, smoothGibbsDensity_entropy] at he
  have hc : 1/(4*A) < endpointConstant d := by
    have h := (div_lt_iff₀ (by positivity : 0 < 4*endpointConstant d)).mp hA
    apply (div_lt_iff₀ (by positivity : 0 < 4*A)).mpr
    nlinarith
  rw [maximizer_functional_eq_density hd hR hA0 hu hmax]
  exact sub_nonpos.mpr ((mul_le_mul_of_nonneg_right hc.le (energy_nonneg _)).trans he)

/-- This is the precise remaining sign statement: orders zero and one have
already been proved, and the potential itself need not be nonnegative. -/
def HigherSteinerEulerPartials (d : ℕ) : Prop :=
  ∀ (A : ℝ), 1/(4*endpointConstant d) < A → ∀ u : TorusL2 d, Admissible u →
    (∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) →
    Steiner (smoothGibbsValue u) → Steiner (fun x => (representative u x).re) →
    ∀ is : List (Fin d), 1 < is.length → ∀ x ∈ closedCube d,
      0 ≤ mixedPartial is (EulerUnitProfiles.potential u) x

theorem continuous_endpoint_of_higher_partials {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (hJacobi : HigherSteinerEulerPartials d) (r : ProbabilityDensity d)
    (hr : Continuous r.value) :
    Summable (densitySpectralTerm r) ∧ endpointConstant d*fourierEnergy r ≤ densityEntropy r.value := by
  have hd : 0 < d := by omega
  refine ⟨(PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd r
    (hr.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1, ?_⟩
  by_contra hfail
  obtain ⟨A, hA, u, hu, hpos, hmax, hStR, hStU⟩ :=
    exists_positive_steiner_maximizer hd r hr (lt_of_not_ge hfail)
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hR := roughExponentialBound hd (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  have hnon : functional A u ≤ 0 := maximizer_functional_nonpos_of_partials hd2 hd10 hR hA
    hu hmax hStR hStU (by
      intro is his x hx
      by_cases hlen : 1 < is.length
      · exact hJacobi A hA u hu hmax hStR hStU is hlen x hx
      · cases is with
        | nil => exact (his rfl).elim
        | cons i js =>
          have hj : js = [] := by
            cases js with
            | nil => rfl
            | cons j ks => simp only [List.length_cons] at hlen; omega
          subst js
          exact EulerUnitProfiles.potential_first_nonneg hd hR hA0 hu hmax hStU i hx)
  exact (not_le_of_gt hpos) hnon

theorem endpoint_of_higher_partials {d : ℕ} (hd2 : 2 ≤ d) (hd10 : d ≤ 10)
    (hJacobi : HigherSteinerEulerPartials d) : Endpoint d :=
  HeatEndpointReduction.endpoint_of_continuous_pos (by omega)
    (fun r hr _ => continuous_endpoint_of_higher_partials hd2 hd10 hJacobi r hr)

theorem throughTen_of_higher_partials
    (hJacobi : ∀ d, 2 ≤ d → d ≤ 10 → HigherSteinerEulerPartials d) : EndpointThroughTen := by
  intro d hd hd10
  by_cases he : d = 1
  · subst d; exact endpoint_one
  · exact endpoint_of_higher_partials (by omega) hd10 (hJacobi d (by omega) hd10)

#print axioms maximizer_functional_nonpos_of_partials
#print axioms throughTen_of_higher_partials
end Legacy.BecknerOnofri.SteinerEndpointReduction
