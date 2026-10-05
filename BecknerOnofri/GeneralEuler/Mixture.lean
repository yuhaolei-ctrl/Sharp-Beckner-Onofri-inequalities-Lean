import BecknerOnofri.GeneralEuler.CriticalComparison
import BecknerOnofri.GeneralEuler.HigherPartialSigns
import BecknerOnofri.GenericCosineRepresentation

/-! The Jacobi strict-comparison and positive-Taylor argument for general
smooth monotone Euler pairs, without variational optimality. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Legacy.BecknerOnofri
open scoped ContDiff
namespace BecknerOnofri.GeneralEuler
open TorusSobolev SubcriticalAttainment SubcriticalEuler WienerFourier SmoothFourier
open SteinerSelection FiniteDifferences AngularMixedTerms JacobiTensorSpectrum

theorem rough {d : ℕ} (hd : 0 < d) :
    RoughExponentialBound d (endpointConstant d/2)
      (GreenRoughEnergy.partition d (endpointConstant d/2)) := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact GenericAttainment.rough_bound hd (by positivity) (by linarith)

theorem mixedPartials {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {u : TorusL2 d} (hu : Admissible u) (hE : Regularity.Data A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re))
    (is : List (Fin d)) (his : is ≠ []) :
    ∀ y ∈ closedCube d, 0 ≤ mixedPartial is (UnitProfiles.potential u) y :=
  HigherPartialSigns.mixedPartials_nonnegative hd (rough hd) hA hu hE hStR hStU
    (fun js hjs => CriticalComparison.criticalInverse_positive (countIndex js)
      (SpectralIntertwining.countIndex_ne_zero js hjs))
    (CriticalComparison.higher_norm_lt_one hd (rough hd) hA hu hE hStR hStU) is his

theorem mixture {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {u : TorusL2 d} (hu : Admissible u) (hE : Regularity.Data A u)
    (hStR : Steiner (smoothGibbsValue u))
    (hStU : Steiner (fun x => (representative u x).re)) :
    GenericCosineRepresentation.HasPositiveCosineMixture (smoothGibbsValue u) := by
  have hs := Regularity.fourier_summable hd (rough hd) hA hu hE
  have hnon : BernsteinPositiveCoefficients.NonnegativeMixedPartials (UnitProfiles.density u) :=
    NormalizedExponentialPartials.normalized_exp_nonnegative_mixed (partition_pos (rough hd) hu)
      (UnitProfiles.potential_contDiffOn hd (rough hd) hA hu hE hStU)
      (fun _ hx => UnitProfiles.density_eq_exp hd (rough hd) hA hu hE hStU hStR hx)
      (mixedPartials hd hA hu hE hStR hStU)
  exact GenericCosineRepresentation.positive_profile_mixture hd (smoothGibbsDensity (rough hd) hu hs)
    (UnitProfiles.density_contDiffOn hd (rough hd) hA hu hE hStR) hnon
    (UnitProfiles.density_representation hd (rough hd) hA hu hE hStR)

#print axioms mixedPartials
#print axioms mixture
end BecknerOnofri.GeneralEuler
