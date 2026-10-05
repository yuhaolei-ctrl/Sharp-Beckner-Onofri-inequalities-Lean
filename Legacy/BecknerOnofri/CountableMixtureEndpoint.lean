import Legacy.BecknerOnofri.FiniteMixtureEndpoint
import Legacy.BecknerOnofri.CosineMixtureApproximation
import Legacy.BecknerOnofri.PositiveCosineRepresentation

/-! The endpoint for countable cosine mixtures with a summable uniform
majorant, and for normalized densities given by summable positive cosine
monomial series. There is no strict positivity assumption on the limit. -/

noncomputable section
open MeasureTheory Legacy.TorusEndpoint

namespace Legacy.BecknerOnofri.CountableMixtureEndpoint
open CosineMixtureApproximation

theorem countable_mixture_endpoint {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    Summable (densitySpectralTerm (probabilityDensity w N hw hm hSup)) ∧
      endpointConstant d * fourierEnergy (probabilityDensity w N hw hm hSup) ≤
        densityEntropy (probabilityDensity w N hw hm hSup).value := by
  apply EndpointClosure.endpoint_of_L1_entropy_limit (by omega : 0 < d)
    (approximatingDensity w N hw hm) (probabilityDensity w N hw hm hSup)
    _ (density_L1_tendsto w N hw hm hSup) (density_entropy_tendsto w N hw hm hSup)
  intro m
  exact FiniteMixtureEndpoint.finite_mixture_endpoint hd3 hd10
    (Finset.range (m+1)) (finiteWeight w m) (finiteIndex N m)
    (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)
    (approximatingDensity_pos w N hw hm m)

theorem positive_monomial_series_endpoint {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (heq : ∀ x, r.value x = ∑' n, c n * PositiveCosineRepresentation.monomial (N n) x) :
    Summable (densitySpectralTerm r) ∧
      endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  let w := PositiveCosineRepresentation.weights c N
  have hw := PositiveCosineRepresentation.weights_nonneg c N hc
  have hm := PositiveCosineRepresentation.weights_hasSum_one r c N hc hs heq
  have hSup := PositiveCosineRepresentation.weights_majorant_summable c N hs
  have h := countable_mixture_endpoint hd3 hd10 w N hw hm hSup
  have hv : (probabilityDensity w N hw hm hSup).value = r.value :=
    (PositiveCosineRepresentation.density_eq_countable_mixture r c N heq).symm
  have ht : densitySpectralTerm (probabilityDensity w N hw hm hSup) = densitySpectralTerm r := by
    funext k
    simp only [densitySpectralTerm, hv]
  simpa only [fourierEnergy, ht, hv] using h

#print axioms countable_mixture_endpoint
#print axioms positive_monomial_series_endpoint
end Legacy.BecknerOnofri.CountableMixtureEndpoint
