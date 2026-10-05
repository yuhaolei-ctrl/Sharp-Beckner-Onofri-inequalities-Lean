module

public import Legacy.BecknerOnofri.BernsteinPositiveCoefficients
public import Legacy.BecknerOnofri.PositivePolynomialEndpoint

@[expose] public section

/-! The genuine density endpoint for smooth absolutely monotone cosine profiles.
The profile representation by a positive series is a proved intermediate result.
Selecting such a profile from an arbitrary counterexample remains separate.
-/
namespace Legacy.BecknerOnofri.AbsolutelyMonotoneEndpoint
open Legacy.TorusEndpoint BernsteinPositiveCoefficients
open scoped ContDiff

theorem endpoint {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {f : FiniteDifferences.Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d))
    (hpos : NonnegativeMixedPartials f)
    (hr : ∀ x, r.value x = restriction f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧
      endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  apply PositivePolynomialEndpoint.positive_cube_series_endpoint hd3 hd10 r
    (taylorCoefficient f) (taylorCoefficient_nonneg hpos) (positiveTaylor_mass hf hpos).summable
  intro x
  rw [hr]
  exact (positiveTaylor_hasSum hf hpos _).tsum_eq.symm

#print axioms endpoint
end Legacy.BecknerOnofri.AbsolutelyMonotoneEndpoint
