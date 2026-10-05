module

public import Legacy.BecknerOnofri.CountableMixtureEndpoint
public import Legacy.BecknerOnofri.PositivePolynomialLimit
public import Mathlib.Basic.Denumerable

@[expose] public section

/-! Connect actual multivariate positive polynomial limits with the density
endpoint. The polynomial/derivative construction for selected Euler densities
remains a separate obligation. -/

noncomputable section
open Legacy.TorusEndpoint Filter
open scoped Topology

namespace Legacy.BecknerOnofri.PositivePolynomialEndpoint
open PositivePolynomialLimit

theorem positive_cube_series_endpoint {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) (c : Index d → ℝ) (hc : ∀ a, 0 ≤ c a) (hs : Summable c)
    (hr : ∀ x, r.value x = ∑' a, c a * monomialValue a (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  letI : Countable (Index d) :=
    (Finsupp.equivFunOnFinite : Index d ≃ (Fin d → ℕ)).injective.countable
  let e : ℕ ≃ Index d := Classical.choice (inferInstance : Nonempty (ℕ ≃ Index d))
  apply CountableMixtureEndpoint.positive_monomial_series_endpoint hd3 hd10 r
    (fun n => c (e n)) (fun n i => (e n) i) (fun n => hc (e n)) (e.summable_iff.mpr hs)
  intro x
  rw [hr]
  exact (e.tsum_eq (fun a => c a * monomialValue a (PositiveCosineRepresentation.cube x))).symm

theorem positive_polynomial_limit_endpoint {d : ℕ} (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (r : ProbabilityDensity d) {P : ℕ → MvPolynomial (Fin d) ℝ}
    (hP : ∀ m a, 0 ≤ (P m).coeff a) {M : ℝ}
    (hmass : ∀ m, MvPolynomial.eval (fun _ => (1 : ℝ)) (P m) = M)
    {c : Index d → ℝ} (hlim : ∀ a, Tendsto (fun m => (P m).coeff a) atTop (𝓝 (c a)))
    {f : Cube d → ℝ} (hfc : Continuous f)
    (hf : ∀ y, Tendsto (fun m => MvPolynomial.eval (fun i => (y i : ℝ)) (P m)) atTop (𝓝 (f y)))
    (hr : ∀ x, r.value x = f (PositiveCosineRepresentation.cube x)) :
    Summable (densitySpectralTerm r) ∧ endpointConstant d * fourierEnergy r ≤ densityEntropy r.value := by
  apply positive_cube_series_endpoint hd3 hd10 r c (limit_coefficient_nonneg hP hlim)
    (limit_coefficient_summable hP hmass hlim)
  intro x
  rw [hr]
  exact representation hP hmass hlim hfc hf _

#print axioms positive_cube_series_endpoint
#print axioms positive_polynomial_limit_endpoint
end Legacy.BecknerOnofri.PositivePolynomialEndpoint
