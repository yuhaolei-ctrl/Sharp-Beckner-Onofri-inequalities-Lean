module

public import Legacy.TorusEndpoint.FourierEntropy
public import Legacy.TorusEndpoint.FiniteCone
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Conditional summability of actual half-cone Fourier energy

Every finite half-cone exponential estimate is an explicit hypothesis.
Summability is proved from the resulting nonnegative finite-sum bounds;
no finite-energy hypothesis or identification with a Green kernel is used.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint

abbrev PositiveFrequency (d : ℕ) :=
  {k : Frequency d // FiniteCone.LexPositive k}

/-- Real densities have the usual conjugate symmetry, for the actual
Haar-integral Fourier coefficients, without a formal-series convention. -/
theorem densityFourier_neg {d : ℕ} (rho : ProbabilityDensity d) (k : Frequency d) :
    densityFourier rho.value (-k) = conj (densityFourier rho.value k) := by
  calc
    densityFourier rho.value (-k) =
        ∫ x, UnitAddTorus.mFourier k x * (rho.value x : ℂ) ∂torusMeasure d := by
      simp only [densityFourier, neg_neg]
    _ = ∫ x, conj (UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ))
        ∂torusMeasure d := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      simp [UnitAddTorus.mFourier_neg]
    _ = conj (densityFourier rho.value k) := integral_conj

theorem densityFourier_norm_neg {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    ‖densityFourier rho.value (-k)‖ = ‖densityFourier rho.value k‖ := by
  rw [densityFourier_neg, Complex.norm_conj]

/-- Every finite set in the subtype half-cone has the actual spectral bound. -/
theorem finite_positive_spectral_sum_le {d : ℕ} (rho : ProbabilityDensity d)
    (h_entropy : rho.FiniteEntropy) (a : Frequency d → ℝ)
    (h_a : ∀ k, FiniteCone.LexPositive k → 0 < a k)
    (h_exp : ∀ s : Finset (Frequency d),
      (∀ k ∈ s, FiniteCone.LexPositive k) → ∀ c : Frequency d → ℂ,
      Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
        ∑ k ∈ s, a k * ‖c k‖^2)
    (s : Finset (PositiveFrequency d)) :
    (∑ k ∈ s, ‖densityFourier rho.value k.val‖^2 / a k.val) ≤
      densityEntropy rho.value := by
  classical
  let S : Finset (Frequency d) := s.map (Function.Embedding.subtype _)
  have hS : ∀ k ∈ S, FiniteCone.LexPositive k := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨j, hj, hjk⟩
    subst k
    exact j.property
  have h := entropy_ge_finite_fourier_energy rho h_entropy S a
    (fun k hk => h_a k (hS k hk)) (h_exp S hS)
  simpa only [S, Finset.sum_map, Function.Embedding.subtype_apply] using h

/-- The finite test estimates imply both summability and the infinite
half-cone spectral entropy bound. The exponential premise remains explicit. -/
theorem positive_spectral_summable_and_tsum_le {d : ℕ} (rho : ProbabilityDensity d)
    (h_entropy : rho.FiniteEntropy) (a : Frequency d → ℝ)
    (h_a : ∀ k, FiniteCone.LexPositive k → 0 < a k)
    (h_exp : ∀ s : Finset (Frequency d),
      (∀ k ∈ s, FiniteCone.LexPositive k) → ∀ c : Frequency d → ℂ,
      Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
        ∑ k ∈ s, a k * ‖c k‖^2) :
    Summable (fun k : PositiveFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val) ∧
    (∑' k : PositiveFrequency d, ‖densityFourier rho.value k.val‖^2 / a k.val) ≤
      densityEntropy rho.value := by
  have h_nonneg : 0 ≤ (fun k : PositiveFrequency d =>
      ‖densityFourier rho.value k.val‖^2 / a k.val) := by
    intro k
    exact div_nonneg (sq_nonneg _) (h_a k.val k.property).le
  have h_finite : ∀ s : Finset (PositiveFrequency d),
      (∑ k ∈ s, ‖densityFourier rho.value k.val‖^2 / a k.val) ≤
        densityEntropy rho.value :=
    finite_positive_spectral_sum_le rho h_entropy a h_a h_exp
  exact ⟨summable_of_sum_le h_nonneg h_finite,
    Real.tsum_le_of_sum_le h_nonneg h_finite⟩

end Legacy.TorusEndpoint
