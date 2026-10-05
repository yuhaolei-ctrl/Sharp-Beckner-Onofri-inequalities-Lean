import Legacy.TorusEndpoint.FiniteAtomCriterion
import Legacy.TorusEndpoint.FullSpectral

/-!
# From actual finite-atom coefficient caps to spectral entropy

The only coefficient hypothesis below is an explicit upper bound on the
complete finite word sums of `FiniteAtomCoefficients`. All support and
Fourier-evaluation bridges are proved from actual finite algebra elements.
The atom weight `a` appears as `1 / a` in the exponential quadratic cost,
and as the multiplier `a` in the final spectral energy. No dimension-specific
coefficient cap or physical Green-kernel identification is asserted here.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint

/-- The actual algebra element whose coefficient is `c k` on `s`, and zero
off `s`. Zero coefficients in the supplied finite set are allowed. -/
noncomputable def finiteFourierAlgebra {d : ℕ}
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) :
    AddMonoidAlgebra ℂ (Frequency d) := by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset s
    (fun k => if k ∈ s then c k else 0) (by
      intro k hk
      by_contra hn
      exact hk (if_neg hn)))

theorem finiteFourierAlgebra_coeff {d : ℕ}
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) (k : Frequency d) :
    (finiteFourierAlgebra s c).coeff k = if k ∈ s then c k else 0 := by
  classical
  rfl

theorem finiteFourierAlgebra_support_subset {d : ℕ}
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) :
    (finiteFourierAlgebra s c).coeff.support ⊆ s := by
  classical
  intro k hk
  by_contra hn
  have hne := Finsupp.mem_support_iff.mp hk
  apply hne
  rw [finiteFourierAlgebra_coeff, if_neg hn]

theorem finiteFourierAlgebra_eval {d : ℕ}
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) :
    polynomialFourierEval d (finiteFourierAlgebra s c) = fourierPolynomial s c := by
  classical
  rw [polynomialFourierEval_eq]
  unfold fourierPolynomial
  calc
    _ = ∑ k ∈ s, (finiteFourierAlgebra s c).coeff k • UnitAddTorus.mFourier k := by
      apply Finset.sum_subset (finiteFourierAlgebra_support_subset s c)
      intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk]
      exact zero_smul ℂ (UnitAddTorus.mFourier k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [finiteFourierAlgebra_coeff, if_pos hk]

theorem finiteFourierAlgebra_weightedL2Sq {d : ℕ}
    (s : Finset (Frequency d)) (c : Frequency d → ℂ) (a : Frequency d → ℝ) :
    polynomialWeightedL2Sq (finiteFourierAlgebra s c) a =
      ∑ k ∈ s, ‖c k‖ ^ 2 / a k := by
  classical
  rw [polynomialWeightedL2Sq_eq_sum _ _ s (finiteFourierAlgebra_support_subset s c)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteFourierAlgebra_coeff, if_pos hk]

/-- Explicit global family of finite-atom coefficient caps. The separator
is any integer functional positive on the selected finite alphabet. Its
existence for each finite positive alphabet is already proved in `FiniteCone`.
Only nonzero generated outputs need a bound. -/
def GlobalFiniteAtomCap {d : ℕ} (a : Frequency d → ℝ) : Prop :=
  ∀ atoms : List (Frequency d),
    (∀ k ∈ atoms, FiniteCone.LexPositive k) →
    ∀ w : Frequency d, (∀ k ∈ atoms, 0 < FiniteCone.eval w k) →
    ∀ k : Frequency d, k ≠ 0 → FiniteAtomCriterion.Generated atoms k →
      FiniteAtomCoefficients.coefficient atoms w a 1 k ≤ 1

/-- The explicit finite-atom cap supplies every finite positive-cone Fourier
log-exponential bound, including arbitrary zero coefficients on its index set. -/
theorem finite_fourier_log_integral_exp_le_of_global_cap {d : ℕ}
    (a : Frequency d → ℝ)
    (ha : ∀ k : Frequency d, FiniteCone.LexPositive k → 0 < a k)
    (hcap : GlobalFiniteAtomCap a)
    (s : Finset (Frequency d)) (hs : ∀ k ∈ s, FiniteCone.LexPositive k)
    (c : Frequency d → ℂ) :
    Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
      ∑ k ∈ s, ‖c k‖ ^ 2 / a k := by
  classical
  have hpos : ∀ k ∈ s.toList, FiniteCone.LexPositive k := by
    intro k hk
    exact hs k (Finset.mem_toList.mp hk)
  obtain ⟨w, hw⟩ := FiniteCone.exists_positive_weights d s.toList hpos
  have hF : ∀ k ∈ (finiteFourierAlgebra s c).coeff.support, k ∈ s.toList := by
    intro k hk
    exact Finset.mem_toList.mpr (finiteFourierAlgebra_support_subset s c hk)
  have h := FiniteAtomCriterion.finite_atom_log_integral_exp_le
    s.toList w a (finiteFourierAlgebra s c) hw
    (fun k hk => ha k (hpos k hk)) hF (hcap s.toList hpos w hw)
  rw [finiteFourierAlgebra_eval, finiteFourierAlgebra_weightedL2Sq] at h
  exact h

/-- In the existing entropy interface the denominator weight is `1 / a`.
This theorem spells out the reciprocal convention without suppressing it. -/
theorem finite_fourier_log_integral_exp_le_reciprocal_of_global_cap {d : ℕ}
    (a : Frequency d → ℝ)
    (ha : ∀ k : Frequency d, FiniteCone.LexPositive k → 0 < a k)
    (hcap : GlobalFiniteAtomCap a)
    (s : Finset (Frequency d)) (hs : ∀ k ∈ s, FiniteCone.LexPositive k)
    (c : Frequency d → ℂ) :
    Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
      ∑ k ∈ s, (1 / a k) * ‖c k‖ ^ 2 := by
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using
    finite_fourier_log_integral_exp_le_of_global_cap a ha hcap s hs c

/-- Positive even atom weights satisfying the explicit global finite cap give
summability and the entropy bound for the actual nonzero full Fourier spectrum.
There is no prior finite-energy assumption and no residual exponential premise. -/
theorem full_spectral_entropy_of_global_coefficient_cap {d : ℕ}
    (rho : ProbabilityDensity d) (h_entropy : rho.FiniteEntropy)
    (a : Frequency d → ℝ)
    (ha : ∀ k : Frequency d, k ≠ 0 → 0 < a k)
    (h_even : ∀ k : Frequency d, k ≠ 0 → a (-k) = a k)
    (hcap : GlobalFiniteAtomCap a) :
    Summable (fun k : NonzeroFrequency d =>
      a k.val * ‖densityFourier rho.value k.val‖ ^ 2) ∧
    (∑' k : NonzeroFrequency d, a k.val * ‖densityFourier rho.value k.val‖ ^ 2) ≤
      2 * densityEntropy rho.value := by
  have hpos : ∀ k : Frequency d, FiniteCone.LexPositive k → 0 < a k := by
    intro k hk
    exact ha k (FiniteCone.positive_ne_zero hk)
  have h := full_spectral_summable_and_entropy_bound rho h_entropy (fun k => 1 / a k)
    (fun k hk => one_div_pos.mpr (ha k hk))
    (fun k hk => by rw [h_even k hk])
    (fun s hs c => finite_fourier_log_integral_exp_le_reciprocal_of_global_cap
      a hpos hcap s hs c)
  simpa only [one_div, div_eq_mul_inv, inv_inv, one_mul, mul_one, mul_comm] using h

end Legacy.TorusEndpoint
