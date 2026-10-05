module

public import Legacy.TorusEndpoint.TorusFourier
public import Legacy.TorusEndpoint.FiniteFeatureEntropy

@[expose] public section

/-!
# Actual finite Fourier moments and entropy

The theorem at the end concerns the actual Haar integrals in TorusFourier.
Its sharp logarithmic exponential upper bound remains an explicit
hypothesis; this module does not assert the coefficient criterion.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint

theorem fourier_character_norm_le_one {d : ℕ} (k : Frequency d) (x : Torus d) :
    ‖UnitAddTorus.mFourier k x‖ ≤ 1 := by
  calc
    ‖UnitAddTorus.mFourier k x‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
      (UnitAddTorus.mFourier k).norm_coe_le_norm x
    _ = 1 := UnitAddTorus.mFourier_norm

theorem densityFourier_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    Integrable (fun x => UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ))
      (torusMeasure d) := by
  exact rho.integrable.ofReal.bdd_mul
    (UnitAddTorus.mFourier (-k)).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (fourier_character_norm_le_one (-k)))

theorem densityFourier_re_moment {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    (∫ x, rho.value x * (UnitAddTorus.mFourier (-k) x).re ∂torusMeasure d) =
      (densityFourier rho.value k).re := by
  have h := integral_re (densityFourier_integrable rho k)
  change (∫ x, (UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ)).re
      ∂torusMeasure d) = (densityFourier rho.value k).re at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, mul_comm] using h

theorem densityFourier_im_moment {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    (∫ x, rho.value x * (UnitAddTorus.mFourier (-k) x).im ∂torusMeasure d) =
      (densityFourier rho.value k).im := by
  have h := integral_im (densityFourier_integrable rho k)
  change (∫ x, (UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ)).im
      ∂torusMeasure d) = (densityFourier rho.value k).im at h
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    zero_add, add_zero, mul_comm] using h

/-- The real and imaginary parts of the negative-frequency character.
This convention makes their density moments exactly re/im of rho-hat(k). -/
noncomputable def fourierRealFeature {d : ℕ} (p : Frequency d × Bool)
    (x : Torus d) : ℝ :=
  if p.2 then (UnitAddTorus.mFourier (-p.1) x).im
  else (UnitAddTorus.mFourier (-p.1) x).re

theorem fourierRealFeature_measurable {d : ℕ} (p : Frequency d × Bool) :
    Measurable (fourierRealFeature p) := by
  rcases p with ⟨k, b⟩
  cases b
  · exact (Complex.continuous_re.comp (UnitAddTorus.mFourier (-k)).continuous).measurable
  · exact (Complex.continuous_im.comp (UnitAddTorus.mFourier (-k)).continuous).measurable

theorem fourierRealFeature_bound {d : ℕ} (p : Frequency d × Bool)
    (x : Torus d) : ‖fourierRealFeature p x‖ ≤ 1 := by
  rcases p with ⟨k, b⟩
  cases b
  · exact (Complex.abs_re_le_norm _).trans (fourier_character_norm_le_one (-k) x)
  · exact (Complex.abs_im_le_norm _).trans (fourier_character_norm_le_one (-k) x)

theorem fourier_real_test_identity {d : ℕ} (s : Finset (Frequency d))
    (t : Frequency d × Bool → ℝ) (x : Torus d) :
    (∑ p ∈ s.product Finset.univ, 2 * t p * fourierRealFeature p x) =
      2 * (fourierPolynomial s (fun k => (⟨t (k, false), t (k, true)⟩ : ℂ)) x).re := by
  classical
  simp only [Finset.product_eq_sprod, Finset.sum_product, Fintype.sum_bool, fourierPolynomial,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, Complex.re_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourierRealFeature, Bool.false_eq_true, if_false, if_true,
    UnitAddTorus.mFourier_neg, Complex.conj_re, Complex.conj_im, Complex.mul_re]
  ring

/-- A genuine finite spectral entropy bound, conditional only on the
displayed exponential-integral estimate and finite entropy. -/
theorem entropy_ge_finite_fourier_energy {d : ℕ} (rho : ProbabilityDensity d)
    (h_entropy : rho.FiniteEntropy) (s : Finset (Frequency d))
    (a : Frequency d → ℝ) (h_a : ∀ k ∈ s, 0 < a k)
    (h_exp : ∀ c : Frequency d → ℂ,
      Real.log (∫ x, Real.exp (2 * (fourierPolynomial s c x).re) ∂torusMeasure d) ≤
        ∑ k ∈ s, a k * ‖c k‖^2) :
    (∑ k ∈ s, ‖densityFourier rho.value k‖^2 / a k) ≤ densityEntropy rho.value := by
  classical
  have h := entropy_ge_finite_feature_energy (μ := torusMeasure d)
    (s.product Finset.univ) fourierRealFeature (fun p => a p.1) (fun _ => 1)
    rho.nonneg rho.mass rho.integrable h_entropy
    (fun p _ => fourierRealFeature_measurable p)
    (fun p _ x => fourierRealFeature_bound p x)
    (fun p hp => h_a p.1 (Finset.mem_product.mp hp).1) ?_
  · change _ ≤ ∫ x, rho.value x * Real.log (rho.value x) ∂torusMeasure d
    have h_sum :
        (∑ p ∈ s.product Finset.univ,
          (∫ x, rho.value x * fourierRealFeature p x ∂torusMeasure d)^2 / a p.1) =
          ∑ k ∈ s, ‖densityFourier rho.value k‖^2 / a k := by
      simp only [Finset.product_eq_sprod, Finset.sum_product, Fintype.sum_bool,
        fourierRealFeature, Bool.false_eq_true, if_false, if_true,
        densityFourier_re_moment, densityFourier_im_moment]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← add_div, Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [h_sum] at h
    exact h
  · intro t
    have he := h_exp (fun k => (⟨t (k, false), t (k, true)⟩ : ℂ))
    simp_rw [fourier_real_test_identity]
    convert he using 1
    simp only [Finset.product_eq_sprod, Finset.sum_product, Fintype.sum_bool,
      Complex.sq_norm, Complex.normSq_apply]
    apply Finset.sum_congr rfl
    intro k hk
    ring

end Legacy.TorusEndpoint
