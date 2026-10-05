module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Tactic

@[expose] public section

/-! Unit-volume cubic torus and finite Fourier Parseval identity.
No endpoint inequality or kernel identity is asserted in this module. -/

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Legacy.TorusEndpoint

abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
abbrev Frequency (d : ℕ) := Fin d → ℤ

noncomputable def torusMeasure (d : ℕ) : Measure (Torus d) :=
  volume

theorem torusMeasure_explicit (d : ℕ) : torusMeasure d =
    Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := rfl

instance torusMeasure_probability (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

noncomputable def fourierPolynomial {d : ℕ} (s : Finset (Frequency d))
    (a : Frequency d → ℂ) : C(Torus d, ℂ) :=
  ∑ k ∈ s, a k • UnitAddTorus.mFourier k

noncomputable def densityFourier {d : ℕ} (rho : Torus d → ℝ) (k : Frequency d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-k) x * (rho x : ℂ) ∂torusMeasure d

noncomputable def densityEntropy {d : ℕ} (rho : Torus d → ℝ) : ℝ :=
  ∫ x, rho x * Real.log (rho x) ∂torusMeasure d

/-- A real density of unit mass; finite entropy is a separate condition. -/
structure ProbabilityDensity (d : ℕ) where
  value : Torus d → ℝ
  nonneg : ∀ᵐ x ∂torusMeasure d, 0 ≤ value x
  integrable : Integrable value (torusMeasure d)
  mass : (∫ x, value x ∂torusMeasure d) = 1

def ProbabilityDensity.FiniteEntropy {d : ℕ} (rho : ProbabilityDensity d) : Prop :=
  Integrable (fun x => rho.value x * Real.log (rho.value x)) (torusMeasure d)

theorem densityFourier_zero {d : ℕ} (rho : ProbabilityDensity d) :
    densityFourier rho.value 0 = 1 := by
  simp only [densityFourier, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_mul]
  calc
    _ = Complex.ofReal (∫ x, rho.value x ∂torusMeasure d) := integral_complex_ofReal
    _ = 1 := by rw [rho.mass]; norm_num

theorem finite_parseval_complex {d : ℕ} (s : Finset (Frequency d)) (a : Frequency d → ℂ) :
    (∫ x, fourierPolynomial s a x * conj (fourierPolynomial s a x) ∂torusMeasure d) =
      ∑ k ∈ s, conj (a k) * a k := by
  have h := (UnitAddTorus.orthonormal_mFourier (d := Fin d)).inner_sum a a s
  simpa only [UnitAddTorus.mFourierLp, ← map_smul, ← map_sum,
    ContinuousMap.inner_toLp, fourierPolynomial, torusMeasure] using h

theorem finite_parseval {d : ℕ} (s : Finset (Frequency d)) (a : Frequency d → ℂ) :
    (∫ x, ‖fourierPolynomial s a x‖ ^ 2 ∂torusMeasure d) = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (finite_parseval_complex s a)
  have hi : Integrable (fun x => fourierPolynomial s a x *
      conj (fourierPolynomial s a x)) (torusMeasure d) := by
    exact ((fourierPolynomial s a).continuous.mul
      ((fourierPolynomial s a).continuous.star)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [← integral_re hi] at h
  change (∫ x, (fourierPolynomial s a x * conj (fourierPolynomial s a x)).re
      ∂torusMeasure d) = (∑ k ∈ s, conj (a k) * a k).re at h
  have hl (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hr (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simpa only [Complex.re_sum, hl, hr] using h

end Legacy.TorusEndpoint
