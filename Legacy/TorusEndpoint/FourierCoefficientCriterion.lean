import Legacy.TorusEndpoint.WeightedPolynomial
import Legacy.TorusEndpoint.TorusFourier
import Legacy.TorusEndpoint.ExponentialLimit
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# A conditional Fourier coefficient criterion

The Fourier evaluation map below is an actual algebra homomorphism, proved
from the torus characters. Weighted polynomial estimates and finite Parseval
then give the binomial integral bounds used by the exponential-limit theorem.
The coefficient-family hypotheses are explicit; no particular family or
dimension-specific coefficient certification is manufactured here.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.TorusEndpoint

/-- The torus characters, with additive frequencies written multiplicatively. -/
noncomputable def torusCharacterHom (d : ℕ) :
    Multiplicative (Frequency d) →* C(Torus d, ℂ) where
  toFun k := UnitAddTorus.mFourier k.toAdd
  map_one' := UnitAddTorus.mFourier_zero
  map_mul' k l := by
    ext x
    exact UnitAddTorus.mFourier_add

/-- Evaluation of actual finitely supported algebra coefficients as a continuous
torus function. Its algebra-homomorphism laws are inherited from `lift`. -/
noncomputable def polynomialFourierEval (d : ℕ) :
    AddMonoidAlgebra ℂ (Frequency d) →ₐ[ℂ] C(Torus d, ℂ) :=
  AddMonoidAlgebra.lift ℂ C(Torus d, ℂ) (Frequency d) (torusCharacterHom d)

theorem polynomialFourierEval_eq {d : ℕ} (F : AddMonoidAlgebra ℂ (Frequency d)) :
    polynomialFourierEval d F = fourierPolynomial F.coeff.support F.coeff := by
  rw [polynomialFourierEval, AddMonoidAlgebra.lift_apply]
  rfl

@[simp] theorem polynomialFourierEval_one (d : ℕ) :
    polynomialFourierEval d 1 = 1 := map_one _

@[simp] theorem polynomialFourierEval_add {d : ℕ}
    (F H : AddMonoidAlgebra ℂ (Frequency d)) :
    polynomialFourierEval d (F + H) = polynomialFourierEval d F + polynomialFourierEval d H :=
  map_add _ _ _

@[simp] theorem polynomialFourierEval_mul {d : ℕ}
    (F H : AddMonoidAlgebra ℂ (Frequency d)) :
    polynomialFourierEval d (F * H) = polynomialFourierEval d F * polynomialFourierEval d H :=
  map_mul _ _ _

@[simp] theorem polynomialFourierEval_pow {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (n : ℕ) :
    polynomialFourierEval d (F ^ n) = polynomialFourierEval d F ^ n := map_pow _ _ _

@[simp] theorem polynomialFourierEval_smul {d : ℕ}
    (c : ℂ) (F : AddMonoidAlgebra ℂ (Frequency d)) :
    polynomialFourierEval d (c • F) = c • polynomialFourierEval d F := map_smul _ _ _

/-- The finite coefficient Parseval theorem now applies to actual algebra elements. -/
theorem polynomialFourierEval_parseval {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) :
    (∫ x, ‖polynomialFourierEval d F x‖ ^ 2 ∂torusMeasure d) =
      ∑ k ∈ F.coeff.support, ‖F.coeff k‖ ^ 2 := by
  rw [polynomialFourierEval_eq]
  exact finite_parseval _ _

theorem polynomialFourierEval_binomial {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (M : ℕ) (x : Torus d) :
    polynomialFourierEval d ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ M) x =
      (1 + polynomialFourierEval d F x / (M : ℂ)) ^ M := by
  simp [div_eq_mul_inv, smul_eq_mul, mul_comm]

/-- A weight bounded above by one yields an integral bound without further
orthogonality assumptions, by the already proved finite Parseval identity. -/
theorem polynomialFourierEval_integral_le_weighted {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (C : Frequency d → ℝ)
    (hpos : ∀ k ∈ F.coeff.support, 0 < C k)
    (hcap : ∀ k ∈ F.coeff.support, C k ≤ 1) :
    (∫ x, ‖polynomialFourierEval d F x‖ ^ 2 ∂torusMeasure d) ≤
      polynomialWeightedL2Sq F C := by
  rw [polynomialFourierEval_parseval]
  exact polynomial_coeff_sq_sum_le_weighted F C hpos hcap

/-- Explicit hypotheses on a candidate coefficient family for one fixed
polynomial. This structure has no constructed instance in this module.
In particular, the final coefficient cap is an essential unproved premise
until a concrete family and its dimension-specific certificate are supplied. -/
structure PolynomialCoefficientConditions {G : Type*} [AddMonoid G] [DecidableEq G]
    (F : AddMonoidAlgebra ℂ G) (a : G → ℝ) (C : ℝ → G → ℝ) : Prop where
  zero_coefficient : F.coeff 0 = 0
  atom_positive : ∀ k ∈ F.coeff.support, 0 < a k
  zero_parameter : C 0 0 = 1
  unit_coefficient : ∀ q : ℝ, 0 < q → C q 0 = 1
  one_atom : ∀ q : ℝ, 0 < q → ∀ k ∈ F.coeff.support, q * a k ≤ C q k
  power_positive : ∀ q : ℝ, 0 < q → ∀ (n : ℕ) k,
    k ∈ ((1 + (q : ℂ) • F) ^ n).coeff.support → 0 < C ((n : ℝ) * q) k
  finite_convolution : ∀ q : ℝ, 0 < q → ∀ (n : ℕ) k,
    k ∈ ((1 + (q : ℂ) • F) ^ (n + 1)).coeff.support →
      ∑ ij ∈ ((1 + (q : ℂ) • F) ^ n).coeff.support ×ˢ
          (1 + (q : ℂ) • F).coeff.support with ij.1 + ij.2 = k,
        C ((n : ℝ) * q) ij.1 * C q ij.2 ≤ C (((n : ℝ) + 1) * q) k
  final_coefficient_cap : ∀ k, C 1 k ≤ 1

/-- The genuine binomial integral estimate is deduced from the explicit
coefficient conditions, not assumed as a further analytic hypothesis. -/
theorem fourier_binomial_integral_le_of_coefficient_conditions {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (a : Frequency d → ℝ)
    (C : ℝ → Frequency d → ℝ) (h : PolynomialCoefficientConditions F a C)
    (M : ℕ) (hM : 0 < M) :
    (∫ x, ‖(1 + polynomialFourierEval d F x / (M : ℂ)) ^ M‖ ^ 2 ∂torusMeasure d) ≤
      (1 + polynomialWeightedL2Sq F a / (M : ℝ)) ^ M := by
  have hMr : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hq : 0 < 1 / (M : ℝ) := one_div_pos.mpr hMr
  have htime : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  have hweighted := polynomialWeightedL2Sq_binomial_le F a C M hM
    h.zero_coefficient h.atom_positive h.zero_parameter (h.unit_coefficient _ hq)
    (h.one_atom _ hq) (h.power_positive _ hq) (h.finite_convolution _ hq)
  have hlast : ∀ k ∈ ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ M).coeff.support,
      0 < C 1 k := by
    intro k hk
    simpa only [htime] using h.power_positive (1 / (M : ℝ)) hq M k hk
  calc
    _ = ∫ x, ‖polynomialFourierEval d
          ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ M) x‖ ^ 2 ∂torusMeasure d := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        dsimp only
        rw [polynomialFourierEval_binomial]
    _ ≤ polynomialWeightedL2Sq ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ M) (C 1) :=
      polynomialFourierEval_integral_le_weighted _ _ hlast
        (fun k _ ↦ h.final_coefficient_cap k)
    _ ≤ _ := hweighted

/-- Conditional exponential integral theorem for an actual finite Fourier
polynomial. All analytic polynomial bounds are proved above; only the
explicit coefficient-family conditions remain to be instantiated. -/
theorem fourier_integral_exp_le_of_coefficient_conditions {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (a : Frequency d → ℝ)
    (C : ℝ → Frequency d → ℝ) (h : PolynomialCoefficientConditions F a C) :
    (∫ x, Real.exp (2 * (polynomialFourierEval d F x).re) ∂torusMeasure d) ≤
      Real.exp (polynomialWeightedL2Sq F a) := by
  apply ExponentialLimit.continuous_compact_integral_exp_le
    (torusMeasure d) (polynomialFourierEval d F) (polynomialWeightedL2Sq F a)
    (polynomialFourierEval d F).continuous
  intro M hM
  exact fourier_binomial_integral_le_of_coefficient_conditions F a C h M
    (Nat.succ_le_iff.mp hM)

/-- The corresponding logarithmic bound, with the normalization inherited
from the unit-volume torus probability measure. -/
theorem fourier_log_integral_exp_le_of_coefficient_conditions {d : ℕ}
    (F : AddMonoidAlgebra ℂ (Frequency d)) (a : Frequency d → ℝ)
    (C : ℝ → Frequency d → ℝ) (h : PolynomialCoefficientConditions F a C) :
    Real.log (∫ x, Real.exp (2 * (polynomialFourierEval d F x).re) ∂torusMeasure d) ≤
      polynomialWeightedL2Sq F a := by
  apply ExponentialLimit.continuous_compact_log_integral_exp_le
    (torusMeasure d) (polynomialFourierEval d F) (polynomialWeightedL2Sq F a)
    (polynomialFourierEval d F).continuous
  intro M hM
  exact fourier_binomial_integral_le_of_coefficient_conditions F a C h M
    (Nat.succ_le_iff.mp hM)

end Legacy.TorusEndpoint
