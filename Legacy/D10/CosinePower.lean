import Legacy.D10.BinomialReal
import Legacy.TorusEndpoint.TorusFourier

/-! # Actual normalized cosine powers on the unit circle -/

noncomputable section

namespace Legacy.D10

open Finset MeasureTheory
open scoped ComplexConjugate

/-- An actual nonnegative function on the circle. Its numerator is
`|1 + exp(2πix)|^(2n)`, so this equals the usual normalized cosine power. -/
def cosinePower (n : ℕ) (x : UnitAddCircle) : ℝ :=
  Complex.normSq (1 + fourier 1 x) ^ n / ((2 * n).choose n : ℝ)

theorem cosinePower_nonneg (n : ℕ) (x : UnitAddCircle) : 0 ≤ cosinePower n x := by
  unfold cosinePower
  exact div_nonneg (pow_nonneg (Complex.normSq_nonneg _) _) (Nat.cast_nonneg _)

theorem cosinePower_continuous (n : ℕ) : Continuous (cosinePower n) := by
  unfold cosinePower
  fun_prop

theorem cosinePower_integrable (n : ℕ) :
    Integrable (cosinePower n) AddCircle.haarAddCircle :=
  (cosinePower_continuous n).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma fourier_pow (k : ℤ) (n : ℕ) (x : UnitAddCircle) :
    fourier k x ^ n = fourier ((n : ℤ) * k) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← fourier_add]
    congr 1
    push_cast
    ring

lemma cosinePower_normSq (x : UnitAddCircle) :
    (Complex.normSq (1 + fourier 1 x) : ℂ) =
      fourier (-1) x * (1 + fourier 1 x)^2 := by
  rw [Complex.normSq_eq_conj_mul_self, map_add, map_one, ← fourier_neg]
  have h : fourier (-1) x * fourier 1 x = 1 := by
    rw [← fourier_add]
    norm_num
  linear_combination -(1 + fourier 1 x) * h

lemma cosinePower_complex (n : ℕ) (x : UnitAddCircle) :
    (cosinePower n x : ℂ) =
      (((2 * n).choose n : ℂ)⁻¹ * fourier (-(n : ℤ)) x) *
        (1 + fourier 1 x)^(2 * n) := by
  rw [cosinePower, Complex.ofReal_div, Complex.ofReal_pow, cosinePower_normSq,
    mul_pow, fourier_pow]
  simp only [mul_neg_one, Complex.ofReal_natCast]
  rw [pow_mul]
  ring

theorem cosinePower_fourier_expansion (n : ℕ) (x : UnitAddCircle) :
    (cosinePower n x : ℂ) =
      ∑ j ∈ range (2 * n + 1),
        (((2 * n).choose j : ℂ) / ((2 * n).choose n : ℂ)) *
          fourier ((j : ℤ) - n) x := by
  rw [cosinePower_complex, add_comm (1 : ℂ), add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one]
  rw [fourier_pow]
  simp only [mul_one]
  have h : fourier (-(n : ℤ)) x * fourier (j : ℤ) x =
      fourier ((j : ℤ) - n) x := by
    rw [← fourier_add]
    congr 1
    ring
  linear_combination (((2 * n).choose j : ℂ) / ((2 * n).choose n : ℂ)) * h

lemma cosinePower_normSq_real (x : UnitAddCircle) :
    Complex.normSq (1 + fourier 1 x) = 2 + 2 * (fourier 1 x).re := by
  have hz : Complex.normSq (fourier 1 x) = 1 := by
    simp [fourier_apply]
  simp [Complex.normSq_add, hz]
  ring

/-- On representatives, the constructed circle function is exactly the
normalized cosine power appearing in the endpoint proof. -/
theorem cosinePower_coe (n : ℕ) (x : ℝ) :
    cosinePower n (x : UnitAddCircle) =
      (4 : ℝ)^n / ((2 * n).choose n : ℝ) * Real.cos (Real.pi * x)^(2 * n) := by
  have hz : (fourier 1 (x : UnitAddCircle)).re = Real.cos (2 * Real.pi * x) := by
    rw [fourier_coe_apply]
    simp [Complex.exp_re]
  unfold cosinePower
  rw [cosinePower_normSq_real, hz]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
  rw [show 2 + 2 * (2 * Real.cos (Real.pi * x)^2 - 1) =
      4 * Real.cos (Real.pi * x)^2 by ring, mul_pow, pow_mul]
  ring

end Legacy.D10
