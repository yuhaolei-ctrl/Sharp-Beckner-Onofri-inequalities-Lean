import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

/-!
# Rational normalized central binomial coefficients

These are the nonnegative-frequency coefficients of the normalized cosine
powers in Sections 1--2 of `ENDPOINT_PROOF.md`.
-/

namespace Legacy.D10

open Finset

/-- Rational harmonic number, with the same convention as mathlib's `harmonic`. -/
def harmonicNumber (n : ℕ) : ℚ := ∑ k ∈ range n, (k + 1 : ℚ)⁻¹

/-- The Fourier coefficient of the normalized cosine power at a nonnegative
frequency. Frequencies beyond `n` vanish by the convention for `Nat.choose`. -/
def binomialCoeff (n k : ℕ) : ℚ :=
  ((2 * n).choose (n + k) : ℚ) / ((2 * n).choose n : ℚ)

lemma central_choose_pos (n : ℕ) : 0 < (2 * n).choose n :=
  Nat.choose_pos (by omega)

@[simp] lemma binomialCoeff_zero (n : ℕ) : binomialCoeff n 0 = 1 := by
  simp [binomialCoeff, ne_of_gt (central_choose_pos n)]

lemma binomialCoeff_nonneg (n k : ℕ) : 0 ≤ binomialCoeff n k := by
  unfold binomialCoeff
  positivity

lemma binomialCoeff_eq_zero {n k : ℕ} (h : n < k) :
    binomialCoeff n k = 0 := by
  simp [binomialCoeff, Nat.choose_eq_zero_of_lt (show 2 * n < n + k by omega)]

lemma binomialCoeff_factorial {n k : ℕ} (h : k ≤ n) :
    binomialCoeff n k = (n.factorial : ℚ) ^ 2 /
      ((n + k).factorial * (n - k).factorial) := by
  rw [binomialCoeff, Nat.cast_choose ℚ (show n + k ≤ 2 * n by omega),
    Nat.cast_choose ℚ (show n ≤ 2 * n by omega)]
  rw [show 2 * n - (n + k) = n - k by omega,
    show 2 * n - n = n by omega]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have h2n : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma binomialCoeff_step (n k : ℕ) (h : k ≤ n) :
    (n + k + 1 : ℚ) * binomialCoeff n (k + 1) =
      (n - k : ℚ) * binomialCoeff n k := by
  have H := Nat.choose_succ_right_eq (2 * n) (n + k)
  have Hq : (((2 * n).choose (n + k + 1) : ℚ) * (n + k + 1)) =
      ((2 * n).choose (n + k) : ℚ) * (n - k) := by
    rw [show 2 * n - (n + k) = n - k by omega] at H
    exact_mod_cast H
  unfold binomialCoeff
  rw [show n + (k + 1) = n + k + 1 by omega]
  linear_combination Hq / (((2 * n).choose n : ℚ))

/-- The first moment telescopes along a row of the normalized binomial array. -/
lemma binomialCoeff_first_moment (n : ℕ) :
    2 * (∑ k ∈ range (n + 1), (k : ℚ) * binomialCoeff n k) = n := by
  have H : ∀ k ∈ range (n + 1),
      2 * ((k : ℚ) * binomialCoeff n k) =
        (n + k : ℚ) * binomialCoeff n k -
          (n + (k + 1) : ℚ) * binomialCoeff n (k + 1) := by
    intro k hk
    have hs := binomialCoeff_step n k (by simpa using mem_range_succ_iff.mp hk)
    linear_combination hs
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl H]
  simpa [Nat.cast_add, Nat.cast_one,
    binomialCoeff_eq_zero (show n < n + 1 by omega)] using
    (Finset.sum_range_sub' (fun k : ℕ => (n + k : ℚ) * binomialCoeff n k) (n + 1))

/-- Row increments are weighted by the squared frequency. -/
lemma binomialCoeff_row_step (n k : ℕ) :
    (n + 1 : ℚ)^2 * (binomialCoeff (n + 1) k - binomialCoeff n k) =
      (k : ℚ)^2 * binomialCoeff (n + 1) k := by
  by_cases h : k ≤ n
  · rw [binomialCoeff_factorial h, binomialCoeff_factorial (by omega : k ≤ n + 1)]
    rw [show n + 1 + k = (n + k) + 1 by omega,
      show n + 1 - k = (n - k) + 1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub h]
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    have hnk : ((n + k).factorial : ℚ) ≠ 0 := by positivity
    have hnm : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    have hp : (n : ℚ) + k + 1 ≠ 0 := by positivity
    have hm : (n : ℚ) - k + 1 ≠ 0 := by
      have : (k : ℚ) ≤ n := by exact_mod_cast h
      linarith
    field_simp
    ring
  · by_cases h' : k = n + 1
    · subst k
      rw [binomialCoeff_eq_zero (by omega : n < n + 1)]
      simp
    · rw [binomialCoeff_eq_zero (by omega : n < k),
        binomialCoeff_eq_zero (by omega : n + 1 < k)]
      simp

lemma binomialCoeff_row_step_div (n k : ℕ) :
    (binomialCoeff (n + 1) k - binomialCoeff n k) / (k : ℚ) =
      (k : ℚ) * binomialCoeff (n + 1) k / (n + 1 : ℚ)^2 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    have hn : (n + 1 : ℚ) ≠ 0 := by positivity
    apply (div_eq_div_iff hkq (pow_ne_zero 2 hn)).2
    linear_combination binomialCoeff_row_step n k

/-- The normalized-binomial harmonic sum increases by `1/(n+1)`. -/
lemma binomialCoeff_harmonic_step (n : ℕ) :
    2 * (∑ k ∈ range (n + 2), binomialCoeff (n + 1) k / (k : ℚ)) =
      2 * (∑ k ∈ range (n + 1), binomialCoeff n k / (k : ℚ)) +
        (n + 1 : ℚ)⁻¹ := by
  have H := Finset.sum_congr (s₁ := range (n + 2)) rfl
    (fun k _ => binomialCoeff_row_step_div n k)
  simp only [sub_div, Finset.sum_sub_distrib, ← Finset.sum_div] at H
  have Hn : (∑ k ∈ range (n + 2), binomialCoeff n k / (k : ℚ)) =
      ∑ k ∈ range (n + 1), binomialCoeff n k / (k : ℚ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp [binomialCoeff_eq_zero (show n < n + 1 by omega)]
  rw [Hn] at H
  have Hm := binomialCoeff_first_moment (n + 1)
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  have Hscaled := congrArg (fun x : ℚ => 2 * x) H
  have Hlast : 2 * ((∑ k ∈ range (n + 2), (k : ℚ) * binomialCoeff (n + 1) k) /
      (n + 1 : ℚ)^2) = (n + 1 : ℚ)⁻¹ := by
    rw [← mul_div_assoc]
    rw [show n + 2 = (n + 1) + 1 by omega, Hm]
    push_cast
    field_simp
  rw [Hlast] at Hscaled
  linarith

/-- The exact harmonic identity used in the mixture-to-entropy reduction.
The zero frequency contributes zero, since division by zero in `ℚ` is zero. -/
theorem binomialCoeff_harmonic (n : ℕ) :
    2 * (∑ k ∈ range (n + 1), binomialCoeff n k / (k : ℚ)) =
      harmonicNumber n := by
  induction n with
  | zero => simp [harmonicNumber]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, binomialCoeff_harmonic_step, ih]
    simp [harmonicNumber, Finset.sum_range_succ]

end Legacy.D10
