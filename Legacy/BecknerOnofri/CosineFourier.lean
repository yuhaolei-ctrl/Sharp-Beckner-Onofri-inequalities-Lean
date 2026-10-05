module

public import Legacy.D10.CosinePower
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! The actual Fourier coefficients and mass of the normalized cosine powers.
The coefficients are unsquared; squares arise only when computing energy. -/

noncomputable section

open Finset MeasureTheory

namespace Legacy.BecknerOnofri.CosineFourier

theorem coefficient_sum (n : ℕ) (k : ℤ) :
    fourierCoeff (fun x => (Legacy.D10.cosinePower n x : ℂ)) k =
      ∑ j ∈ range (2 * n + 1),
        (((2 * n).choose j : ℂ) / ((2 * n).choose n : ℂ)) *
          (Pi.single ((j : ℤ) - n) 1 : ℤ → ℂ) k := by
  have heq : (fun x => (Legacy.D10.cosinePower n x : ℂ)) =
      ∑ j ∈ range (2 * n + 1),
        (fun x => (((2 * n).choose j : ℂ) / ((2 * n).choose n : ℂ)) *
          fourier ((j : ℤ) - n) x) := by
    funext x
    simpa using Legacy.D10.cosinePower_fourier_expansion n x
  rw [heq, fourierCoeff.sum]
  · simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier]
  · intro j hj
    exact ((fourier ((j : ℤ) - n)).continuous.const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem coefficient_nat (n k : ℕ) :
    fourierCoeff (fun x => (Legacy.D10.cosinePower n x : ℂ)) (k : ℤ) =
      (Legacy.D10.binomialCoeffReal n k : ℂ) := by
  rw [coefficient_sum, Legacy.D10.binomialCoeffReal_formula]
  push_cast
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single (n + k)]
    · simp
    · intro b hb hbk
      have hne : (b : ℤ) - n ≠ k := by omega
      simp [Pi.single_eq_of_ne (Ne.symm hne)]
    · intro h
      exact (h (mem_range.mpr (by omega))).elim
  · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * n < n + k)]
    simp only [Nat.cast_zero, zero_div]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : (b : ℤ) - n ≠ k := by have := mem_range.mp hb; omega
    simp [Pi.single_eq_of_ne (Ne.symm hne)]

theorem coefficient_neg_nat (n k : ℕ) :
    fourierCoeff (fun x => (Legacy.D10.cosinePower n x : ℂ)) (-(k : ℤ)) =
      (Legacy.D10.binomialCoeffReal n k : ℂ) := by
  rw [coefficient_sum, Legacy.D10.binomialCoeffReal_formula]
  push_cast
  by_cases hk : k ≤ n
  · rw [Finset.sum_eq_single (n - k)]
    · have hindex : ((n - k : ℕ) : ℤ) - n = -(k : ℤ) := by omega
      rw [hindex, Pi.single_eq_same, mul_one,
        ← Nat.choose_symm (show n + k ≤ 2 * n by omega)]
      rw [show 2 * n - (n + k) = n - k by omega]
    · intro b hb hbk
      have hne : (b : ℤ) - n ≠ -(k : ℤ) := by omega
      simp [Pi.single_eq_of_ne (Ne.symm hne)]
    · intro h
      exact (h (mem_range.mpr (by omega))).elim
  · rw [Nat.choose_eq_zero_of_lt (by omega : 2 * n < n + k)]
    simp only [Nat.cast_zero, zero_div]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : (b : ℤ) - n ≠ -(k : ℤ) := by omega
    simp [Pi.single_eq_of_ne (Ne.symm hne)]

theorem coefficient (n : ℕ) (k : ℤ) :
    fourierCoeff (fun x => (Legacy.D10.cosinePower n x : ℂ)) k =
      (Legacy.D10.binomialCoeffReal n k.natAbs : ℂ) := by
  cases k with
  | ofNat k => simpa using coefficient_nat n k
  | negSucc k =>
      convert coefficient_neg_nat n (k + 1) using 1 <;> congr 1

theorem mass (n : ℕ) :
    (∫ x, Legacy.D10.cosinePower n x ∂AddCircle.haarAddCircle) = 1 := by
  have h := coefficient_nat n 0
  have hc : ((2 * n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
  simp only [Nat.cast_zero, fourierCoeff, neg_zero, fourier_zero,
    one_smul] at h
  rw [integral_complex_ofReal, Legacy.D10.binomialCoeffReal_formula] at h
  simpa [hc] using congrArg Complex.re h

end Legacy.BecknerOnofri.CosineFourier
