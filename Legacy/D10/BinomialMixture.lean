import Legacy.D10.Binomial

/-! # The hypergeometric mixing weights for normalized cosine powers -/

namespace Legacy.D10

set_option maxHeartbeats 20000

open Finset

/-- The unnormalized hypergeometric weights sum by Vandermonde's identity. -/
theorem sum_choose_mul_choose (n m : ℕ) :
    ∑ l ∈ range (n + 1), n.choose l * m.choose l = (n + m).choose n := by
  rw [Nat.add_choose_eq, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ l ∈ range (n + 1), n.choose (n - l) * m.choose (n - (n - l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      have h : l ≤ n := mem_range_succ_iff.mp hl
      rw [Nat.sub_sub_self h, Nat.choose_symm h]
    _ = _ := by
      simpa using Finset.sum_range_reflect
        (fun l => n.choose l * m.choose (n - l)) (n + 1)

/-- Conditional probability of the latent cosine-power index. -/
def hypergeometricWeight (n m l : ℕ) : ℚ :=
  ((n.choose l : ℚ) * m.choose l) / ((n + m).choose n : ℚ)

lemma hypergeometricWeight_nonneg (n m l : ℕ) :
    0 ≤ hypergeometricWeight n m l := by
  unfold hypergeometricWeight
  positivity

theorem sum_hypergeometricWeight (n m : ℕ) :
    ∑ l ∈ range (n + 1), hypergeometricWeight n m l = 1 := by
  have hc : ((n + m).choose n : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos (Nat.le_add_right n m)))
  unfold hypergeometricWeight
  rw [← Finset.sum_div]
  have H : (∑ l ∈ range (n + 1), (n.choose l : ℚ) * m.choose l) =
      ((n + m).choose n : ℚ) := by exact_mod_cast sum_choose_mul_choose n m
  rw [H, div_self hc]

/-- Factorial cancellation in a single summand of the shifted Vandermonde sum. -/
lemma hypergeometric_summand (n m k r : ℕ) (hk : k ≤ m) (hr : r + k ≤ n) :
    (n.choose (r + k) : ℚ) * m.choose (r + k) * binomialCoeff (r + k) k =
      ((n.factorial : ℚ) * m.factorial / ((n + k).factorial * (m - k).factorial)) *
        ((n + k).choose (n - k - r) : ℚ) * (m - k).choose r := by
  by_cases hm : r + k ≤ m
  · rw [Nat.cast_choose ℚ hr, Nat.cast_choose ℚ hm,
      binomialCoeff_factorial (show k ≤ r + k by omega),
      Nat.cast_choose ℚ (show n - k - r ≤ n + k by omega),
      Nat.cast_choose ℚ (show r ≤ m - k by omega)]
    rw [show r + k - k = r by omega,
      show n + k - (n - k - r) = r + k + k by omega,
      show n - k - r = n - (r + k) by omega,
      show m - k - r = m - (r + k) by omega]
    have hf (j : ℕ) : (j.factorial : ℚ) ≠ 0 := by positivity
    field_simp [hf]
  · have hm' : m - k < r := by omega
    rw [Nat.choose_eq_zero_of_lt (show m < r + k by omega),
      Nat.choose_eq_zero_of_lt hm']
    simp

lemma hypergeometric_raw_sum (n m k : ℕ) (hn : k ≤ n) (hm : k ≤ m) :
    (∑ l ∈ range (n + 1),
      (n.choose l : ℚ) * m.choose l * binomialCoeff l k) =
      ((n.factorial : ℚ) * m.factorial / ((n + k).factorial * (m - k).factorial)) *
        ((n + m).choose (n - k) : ℚ) := by
  let f : ℕ → ℚ := fun l => (n.choose l : ℚ) * m.choose l * binomialCoeff l k
  have Hz : ∑ l ∈ range k, f l = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    simp [f, binomialCoeff_eq_zero (mem_range.mp hl)]
  have Hsplit : (∑ l ∈ range (n + 1), f l) =
      ∑ r ∈ range (n - k + 1), f (r + k) := by
    rw [show n + 1 = k + (n - k + 1) by omega,
      Finset.sum_range_add, Hz, zero_add]
    simp only [Nat.add_comm k]
  change (∑ l ∈ range (n + 1), f l) = _
  rw [Hsplit]
  simp only [f]
  rw [Finset.sum_congr rfl (fun r hr =>
    hypergeometric_summand n m k r hm (by have := mem_range.mp hr; omega))]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have HV := Nat.add_choose_eq (m - k) (n + k) (n - k)
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk] at HV
  rw [show m - k + (n + k) = n + m by omega] at HV
  have HVq : ((n + m).choose (n - k) : ℚ) =
      ∑ r ∈ range (n - k + 1),
        ((m - k).choose r : ℚ) * (n + k).choose (n - k - r) := by
    exact_mod_cast HV
  rw [HVq]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- The hypergeometric latent index gives the product of the two original
normalized binomial coefficients, without squaring a component coefficient. -/
theorem hypergeometric_product (n m k : ℕ) :
    (∑ l ∈ range (n + 1), hypergeometricWeight n m l * binomialCoeff l k) =
      binomialCoeff n k * binomialCoeff m k := by
  by_cases hn : k ≤ n
  · by_cases hm : k ≤ m
    · simp only [hypergeometricWeight, div_mul_eq_mul_div, ← Finset.sum_div]
      rw [hypergeometric_raw_sum n m k hn hm,
        binomialCoeff_factorial hn, binomialCoeff_factorial hm,
        Nat.cast_choose ℚ (show n - k ≤ n + m by omega),
        Nat.cast_choose ℚ (show n ≤ n + m by omega)]
      rw [show n + m - (n - k) = m + k by omega,
        show n + m - n = m by omega]
      have hf (j : ℕ) : (j.factorial : ℚ) ≠ 0 := by positivity
      field_simp [hf]
    · rw [binomialCoeff_eq_zero (show m < k by omega), mul_zero]
      apply Finset.sum_eq_zero
      intro l hl
      by_cases hml : l ≤ m
      · rw [binomialCoeff_eq_zero (show l < k by omega), mul_zero]
      · simp [hypergeometricWeight, Nat.choose_eq_zero_of_lt (show m < l by omega)]
  · rw [binomialCoeff_eq_zero (show n < k by omega), zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    have hl' := mem_range.mp hl
    rw [binomialCoeff_eq_zero (show l < k by omega), mul_zero]

end Legacy.D10
