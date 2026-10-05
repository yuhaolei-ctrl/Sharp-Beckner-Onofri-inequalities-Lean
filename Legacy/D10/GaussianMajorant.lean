import Legacy.D10.Binomial

/-! A rational proof of the binomial Gaussian majorant used in the scalar
tail argument. No transcendental comparison or numerical estimate is needed
for the integer-power majorant. -/

namespace Legacy.D10

private def quotient (x : ℚ) : ℚ := (1 - x) / (1 + x)

private theorem quotient_mul_le {x y : ℚ}
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    quotient (x * y) ≤ quotient x + quotient y := by
  have hd : quotient x + quotient y - quotient (x * y) =
      (1 - x) * (1 - y) * (1 - x * y) /
        ((1 + x) * (1 + y) * (1 + x * y)) := by
    unfold quotient
    have h1 : 1 + x ≠ 0 := by positivity
    have h2 : 1 + y ≠ 0 := by positivity
    have h3 : 1 + x * y ≠ 0 := by positivity
    field_simp
    ring
  have hxy : x * y ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx') hy]
  have hp : 0 ≤ (1 - x) * (1 - y) * (1 - x * y) /
      ((1 + x) * (1 + y) * (1 + x * y)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy'))
        (sub_nonneg.mpr hxy)
    · positivity
  linarith

private theorem quotient_pow_le {q : ℚ} (hq : 0 ≤ q) (hq' : q ≤ 1) (m : ℕ) :
    quotient (q ^ m) ≤ (m : ℚ) * quotient q := by
  induction m with
  | zero => simp [quotient]
  | succ m ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have H : quotient (q ^ m * q) ≤ quotient (q ^ m) + quotient q :=
      quotient_mul_le (pow_nonneg hq m) (pow_le_one₀ (n := m) hq hq') hq hq'
    linarith

/-- An individual ratio of consecutive binomial coefficients is bounded by
an odd power of the first ratio. -/
theorem binomial_ratio_majorant (n k : ℕ) :
    ((n : ℚ) - k) / (n + k + 1) ≤ ((n : ℚ) / (n + 1)) ^ (2 * k + 1) := by
  let q : ℚ := (n : ℚ) / (n + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hquot : quotient q = 1 / (2 * (n : ℚ) + 1) := by
    dsimp [q, quotient]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hn' : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have H := quotient_pow_le hq hq' (2 * k + 1)
  rw [hquot, quotient, mul_one_div] at H
  have hp : 0 < 1 + q ^ (2 * k + 1) := by positivity
  have hn : 0 < 2 * (n : ℚ) + 1 := by positivity
  have H' := (div_le_div_iff₀ hp hn).mp H
  push_cast at H'
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < n + k + 1)).mpr
  change (n : ℚ) - k ≤ q ^ (2 * k + 1) * (n + k + 1)
  nlinarith

/-- Exact rational form of the Gaussian majorant, valid also at `n = 0` and
outside the finite support. The exponent is the square of the frequency. -/
theorem binomialCoeff_gaussian (n k : ℕ) :
    binomialCoeff n k ≤ ((n : ℚ) / (n + 1)) ^ (k ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k ≤ n
    · have hr := binomial_ratio_majorant n k
      have hn : (0 : ℚ) < n + k + 1 := by positivity
      have hc : binomialCoeff n (k + 1) =
          (((n : ℚ) - k) / (n + k + 1)) * binomialCoeff n k := by
        have H := binomialCoeff_step n k hk
        field_simp
        linear_combination H
      rw [hc]
      calc
        _ ≤ (((n : ℚ) / (n + 1)) ^ (2 * k + 1)) * binomialCoeff n k :=
          mul_le_mul_of_nonneg_right hr (binomialCoeff_nonneg n k)
        _ ≤ (((n : ℚ) / (n + 1)) ^ (2 * k + 1)) *
            (((n : ℚ) / (n + 1)) ^ (k ^ 2)) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; ring
    · rw [binomialCoeff_eq_zero (by omega : n < k + 1)]
      positivity

end Legacy.D10
