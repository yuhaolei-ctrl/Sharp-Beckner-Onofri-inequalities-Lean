import BecknerOnofri.EntropyTailAxisFactors

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

theorem scalarCoefficient_zero {n j : ℕ} (hj : n < j) : scalarCoefficient n j = 0 := by
  rw [scalarCoefficient_eq, Legacy.D10.binomialCoeffReal,
    Legacy.D10.binomialCoeff_eq_zero hj, Rat.cast_zero]

theorem scalarHarmonic_summable (n : ℕ) :
    Summable (fun j : ℕ => scalarCoefficient n j/(j : ℝ)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (n+1))
  intro j hj
  have hn : n < j := by simp only [Finset.mem_range, not_lt] at hj; omega
  rw [scalarCoefficient_zero hn, zero_div]

theorem scalarHarmonic_tsum (n : ℕ) :
    2*(∑' j : ℕ, scalarCoefficient n j/(j : ℝ)) = (harmonic n : ℝ) := by
  have he : (∑' j : ℕ, scalarCoefficient n j/(j : ℝ)) =
      ∑ j ∈ Finset.range (n+1), scalarCoefficient n j/(j : ℝ) := by
    apply tsum_eq_sum
    intro j hj
    have hn : n < j := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [scalarCoefficient_zero hn, zero_div]
  rw [he]
  simpa only [scalarCoefficient_eq, harmonic, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one] using
      Legacy.D10.binomialCoeffReal_harmonic n

theorem scalarHarmonic_tail (n : ℕ) :
    (harmonic n : ℝ)-2*scalarCoefficient n 1-scalarCoefficient n 2 =
      2*∑' j : ℕ, scalarCoefficient n (j+3)/(j+3 : ℝ) := by
  have h := (scalarHarmonic_summable n).sum_add_tsum_nat_add 3
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_add, div_zero, zero_add, div_one] at h
  rw [← scalarHarmonic_tsum]
  linarith

theorem scalarBudget_eq_axis_tail (n : ℕ) :
    scalarBudget n = 12*((21/500)*scalarCoefficient n 2+
      (27/20)*∑' j : ℕ, scalarCoefficient n (j+3)/(j+3 : ℝ)) := by
  rw [scalarBudget, scalarHarmonic_tail]
  ring

#print axioms scalarBudget_eq_axis_tail
end BecknerOnofri.HighDim.EntropyTail
