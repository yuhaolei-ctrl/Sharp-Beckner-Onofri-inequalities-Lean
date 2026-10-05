import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Exact scalar Taylor coefficients and their finite convolution identity.
These provide the factorial factors in finite-atom exponential coefficients. -/

open scoped BigOperators

namespace Legacy.TorusEndpoint

noncomputable def scalarExpTerm (q : ℝ) (n : ℕ) : ℝ := q ^ n / n.factorial

@[simp] theorem scalarExpTerm_zero (q : ℝ) : scalarExpTerm q 0 = 1 := by
  simp [scalarExpTerm]

@[simp] theorem scalarExpTerm_one (q : ℝ) : scalarExpTerm q 1 = q := by
  simp [scalarExpTerm]

theorem scalarExpTerm_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ scalarExpTerm q n := by
  unfold scalarExpTerm
  positivity

theorem scalarExpTerm_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (n : ℕ) :
    scalarExpTerm p n ≤ scalarExpTerm q n := by
  unfold scalarExpTerm
  gcongr

theorem scalarExpTerm_convolution (p q : ℝ) (n : ℕ) :
    scalarExpTerm (p + q) n =
      ∑ ij ∈ Finset.antidiagonal n, scalarExpTerm p ij.1 * scalarExpTerm q ij.2 := by
  have h := congrArg (PowerSeries.coeff n)
    (PowerSeries.exp_mul_exp_eq_exp_add (A := ℝ) p q)
  simpa [PowerSeries.coeff_mul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, scalarExpTerm, div_eq_mul_inv] using h.symm

theorem scalarExpTerm_convolution_range (p q : ℝ) (n : ℕ) :
    scalarExpTerm (p + q) n =
      ∑ j ∈ Finset.range (n + 1), scalarExpTerm p j * scalarExpTerm q (n - j) := by
  rw [scalarExpTerm_convolution, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem scalarExpTerm_partial_sum_le_exp {q : ℝ} (hq : 0 ≤ q) (N : ℕ) :
    (∑ n ∈ Finset.range N, scalarExpTerm q n) ≤ Real.exp q :=
  Real.sum_le_exp_of_nonneg hq N

end Legacy.TorusEndpoint
