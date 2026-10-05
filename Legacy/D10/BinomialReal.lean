module

public import Legacy.D10.BinomialMixture

@[expose] public section

/-! # Real-valued interfaces for the exact rational mixture algebra -/

namespace Legacy.D10

open Finset

/-- The normalized cosine-power coefficient, cast to the real numbers. -/
def binomialCoeffReal (n k : ℕ) : ℝ := (binomialCoeff n k : ℚ)

/-- The finite hypergeometric probability weight, cast to the real numbers. -/
def hypergeometricWeightReal (n m l : ℕ) : ℝ := (hypergeometricWeight n m l : ℚ)

theorem binomialCoeffReal_formula (n k : ℕ) :
    binomialCoeffReal n k =
      ((2 * n).choose (n + k) : ℝ) / ((2 * n).choose n : ℝ) := by
  simp [binomialCoeffReal, binomialCoeff]

theorem binomialCoeffReal_harmonic (n : ℕ) :
    2 * (∑ k ∈ range (n + 1), binomialCoeffReal n k / (k : ℝ)) =
      ∑ k ∈ range n, (k + 1 : ℝ)⁻¹ := by
  unfold binomialCoeffReal
  have H := binomialCoeff_harmonic n
  unfold harmonicNumber at H
  have HR := congrArg (fun x : ℚ => (x : ℝ)) H
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sum, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_inv, Rat.cast_add, Rat.cast_one] using HR

theorem hypergeometricWeightReal_nonneg (n m l : ℕ) :
    0 ≤ hypergeometricWeightReal n m l := by
  unfold hypergeometricWeightReal
  exact_mod_cast hypergeometricWeight_nonneg n m l

theorem sum_hypergeometricWeightReal (n m : ℕ) :
    ∑ l ∈ range (n + 1), hypergeometricWeightReal n m l = 1 := by
  unfold hypergeometricWeightReal
  exact_mod_cast sum_hypergeometricWeight n m

theorem hypergeometric_product_real (n m k : ℕ) :
    (∑ l ∈ range (n + 1), hypergeometricWeightReal n m l * binomialCoeffReal l k) =
      binomialCoeffReal n k * binomialCoeffReal m k := by
  unfold hypergeometricWeightReal binomialCoeffReal
  exact_mod_cast hypergeometric_product n m k

end Legacy.D10
