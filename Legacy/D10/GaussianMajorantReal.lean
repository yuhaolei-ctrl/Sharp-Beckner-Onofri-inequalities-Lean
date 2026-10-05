module

public import Legacy.D10.GaussianMajorant
public import Legacy.D10.BinomialReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Legacy.D10

/-- The exact real integer-power form of the binomial majorant. -/
theorem binomialCoeffReal_power_majorant (n k : ℕ) :
    binomialCoeffReal n k ≤ ((n : ℝ) / (n + 1)) ^ (k ^ 2) := by
  unfold binomialCoeffReal
  have H := (Rat.cast_le (K := ℝ)).mpr (binomialCoeff_gaussian n k)
  push_cast at H
  exact H

/-- The Gaussian form used in the Mellin/theta bound, with the precise
parameter `log (1 + 1/n)` from the proof manuscript. -/
theorem binomialCoeffReal_gaussian (n k : ℕ) (hn : 0 < n) :
    binomialCoeffReal n k ≤
      Real.exp (-Real.log (1 + 1 / (n : ℝ)) * (k : ℝ) ^ 2) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : Real.exp (-Real.log (1 + 1 / (n : ℝ))) = (n : ℝ) / (n + 1) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have he : ((n : ℝ) / (n + 1)) ^ (k ^ 2) =
      Real.exp (-Real.log (1 + 1 / (n : ℝ)) * (k : ℝ) ^ 2) := by
    rw [← hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  exact he ▸ binomialCoeffReal_power_majorant n k

end Legacy.D10
