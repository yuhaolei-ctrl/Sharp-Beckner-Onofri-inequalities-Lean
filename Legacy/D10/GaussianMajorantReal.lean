module

public import Legacy.D10.GaussianMajorant
public import Legacy.D10.BinomialReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import BecknerOnofri.V2.Reaudit.ScalarBridges.GaussianBinomial

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
parameter `log (1 + 1/n)` from the proof manuscript.

Proved along the printed route of Lemma `lem:gaussian-binomial` (positive artanh series,
`BecknerOnofri.V2.Reaudit.ScalarBridges.gaussian_binomial_printed`); the earlier rational
subadditivity induction (`binomialCoeff_gaussian`, `binomialCoeffReal_power_majorant`) is no
longer used here. -/
theorem binomialCoeffReal_gaussian (n k : ℕ) (hn : 0 < n) :
    binomialCoeffReal n k ≤
      Real.exp (-Real.log (1 + 1 / (n : ℝ)) * (k : ℝ) ^ 2) := by
  have h := BecknerOnofri.V2.Reaudit.ScalarBridges.gaussian_binomial_printed n hn (k : ℤ)
  rw [BecknerOnofri.V2.Reaudit.ScalarBridges.binomA_natCast, ← binomialCoeffReal_formula] at h
  simpa using h

end Legacy.D10
