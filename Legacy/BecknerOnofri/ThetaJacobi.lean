module

public import Legacy.BecknerOnofri.ThetaDomination
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

@[expose] public section

/-!
Jacobi transformation for the actual real theta series with manuscript
normalization `realTheta t = ∑' j : ℤ, exp (-t*j²)`.

Mathlib's real Gaussian Poisson formula uses the parameter `a` in `exp(-π*a*j²)`.
The proof below explicitly substitutes `a=t/π` and verifies both arguments and
the positive-real square-root factor. No lattice or Fourier interface is assumed.
-/

namespace Legacy.BecknerOnofri.ThetaDomination

/-- Jacobi transformation with the exact normalization used in the manuscript. -/
theorem realTheta_jacobi {t : ℝ} (ht : 0 < t) :
    realTheta t = Real.sqrt (Real.pi / t) * realTheta (Real.pi ^ 2 / t) := by
  have h := Real.tsum_exp_neg_mul_int_sq (div_pos ht Real.pi_pos)
  have hleft : -Real.pi * (t / Real.pi) = -t := by
    field_simp
  have hright : -Real.pi / (t / Real.pi) = -(Real.pi ^ 2 / t) := by
    field_simp
  have hfactor : (1 : ℝ) / (t / Real.pi) ^ (1 / 2 : ℝ) =
      Real.sqrt (Real.pi / t) := by
    rw [← Real.sqrt_eq_rpow, one_div, ← Real.sqrt_inv, inv_div]
  rw [hleft, hright, hfactor] at h
  exact h

/-- The natural-dimensional theta power transforms with the real power `d/2`.
This includes odd dimensions and makes no integer-half-dimension assumption. -/
theorem realTheta_pow_jacobi {t : ℝ} (ht : 0 < t) (d : ℕ) :
    realTheta t ^ d = (Real.pi / t) ^ ((d : ℝ) / 2) *
      realTheta (Real.pi ^ 2 / t) ^ d := by
  rw [realTheta_jacobi ht, mul_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos Real.pi_pos ht).le]
  congr 1
  ring

end Legacy.BecknerOnofri.ThetaDomination
