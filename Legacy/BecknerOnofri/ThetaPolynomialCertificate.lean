import Legacy.BecknerOnofri.ThetaCertificate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A finite theta-polynomial certificate

This module certifies the complete degree-40 polynomial (1+2x+3x^4)^10-1.
It also certifies its rational integral majorant, including every degree.
The analytic theta majorization and integral bounds are separate obligations.
The generated integer arrays are checked inside Lean's kernel.
-/

namespace Legacy.BecknerOnofri.ThetaPolynomialCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset

/-- All coefficients, including the constant coefficient at index zero. -/
def coefficients : Array ℕ := #[1, 20, 180, 960, 3390, 8604, 17760, 35520, 72405, 132560, 207664, 319680, 525960, 786480, 997920, 1321920, 1935090, 2381400, 2472120, 3136320, 4143636, 3878280, 3538080, 4898880, 5051970, 3184272, 3674160, 4898880, 2711880, 1574640, 3149280, 2099520, 295245, 1180980, 1180980, 0, 196830, 393660, 0, 0, 59049]

/-- Coefficient of x^q; the array convention gives zero beyond degree 40. -/
def coeff (q : ℕ) : ℕ := coefficients[q]!

theorem coeff_zero : coeff 0 = 1 := by decide +kernel

theorem coeff_cast_nonneg (q : ℕ) : (0 : ℝ) ≤ coeff q := Nat.cast_nonneg _

/-- The literal array really is the complete expansion; no tail is omitted. -/
theorem polynomial_identity (x : ℝ) :
    (1 + 2*x + 3*x^4)^10 - 1 =
      ∑ q ∈ range 40, (coeff (q+1) : ℝ) * x^(q+1) := by
  norm_num [coeff, coefficients, sum_range_succ]
  ring

def factorQ (A : ℚ) : ℚ :=
  1/A + 4/A^2 + 12/A^3 + 24/A^4 + 24/A^5 +
    (A^2 + 5*A + 2) / (A * (A^2 + 6*A + 6))

def termQ (q : ℕ) : ℚ :=
  coeff q * ThetaCertificate.r^q * factorQ (ThetaCertificate.a*q)

def upperQ : ℚ := ∑ q ∈ range 40, termQ (q+1)

/-- Upward rounded witnesses at scale 10^12, indexed by q-1. -/
def rounded : Array ℕ := #[1459125207561, 156702351207, 20570797669, 2199652302, 185983454, 13508923, 985145, 75076, 5235, 317, 20, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1]

/-- All forty individual roundings are proved by kernel reduction. -/
theorem term_checks : ∀ i : Fin 40,
    termQ (i.val+1) ≤ (rounded[i.val]! : ℚ) / 1000000000000 := by
  decide +kernel

theorem rounded_check :
    (∑ q ∈ range 40, (rounded[q]! : ℚ) / 1000000000000) < 41/25 := by
  decide +kernel

/-- The exact, unrounded rational expression is below 41/25. -/
theorem rational_upper_lt : upperQ < (41/25 : ℚ) := by
  apply lt_of_le_of_lt _ rounded_check
  unfold upperQ
  apply sum_le_sum
  intro q hq
  exact term_checks ⟨q, mem_range.mp hq⟩

noncomputable def factorReal (A : ℝ) : ℝ :=
  1/A + 4/A^2 + 12/A^3 + 24/A^4 + 24/A^5 +
    (A^2 + 5*A + 2) / (A * (A^2 + 6*A + 6))

noncomputable def upperReal : ℝ :=
  ∑ q ∈ range 40, (coeff (q+1) : ℝ) * (ThetaCertificate.r : ℝ)^(q+1) *
    factorReal ((ThetaCertificate.a : ℝ)*(q+1))

theorem factor_real_cast (A : ℚ) : (factorQ A : ℝ) = factorReal (A : ℝ) := by
  unfold factorQ factorReal
  push_cast
  rfl

theorem upper_real_cast : (upperQ : ℝ) = upperReal := by
  unfold upperQ upperReal termQ
  push_cast
  simp only [factor_real_cast, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

/-- The real finite sum, ready for use after integrating the theta bound. -/
theorem sum_real_lt :
    (∑ q ∈ range 40, (coeff (q+1) : ℝ) * (ThetaCertificate.r : ℝ)^(q+1) *
      factorReal ((ThetaCertificate.a : ℝ)*(q+1))) < (41/25 : ℝ) := by
  change upperReal < (41/25 : ℝ)
  rw [← upper_real_cast]
  have h := (Rat.cast_lt (K := ℝ)).2 rational_upper_lt
  norm_num at h
  exact h

end Legacy.BecknerOnofri.ThetaPolynomialCertificate

#print axioms Legacy.BecknerOnofri.ThetaPolynomialCertificate.polynomial_identity
#print axioms Legacy.BecknerOnofri.ThetaPolynomialCertificate.rational_upper_lt
#print axioms Legacy.BecknerOnofri.ThetaPolynomialCertificate.sum_real_lt
