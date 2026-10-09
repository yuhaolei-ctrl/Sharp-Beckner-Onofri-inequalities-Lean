module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Rational certificates of Appendix B.1 (`subsec:d12-tail-arithmetic`)

Exact rational definitions of the finite sums specified in Appendix B.1, and kernel-checked
strict rational comparisons.  *No* soundness theorem relating them to `Real.log`, `ζ`, `exp`
is proved in this file: those bridges (`ℓ_M(a) ≤ log a ≤ u_M(a)`, the zeta tail comparison,
the Taylor polynomial bounds `E_M(z) ≤ e^{-z}`) are separate Lean obligations in the
real-analytic file.  All comparisons below are the ones listed in the source;
the Python mirror is `reports/ThetaTail/indep_check.py`. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

/-- `z = (a-1)/(a+1)` -/
def logZ (a : ℚ) : ℚ := (a - 1) / (a + 1)

/-- `ℓ_M(a) = 2 ∑_{k=0}^M z^{2k+1}/(2k+1)`. -/
def logLower (M : ℕ) (a : ℚ) : ℚ :=
  2 * ∑ k ∈ range (M + 1), (logZ a) ^ (2 * k + 1) / (2 * k + 1)

/-- `u_M(a) = ℓ_M(a) + 2 z^{2M+3} / ((2M+3)(1-z²))`. -/
def logUpper (M : ℕ) (a : ℚ) : ℚ :=
  logLower M a + 2 * (logZ a) ^ (2 * M + 3) / ((2 * M + 3) * (1 - (logZ a) ^ 2))

/-- partial zeta sum `∑_{k=1}^N k^{-p}` -/
def zetaPartial (p N : ℕ) : ℚ := ∑ k ∈ Icc 1 N, 1 / (k : ℚ) ^ p

/-- upper tail comparison `∑_{k≤N} k^{-p} + 1/((p-1)N^{p-1})` -/
def zetaUpper (p N : ℕ) : ℚ := zetaPartial p N + 1 / (((p : ℚ) - 1) * (N : ℚ) ^ (p - 1))

/-- `E_M(z) = ∑_{k=0}^M (-z)^k/k!`. -/
def expAlt (M : ℕ) (z : ℚ) : ℚ := ∑ k ∈ range (M + 1), (-z) ^ k / (k.factorial : ℚ)

/-- exponential upper bound `∑_{k≤M} z^k/k! + z^{M+1}/(M+1)! / (1-z/(M+2))`. -/
def expUpper (M : ℕ) (z : ℚ) : ℚ :=
  (∑ k ∈ range (M + 1), z ^ k / (k.factorial : ℚ))
    + z ^ (M + 1) / ((M + 1).factorial : ℚ) / (1 - z / ((M : ℚ) + 2))

/-- the coefficients `d_s` of `(d12-tail-eq:bexceptions)` and the line before it. -/
def dCoeff (s : ℕ) : ℚ :=
  if s = 1 then 8 else if s = 3 then 1952 / 729 else if s = 5 then 24288 / 15625
  else 2 ^ s * (Nat.choose 12 s : ℚ) / (s : ℚ) ^ 6

/-- `∑_{s=1}^{12} d_s E_M(c s)` for the three arguments used. -/
def dExpSum (M : ℕ) (c : ℚ) : ℚ := ∑ s ∈ Icc 1 12, dCoeff s * expAlt M (c * s)

/-- `∑_s d_s E_11(2s/9) (2s/9)^k / k!` of `(eq:fivechecks)` -/
def dExpMoment (k : ℕ) : ℚ :=
  ∑ s ∈ Icc 1 12, dCoeff s * expAlt 11 (2 * s / 9) * (2 * s / 9) ^ k / (k.factorial : ℚ)

/-- harmonic partial sum -/
def harmonicQ (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, 1 / (k : ℚ)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- logarithm enclosures (`M = 16`)
theorem log2_lower : (693 : ℚ) / 1000 < logLower 16 2 := by decide +kernel
theorem log2_upper2 : 2 * logUpper 16 2 < (1387 : ℚ) / 1000 := by decide +kernel
theorem log3_lower : (1098 : ℚ) / 1000 < logLower 16 3 := by decide +kernel
theorem log20_upper : 4 * logUpper 16 2 + logUpper 16 (5 / 4) < (2995733 : ℚ) / 10 ^ 6 := by
  decide +kernel
theorem log92_lower : (3 : ℚ) / 2 < logLower 16 (9 / 2) := by decide +kernel
theorem log52_upper : logUpper 16 (5 / 2) < (9163 : ℚ) / 10000 := by decide +kernel
theorem log72_upper : logUpper 16 (7 / 2) < (1566 : ℚ) / 1250 := by decide +kernel

-- zeta comparisons
theorem zeta6_upper : zetaUpper 6 5 < (101737 : ℚ) / 100000 := by decide +kernel
theorem zeta6_coeff : (63 : ℚ) / 8 * (101737 / 100000) < 2003 / 250 := by decide +kernel
theorem zeta5_upper : zetaUpper 5 6 < (1037 : ℚ) / 1000 := by decide +kernel
theorem zeta4_lower : (27 : ℚ) / 25 < zetaPartial 4 5 := by decide +kernel
theorem zeta2_upper : zetaUpper 2 5 < (5 : ℚ) / 3 := by decide +kernel

/-- `c₀ < 77/1000` (rational form of the printed estimate) -/
theorem c0_upper :
    (1387 : ℚ) / 8000 * (101737 / 100000)
      - 63 / 8 * (693 / 64000 + 1098 / 729000 + 1386 / 4096000) < 77 / 1000 := by decide +kernel

-- harmonic number and log 20
theorem harmonic20_lower : (3597739 : ℚ) / 10 ^ 6 < harmonicQ 20 := by decide +kernel
theorem gamma_lower : (577 : ℚ) / 1000 < 3597739 / 10 ^ 6 - 2995733 / 10 ^ 6 - 1 / 40 := by
  decide +kernel

-- exponential
theorem exp85_upper : expUpper 8 (8 / 5) < 5 := by decide +kernel

-- d_s data
theorem dCoeff_pos : ∀ s ∈ Icc 1 12, 0 < dCoeff s := by decide +kernel

theorem smallG_52 : (8817 : ℚ) / 1000 < dExpSum 13 (2 / 5) := by decide +kernel
theorem smallG_72 : (272 : ℚ) / 25 < dExpSum 11 (2 / 7) := by decide +kernel

/-- the five coefficient comparisons `(eq:fivechecks)` -/
theorem five_checks_0 : (309 : ℚ) / 25 < dExpMoment 0 := by decide +kernel
theorem five_checks_1 : (287 : ℚ) / 50 < dExpMoment 1 := by decide +kernel
theorem five_checks_2 : (52 : ℚ) / 25 < dExpMoment 2 := by decide +kernel
theorem five_checks_3 : (7 : ℚ) / 10 < dExpMoment 3 := by decide +kernel
theorem five_checks_4 : (11 : ℚ) / 50 < dExpMoment 4 := by decide +kernel

end BecknerOnofri.V2.ThetaTail
