import Legacy.D10.FiniteScalarSemantics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Finite certificates for Section 3 of the September 16 manuscript.
The cutoff 64 is a formalization optimization: all remaining polynomial mass
is retained with the upper weight at 65. Thus no omitted tail is discarded.
`FiniteCheck` is arithmetic, not by itself the Fourier/entropy theorem.
-/
namespace Legacy.BecknerOnofri.FiniteScalar
open Legacy.D10.FiniteScalar
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def scale : Nat := 2^40

def reciprocalUnits (d q : Nat) : Nat :=
  let m := d / 2
  if d % 2 = 0 then (scale + q^m - 1) / q^m
  else
    let den := q^m * Nat.sqrt (q*scale*scale)
    (scale*scale + den - 1) / den

def lambdaUpper (d : Nat) : ℚ :=
  let m := d/2
  if d % 2 = 0 then (d * Nat.factorial (m-1) : Nat) / ((314159 : ℚ)/100000)^m
  else (d * Nat.factorial (2*m) : Nat) /
    ((4^m * Nat.factorial m : Nat) * ((314159 : ℚ)/100000)^m)

def retainedMass (n d : Nat) : Nat := (shellArray n d).toList.sum

def numeratorWith (d n : Nat) (a : Array Nat) : Nat :=
  ((List.range 64).map (fun j => a[j+1]! * reciprocalUnits d (j+1))).sum +
    (4^(d*n) - a.toList.sum) * reciprocalUnits d 65

def energyUpperWith (d n : Nat) (a : Array Nat) : ℚ :=
  (numeratorWith d n a : ℚ) / ((scale * central n ^ d : Nat) : ℚ)

def energyUpper (d n : Nat) : ℚ := energyUpperWith d n (shellArray n d)

def FiniteCheck (d n : Nat) : Prop :=
  0 < central n ∧ retainedMass n d ≤ 4^(d*n) ∧
    lambdaUpper d * energyUpper d n + 3/1100 < d * harmonic n

instance (d n : Nat) : Decidable (FiniteCheck d n) := inferInstanceAs
  (Decidable (0 < central n ∧ retainedMass n d ≤ 4^(d*n) ∧
    lambdaUpper d * energyUpper d n + 3/1100 < d * harmonic n))

/-- Exact integer criterion for an upward-rounded reciprocal square root. -/
theorem reciprocal_sqrt_le {S U q d : Nat} (hS : 0 < S) (hq : 0 < q)
    (h : S^2 ≤ U^2 * q^d) :
    1 / Real.sqrt ((q : ℝ)^d) ≤ (U : ℝ) / (S : ℝ) := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hqp : (0 : ℝ) < (q : ℝ)^d := pow_pos (by exact_mod_cast hq) _
  have hr : 0 < Real.sqrt ((q : ℝ)^d) := Real.sqrt_pos.2 hqp
  have hr2 := Real.sq_sqrt (le_of_lt hqp)
  have hu : (0 : ℝ) ≤ U := by positivity
  have hh : (S : ℝ)^2 ≤ (U : ℝ)^2 * (q : ℝ)^d := by exact_mod_cast h
  have he : ((U : ℝ) * Real.sqrt ((q : ℝ)^d))^2 = (U : ℝ)^2 * (q : ℝ)^d := by
    rw [mul_pow, hr2]
  have hup : 0 ≤ (U : ℝ) * Real.sqrt ((q : ℝ)^d) := mul_nonneg hu (le_of_lt hr)
  have hmul : (S : ℝ) ≤ (U : ℝ) * Real.sqrt ((q : ℝ)^d) := by
    nlinarith [sq_nonneg ((U : ℝ)*Real.sqrt ((q : ℝ)^d)-(S : ℝ))]
  apply (div_le_div_iff₀ hr hs).2
  simpa using hmul

/-- The reciprocal square root is exactly the manuscript's q^(-d/2). -/
theorem reciprocal_sqrt_eq_rpow (q d : Nat) (hq : 0 < q) :
    1 / Real.sqrt ((q : ℝ)^d) = (q : ℝ)^(-(d : ℝ)/2) := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0]
  rw [one_div, ← Real.rpow_neg hq0]
  congr 1
  ring

end Legacy.BecknerOnofri.FiniteScalar
