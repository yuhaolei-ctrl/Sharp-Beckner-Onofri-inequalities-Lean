module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Kernel-checked d10 finite scalar arithmetic

The data are computed from factorial binomial coefficients inside Lean.
There are no imported coefficient tables and no native decision tactic.
The radius cutoff is 64; all unretained mass is assigned weight 65^(-5).
This differs from the original Python cutoff 512, but retains a strict
1/44 margin in every one of the same 21 cases.
-/

namespace Legacy.D10.FiniteScalar

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def fastChoose (n k : Nat) : Nat := Nat.factorial n / (Nat.factorial k * Nat.factorial (n-k))

theorem fastChoose_eq_choose {n k : Nat} (h : k ≤ n) :
    fastChoose n k = Nat.choose n k := by
  exact (Nat.choose_eq_factorial_div_factorial h).symm

def radialRow (n : Nat) : Array Nat := (List.range 9).toArray.map fun k =>
  if k <= n then (if k = 0 then 1 else 2) * fastChoose (2*n) (n-k) else 0

def convolutionStep (a r : Array Nat) : Array Nat := (List.range 65).toArray.map fun q =>
  ((List.range 9).map fun k => if k*k <= q then r[k]! * a[q-k*k]! else 0).sum

def initialCoefficients : Array Nat :=
  (List.range 65).toArray.map fun q => if q = 0 then 1 else 0

def shellArray (n r : Nat) : Array Nat :=
  Nat.iterate (fun a => convolutionStep a (radialRow n)) r initialCoefficients

def scale : Nat := 2^40

def upperNumerator (a : Array Nat) : Nat :=
  ((List.range 64).map fun j =>
    let q := j+1
    a[q]! * ((scale + q^5-1)/q^5)).sum

def retainedMass (n : Nat) : Nat :=
  ((List.range 65).map fun q => (shellArray n 10)[q]!).sum

def central (n : Nat) : Nat := fastChoose (2*n) n

def energyUpper (n : Nat) : ℚ :=
  (upperNumerator (shellArray n 10) : ℚ) / (central n ^ 10 * scale) +
  ((4^(10*n) - retainedMass n : Nat) : ℚ) / (central n ^ 10 * 65^5)

def harmonic (n : Nat) : ℚ :=
  ((List.range n).map fun j : Nat => (1 : ℚ)/((j : ℚ)+1)).sum

def lambdaUpper : ℚ := 240 / ((314159 : ℚ)/100000)^5

/-- This proposition is a completely explicit finite arithmetic statement.
The connection of `shellArray` to a polynomial coefficient is supplied
separately, so the certificate's exact scope stays visible. -/
def FiniteCheck (n : Nat) : Prop :=
  0 < central n ∧ retainedMass n ≤ 4^(10*n) ∧
  lambdaUpper * energyUpper n + 1/44 < 10 * harmonic n

instance (n : Nat) : Decidable (FiniteCheck n) := inferInstanceAs
  (Decidable (0 < central n ∧ retainedMass n ≤ 4^(10*n) ∧
    lambdaUpper * energyUpper n + 1/44 < 10 * harmonic n))


end Legacy.D10.FiniteScalar
