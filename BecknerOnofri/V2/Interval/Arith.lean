module

@[expose] public section

/-!
# Dyadic interval arithmetic of the d12 spin verifier (computational core)

(G13.)  This file mirrors `Interval`, `log_point` and `LOG2` of the recovered
producer `verify_explicit_family.py` (SHA-256 2576ddb1...c10b5) using only `Int`/`Nat`.
An interval `⟨lo, hi⟩` stands for `[lo/2^110, hi/2^110]`; lower endpoints are rounded down and
upper endpoints up.  Every operation that can fail (reciprocal of an interval containing zero,
logarithm with nonpositive lower endpoint, empty intersection) returns `none`.  No default
interval is ever produced.

Soundness statements for these operations live in `ArithSound.lean` (needs Mathlib reals).
-/

namespace BecknerOnofri.V2.Interval

/-- `2^110`. -/
def scale : Int := 2 ^ 110

/-- Floor division by a positive integer. -/
def fdiv (a b : Int) : Int := a / b

/-- Ceiling division by a positive integer. -/
def cdiv (a b : Int) : Int := -((-a) / b)

/-- An interval `[lo/2^110, hi/2^110]`, with the invariant `lo ≤ hi` enforced by `mk?`. -/
structure Iv where
  lo : Int
  hi : Int
deriving DecidableEq, Repr

namespace Iv

/-- Checked constructor (`Interval.raw` of the producer): rejects `lo > hi`. -/
def mk? (lo hi : Int) : Option Iv := if lo ≤ hi then some ⟨lo, hi⟩ else none

def zero : Iv := ⟨0, 0⟩

/-- Exact integer `k`. -/
def ofInt (k : Int) : Iv := ⟨k * scale, k * scale⟩

/-- Outward enclosure of the rational `n/d` (`d > 0`): `Interval(Fraction(n, d))`. -/
def ofRat (n : Int) (d : Nat) : Iv := ⟨fdiv (n * scale) d, cdiv (n * scale) d⟩

/-- Outward enclosure `Interval(lo, hi)` of the rational endpoints `n₁/d₁ ≤ n₂/d₂`. -/
def ofRat2 (n₁ : Int) (d₁ : Nat) (n₂ : Int) (d₂ : Nat) : Iv :=
  ⟨fdiv (n₁ * scale) d₁, cdiv (n₂ * scale) d₂⟩

def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

/-- All four endpoint products, then outward rounding. -/
def mul (a b : Iv) : Iv :=
  let p₁ := a.lo * b.lo
  let p₂ := a.lo * b.hi
  let p₃ := a.hi * b.lo
  let p₄ := a.hi * b.hi
  ⟨fdiv (min (min p₁ p₂) (min p₃ p₄)) scale, cdiv (max (max p₁ p₂) (max p₃ p₄)) scale⟩

/-- Reciprocal of an interval with positive lower endpoint. -/
def recipPos (a : Iv) : Iv := ⟨fdiv (scale * scale) a.hi, cdiv (scale * scale) a.lo⟩

/-- Reciprocal of an interval *not containing zero*; both signs are treated.
Mirrors `Interval.reciprocal`; the negative case is `1/[lo,hi] = -(1/[-hi,-lo])`, which gives
exactly the producer's `[S²//hi, ⌈S²/lo⌉]`, so that only positive divisors occur. -/
def recip (a : Iv) : Option Iv :=
  if 0 < a.lo then some (recipPos a)
  else if a.hi < 0 then some (recipPos a.neg).neg
  else none

/-- `max |lo| |hi|` (the producer's `absup`). -/
def absup (a : Iv) : Int := max a.lo.natAbs a.hi.natAbs

/-- Intersection; an empty intersection is a failure (producer: `Empty intersection`). -/
def meet? (a b : Iv) : Option Iv := mk? (max a.lo b.lo) (min a.hi b.hi)

end Iv

/-! ### Logarithm -/

/-- `lcm(1,3,…,2n-1)`. -/
def oddLcm : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.lcm (oddLcm n) (2 * n + 1)

/-- Numerator of `2 Σ_{n<42} (1/3)^(2n+1)/(2n+1)` over the denominator `3^85 * oddLcm 42`. -/
def log2Num : Nat :=
  (List.range 42).foldl (fun acc n => acc + 2 * 3 ^ (84 - 2 * n) * (oddLcm 42 / (2 * n + 1))) 0

/-- The enclosure of `log 2` of the producer:
`Interval(low, low + 2y^85/(85 (1-y^2)))`, `y = 1/3`, where `2y^85/(85(1-y²)) = 9/(340 · 3^85)`. -/
def log2Iv : Iv :=
  let D : Nat := 3 ^ 85 * oddLcm 42
  ⟨fdiv (log2Num * scale) D, cdiv ((340 * log2Num + 9 * oddLcm 42) * scale) (340 * D)⟩

/-- One step of the atanh series: `(ans, term) ↦ (ans + term * (2/(2n+1)), term * z²)`. -/
def seriesStep (z2 : Iv) (st : Iv × Iv) (n : Nat) : Iv × Iv :=
  (st.1.add (st.2.mul (Iv.ofRat 2 (2 * n + 1))), st.2.mul z2)

/-- The first `m` steps of the series, started at `(0, z)`. -/
def seriesFold (z z2 : Iv) (m : Nat) : Iv × Iv :=
  (List.range m).foldl (seriesStep z2) (Iv.zero, z)

/-- `z = (x-1)/(x+1)` of the producer (fails if the interval `x+1` contains zero). -/
def zOf (x : Iv) : Option Iv :=
  (x.add (Iv.ofInt 1)).recip.map ((x.add (Iv.ofInt 1).neg).mul)

/-- The remainder term `2 z^85 / (85 (1 - z²))` of the producer. -/
def remOf (z2 term : Iv) : Option Iv :=
  (((Iv.ofInt 1).add z2.neg).mul (Iv.ofInt 85)).recip.map fun den => (term.mul (Iv.ofInt 2)).mul den

/-- The 42-term atanh enclosure of `log v` for an interval `x` enclosing `v ∈ [1, 2)`. -/
def logCore (x : Iv) : Option Iv :=
  (zOf x).bind fun z =>
    let z2 := z.mul z
    let st := seriesFold z z2 42
    (remOf z2 st.2).bind fun rem => Iv.mk? st.1.lo (st.1.hi + rem.hi)

/-- The 42-term atanh enclosure of `log (a / 2^110)` for a positive integer `a`
(producer: `log_point`).  `a / 2^110 = 2^k v`, `1 ≤ v < 2`, `z = (v-1)/(v+1)`. -/
def logPoint (a : Int) : Option Iv :=
  let k : Int := (Nat.log2 a.toNat : Int) - 110
  let x : Iv := Iv.ofRat (a * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)
  (logCore x).map fun r => r.add (log2Iv.mul (Iv.ofInt k))

namespace Iv

/-- Logarithm of an interval with positive lower endpoint (monotonicity). -/
def log (a : Iv) : Option Iv :=
  if 0 < a.lo then do
    let l ← logPoint a.lo
    let h ← logPoint a.hi
    mk? l.lo h.hi
  else none

end Iv

end BecknerOnofri.V2.Interval
