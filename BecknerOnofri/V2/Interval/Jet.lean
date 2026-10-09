module

public import BecknerOnofri.V2.Interval.Arith

@[expose] public section

/-!
# Normalized derivative jets and centered jets (computational core)

(G13.)  Mirrors `TaylorJet` and `CenteredJet` of `verify_explicit_family.py`.
A jet is a list of exactly `7` intervals; entry `k` encloses `a^{(k)}/k!`.  A centered jet
holds `mid` (the jet at the exact cell centre) and `box` (the jet over the whole cell); the
mean-value tightening `box_k ∩ (mid_k + (k+1)[-r,r] box_{k+1})` is applied after every
operation, in descending order `k = 5, …, 0`, and an empty intersection is a failure.
-/

namespace BecknerOnofri.V2.Interval

abbrev Jet := List Iv

namespace Jet

def order : Nat := 6

def zeros : Jet := List.replicate 7 Iv.zero

/-- Constant jet. -/
def const (c : Iv) : Jet := c :: List.replicate 6 Iv.zero

/-- The variable jet `[x, 1, 0, …]`. -/
def var (x : Iv) : Jet := x :: Iv.ofInt 1 :: List.replicate 5 Iv.zero

def get (a : Jet) (k : Nat) : Iv := a.getD k Iv.zero

def add (a b : Jet) : Jet := List.zipWith Iv.add a b

def neg (a : Jet) : Jet := a.map Iv.neg

/-- Cauchy product `c_n = Σ_{k≤n} a_k b_{n-k}`, each product rounded separately. -/
def mul (a b : Jet) : Jet :=
  (List.range 7).map fun n =>
    (List.range (n + 1)).foldl (fun acc k => acc.add ((a.get k).mul (b.get (n - k)))) Iv.zero

/-- Coefficientwise multiplication by an interval constant (producer: `jet * Interval`). -/
def smul (a : Jet) (c : Iv) : Jet := a.map fun x => x.mul c

/-- One step of the reciprocal recurrence; `n = out.length` is the index of the new entry:
`b_n = -(1/a_0) Σ_{k=1}^n a_k b_{n-k}`. -/
def recipStep (a : Jet) (inv0 : Iv) (out : List Iv) : List Iv :=
  let n := out.length
  let s := (List.range n).foldl
    (fun acc k0 => acc.add ((a.get (k0 + 1)).mul (out.getD (n - (k0 + 1)) Iv.zero))) Iv.zero
  out ++ [s.neg.mul inv0]

/-- The first `N + 1` reciprocal entries. -/
def recipFold (a : Jet) (inv0 b0 : Iv) : Nat → List Iv
  | 0 => [b0]
  | N + 1 => recipStep a inv0 (recipFold a inv0 b0 N)

/-- Reciprocal: `b_0 = 1/a_0`, `b_n = -(1/a_0) Σ_{k=1}^n a_k b_{n-k}`. -/
def recip (a : Jet) : Option Jet := do
  let b0 ← (a.get 0).recip
  let inv0 ← (a.get 0).recip
  pure (recipFold a inv0 b0 6)

/-- One step of the logarithm recurrence; `n = out.length` is the index of the new entry:
`ℓ_n = (n a_n - Σ_{k=1}^{n-1} k ℓ_k a_{n-k}) / (n a_0)`. -/
def logStep (a : Jet) (out : List Iv) : Option (List Iv) :=
  let n := out.length
  let s := (List.range (n - 1)).foldl
    (fun acc k0 => acc.add (((out.getD (k0 + 1) Iv.zero).mul (Iv.ofInt (k0 + 1))).mul
      (a.get (n - (k0 + 1))))) Iv.zero
  let num := ((a.get n).mul (Iv.ofInt n)).add s.neg
  (((a.get 0).mul (Iv.ofInt n)).recip).map fun den => out ++ [num.mul den]

/-- The first `N + 1` logarithm entries. -/
def logFold (a : Jet) (l0 : Iv) : Nat → Option (List Iv)
  | 0 => some [l0]
  | N + 1 => (logFold a l0 N).bind (logStep a)

/-- Logarithm: `ℓ_0 = log a_0`, `ℓ_n = (n a_n - Σ_{k=1}^{n-1} k ℓ_k a_{n-k}) / (n a_0)`. -/
def log (a : Jet) : Option Jet := do
  let l0 ← (a.get 0).log
  logFold a l0 6

end Jet

/-- Context of a cell: the radius enclosure `Interval(-r, r)`, the centre enclosure
`Interval(m)` and the cell enclosure `Interval(lo, hi)`. -/
structure Ctx where
  rad : Iv
  center : Iv
  cell : Iv

/-- A centered jet. -/
structure CJet where
  mid : Jet
  box : Jet

namespace CJet

/-- Mean-value tightening, descending: processes the indices `j-1, …, 0` of the `acc`
(which holds the already tightened entries `j, …, 6`), failing on an empty intersection. -/
def tightGo (x : Ctx) (mid box : Jet) : Nat → List Iv → Option (List Iv)
  | 0, acc => some acc
  | j + 1, acc =>
    let next := acc.headD Iv.zero
    let cand := (mid.get j).add ((x.rad.mul (Iv.ofInt (j + 1))).mul next)
    ((box.get j).meet? cand).bind fun new => tightGo x mid box j (new :: acc)

/-- Mean-value tightening, descending in `k = 5, …, 0`, failing on an empty intersection. -/
def tight (x : Ctx) (mid box : Jet) : Option Jet := tightGo x mid box 6 [box.get 6]

/-- Smart constructor (the producer's `CenteredJet(mid=…, box=…)`): tightens the box. -/
def build (x : Ctx) (mid box : Jet) : Option CJet := do
  let b ← tight x mid box
  pure ⟨mid, b⟩

def const (c : Iv) : CJet := ⟨Jet.const c, Jet.const c⟩

def var (x : Ctx) : Option CJet :=
  build x (Jet.var x.center) (Jet.var x.cell)

def add (x : Ctx) (a b : CJet) : Option CJet := build x (a.mid.add b.mid) (a.box.add b.box)

def neg (x : Ctx) (a : CJet) : Option CJet := build x a.mid.neg a.box.neg

def mul (x : Ctx) (a b : CJet) : Option CJet := build x (a.mid.mul b.mid) (a.box.mul b.box)

def smul (x : Ctx) (a : CJet) (c : Iv) : Option CJet := build x (a.mid.smul c) (a.box.smul c)

def addc (x : Ctx) (a : CJet) (c : Iv) : Option CJet :=
  build x (a.mid.add (Jet.const c)) (a.box.add (Jet.const c))

def recip (x : Ctx) (a : CJet) : Option CJet := do
  let m ← a.mid.recip
  let b ← a.box.recip
  build x m b

def log (x : Ctx) (a : CJet) : Option CJet := do
  let m ← a.mid.log
  let b ← a.box.log
  build x m b

end CJet

end BecknerOnofri.V2.Interval
