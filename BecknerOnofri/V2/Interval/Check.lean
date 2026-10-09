module

public import BecknerOnofri.V2.Interval.Prog

@[expose] public section

/-!
# Cell checker: the three rows of the d12 scalar verification

(G13.)  Mirrors `check_range`/`bounds` of `verify_explicit_family.py`.
Cell `k` of a row `[a,b]` with `N` cells is `[a + (b-a)k/N, a + (b-a)(k+1)/N]`, written with the
common denominator `aD*bD*N`.  All comparisons are exact integer cross-multiplications.
-/

namespace BecknerOnofri.V2.Interval

/-- A closed cell `[lo/den, hi/den]`. -/
structure Cell where
  lo : Int
  hi : Int
  den : Nat
deriving Repr

def Cell.ctx (c : Cell) : Ctx :=
  { rad := Iv.ofRat2 (-(c.hi - c.lo)) (2 * c.den) (c.hi - c.lo) (2 * c.den)
    center := Iv.ofRat (c.lo + c.hi) (2 * c.den)
    cell := Iv.ofRat2 c.lo c.den c.hi c.den }

/-- A row of the table: the range `[aN/aD, bN/bD]`, the number of cells, the three
rational margins `(num, den)`, and whether the first-row (fourth-derivative) test applies. -/
structure Row where
  small : Bool
  aN : Int
  aD : Nat
  bN : Int
  bD : Nat
  count : Nat
  m0 : Int × Nat
  m1 : Int × Nat
  m2 : Int × Nat

def Row.cell (r : Row) (k : Nat) : Cell :=
  let den := r.aD * r.bD * r.count
  let base : Int := r.aN * r.bD * r.count
  let step : Int := r.bN * r.aD - r.aN * r.bD
  { lo := base + step * k, hi := base + step * (k + 1), den := den }

/-- `a/b > c/d` for positive denominators. -/
def gtQ (a : Int) (b : Nat) (c : Int) (d : Nat) : Bool := decide (c * b < a * d)
/-- `a/b < c/d` for positive denominators. -/
def ltQ (a : Int) (b : Nat) (c : Int) (d : Nat) : Bool := decide (a * d < c * b)

/-- The two-sided Taylor enclosure (eq:taylorbound) intersected with the box, as rationals
`(num, den)` with common denominator `scale * rd^6`: returns `(lower, upper)` numerators. -/
def taylorEnclosure (mid box : Jet) (rn : Int) (rd : Nat) : Int × Int :=
  let err : Int := (List.range 5).foldl
    (fun acc k0 => acc + ((mid.get (k0 + 1)).absup : Int) * rn ^ (k0 + 1) * (rd : Int) ^ (5 - k0))
    ((box.get 6).absup * rn ^ 6)
  let c0 := mid.get 0
  let rd6 : Int := (rd : Int) ^ 6
  let low := c0.lo * rd6 - err
  let high := c0.hi * rd6 + err
  let bl := (box.get 0).lo * rd6
  let bh := (box.get 0).hi * rd6
  (max low bl, min high bh)

/-- `gtQ`-test of the first-row margins of a single quantity. -/
def Row.okLow (m : Int × Nat) (e : Int × Int) (den : Nat) : Bool :=
  decide (e.1 ≤ e.2) && gtQ e.1 den m.1 m.2

/-- Taylor-type test of the register `i` against the margin `m`: the lower end of the
Taylor-and-box enclosure over the cell `c` exceeds `m` (exact integer cross-multiplication). -/
def Row.okAt (c : Cell) (st : RS) (m : Int × Nat) (i : Nat) : Bool :=
  match st.get i with
  | some cj =>
    Row.okLow m (taylorEnclosure cj.mid cj.box (c.hi - c.lo) (2 * c.den))
      (scale.toNat * (2 * c.den) ^ 6)
  | none => false

/-- First-row test for the register `i` of `f`: `f⁗/4! - 1/10 > m` (box entry 4). -/
def Row.okSmallF (m : Int × Nat) (st : RS) (i : Nat) : Bool :=
  match st.get i with
  | some fj => gtQ (fj.box.get 4).lo scale.toNat (1 * m.2 + 10 * m.1) (10 * m.2)
  | none => false

/-- First-row test for the register `i` of `𝒱`: `1/50 - 𝒱⁗/4! > m` (box entry 4). -/
def Row.okSmallV (m : Int × Nat) (st : RS) (i : Nat) : Bool :=
  match st.get i with
  | some vj => ltQ (vj.box.get 4).hi scale.toNat (1 * m.2 - 50 * m.1) (50 * m.2)
  | none => false

/-- First-row test for a register of `e_j + 1/4`: box entry 0 exceeds `m`. -/
def Row.okSmallE (m : Int × Nat) (st : RS) (i : Nat) : Bool :=
  match st.get i with
  | some ej => gtQ (ej.box.get 0).lo scale.toNat m.1 m.2
  | none => false

/-- Check the three margin conditions of a single cell (returns `false` on any failure,
including every arithmetic failure of the interpreter and any out-of-range output register). -/
def Row.checkCell (r : Row) (k : Nat) : Bool :=
  let c := r.cell k
  let pr := familyProg r.small
  match runRS c.ctx pr.1 with
  | none => false
  | some st =>
    if r.small then
      Row.okSmallF r.m0 st pr.2.f && Row.okSmallV r.m1 st pr.2.v &&
        pr.2.e.all (Row.okSmallE r.m2 st)
    else
      Row.okAt c st r.m0 pr.2.f && Row.okAt c st r.m1 pr.2.v &&
        pr.2.e.all (Row.okAt c st r.m2)

/-- Row 1: `[0, 1/8]`, 32 cells, margins `2/5, 3/400, 6/25`. -/
def row1 : Row := ⟨true, 0, 1, 1, 8, 32, (2, 5), (3, 400), (6, 25)⟩
/-- Row 2: `[1/8, 7/8]`, 64 cells, margins `1/100, 7/1000, 9/100`. -/
def row2 : Row := ⟨false, 1, 8, 7, 8, 64, (1, 100), (7, 1000), (9, 100)⟩
/-- Row 3: `[7/8, 99/100]`, 64 cells, margins `1/50, 1/100, 7/250`. -/
def row3 : Row := ⟨false, 7, 8, 99, 100, 64, (1, 50), (1, 100), (7, 250)⟩

/-- The three rows of the verification table. -/
def rows : List Row := [row1, row2, row3]

end BecknerOnofri.V2.Interval
