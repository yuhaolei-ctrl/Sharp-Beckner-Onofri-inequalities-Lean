module

@[expose] public section

/-!
# Fixed-point Taylor models for Lemma 5.20 (lem:section5-scalar-pressure)

Computational core of the certificate for `t⁴/200 < 𝓑(t)` on `[1/16, 99/100]`.
An interval `⟨lo, hi⟩` of integers stands for `[lo/2¹⁰⁰, hi/2¹⁰⁰]`; every operation rounds
outward. On a cell `t = t₀ + s`, `|s| ≤ h`, a first-order Taylor model `⟨c₀, c₁, r, ok⟩`
encloses a function `f` if, at every such `s`, `f(t₀ + s) = a₀ + a₁ s + ρ s²` with
`a₀ ∈ c₀`, `a₁ ∈ c₁`, `ρ ∈ r` (when `ok`). Reciprocals, logarithms and exponentials are
expanded to second order around the constant coefficient, with explicit remainders.
This file only contains the kernel-reducible algorithms; their soundness is proved in
`SpinPressureCertificateSound*`.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

/-- The fixed-point scale `2¹⁰⁰`. -/
def scale : Int := 1267650600228229401496703205376

/-- Floor division by a positive integer. -/
def fdiv (a b : Int) : Int := a / b

/-- Ceiling division by a positive integer. -/
def cdiv (a b : Int) : Int := -((-a) / b)

/-- An interval `[lo/2¹⁰⁰, hi/2¹⁰⁰]`. -/
structure Iv where
  lo : Int
  hi : Int

namespace Iv

/-- The zero interval. -/
def zero : Iv := ⟨0, 0⟩
/-- The interval `[1, 1]`. -/
def one : Iv := ⟨scale, scale⟩
/-- Interval sum. -/
def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩
/-- Interval negation. -/
def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩
/-- Outward-rounded interval product. -/
def mul (a b : Iv) : Iv :=
  let p₁ := a.lo * b.lo
  let p₂ := a.lo * b.hi
  let p₃ := a.hi * b.lo
  let p₄ := a.hi * b.hi
  ⟨fdiv (min (min p₁ p₂) (min p₃ p₄)) scale, cdiv (max (max p₁ p₂) (max p₃ p₄)) scale⟩
/-- Enclosure of the rational `n/d` (`d > 0`). -/
def ofRat (n d : Int) : Iv := ⟨fdiv (n * scale) d, cdiv (n * scale) d⟩
/-- The integer `k`. -/
def ofInt (k : Int) : Iv := ⟨k * scale, k * scale⟩
/-- Reciprocal of a positive interval. -/
def inv (a : Iv) : Iv := ⟨fdiv (scale * scale) a.hi, cdiv (scale * scale) a.lo⟩
/-- Division by a positive natural number. -/
def divNat (a : Iv) (n : Nat) : Iv := ⟨fdiv a.lo n, cdiv a.hi n⟩
/-- The magnitude `max |lo| |hi|` (in fixed point). -/
def mag (a : Iv) : Int := max a.lo.natAbs a.hi.natAbs
/-- Enclosure `[0, mag²]` of the squares of the elements. -/
def sq (a : Iv) : Iv := ⟨0, cdiv (a.mag * a.mag) scale⟩
/-- Squaring of an interval containing a positive number. -/
def sqPos (a : Iv) : Iv := ⟨fdiv (max a.lo 0 * max a.lo 0) scale, cdiv (a.hi * a.hi) scale⟩
/-- Iterated `sqPos`. -/
def sqIter (a : Iv) : Nat → Iv
  | 0 => a
  | k + 1 => sqPos (sqIter a k)

end Iv

/-! ### Exponential and logarithm of a fixed-point number -/

/-- Number of halvings bringing `|m|/2¹⁰⁰` below `1/64` (efficiency only, not trusted). -/
def halvings (m : Int) : Nat → Nat
  | 0 => 0
  | f + 1 => if m.natAbs ≤ scale / 64 then 0 else halvings (m / 2) f + 1

/-- Horner evaluation of `∑_{j<n} yʲ/j!` written as `1 + y/1 (1 + y/2 (⋯))`. -/
def expHorner (y : Iv) : Nat → Nat → Iv
  | 0, _ => Iv.one
  | r + 1, j => Iv.add Iv.one (Iv.divNat (Iv.mul y (expHorner y r (j + 1))) j)

/-- Upper bounds `⌈mⁿ⌉` of the powers of a fixed-point number. -/
def powUp (m : Int) : Nat → Int
  | 0 => scale
  | n + 1 => cdiv (powUp m n * m) scale

/-- Upper fixed-point bound for `|y|¹⁴ · 15/(14! · 14)`, given `|y| ≤ m`. -/
def expTail (m : Int) : Int := cdiv (powUp m 14 * 15) 1220496076800

/-- Enclosure of `exp (m/2¹⁰⁰)` with a flag stating that the reduced argument has
`|y| ≤ 1`. -/
def expPoint (m : Int) : Iv × Bool :=
  let k := halvings m 64
  let y : Iv := ⟨fdiv m (2 ^ k), cdiv m (2 ^ k)⟩
  let h := expHorner y 13 1
  let e := expTail y.mag
  (Iv.sqIter ⟨h.lo - e, h.hi + e⟩ k, decide (y.mag ≤ scale))

/-- Enclosure of `exp` on an interval, with a validity flag. -/
def expIv (a : Iv) : Iv × Bool :=
  let e := expPoint a.lo
  let w := a.hi - a.lo
  (⟨e.1.lo, cdiv (e.1.hi * scale) (scale - w)⟩, e.2 && decide (0 ≤ w) && decide (w < scale))

/-- `log 2 · 2¹⁰⁰`, only used for an unverified first approximation. -/
def lnTwo : Int := 878668439483319573618263538048

/-- Normalize `m > 0` to `m' ∈ [2¹⁰⁰, 2¹⁰¹)`, `m ≈ m' 2^e` (untrusted). -/
def normalize (m : Int) (e : Int) : Nat → Int × Int
  | 0 => (m, e)
  | f + 1 =>
    if 2 * scale ≤ m then normalize (m / 2) (e + 1) f
    else if m < scale then normalize (m * 2) (e - 1) f else (m, e)

/-- Horner sum for `∑_{i < r} z²ⁱ/(2i+1)` (untrusted approximation). -/
def atanhHorner (z2 : Int) : Nat → Int → Int
  | 0, acc => acc
  | r + 1, acc => atanhHorner z2 r (fdiv scale (2 * r + 1) + fdiv (z2 * acc) scale)

/-- Untrusted approximation of `log (m/2¹⁰⁰) · 2¹⁰⁰`; it is only a candidate, checked
afterwards with `expPoint`. -/
def approxLog (m : Int) : Int :=
  let p := normalize m 0 256
  let z := fdiv ((p.1 - scale) * scale) (p.1 + scale)
  let z2 := fdiv (z * z) scale
  p.2 * lnTwo + 2 * fdiv (z * atanhHorner z2 27 0) scale

/-- Slack `2⁻⁷⁰` (in fixed point) of the verified logarithm. -/
def logSlack : Int := 1073741824

/-- Verified enclosure of `log` on a positive interval, with a validity flag. -/
def logIv (a : Iv) : Iv × Bool :=
  let L := approxLog a.lo
  let e := expPoint L
  (⟨L - logSlack, L + logSlack + cdiv ((a.hi - a.lo) * scale) a.lo⟩,
    e.2 && decide (0 < a.lo) && decide (e.1.hi * scale ≤ a.lo * (scale + logSlack)) &&
      decide (a.lo * scale ≤ e.1.lo * (scale + logSlack)) && decide (a.lo ≤ a.hi))

/-! ### First-order Taylor models -/

/-- Data of a cell: the midpoint and enclosures of `s` and `s²` for `|s| ≤ h`. -/
structure Ctx where
  mid : Iv
  s1 : Iv
  s2 : Iv

/-- The cell `[lo/d, hi/d]`. -/
def mkCtx (lo hi d : Int) : Ctx :=
  let H := cdiv ((hi - lo) * scale) (2 * d)
  ⟨Iv.ofRat (lo + hi) (2 * d), ⟨-H, H⟩, ⟨0, cdiv (H * H) scale⟩⟩

/-- A model `c₀ + c₁ s + r s²` with a validity flag. -/
structure TM where
  c0 : Iv
  c1 : Iv
  r : Iv
  ok : Bool

namespace TM

/-- Constant model. -/
def const (a : Iv) : TM := ⟨a, Iv.zero, Iv.zero, true⟩
/-- The identity `t = t₀ + s`. -/
def var (x : Ctx) : TM := ⟨x.mid, Iv.one, Iv.zero, true⟩
/-- Sum. -/
def add (X Y : TM) : TM := ⟨X.c0.add Y.c0, X.c1.add Y.c1, X.r.add Y.r, X.ok && Y.ok⟩
/-- Negation. -/
def neg (X : TM) : TM := ⟨X.c0.neg, X.c1.neg, X.r.neg, X.ok⟩
/-- Difference. -/
def sub (X Y : TM) : TM := add X (neg Y)
/-- Multiplication by an interval constant. -/
def scal (a : Iv) (X : TM) : TM := ⟨a.mul X.c0, a.mul X.c1, a.mul X.r, X.ok⟩
/-- Enclosure of the linear part `c₀ + c₁ s`. -/
def lin (x : Ctx) (X : TM) : Iv := X.c0.add (X.c1.mul x.s1)
/-- Enclosure of the values on the cell. -/
def range (x : Ctx) (X : TM) : Iv := (lin x X).add (X.r.mul x.s2)
/-- Product. -/
def mul (x : Ctx) (X Y : TM) : TM :=
  ⟨X.c0.mul Y.c0, (X.c0.mul Y.c1).add (X.c1.mul Y.c0),
    (((X.c1.mul Y.c1).add (X.r.mul (lin x Y))).add (Y.r.mul (lin x X))).add
      ((X.r.mul Y.r).mul x.s2), X.ok && Y.ok⟩

/-- Reciprocal: `1/x = (1/α₀)(1 - q + q²/(1+q))`, `q = (x - α₀)/α₀ = s u`. -/
def inv (x : Ctx) (X : TM) : TM :=
  let i₀ := X.c0.inv
  let q₁ := X.c1.mul i₀
  let qr := X.r.mul i₀
  let U := q₁.add (qr.mul x.s1)
  let V := (q₁.mul x.s1).add (qr.mul x.s2)
  let R := U.sq.mul (Iv.one.add V).inv
  let Y := scal i₀ ⟨Iv.one, q₁.neg, qr.neg.add R, true⟩
  ⟨Y.c0, Y.c1, Y.r, X.ok && decide (0 < X.c0.lo) && decide (0 < scale + V.lo)⟩

/-- Logarithm: `log x = log α₀ + q - q²/2 + E`, `|E| ≤ |q|³/(1-|q|)`. -/
def log (x : Ctx) (X : TM) : TM :=
  let i₀ := X.c0.inv
  let L := logIv X.c0
  let q₁ := X.c1.mul i₀
  let qr := X.r.mul i₀
  let U := q₁.add (qr.mul x.s1)
  let V := (q₁.mul x.s1).add (qr.mul x.s2)
  let mV := V.mag
  let B := ((U.sq.mul ⟨mV, mV⟩).mul (Iv.inv ⟨scale - mV, scale - mV⟩)).hi
  let R := (U.sq.divNat 2).neg.add ⟨-B, B⟩
  ⟨L.1, q₁, qr.add R, X.ok && L.2 && decide (0 < X.c0.lo) && decide (mV < scale)⟩

/-- Exponential: `exp x = exp α₀ (1 + q + q²/2 + E)`, `|E| ≤ 2|q|³/9`. -/
def exp (x : Ctx) (X : TM) : TM :=
  let E := expIv X.c0
  let U := X.c1.add (X.r.mul x.s1)
  let V := (X.c1.mul x.s1).add (X.r.mul x.s2)
  let mV := V.mag
  let B := ((U.sq.mul ⟨mV, mV⟩).mul (Iv.ofRat 2 9)).hi
  let R := (U.sq.divNat 2).add ⟨-B, B⟩
  let Y := scal E.1 ⟨Iv.one, X.c1, X.r.add R, true⟩
  ⟨Y.c0, Y.c1, Y.r, X.ok && E.2 && decide (mV ≤ scale)⟩

/-- Sum of a list of models. -/
def sum : List TM → TM
  | [] => const Iv.zero
  | X :: Xs => add X (sum Xs)

end TM

/-! ### The scalar `𝓑(t) - t⁴/200` -/

/-- A rational `n/d` as a pair. -/
abbrev RatPair := Int × Int

/-- `w_s`, `s = 1, …, 12`. -/
def weightData : List RatPair :=
  [(12, 1), (33, 16), (880, 729), (495, 512), (12672, 15625), (154, 243), (50688, 117649),
    (495, 2048), (56320, 531441), (528, 15625), (12288, 1771561), (1, 1458)]

/-- `b_j`. -/
def referenceData : List RatPair :=
  [(1, 4096), (3, 1024), (33, 2048), (55, 1024), (495, 4096), (99, 512), (231, 1024),
    (99, 512), (495, 4096), (55, 1024), (33, 2048), (3, 1024), (1, 4096)]

/-- `x_j`. -/
def coordinateData : List RatPair :=
  [(-1, 1), (-5, 6), (-2, 3), (-1, 2), (-1, 3), (-1, 6), (0, 1), (1, 6), (1, 3), (1, 2),
    (2, 3), (5, 6), (1, 1)]

/-- Rows `(w_s A_{s,j})_s` for `j = 0, …, 12`. -/
def weightedMomentData : List (List RatPair) :=
  [[(-12, 1), (33, 16), (-880, 729), (495, 512), (-12672, 15625), (154, 243),
      (-50688, 117649), (495, 2048), (-56320, 531441), (528, 15625), (-12288, 1771561),
      (1, 1458)],
    [(-10, 1), (11, 8), (-440, 729), (165, 512), (-2112, 15625), (0, 1), (8448, 117649),
      (-165, 2048), (28160, 531441), (-352, 15625), (10240, 1771561), (-1, 1458)],
    [(-8, 1), (13, 16), (-160, 729), (15, 512), (768, 15625), (-14, 243), (3072, 117649),
      (15, 2048), (-10240, 531441), (208, 15625), (-8192, 1771561), (1, 1458)],
    [(-6, 1), (3, 8), (-8, 729), (-27, 512), (576, 15625), (0, 1), (-2304, 117649),
      (27, 2048), (512, 531441), (-96, 15625), (6144, 1771561), (-1, 1458)],
    [(-4, 1), (1, 16), (16, 243), (-17, 512), (-128, 15625), (14, 729), (-512, 117649),
      (-17, 2048), (1024, 177147), (16, 15625), (-4096, 1771561), (1, 1458)],
    [(-2, 1), (-1, 8), (40, 729), (5, 512), (-64, 3125), (0, 1), (1280, 117649),
      (-5, 2048), (-2560, 531441), (32, 15625), (2048, 1771561), (-1, 1458)],
    [(0, 1), (-3, 16), (0, 1), (15, 512), (0, 1), (-10, 729), (0, 1), (15, 2048), (0, 1),
      (-48, 15625), (0, 1), (1, 1458)],
    [(2, 1), (-1, 8), (-40, 729), (5, 512), (64, 3125), (0, 1), (-1280, 117649),
      (-5, 2048), (2560, 531441), (32, 15625), (-2048, 1771561), (-1, 1458)],
    [(4, 1), (1, 16), (-16, 243), (-17, 512), (128, 15625), (14, 729), (512, 117649),
      (-17, 2048), (-1024, 177147), (16, 15625), (4096, 1771561), (1, 1458)],
    [(6, 1), (3, 8), (8, 729), (-27, 512), (-576, 15625), (0, 1), (2304, 117649),
      (27, 2048), (-512, 531441), (-96, 15625), (-6144, 1771561), (-1, 1458)],
    [(8, 1), (13, 16), (160, 729), (15, 512), (-768, 15625), (-14, 243), (-3072, 117649),
      (15, 2048), (10240, 531441), (208, 15625), (8192, 1771561), (1, 1458)],
    [(10, 1), (11, 8), (440, 729), (165, 512), (2112, 15625), (0, 1), (-8448, 117649),
      (-165, 2048), (-28160, 531441), (-352, 15625), (-10240, 1771561), (-1, 1458)],
    [(12, 1), (33, 16), (880, 729), (495, 512), (12672, 15625), (154, 243),
      (50688, 117649), (495, 2048), (56320, 531441), (528, 15625), (12288, 1771561),
      (1, 1458)]]

/-- Enclosure of a rational pair. -/
def ofPair (p : RatPair) : Iv := Iv.ofRat p.1 p.2

/-- Powers `p, p z, …, p zⁿ⁻¹` of a model. -/
def powList (x : Ctx) (z : TM) : Nat → TM → List TM
  | 0, _ => []
  | n + 1, p => p :: powList x z n (TM.mul x p z)

/-- The power `z^(n+1)` of a model. -/
def powModel (x : Ctx) (z : TM) : Nat → TM
  | 0 => z
  | n + 1 => TM.mul x (powModel x z n) z

/-- `∑_{i<n} F i`. -/
def sumRange (n : Nat) (F : Nat → TM) : TM := TM.sum ((List.range n).map F)

/-- `∑_{i<12} cᵢ mᵢ` for rational coefficients `cᵢ`. -/
def linComb (cs : List RatPair) (ms : List TM) : TM :=
  sumRange 12 fun i => TM.scal (ofPair (cs.getD i (0, 1))) (ms.getD i (TM.const Iv.zero))

/-- The moments `m_s = (4(1-t) zˢ + t⁵)/(4 - 4t + t⁵)`, `s = 1, …, 12`. -/
def momentModels (x : Ctx) (pp t5 invDen z : TM) : List TM :=
  (powList x z 12 z).map fun zr => TM.mul x (TM.add (TM.mul x pp zr) t5) invDen

/-- The logarithm `log (q_j/b_j)`. -/
def logRatioModel (common lp lm l12 : TM) (j : Nat) : TM :=
  if j < 12 then
    TM.add common (TM.add (TM.scal (Iv.ofInt j) lp) (TM.scal (Iv.ofInt (12 - j : Int)) lm))
  else l12

/-- The `j`-th summand `b_j exp(E_j)` of the pressure sum (eq:12-pressure-cancellation). -/
def pressureTerm (x : Ctx) (t mu invTau lq : TM) (ms : List TM) (b xj : RatPair)
    (row : List RatPair) : TM :=
  let lin := linComb row ms
  let ex := TM.add (TM.add (TM.scal (Iv.ofRat (-43) 25) lq) (TM.scal (Iv.ofInt 2) lin))
    (TM.mul x mu (TM.sub (TM.const (ofPair xj)) t))
  TM.scal (ofPair b) (TM.exp x (TM.mul x ex invTau))

/-- Taylor model of `𝓑(t) - t⁴/200` on the cell `x`. -/
def scalarModel (x : Ctx) : TM :=
  let t := TM.var x
  let t2 := TM.mul x t t
  let t3 := TM.mul x t2 t
  let t4 := TM.mul x t2 t2
  let t5 := TM.mul x t4 t
  let t8 := TM.mul x t4 t4
  let t10 := TM.mul x t5 t5
  let z := TM.sub t (TM.scal (Iv.ofRat 1 4) t5)
  let pp := TM.sub (TM.const (Iv.ofInt 4)) (TM.scal (Iv.ofInt 4) t)
  let den := TM.add pp t5
  let invDen := TM.inv x den
  let ms := momentModels x pp t5 invDen z
  let energy := sumRange 12 fun i =>
    TM.scal (ofPair (weightData.getD i (0, 1)))
      (TM.mul x (ms.getD i (TM.const Iv.zero)) (ms.getD i (TM.const Iv.zero)))
  let half := TM.inv x (TM.sub (TM.const Iv.one) (TM.scal (Iv.ofRat 1 2) t2))
  let eta := TM.mul x (TM.mul x (TM.sub (TM.const Iv.one) t2)
    (TM.add (TM.scal (Iv.ofRat 9 20) t2) (TM.scal (Iv.ofRat 297 100) t8))) half
  let tau := TM.add (TM.const (Iv.ofRat 7 25)) eta
  let invTau := TM.inv x tau
  let mu := TM.mul x (TM.scal (Iv.ofRat 5 2) t3) half
  let logDen := TM.log x den
  let common := TM.sub (TM.log x pp) logDen
  let onez := TM.add (TM.const Iv.one) z
  let lp := TM.log x onez
  let lm := TM.log x (TM.sub (TM.const Iv.one) z)
  let l12 := TM.sub (TM.log x (TM.add (TM.mul x pp (powModel x onez 11))
    (TM.scal (Iv.ofInt 4096) t5))) logDen
  let pressure := sumRange 13 fun j =>
    pressureTerm x t mu invTau (logRatioModel common lp lm l12 j) ms
      (referenceData.getD j (0, 1)) (coordinateData.getD j (0, 1)) (weightedMomentData.getD j [])
  let psi := TM.add (TM.scal (Iv.ofRat 3 40) t4) (TM.scal (Iv.ofRat 33 200) t10)
  let onet := TM.add (TM.const Iv.one) t
  let onemt := TM.sub (TM.const Iv.one) t
  let bent := TM.scal (Iv.ofRat 1 2)
    (TM.add (TM.mul x onet (TM.log x onet)) (TM.mul x onemt (TM.log x onemt)))
  TM.sub (TM.sub (TM.sub (TM.add energy (TM.scal (Iv.ofInt 12) psi))
    (TM.scal (Iv.ofInt 12) (TM.mul x eta bent))) (TM.mul x tau (TM.log x pressure)))
    (TM.scal (Iv.ofRat 1 200) t4)

/-- The cell check: the model is valid and its range on `[lo/d, hi/d]` is positive. -/
def checkCell (lo hi d : Int) : Bool :=
  let x := mkCtx lo hi d
  let X := scalarModel x
  X.ok && decide (0 < (TM.range x X).lo) && decide (0 < d) && decide (lo ≤ hi)

end BecknerOnofri.HighDim.Spin.PressureCertificate
