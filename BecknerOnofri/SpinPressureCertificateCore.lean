module

@[expose] public section

/-!
# Fixed-point Taylor models for Lemma 5.19 (lem:section5-scalar-pressure)

Computational core of the certificate for `t⁴/200 < 𝓑(t)` on `[1/16, 99/100]`.
An interval `⟨lo, hi⟩` of integers stands for `[lo/2¹⁰⁰, hi/2¹⁰⁰]`; every operation rounds
outward. A Taylor model on a cell `t = t₀ + s`, `|s| ≤ h`, is a list of interval
coefficients of `1, s, …, s⁴` and an interval remainder multiplying `s⁵`, together with a
validity flag. This file only contains the (kernel-reducible) algorithms; their soundness is
proved in `SpinPressureCertificateSound*`.
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
/-- Integer power by repeated products. -/
def pow (a : Iv) : Nat → Iv
  | 0 => one
  | k + 1 => mul (pow a k) a
/-- Squaring of an interval containing a positive number. -/
def sqPos (a : Iv) : Iv := ⟨fdiv (max a.lo 0 * max a.lo 0) scale, cdiv (a.hi * a.hi) scale⟩
/-- Iterated `sqPos`. -/
def sqIter (a : Iv) : Nat → Iv
  | 0 => a
  | k + 1 => sqPos (sqIter a k)

end Iv

/-! ### Exponential and logarithm of a fixed-point number -/

/-- Number of halvings bringing `|m|/2¹⁰⁰` below `1/2` (efficiency only, not trusted). -/
def halvings (m : Int) : Nat → Nat
  | 0 => 0
  | f + 1 => if m.natAbs ≤ scale / 2 then 0 else halvings (m / 2) f + 1

/-- Horner evaluation of `∑_{j<n} yʲ/j!` written as `1 + y/1 (1 + y/2 (⋯))`. -/
def expHorner (y : Iv) : Nat → Nat → Iv
  | 0, _ => Iv.one
  | r + 1, j => Iv.add Iv.one (Iv.divNat (Iv.mul y (expHorner y r (j + 1))) j)

/-- Number of Taylor terms used for the exponential of a reduced argument. -/
def expTerms : Nat := 27

/-- Upper fixed-point bound for `|y|ⁿ (n+1)/(n! n)` with `n = 27`, given `mag y`. -/
def expTail (my : Int) : Int :=
  let pw := (List.replicate expTerms ()).foldl (fun p _ => cdiv (p * my) scale) scale
  cdiv (pw * 28) (10888869450418352160768000000 * 27)

/-- Enclosure of `exp (m/2¹⁰⁰)`, together with a flag stating that the reduced argument
satisfies `|y| ≤ 1`. -/
def expPoint (m : Int) : Iv × Bool :=
  let k := halvings m 64
  let y : Iv := ⟨fdiv m (2 ^ k), cdiv m (2 ^ k)⟩
  let h := expHorner y (expTerms - 1) 1
  let e := expTail (Iv.mag y)
  (Iv.sqIter ⟨h.lo - e, h.hi + e⟩ k, decide (Iv.mag y ≤ scale))

/-- Enclosure of `exp` on an interval, with a validity flag. -/
def expIv (a : Iv) : Iv × Bool :=
  let e₁ := expPoint a.lo
  let e₂ := expPoint a.hi
  (⟨e₁.1.lo, e₂.1.hi⟩, e₁.2 && e₂.2)

/-- `log 2 · 2¹⁰⁰`, only used for an unverified first approximation. -/
def lnTwo : Int := 878668439483319573618263538048

/-- Normalize `m > 0` to `m' ∈ [2¹⁰⁰, 2¹⁰¹)`, `m = m' 2^e` (approximately; untrusted). -/
def normalize (m : Int) (e : Int) : Nat → Int × Int
  | 0 => (m, e)
  | f + 1 =>
    if 2 * scale ≤ m then normalize (m / 2) (e + 1) f
    else if m < scale then normalize (m * 2) (e - 1) f else (m, e)

/-- Horner sum for `∑_{i ≤ r} z²ⁱ/(2i+1)` (untrusted approximation). -/
def atanhHorner (z2 : Int) : Nat → Int → Int
  | 0, acc => acc
  | r + 1, acc => atanhHorner z2 r (fdiv scale (2 * r + 1) + fdiv (z2 * acc) scale)

/-- Untrusted approximation of `log (m/2¹⁰⁰) · 2¹⁰⁰`; it is only a candidate,
checked afterwards with `expPoint`. -/
def approxLog (m : Int) : Int :=
  let p := normalize m 0 256
  let z := fdiv ((p.1 - scale) * scale) (p.1 + scale)
  let z2 := fdiv (z * z) scale
  p.2 * lnTwo + 2 * fdiv (z * atanhHorner z2 27 0) scale

/-- Slack added to the approximate logarithm before verification. -/
def logSlack : Int := 1073741824

/-- Verified enclosure of `log` on a positive interval, with a validity flag. -/
def logIv (a : Iv) : Iv × Bool :=
  let l₁ := approxLog a.lo - logSlack
  let l₂ := approxLog a.hi + logSlack
  let e₁ := expPoint l₁
  let e₂ := expPoint l₂
  (⟨l₁, l₂⟩, decide (0 < a.lo) && e₁.2 && e₂.2 && decide (e₁.1.hi ≤ a.lo) &&
    decide (a.hi ≤ e₂.1.lo))

/-! ### Polynomials with interval coefficients -/

/-- Sum of coefficient lists. -/
def padd : List Iv → List Iv → List Iv
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Iv.add a b :: padd p q

/-- Product of coefficient lists. -/
def pmul : List Iv → List Iv → List Iv
  | [], _ => []
  | a :: p, q => padd (q.map (Iv.mul a)) (Iv.zero :: pmul p q)

/-- `∑ₖ pₖ wₖ`, where `wₖ` encloses `sᵏ⁺ⁱ` (the powers list starts at the `i`-th power). -/
def prange : List Iv → List Iv → Iv
  | a :: p, w :: ws => Iv.add (Iv.mul a w) (prange p ws)
  | _, _ => Iv.zero

/-- The polynomial degree of the Taylor models. -/
def degree : Nat := 4

/-- Data of a cell: the midpoint and enclosures of `sᵏ`, `k ≤ 10`, for `|s| ≤ h`. -/
structure Ctx where
  mid : Iv
  pows : List Iv

/-- Upper bounds `hᵏ`, `k < n`, in fixed point. -/
def powBounds (H : Int) : Nat → Int → List Int
  | 0, _ => []
  | n + 1, p => p :: powBounds H n (cdiv (p * H) scale)

/-- Enclosures of `sᵏ` for `|s| ≤ H/2¹⁰⁰`. -/
def powRanges (H : Int) : List Iv :=
  ((powBounds H 11 scale).zip (List.range 11)).map fun (p, k) =>
    if k = 0 then Iv.one else if k % 2 = 0 then ⟨0, p⟩ else ⟨-p, p⟩

/-- The cell `[lo/d, hi/d]`. -/
def mkCtx (lo hi d : Int) : Ctx :=
  ⟨Iv.ofRat (lo + hi) (2 * d), powRanges (cdiv ((hi - lo) * scale) (2 * d))⟩

/-! ### Taylor models -/

/-- A Taylor model: coefficients, remainder (times `s⁵`) and a validity flag. -/
structure TM where
  c : List Iv
  r : Iv
  ok : Bool

namespace TM

/-- Constant model. -/
def const (a : Iv) : TM := ⟨[a], Iv.zero, true⟩
/-- The identity `t = t₀ + s`. -/
def var (x : Ctx) : TM := ⟨[x.mid, Iv.one], Iv.zero, true⟩
/-- An invalid model. -/
def bad : TM := ⟨[], Iv.zero, false⟩
/-- Sum. -/
def add (X Y : TM) : TM := ⟨padd X.c Y.c, Iv.add X.r Y.r, X.ok && Y.ok⟩
/-- Negation. -/
def neg (X : TM) : TM := ⟨X.c.map Iv.neg, Iv.neg X.r, X.ok⟩
/-- Difference. -/
def sub (X Y : TM) : TM := add X (neg Y)
/-- Multiplication by an interval constant. -/
def scal (a : Iv) (X : TM) : TM := ⟨X.c.map (Iv.mul a), Iv.mul a X.r, X.ok⟩
/-- Enclosure of the values on the cell. -/
def range (x : Ctx) (X : TM) : Iv :=
  Iv.add (prange X.c x.pows) (Iv.mul X.r (x.pows.getD (degree + 1) Iv.zero))
/-- Product, truncated at degree four. -/
def mul (x : Ctx) (X Y : TM) : TM :=
  let f := pmul X.c Y.c
  let r := Iv.add (Iv.add (Iv.add (prange (f.drop (degree + 1)) x.pows)
    (Iv.mul X.r (prange Y.c x.pows))) (Iv.mul Y.r (prange X.c x.pows)))
    (Iv.mul (Iv.mul X.r Y.r) (x.pows.getD (degree + 1) Iv.zero))
  ⟨f.take (degree + 1), r, X.ok && Y.ok⟩
/-- Add an interval to the remainder. -/
def addRem (X : TM) (R : Iv) : TM := ⟨X.c, Iv.add X.r R, X.ok⟩
/-- Horner evaluation `c₀ + q (c₁ + q (⋯))` of constant coefficients at a model. -/
def horner (x : Ctx) (q : TM) : List Iv → TM
  | [] => const Iv.zero
  | a :: cs => add (const a) (mul x q (horner x q cs))
/-- The constant coefficient. -/
def head (X : TM) : Iv := X.c.headD Iv.zero
/-- Enclosure of `(X - X(0))/s` from the non-constant coefficients and remainder. -/
def quotRange (x : Ctx) (rest : List Iv) (r : Iv) : Iv :=
  Iv.add (prange rest x.pows) (Iv.mul r (x.pows.getD degree Iv.zero))

/-- Reciprocal: `1/x = (1/α₀) ∑ (-q)ᵏ + (1/α₀) (-q)⁵/(1+q)`. -/
def inv (x : Ctx) (X : TM) : TM :=
  let a₀ := X.head
  let i₀ := Iv.inv a₀
  let rest := X.c.tail.map (Iv.mul i₀)
  let r := Iv.mul i₀ X.r
  let q : TM := ⟨Iv.zero :: rest, r, X.ok⟩
  let U := quotRange x rest r
  let V := range x q
  let R := Iv.neg (Iv.mul (Iv.pow U 5) (Iv.inv (Iv.add Iv.one V)))
  let s := horner x q [Iv.one, Iv.ofInt (-1), Iv.one, Iv.ofInt (-1), Iv.one]
  let Y := scal i₀ (addRem s R)
  ⟨Y.c, Y.r, Y.ok && decide (0 < a₀.lo) && decide (0 < scale + V.lo)⟩

/-- Logarithm: `log x = log α₀ + ∑_{k ≤ 4} (-1)ᵏ⁻¹ qᵏ/k + s⁵ R`. -/
def log (x : Ctx) (X : TM) : TM :=
  let a₀ := X.head
  let i₀ := Iv.inv a₀
  let L := logIv a₀
  let rest := X.c.tail.map (Iv.mul i₀)
  let r := Iv.mul i₀ X.r
  let q : TM := ⟨Iv.zero :: rest, r, X.ok⟩
  let U := quotRange x rest r
  let V := range x q
  let mU := Iv.mag U
  let mV := Iv.mag V
  let B := (Iv.mul (Iv.mul (Iv.pow ⟨mU, mU⟩ 5) ⟨mV, mV⟩) (Iv.inv ⟨scale - mV, scale - mV⟩)).hi
  let R := Iv.add (Iv.mul (Iv.pow U 5) (Iv.ofRat 1 5)) ⟨-B, B⟩
  let s := horner x q [Iv.zero, Iv.one, Iv.ofRat (-1) 2, Iv.ofRat 1 3, Iv.ofRat (-1) 4]
  let Y := add (const L.1) (addRem s R)
  ⟨Y.c, Y.r, Y.ok && L.2 && decide (0 < a₀.lo) && decide (mV < scale)⟩

/-- Exponential: `exp x = exp α₀ (∑_{k ≤ 4} qᵏ/k! + s⁵ R)`. -/
def exp (x : Ctx) (X : TM) : TM :=
  let a₀ := X.head
  let E := expIv a₀
  let rest := X.c.tail
  let q : TM := ⟨Iv.zero :: rest, X.r, X.ok⟩
  let U := quotRange x rest X.r
  let V := range x q
  let mU := Iv.mag U
  let mV := Iv.mag V
  let B := (Iv.mul (Iv.mul (Iv.pow ⟨mU, mU⟩ 5) ⟨mV, mV⟩) (Iv.ofRat 7 4320)).hi
  let R := Iv.add (Iv.mul (Iv.pow U 5) (Iv.ofRat 1 120)) ⟨-B, B⟩
  let s := horner x q [Iv.one, Iv.one, Iv.ofRat 1 2, Iv.ofRat 1 6, Iv.ofRat 1 24]
  let Y := scal E.1 (addRem s R)
  ⟨Y.c, Y.r, Y.ok && E.2 && decide (mV ≤ scale)⟩

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

/-- Powers `z, z², …, zⁿ` of a model (in this order). -/
def powList (x : Ctx) (z : TM) : Nat → TM → List TM
  | 0, _ => []
  | n + 1, p => p :: powList x z n (TM.mul x p z)

/-- `∑_s c_s m_s`. -/
def linComb (cs : List RatPair) (ms : List TM) : TM :=
  TM.sum ((cs.zip ms).map fun (c, m) => TM.scal (ofPair c) m)

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
  let zs := powList x z 12 z
  let ms := zs.map fun zr => TM.mul x (TM.add (TM.mul x pp zr) t5) invDen
  let energy := linComb weightData (ms.map fun m => TM.mul x m m)
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
  let pz := (powList x onez 12 onez).getLastD TM.bad
  let l12 := TM.sub (TM.log x (TM.add (TM.mul x pp pz) (TM.scal (Iv.ofInt 4096) t5))) logDen
  let lqs := (List.range 12).map fun (j : Nat) =>
    TM.add common (TM.add (TM.scal (Iv.ofInt j) lp) (TM.scal (Iv.ofInt (12 - j : Int)) lm))
  let terms := ((((lqs ++ [l12]).zip referenceData).zip coordinateData).zip
    weightedMomentData).map fun (((lq, b), xj), row) =>
      pressureTerm x t mu invTau lq ms b xj row
  let pressure := TM.sum terms
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
