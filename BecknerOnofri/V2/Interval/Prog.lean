module

public import BecknerOnofri.V2.Interval.Jet

@[expose] public section

/-!
# Straight-line programs for the d12 spin family and their interval evaluation

(G13.)  A program is a finite list of `Op`s; operation number `i` produces
register `i` and refers only to earlier registers (checked at run time: a bad reference is a
failure).  The builder `family` emits exactly the operations that
`evaluate(t)` of `verify_explicit_family.py` performs, in the same association order.
-/

namespace BecknerOnofri.V2.Interval

/-- Binomial coefficient by Pascal's rule (kernel friendly). -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Constants appearing in the program; each denotes a rational (or a rounded product). -/
inductive Const
  | q (n : Int) (d : Nat)
  | prod (n₁ : Int) (d₁ : Nat) (n₂ : Int) (d₂ : Nat)
  | inv (n : Int) (d : Nat)
deriving Repr

def Const.toIv : Const → Option Iv
  | .q n d => if 0 < d then some (Iv.ofRat n d) else none
  | .prod n₁ d₁ n₂ d₂ => if 0 < d₁ ∧ 0 < d₂ then some ((Iv.ofRat n₁ d₁).mul (Iv.ofRat n₂ d₂)) else none
  | .inv n d => if 0 < d then (Iv.ofRat n d).recip else none

inductive Op
  | var
  | const (c : Const)
  | add (i j : Nat)
  | neg (i : Nat)
  | mul (i j : Nat)
  | smul (i : Nat) (c : Const)
  | addc (i : Nat) (c : Const)
  | inv (i : Nat)
  | log (i : Nat)
deriving Repr

abbrev Prog := List Op

/-- Interpreter state: the number of registers and the registers, newest first.  (Kernel
evaluation of a left-nested `regs ++ [r]` is quadratic; a reversed cons list is not.) -/
structure RS where
  n : Nat
  rev : List CJet

/-- Register `i` (in creation order). -/
def RS.get (st : RS) (i : Nat) : Option CJet :=
  if i < st.n then st.rev[st.n - 1 - i]? else none

/-- One step of the interpreter. -/
def step (x : Ctx) (st : RS) : Op → Option CJet
  | .var => CJet.var x
  | .const c => (c.toIv).map CJet.const
  | .add i j => do CJet.add x (← st.get i) (← st.get j)
  | .neg i => do CJet.neg x (← st.get i)
  | .mul i j => do CJet.mul x (← st.get i) (← st.get j)
  | .smul i c => do CJet.smul x (← st.get i) (← c.toIv)
  | .addc i c => do CJet.addc x (← st.get i) (← c.toIv)
  | .inv i => do CJet.recip x (← st.get i)
  | .log i => do CJet.log x (← st.get i)

/-- Run a program; `none` if any operation fails. -/
def runRS (x : Ctx) (p : Prog) : Option RS :=
  p.foldlM (fun st op => do
    let r ← step x st op
    pure ⟨st.n + 1, r :: st.rev⟩) ⟨0, []⟩

/-- The registers in creation order. -/
def run (x : Ctx) (p : Prog) : Option (List CJet) := (runRS x p).map fun st => st.rev.reverse

/-! ### Builder -/

structure BS where
  ops : List Op
  n : Nat

abbrev B := StateM BS

def emit (o : Op) : B Nat := modifyGet fun s => (s.n, ⟨o :: s.ops, s.n + 1⟩)

def cst (n : Int) (d : Nat := 1) : B Nat := emit (.const (.q n d))
def addB (a b : Nat) : B Nat := emit (.add a b)
def negB (a : Nat) : B Nat := emit (.neg a)
def mulB (a b : Nat) : B Nat := emit (.mul a b)
def smulB (a : Nat) (n : Int) (d : Nat := 1) : B Nat := emit (.smul a (.q n d))
def sdivB (a : Nat) (n : Int) (d : Nat := 1) : B Nat := emit (.smul a (.inv n d))
def addcB (a : Nat) (n : Int) (d : Nat := 1) : B Nat := emit (.addc a (.q n d))
def invB (a : Nat) : B Nat := emit (.inv a)
def logB (a : Nat) : B Nat := emit (.log a)

/-- `a - b` of the producer: `a + (-b)`. -/
def subB (a b : Nat) : B Nat := do addB a (← negB b)

/-- `a ** n` of the producer (even: `b*b` with `b = a**(n/2)`; odd: `a * a**(n-1)`; `a**0 = 1`),
with explicit fuel so that the kernel unfolds it structurally. -/
def powB (a : Nat) : Nat → Nat → B Nat
  | 0, _ => cst 1
  | fuel + 1, n =>
    if n = 0 then cst 1
    else if n % 2 = 0 then do
      let b ← powB a fuel (n / 2)
      mulB b b
    else do
      let b ← powB a fuel (n - 1)
      mulB a b

/-- Python's `sum(generator)`: left fold starting from the integer `0`. -/
def sumB (xs : List Nat) : B Nat := do
  let z ← cst 0
  xs.foldlM addB z

/-- Exponent-free Pochhammer ingredients, features and weights as exact rationals. -/
def featureNum (s j : Nat) : Int :=
  (List.range (s + 1)).foldl
    (fun acc l => acc + (if l % 2 = 0 then 1 else -1) * (choose (12 - j) l * choose j (s - l) : Nat))
    0

/-- `A_{s,j}` for the order `s` (1 ≤ s ≤ 12): `featureNum s j / C(12,s)`. -/
def featureDen (s : Nat) : Nat := choose 12 s

def weightNum (s : Nat) : Int := (choose 12 s * 2 ^ (s - 1) : Nat)
def weightDen (s : Nat) : Nat := s ^ 6

/-- Which quantities the program returns. -/
structure Outs where
  f : Nat
  v : Nat
  e : List Nat

/-- `evaluate(t, raw)` of the producer, as a straight-line program.
`raw = true` returns `f + 12 t^4/(14-10u)`, `𝒱`, `e_j + 1/4` (first row); `raw = false` returns
`f/t^4 + 12/(14-10u) - 1/10`, `1/50 - 𝒱/t^4`, `e_j + 1/4`. -/
def family (raw : Bool) : B Outs := do
  let t ← emit .var
  let c1 ← cst 1
  let u ← mulB t t
  let t10 ← powB t 12 10
  let L ← smulB t10 9 2
  let lam ← do mulB L (← invB (← addcB L 1))
  let omt ← addB c1 (← negB t)
  let a ← subB t (← mulB L omt)
  let omu ← addB c1 (← negB u)
  let T1 ← do smulB (← powB omu 12 3) 31
  let T2 ← do mulB (← smulB u 61) (← powB omu 12 2)
  let T3 ← do mulB (← mulB (← smulB u 29) u) omu
  let T4 ← do smulB (← powB u 12 3) 11
  let P ← do addB (← addB (← addB T1 T2) T3) T4
  let uu ← mulB u u
  let hden ← do addB (← mulB P omt) (← sdivB uu 10)
  let h ← do mulB (← mulB u omt) (← invB hden)
  let Ap ← do sdivB (← addcB a 1) 2
  let oma ← addB c1 (← negB a)
  let Am ← sdivB oma 2
  -- Pochhammer-type products
  let mut ups : List Nat := [c1]
  let mut downs : List Nat := [c1]
  let mut den := c1
  for k in List.range 12 do
    let kh ← smulB h k
    let nu ← mulB (ups.getLast?.getD c1) (← addB Ap kh)
    let nd ← mulB (downs.getLast?.getD c1) (← addB Am kh)
    ups := ups ++ [nu]
    downs := downs ++ [nd]
    den ← mulB den (← addcB kh 1)
  let omlam ← addB c1 (← negB lam)
  let invden ← invB den
  let mut ps : List Nat := []
  for j in List.range 13 do
    let x1 ← smulB omlam (choose 12 j)
    let x2 ← mulB x1 (ups.getD j c1)
    let x3 ← mulB x2 (downs.getD (12 - j) c1)
    let x4 ← mulB x3 invden
    let x5 ← if j = 12 then addB x4 lam else pure x4
    ps := ps ++ [x5]
  let mut ls : List Nat := []
  for j in List.range 13 do
    ls := ls ++ [← logB (← emit (.smul (ps.getD j c1) (.inv (choose 12 j) 4096)))]
  -- moments and weighted moments
  let mut ms : List Nat := []
  for s0 in List.range 12 do
    let s := s0 + 1
    let mut terms : List Nat := []
    for j in List.range 13 do
      terms := terms ++ [← emit (.smul (ps.getD j c1) (.q (featureNum s j) (featureDen s)))]
    ms := ms.concat (← sumB terms)
  let mut Mp : List Nat := []
  for j in List.range 13 do
    let mut terms : List Nat := []
    for s0 in List.range 12 do
      let s := s0 + 1
      terms := terms ++ [← emit (.smul (ms.getD s0 c1)
        (.prod (weightNum s) (weightDen s) (featureNum s j) (featureDen s)))]
    Mp := Mp ++ [← sumB terms]
  let ent ← do
    let mut terms : List Nat := []
    for j in List.range 13 do
      terms := terms ++ [← mulB (ps.getD j c1) (ls.getD j c1)]
    sumB terms
  let en2 ← do
    let mut terms : List Nat := []
    for s0 in List.range 12 do
      let s := s0 + 1
      terms := terms ++ [← emit (.smul (← powB (ms.getD s0 c1) 12 2) (.q (weightNum s) (weightDen s)))]
    sumB terms
  let f ← do addB (← smulB ent 2) (← negB en2)
  let mut g : List Nat := []
  for j in List.range 13 do
    let y1 ← addcB (ls.getD j c1) 1
    let y2 ← subB y1 (Mp.getD j c1)
    g := g ++ [← smulB y2 2]
  let meang ← do
    let mut terms : List Nat := []
    for j in List.range 13 do
      terms := terms ++ [← mulB (ps.getD j c1) (g.getD j c1)]
    sumB terms
  -- variance of the spin mean
  let vz ← do
    let aa ← mulB a a
    let A1 ← mulB omlam (← addB c1 (← negB aa))
    let A2 ← sdivB A1 12
    let A3 ← mulB A2 (← addcB (← smulB h 12) 1)
    let A4 ← mulB A3 (← invB (← addcB h 1))
    let B1 ← mulB (← mulB lam omlam) (← powB oma 12 2)
    addB A4 B1
  let mut xt : List Nat := []
  for j in List.range 13 do
    xt := xt ++ [← addB (← cst ((j : Int) - 6) 6) (← negB t)]
  let eta ← do
    let mut terms : List Nat := []
    for j in List.range 13 do
      terms := terms ++ [← mulB (← mulB (ps.getD j c1) (xt.getD j c1)) (g.getD j c1)]
    mulB (← sumB terms) (← invB vz)
  let mut e : List Nat := []
  for j in List.range 13 do
    let z1 ← subB (g.getD j c1) meang
    let z2 ← mulB eta (xt.getD j c1)
    e := e ++ [← subB z1 z2]
  let var ← do
    let mut terms : List Nat := []
    for j in List.range 13 do
      terms := terms ++ [← mulB (ps.getD j c1) (← powB (e.getD j c1) 12 2)]
    sumB terms
  let t4 ← powB t 12 4
  let den14 ← do addB (← cst 14) (← negB (← smulB u 10))
  let e' ← e.mapM fun ej => addcB ej 1 4
  if raw then
    let fr ← do addB f (← mulB (← smulB t4 12) (← invB den14))
    pure ⟨fr, var, e'⟩
  else
    let x1 ← mulB f (← invB t4)
    let x2 ← smulB (← invB den14) 12
    let fr ← do addcB (← addB x1 x2) (-1) 10
    let w ← do addB (← cst 1 50) (← negB (← mulB var (← invB t4)))
    pure ⟨fr, w, e'⟩

/-- The program and output registers.  (Irreducible: proofs treat it as opaque; the kernel still
evaluates it.) -/
@[irreducible] def familyProg (raw : Bool) : Prog × Outs :=
  let r := (family raw).run ⟨[], 0⟩
  (r.2.ops.reverse, r.1)

end BecknerOnofri.V2.Interval
