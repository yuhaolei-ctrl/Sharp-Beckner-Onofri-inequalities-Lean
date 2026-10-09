module

public import BecknerOnofri.V2.Interval.BuilderLoops

@[expose] public section

/-!
# A structured version of the family builder

`family2` emits exactly the same operations as `family` (`familyProg_eq`, a kernel computation
on the two closed programs), but its loops are the structured combinators `mapR`, `pochGo`, `sumB`
whose Hoare specifications are proved in `BuilderLoops`.
-/

namespace BecknerOnofri.V2.Interval

deriving instance DecidableEq for Const
deriving instance DecidableEq for Op
deriving instance DecidableEq for Outs

def psBody (omlam lam invden c1 : ℕ) (ups downs : List ℕ) (j : ℕ) : B ℕ := do
  let x1 ← smulB omlam (choose 12 j)
  let x2 ← mulB x1 (ups.getD j c1)
  let x3 ← mulB x2 (downs.getD (12 - j) c1)
  let x4 ← mulB x3 invden
  if j = 12 then addB x4 lam else pure x4

def lsBody (c1 : ℕ) (ps : List ℕ) (j : ℕ) : B ℕ := do
  let y ← emit (.smul (ps.getD j c1) (.inv (choose 12 j) 4096))
  logB y

def msTerm (c1 : ℕ) (ps : List ℕ) (s0 j : ℕ) : B ℕ :=
  emit (.smul (ps.getD j c1) (.q (featureNum (s0 + 1) j) (featureDen (s0 + 1))))

def msBody (c1 : ℕ) (ps : List ℕ) (s0 : ℕ) : B ℕ := do
  let terms ← mapR (msTerm c1 ps s0) 0 13
  sumB terms

def mpTerm (c1 : ℕ) (ms : List ℕ) (j s0 : ℕ) : B ℕ :=
  emit (.smul (ms.getD s0 c1) (.prod (weightNum (s0 + 1)) (weightDen (s0 + 1))
    (featureNum (s0 + 1) j) (featureDen (s0 + 1))))

def mpBody (c1 : ℕ) (ms : List ℕ) (j : ℕ) : B ℕ := do
  let terms ← mapR (mpTerm c1 ms j) 0 12
  sumB terms

def en2Term (c1 : ℕ) (ms : List ℕ) (s0 : ℕ) : B ℕ := do
  let pw ← powB (ms.getD s0 c1) 12 2
  emit (.smul pw (.q (weightNum (s0 + 1)) (weightDen (s0 + 1))))

def gBody (c1 : ℕ) (ls Mp : List ℕ) (j : ℕ) : B ℕ := do
  let y1 ← addcB (ls.getD j c1) 1
  let ny ← negB (Mp.getD j c1)
  let y2 ← addB y1 ny
  smulB y2 2

def xtBody (t : ℕ) (j : ℕ) : B ℕ := do
  let c ← cst ((j : Int) - 6) 6
  let n ← negB t
  addB c n

def etTerm (c1 : ℕ) (ps xt g : List ℕ) (j : ℕ) : B ℕ := do
  let m1 ← mulB (ps.getD j c1) (xt.getD j c1)
  mulB m1 (g.getD j c1)

def eBody (c1 meang eta : ℕ) (g xt : List ℕ) (j : ℕ) : B ℕ := do
  let nm ← negB meang
  let z1 ← addB (g.getD j c1) nm
  let z2 ← mulB eta (xt.getD j c1)
  let nz ← negB z2
  addB z1 nz

def varTerm (c1 : ℕ) (ps e : List ℕ) (j : ℕ) : B ℕ := do
  let pw ← powB (e.getD j c1) 12 2
  mulB (ps.getD j c1) pw

structure S1 where
  t : ℕ
  c1 : ℕ
  u : ℕ
  lam : ℕ
  a : ℕ
  oma : ℕ
  h : ℕ
  Ap : ℕ
  Am : ℕ

/-- Scalar parameters: `u = t²`, `λ`, `a`, `h = ω`, `A±`. -/
def phase1 : B S1 := do
  let t ← emit .var
  let c1 ← cst 1
  let u ← mulB t t
  let t10 ← powB t 12 10
  let L ← smulB t10 9 2
  let lx1 ← addcB L 1
  let lx2 ← invB lx1
  let lam ← mulB L lx2
  let nt ← negB t
  let omt ← addB c1 nt
  let ly1 ← mulB L omt
  let ly2 ← negB ly1
  let a ← addB t ly2
  let nu ← negB u
  let omu ← addB c1 nu
  let p1 ← powB omu 12 3
  let T1 ← smulB p1 31
  let q1 ← smulB u 61
  let q2 ← powB omu 12 2
  let T2 ← mulB q1 q2
  let w1 ← smulB u 29
  let w2 ← mulB w1 u
  let T3 ← mulB w2 omu
  let r1 ← powB u 12 3
  let T4 ← smulB r1 11
  let P1 ← addB T1 T2
  let P2 ← addB P1 T3
  let P ← addB P2 T4
  let uu ← mulB u u
  let h1 ← mulB P omt
  let h2 ← sdivB uu 10
  let hden ← addB h1 h2
  let g1 ← mulB u omt
  let g2 ← invB hden
  let h ← mulB g1 g2
  let ap1 ← addcB a 1
  let Ap ← sdivB ap1 2
  let na ← negB a
  let oma ← addB c1 na
  let Am ← sdivB oma 2
  pure ⟨t, c1, u, lam, a, oma, h, Ap, Am⟩

structure S2 where
  omlam : ℕ
  ps : List ℕ

/-- Pochhammer products and the law `p(t)`. -/
def phase2 (s : S1) : B S2 := do
  let pr ← pochGo s.Ap s.Am s.h 12 0 s.c1 s.c1 s.c1
  let ups := s.c1 :: pr.ups
  let downs := s.c1 :: pr.downs
  let nl ← negB s.lam
  let omlam ← addB s.c1 nl
  let invden ← invB pr.den
  let ps ← mapR (psBody omlam s.lam invden s.c1 ups downs) 0 13
  pure ⟨omlam, ps⟩

structure S3 where
  f : ℕ
  g : List ℕ
  meang : ℕ

/-- Entropy, moments, the functional and the gradient. -/
def phase3 (c1 : ℕ) (ps : List ℕ) : B S3 := do
  let ls ← mapR (lsBody c1 ps) 0 13
  let ms ← mapR (msBody c1 ps) 0 12
  let Mp ← mapR (mpBody c1 ms) 0 13
  let entT ← mapR (fun j => mulB (ps.getD j c1) (ls.getD j c1)) 0 13
  let ent ← sumB entT
  let en2T ← mapR (en2Term c1 ms) 0 12
  let en2 ← sumB en2T
  let f1 ← smulB ent 2
  let f2 ← negB en2
  let f ← addB f1 f2
  let g ← mapR (gBody c1 ls Mp) 0 13
  let mgT ← mapR (fun j => mulB (ps.getD j c1) (g.getD j c1)) 0 13
  let meang ← sumB mgT
  pure ⟨f, g, meang⟩

structure S4 where
  e : List ℕ
  var : ℕ

/-- Spin variance, regression slope, residuals and their variance. -/
def phase4 (s1 : S1) (s2 : S2) (s3 : S3) : B S4 := do
  let aa ← mulB s1.a s1.a
  let naa ← negB aa
  let ab ← addB s1.c1 naa
  let A1 ← mulB s2.omlam ab
  let A2 ← sdivB A1 12
  let hh1 ← smulB s1.h 12
  let hh2 ← addcB hh1 1
  let A3 ← mulB A2 hh2
  let ih1 ← addcB s1.h 1
  let ih2 ← invB ih1
  let A4 ← mulB A3 ih2
  let lo ← mulB s1.lam s2.omlam
  let po ← powB s1.oma 12 2
  let B1 ← mulB lo po
  let vz ← addB A4 B1
  let xt ← mapR (xtBody s1.t) 0 13
  let etT ← mapR (etTerm s1.c1 s2.ps xt s3.g) 0 13
  let es ← sumB etT
  let ivz ← invB vz
  let eta ← mulB es ivz
  let e ← mapR (eBody s1.c1 s3.meang eta s3.g xt) 0 13
  let vT ← mapR (varTerm s1.c1 s2.ps e) 0 13
  let var ← sumB vT
  pure ⟨e, var⟩

/-- The outputs. -/
def phase5 (raw : Bool) (s1 : S1) (s3 : S3) (s4 : S4) : B Outs := do
  let t4 ← powB s1.t 12 4
  let c14 ← cst 14
  let su ← smulB s1.u 10
  let nsu ← negB su
  let den14 ← addB c14 nsu
  let e' ← mapR (fun j => addcB (s4.e.getD j s1.c1) 1 4) 0 13
  if raw then
    let k1 ← smulB t4 12
    let k2 ← invB den14
    let k3 ← mulB k1 k2
    let fr ← addB s3.f k3
    pure ⟨fr, s4.var, e'⟩
  else
    let it4 ← invB t4
    let x1 ← mulB s3.f it4
    let id14 ← invB den14
    let x2 ← smulB id14 12
    let x12 ← addB x1 x2
    let fr ← addcB x12 (-1) 10
    let c50 ← cst 1 50
    let it4' ← invB t4
    let vt ← mulB s4.var it4'
    let nvt ← negB vt
    let w ← addB c50 nvt
    pure ⟨fr, w, e'⟩

def family2 (raw : Bool) : B Outs := do
  let s1 ← phase1
  let s2 ← phase2 s1
  let s3 ← phase3 s1.c1 s2.ps
  let s4 ← phase4 s1 s2 s3
  phase5 raw s1 s3 s4

/-- The program of `family2`. -/
def family2Prog (raw : Bool) : Prog × Outs :=
  let r := (family2 raw).run ⟨[], 0⟩
  (r.2.ops.reverse, r.1)

theorem familyProg_eq (raw : Bool) : familyProg raw = family2Prog raw := by
  unfold familyProg
  cases raw <;> decide +kernel

end BecknerOnofri.V2.Interval
