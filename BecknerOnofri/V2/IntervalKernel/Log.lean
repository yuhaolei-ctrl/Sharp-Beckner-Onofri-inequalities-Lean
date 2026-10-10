module

public import BecknerOnofri.V2.IntervalKernel.Mul

@[expose] public section

/-!
# A kernel-friendly logarithm

`Iv.log` of the reference implementation evaluates the 42-term `atanh` series with `Int`
interval arithmetic, which is slow in the kernel.  On the admissible range (`1 ≤ v < 2`, everything
non-negative) the same computation can be carried out with natural numbers only.
`logPointF` does this and falls back to the reference `logPoint` whenever one of its (cheap, run
time) guards fails; `logPointF_eq : logPointF a = logPoint a` holds for every `a`.
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

/-- `2^220 = (2^110)^2`. -/
def SS : Nat := 1684996666696914987166688442938726917102321526408785780068975640576

theorem SS_eq : SS = S110 * S110 := by norm_num [SS, S110]

/-- A natural interval, viewed as an `Iv`. -/
def emb (a : Nat × Nat) : Iv := ⟨(a.1 : Int), (a.2 : Int)⟩

theorem S110_pos : 0 < S110 := by norm_num [S110]

/-- Product of non-negative intervals (`lo ≤ hi`), rounded outwards. -/
def mulN (a b : Nat × Nat) : Nat × Nat :=
  (a.1 * b.1 / S110, (a.2 * b.2 + S110m1) / S110)

def addN (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- Reciprocal of a positive natural interval. -/
def recN (a : Nat × Nat) : Nat × Nat :=
  (SS / a.2, (SS + (a.1 - 1)) / a.1)

/-- `Interval(m / d)` for naturals. -/
def ofRatN (m d : Nat) : Nat × Nat :=
  (m * S110 / d, (m * S110 + (d - 1)) / d)

theorem cdiv_nat (m d : Nat) (hd : 0 < d) :
    cdiv (m : Int) (d : Int) = (((m + (d - 1)) / d : Nat) : Int) := by
  unfold cdiv
  have h1 := Nat.div_add_mod (m + (d - 1)) d
  have h2 := Nat.mod_lt (m + (d - 1)) hd
  generalize (m + (d - 1)) / d = q at *
  generalize (m + (d - 1)) % d = r at *
  have h1' : (d : Int) * q + r = m + (d - 1) := by
    have : ((d * q + r : Nat) : Int) = ((m + (d - 1) : Nat) : Int) := by rw [h1]
    push_cast at this
    rw [Nat.cast_sub (by omega)] at this
    simpa using this
  have : (-(m : Int)) / (d : Int) = -(q : Int) := by
    have := (Int.ediv_emod_unique (a := -(m:Int)) (b := (d:Int)) (q := -(q:Int))
      (r := (d : Int) - 1 - r) (by omega)).2 ⟨by linarith, by omega, by omega⟩
    exact this.1
  rw [this]; simp

theorem fdiv_nat (m d : Nat) : fdiv (m : Int) (d : Int) = ((m / d : Nat) : Int) := by
  unfold fdiv; exact (Int.natCast_div m d).symm

theorem mulN_spec {a b : Nat × Nat} (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2) :
    Iv.mul (emb a) (emb b) = emb (mulN a b) := by
  obtain ⟨al, ah⟩ := a
  obtain ⟨bl, bh⟩ := b
  simp only [] at ha hb
  have h12 : al * bl ≤ al * bh := Nat.mul_le_mul_left _ hb
  have h13 : al * bl ≤ ah * bl := Nat.mul_le_mul_right _ ha
  have h24 : al * bh ≤ ah * bh := Nat.mul_le_mul_right _ ha
  have h34 : ah * bl ≤ ah * bh := Nat.mul_le_mul_left _ hb
  have c12 : ((al : Int) * bl) ≤ (al : Int) * bh := by exact_mod_cast h12
  have c13 : ((al : Int) * bl) ≤ (ah : Int) * bl := by exact_mod_cast h13
  have c24 : ((al : Int) * bh) ≤ (ah : Int) * bh := by exact_mod_cast h24
  have c34 : ((ah : Int) * bl) ≤ (ah : Int) * bh := by exact_mod_cast h34
  simp only [Iv.mul, emb, mulN]
  have hmin : min (min ((al : Int) * bl) ((al : Int) * bh)) (min ((ah : Int) * bl) ((ah : Int) * bh))
      = (al : Int) * bl := by
    generalize (al : Int) * bl = P1 at *
    generalize (al : Int) * bh = P2 at *
    generalize (ah : Int) * bl = P3 at *
    generalize (ah : Int) * bh = P4 at *
    omega
  have hmax : max (max ((al : Int) * bl) ((al : Int) * bh)) (max ((ah : Int) * bl) ((ah : Int) * bh))
      = (ah : Int) * bh := by
    generalize (al : Int) * bl = P1 at *
    generalize (al : Int) * bh = P2 at *
    generalize (ah : Int) * bl = P3 at *
    generalize (ah : Int) * bh = P4 at *
    omega
  rw [hmin, hmax]
  have hS : (0 : Int) < (S110 : Int) := by exact_mod_cast S110_pos
  have e1 : (al : Int) * bl = ((al * bl : Nat) : Int) := by push_cast; rfl
  have e2 : (ah : Int) * bh = ((ah * bh : Nat) : Int) := by push_cast; rfl
  rw [scale_eq, e1, e2]
  have hm1 : S110 - 1 = S110m1 := by norm_num [S110, S110m1]
  rw [fdiv_nat, cdiv_nat _ _ S110_pos, hm1]

theorem mulN_le {a b : Nat × Nat} (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2) :
    (mulN a b).1 ≤ (mulN a b).2 := by
  simp only [mulN, Nat.mul_eq, Nat.add_eq]
  calc a.1 * b.1 / S110 ≤ a.2 * b.2 / S110 :=
        Nat.div_le_div_right (Nat.mul_le_mul ha hb)
    _ ≤ (a.2 * b.2 + S110m1) / S110 := Nat.div_le_div_right (Nat.le_add_right _ _)

theorem addN_spec (a b : Nat × Nat) : Iv.add (emb a) (emb b) = emb (addN a b) := by
  simp [Iv.add, emb, addN]

theorem recN_spec {a : Nat × Nat} (ha : 0 < a.1) : Iv.recip (emb a) = some (emb (recN a)) := by
  have h : 0 < (emb a).lo := by simp only [emb]; exact_mod_cast ha
  simp only [Iv.recip, if_pos h, Iv.recipPos]
  congr 1
  have hss : scale * scale = (SS : Int) := by
    rw [scale_eq, SS_eq]; push_cast; rfl
  simp only [emb, recN, hss]
  rw [fdiv_nat, cdiv_nat _ _ ha]

theorem recN_le {a : Nat × Nat} (ha : 0 < a.1) (hb : a.1 ≤ a.2) :
    (recN a).1 ≤ (recN a).2 := by
  simp only [recN, Nat.add_eq, Nat.sub_eq]
  calc SS / a.2 ≤ SS / a.1 := Nat.div_le_div_left hb ha
    _ ≤ (SS + (a.1 - 1)) / a.1 := Nat.div_le_div_right (Nat.le_add_right _ _)

theorem ofRatN_spec (m d : Nat) (hd : 0 < d) :
    Iv.ofRat (m : Int) d = emb (ofRatN m d) := by
  have hs : (m : Int) * scale = ((m * S110 : Nat) : Int) := by
    rw [scale_eq]; push_cast; rfl
  simp only [Iv.ofRat, hs, emb, ofRatN]
  rw [fdiv_nat, cdiv_nat _ _ hd]

theorem ofRatN_le (m d : Nat) : (ofRatN m d).1 ≤ (ofRatN m d).2 := by
  simp only [ofRatN, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  exact Nat.div_le_div_right (Nat.le_add_right _ _)

/-! ### The series -/

def lstep (z2 : Nat × Nat) (st : (Nat × Nat) × (Nat × Nat)) (n : Nat) :
    (Nat × Nat) × (Nat × Nat) :=
  (addN st.1 (mulN st.2 (ofRatN 2 (2 * n + 1))), mulN st.2 z2)

theorem seriesStep_spec {z2 a t : Nat × Nat} (hz : z2.1 ≤ z2.2) (ht : t.1 ≤ t.2) (n : Nat) :
    seriesStep (emb z2) (emb a, emb t) n =
      (emb (lstep z2 (a, t) n).1, emb (lstep z2 (a, t) n).2) := by
  have hd : 0 < 2 * n + 1 := by omega
  have h2 : (2 : Int) = ((2 : Nat) : Int) := rfl
  unfold seriesStep lstep
  simp only []
  rw [h2, ofRatN_spec 2 (2 * n + 1) hd, mulN_spec ht (ofRatN_le _ _), addN_spec,
    mulN_spec ht hz]

theorem fold_spec {z2 : Nat × Nat} (hz : z2.1 ≤ z2.2) :
    ∀ (ns : List Nat) (a t : Nat × Nat), t.1 ≤ t.2 →
      ns.foldl (seriesStep (emb z2)) (emb a, emb t) =
        (emb (ns.foldl (lstep z2) (a, t)).1, emb (ns.foldl (lstep z2) (a, t)).2) ∧
      (ns.foldl (lstep z2) (a, t)).2.1 ≤ (ns.foldl (lstep z2) (a, t)).2.2
  | [], a, t, ht => ⟨rfl, ht⟩
  | n :: ns, a, t, ht => by
    simp only [List.foldl_cons]
    rw [seriesStep_spec hz ht n]
    exact fold_spec hz ns _ _ (mulN_le ht hz)

/-! ### `logCore` -/

def lfin (st : (Nat × Nat) × (Nat × Nat)) (rem : Nat × Nat) : Option (Nat × Nat) :=
  bif Nat.ble st.1.1 (st.1.2 + rem.2) then some (st.1.1, st.1.2 + rem.2) else none

def lrem2 (st : (Nat × Nat) × (Nat × Nat)) (w85 : Nat × Nat) : Option (Nat × Nat) :=
  bif Nat.ble 1 w85.1 then
    lfin st (mulN (mulN st.2 (2 * S110, 2 * S110)) (recN w85))
  else none

def wOf (z2 : Nat × Nat) : Nat × Nat := mulN (S110 - z2.2, S110 - z2.1) (85 * S110, 85 * S110)

def lrem (st : (Nat × Nat) × (Nat × Nat)) (z2 : Nat × Nat) : Option (Nat × Nat) :=
  bif Nat.ble z2.2 S110m1 then lrem2 st (wOf z2) else none

def lcore3 (z z2 : Nat × Nat) : Option (Nat × Nat) :=
  lrem ((List.range 42).foldl (lstep z2) (((0 : Nat), (0 : Nat)), z)) z2

def lcore2 (z : Nat × Nat) : Option (Nat × Nat) := lcore3 z (mulN z z)

def lcore (xlo xhi : Nat) : Option (Nat × Nat) :=
  bif Nat.ble S110 xlo && Nat.ble xlo xhi then
    lcore2 (mulN (xlo - S110, xhi - S110) (recN (xlo + S110, xhi + S110)))
  else none

theorem ofInt_emb (k : Nat) : Iv.ofInt (k : Int) = emb (k * S110, k * S110) := by
  simp only [Iv.ofInt, emb, scale_eq]; push_cast; rfl

theorem logCore_gen (x z z2 : Iv) (hz : zOf x = some z) (hz2 : Iv.mul z z = z2) :
    logCore x = (remOf z2 (seriesFold z z2 42).2).bind fun rem =>
      Iv.mk? (seriesFold z z2 42).1.lo ((seriesFold z z2 42).1.hi + rem.hi) := by
  subst hz2
  unfold logCore
  rw [hz]
  rfl

theorem seriesFold_emb {z2 z : Nat × Nat} (hz : z2.1 ≤ z2.2) (hzz : z.1 ≤ z.2) :
    seriesFold (emb z) (emb z2) 42 =
      (emb ((List.range 42).foldl (lstep z2) ((0, 0), z)).1,
       emb ((List.range 42).foldl (lstep z2) ((0, 0), z)).2) ∧
    ((List.range 42).foldl (lstep z2) ((0, 0), z)).2.1 ≤
      ((List.range 42).foldl (lstep z2) ((0, 0), z)).2.2 := by
  unfold seriesFold
  exact fold_spec hz (List.range 42) (0, 0) z hzz

theorem lfin_sound {st : (Nat × Nat) × (Nat × Nat)} {rem r : Nat × Nat}
    (h : lfin st rem = some r) :
    Iv.mk? (emb st.1).lo ((emb st.1).hi + (emb rem).hi) = some (emb r) := by
  unfold lfin at h
  cases hg : Nat.ble st.1.1 (st.1.2 + rem.2)
  · rw [hg, Bool.cond_false] at h; cases h
  · rw [hg, Bool.cond_true] at h
    have h := Option.some.inj h
    have hle := ble_iff.1 hg
    subst h
    have hle' : (emb st.1).lo ≤ (emb st.1).hi + (emb rem).hi := by
      simp only [emb]; exact_mod_cast hle
    unfold Iv.mk?
    rw [if_pos hle']
    simp only [emb, Nat.add_eq]
    push_cast
    rfl

theorem bind_map_some {α β γ : Type} (a : α) (f : α → β) (g : β → Option γ) :
    (Option.map f (some a)).bind g = g (f a) := rfl

theorem lrem2_sound {st : (Nat × Nat) × (Nat × Nat)} {z2 w85 r : Nat × Nat}
    (hw : Iv.mul (Iv.add (Iv.ofInt 1) (emb z2).neg) (Iv.ofInt 85) = emb w85)
    (hwle : w85.1 ≤ w85.2) (ht : st.2.1 ≤ st.2.2)
    (h : lrem2 st w85 = some r) :
    (remOf (emb z2) (emb st.2)).bind (fun rem => Iv.mk? (emb st.1).lo ((emb st.1).hi + rem.hi))
      = some (emb r) := by
  unfold lrem2 at h
  cases hg : Nat.ble 1 w85.1
  · rw [hg, Bool.cond_false] at h; cases h
  · rw [hg, Bool.cond_true] at h
    have hpos : 0 < w85.1 := ble_iff.1 hg
    have h2 : Iv.ofInt 2 = emb (2 * S110, 2 * S110) := by
      have : (2 : Int) = ((2 : Nat) : Int) := rfl
      rw [this, ofInt_emb]
    have hrle := recN_le hpos hwle
    have ht2 := mulN_spec ht (b := (2 * S110, 2 * S110)) (le_refl _)
    have ht2le := mulN_le ht (b := (2 * S110, 2 * S110)) (le_refl _)
    unfold remOf
    rw [hw, recN_spec hpos]
    rw [bind_map_some]
    rw [h2, ht2, mulN_spec ht2le hrle]
    exact lfin_sound h

theorem lrem_sound {st : (Nat × Nat) × (Nat × Nat)} {z2 r : Nat × Nat}
    (ht : st.2.1 ≤ st.2.2) (hz : z2.1 ≤ z2.2) (h : lrem st z2 = some r) :
    (remOf (emb z2) (emb st.2)).bind (fun rem => Iv.mk? (emb st.1).lo ((emb st.1).hi + rem.hi))
      = some (emb r) := by
  unfold lrem at h
  cases hg : Nat.ble z2.2 S110m1
  · rw [hg, Bool.cond_false] at h; cases h
  · rw [hg, Bool.cond_true] at h
    have hz2S : z2.2 ≤ S110m1 := ble_iff.1 hg
    have hSp := S110_pos
    have hS1 : S110m1 + 1 = S110 := by norm_num [S110, S110m1]
    have hw : Iv.add (Iv.ofInt 1) (emb z2).neg = emb (S110 - z2.2, S110 - z2.1) := by
      have : (1 : Int) = ((1 : Nat) : Int) := rfl
      rw [this, ofInt_emb]
      simp only [Iv.add, Iv.neg, emb]
      have e1 : ((S110 - z2.2 : Nat) : Int) = ((1 * S110 : Nat) : Int) + -(z2.2 : Int) := by omega
      have e2 : ((S110 - z2.1 : Nat) : Int) = ((1 * S110 : Nat) : Int) + -(z2.1 : Int) := by omega
      rw [e1, e2]
    have hwle : (S110 - z2.2, S110 - z2.1).1 ≤ (S110 - z2.2, S110 - z2.1).2 := by
      simp only []; omega
    have h85 : Iv.ofInt 85 = emb (85 * S110, 85 * S110) := by
      have : (85 : Int) = ((85 : Nat) : Int) := rfl
      rw [this, ofInt_emb]
    have hw85 : Iv.mul (Iv.add (Iv.ofInt 1) (emb z2).neg) (Iv.ofInt 85) = emb (wOf z2) := by
      rw [hw, h85]; exact mulN_spec hwle (le_refl _)
    exact lrem2_sound hw85 (mulN_le hwle (b := (85 * S110, 85 * S110)) (le_refl _)) ht h

theorem lcore3_sound {z z2 r : Nat × Nat} (hzle : z.1 ≤ z.2) (hz2 : z2.1 ≤ z2.2)
    {x : Iv} (hx : zOf x = some (emb z)) (hzz : Iv.mul (emb z) (emb z) = emb z2)
    (h : lcore3 z z2 = some r) : logCore x = some (emb r) := by
  rw [logCore_gen _ _ _ hx hzz]
  have hfold := seriesFold_emb hz2 hzle
  rw [hfold.1]
  exact lrem_sound hfold.2 hz2 h

theorem lcore_sound {xlo xhi : Nat} {r : Nat × Nat} (h : lcore xlo xhi = some r) :
    logCore (emb (xlo, xhi)) = some (emb r) := by
  unfold lcore at h
  cases hg : (Nat.ble S110 xlo && Nat.ble xlo xhi)
  · rw [hg, Bool.cond_false] at h; cases h
  rw [hg, Bool.cond_true] at h
  simp only [Bool.and_eq_true] at hg
  have hS : S110 ≤ xlo := ble_iff.1 hg.1
  have hx : xlo ≤ xhi := ble_iff.1 hg.2
  have hSp := S110_pos
  have hx1 : Iv.add (emb (xlo, xhi)) (Iv.ofInt 1) = emb (xlo + S110, xhi + S110) := by
    have : (1 : Int) = ((1 : Nat) : Int) := rfl
    rw [this, ofInt_emb, addN_spec]; simp [addN]
  have hx2 : Iv.add (emb (xlo, xhi)) (Iv.ofInt 1).neg = emb (xlo - S110, xhi - S110) := by
    have : (1 : Int) = ((1 : Nat) : Int) := rfl
    rw [this, ofInt_emb]
    simp only [Iv.add, Iv.neg, emb]
    congr 1 <;> omega
  have hr := recN_le (a := (xlo + S110, xhi + S110)) (by simp; omega) (by simp; omega)
  have hz : zOf (emb (xlo, xhi)) =
      some (emb (mulN (xlo - S110, xhi - S110) (recN (xlo + S110, xhi + S110)))) := by
    unfold zOf
    rw [hx1, recN_spec (by simp; omega)]
    simp only [Option.map_some]
    rw [hx2]
    rw [mulN_spec (by simp; omega) hr]
  have hzle := mulN_le (a := (xlo - S110, xhi - S110)) (b := recN (xlo + S110, xhi + S110))
    (by simp; omega) hr
  exact lcore3_sound hzle (mulN_le hzle hzle) hz (mulN_spec hzle hzle) h

/-! ### `logPoint` -/

def finishLog (k : Int) (o : Option (Nat × Nat)) (fb : Option Iv) : Option Iv :=
  match o with
  | some r => some ((emb r).add (log2Iv.mul (Iv.ofInt k)))
  | none => fb

def logPointN (n : Nat) : Option Iv :=
  let k : Int := (Nat.log2 n : Int) - 110
  let x := ofRatN (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)
  finishLog k (lcore x.1 x.2) (logPoint (n : Int))

def logPointF (a : Int) : Option Iv :=
  match a with
  | Int.ofNat n => logPointN n
  | Int.negSucc _ => logPoint a

theorem logPointN_eq (n : Nat) : logPointN n = logPoint (n : Int) := by
  unfold logPointN
  simp only []
  generalize hk : ((Nat.log2 n : Int) - 110) = k
  cases hl : lcore (ofRatN (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)).1
      (ofRatN (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)).2 with
  | none => rfl
  | some r =>
    have hx : Iv.ofRat ((n : Int) * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)
        = emb (ofRatN (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat)) := by
      have := ofRatN_spec (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat) (by positivity)
      push_cast at this; exact this
    have hc := lcore_sound hl
    unfold finishLog
    unfold logPoint
    simp only [Int.toNat_natCast, hk]
    rw [hx]
    have hc' : logCore (emb (ofRatN (n * 2 ^ (-k).toNat) (2 ^ 110 * 2 ^ k.toNat))) = some (emb r) := hc
    rw [hc']
    rfl

theorem logPointF_eq (a : Int) : logPointF a = logPoint a := by
  cases a with
  | negSucc m => rfl
  | ofNat n => exact logPointN_eq n

end BecknerOnofri.V2.IntervalKernel
