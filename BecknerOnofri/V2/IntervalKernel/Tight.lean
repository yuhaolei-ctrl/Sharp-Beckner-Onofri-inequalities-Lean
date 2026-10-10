module

public import BecknerOnofri.V2.IntervalKernel.Half

@[expose] public section

/-!
# Mean-value tightening on packed registers

`tightF mid box q1` performs `CJet.tight` for a context whose radius is the symmetric interval
`[-q1, q1]`: in that case the six steps `box_j ∩ (mid_j + (j+1) rad · next)` need ONE product each
(`(j+1) q1 * max |next|`).
-/

namespace BecknerOnofri.V2.IntervalKernel

open BecknerOnofri.V2.Interval

theorem min4_sym0 (u v : Int) :
    min (min (-u) (-v)) (min u v) = -(max |u| |v|) ∧
    max (max (-u) (-v)) (max u v) = max |u| |v| := by
  constructor <;> simp only [min_def, max_def, abs_eq_max_neg] <;> split_ifs <;> omega

theorem min4_sym (Q a b : Int) (hQ : 0 ≤ Q) :
    min (min (-Q * a) (-Q * b)) (min (Q * a) (Q * b)) = -(Q * max |a| |b|) ∧
    max (max (-Q * a) (-Q * b)) (max (Q * a) (Q * b)) = Q * max |a| |b| := by
  have h := min4_sym0 (Q * a) (Q * b)
  rw [abs_mul, abs_mul, abs_of_nonneg hQ, ← mul_max_of_nonneg _ _ hQ] at h
  simpa [neg_mul] using h

theorem cdiv_eq (m : Int) : cdiv m scale = (m + (S110m1 : Int)) / S110 := by
  unfold cdiv
  rw [scale_eq]
  unfold S110 S110m1; push_cast; omega

/-- A symmetric radius times `k` times an interval is a symmetric interval. -/
theorem rad_mul_spec (q k nl nh : Int) (hq : 0 ≤ q) (hk : 0 ≤ k) :
    ((⟨-q, q⟩ : Iv).mul (Iv.ofInt k)).mul ⟨nl, nh⟩
      = ⟨-((q * k * max |nl| |nh| + (S110m1 : Int)) / S110),
          (q * k * max |nl| |nh| + (S110m1 : Int)) / S110⟩ := by
  have hS : (0 : Int) < S110 := by unfold S110; norm_num
  have hs : scale = (S110 : Int) := scale_eq
  have h1 : (⟨-q, q⟩ : Iv).mul (Iv.ofInt k) = ⟨-(q * k), q * k⟩ := by
    have hX : 0 ≤ q * (k * scale) := mul_nonneg hq (mul_nonneg hk (by rw [hs]; exact hS.le))
    unfold Iv.mul Iv.ofInt
    simp only [fdiv, cdiv]
    have e1 : -q * (k * scale) = -(q * (k * scale)) := by ring
    rw [e1, min_self, min_self, max_self, max_self,
      min_eq_left (by linarith), max_eq_right (by linarith)]
    have e2 : q * (k * scale) = (q * k) * scale := by ring
    have e3 : -((q * k) * scale) = (-(q * k)) * scale := by ring
    rw [e2, e3, Int.mul_ediv_cancel _ (by rw [hs]; exact hS.ne')]
    simp
  rw [h1]
  have hQ : 0 ≤ q * k := mul_nonneg hq hk
  obtain ⟨m1, m2⟩ := min4_sym (q * k) nl nh hQ
  simp only [Iv.mul, fdiv]
  rw [m1, m2]
  simp only [Iv.mk.injEq]
  rw [cdiv_eq, hs]
  refine ⟨?_, rfl⟩
  unfold S110 S110m1; push_cast; omega

/-- `|n - b|` for a natural `n` and a bias `b`. -/
def absG (b n : Nat) : Nat := bif Nat.ble b n then Nat.sub n b else Nat.sub b n

theorem absG_cast (b n : Nat) (_h : n ≤ 2 * b) : ((absG b n : Nat) : Int) = |(n : Int) - b| := by
  unfold absG
  cases h : Nat.ble b n
  · have : ¬ b ≤ n := fun hh => by have := ble_iff.2 hh; simp_all
    have hl : n ≤ b := by omega
    simp only [Bool.cond_false, Nat.sub_eq]
    rw [abs_of_nonpos (by omega), Nat.cast_sub hl]
    ring
  · have : b ≤ n := ble_iff.1 h
    simp only [Bool.cond_true, Nat.sub_eq]
    rw [abs_of_nonneg (by omega), Nat.cast_sub this]

/-- `|n - B|` for a biased natural. -/
def absB (n : Nat) : Nat := absG B n

theorem absB_cast {n : Nat} (h : n ≤ TWOB) : ((absB n : Nat) : Int) = |dec n| := by
  have := absG_cast B n (by rw [TWOB_eq] at h; exact h)
  exact this

/-- One tightening step at index `j`; `(nl, nh)` is the tightened entry `j+1`, `q1` the radius. -/
def tightStep (mid box q1 j nl nh : Nat) : Nat × Nat × Bool :=
  let m := nmax (absB nl) (absB nh)
  let c := Nat.shiftRight (Nat.add (Nat.mul (Nat.mul (Nat.add j 1) q1) m) S110m1) 110
  let lo := nmax (fld box (2 * j)) (Nat.sub (fld mid (2 * j)) c)
  let hi := nmin (fld box (2 * j + 1)) (Nat.add (fld mid (2 * j + 1)) c)
  (lo, hi, Nat.ble lo hi)

theorem tightStep_spec {lm lb : List Nat} (hlm : ∀ x ∈ lm, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩) {j : Nat} (hj : j < 7) {nl nh : Nat}
    (hnl : nl ≤ TWOB) (hnh : nh ≤ TWOB)
    (hok : (tightStep (packList lm) (packList lb) q1 j nl nh).2.2 = true) :
    (tightStep (packList lm) (packList lb) q1 j nl nh).1 ≤ TWOB ∧
    (tightStep (packList lm) (packList lb) q1 j nl nh).2.1 ≤ TWOB ∧
    ((jetL lb 0).get j).meet?
      (((jetL lm 0).get j).add ((x.rad.mul (Iv.ofInt ((j : Int) + 1))).mul ⟨dec nl, dec nh⟩))
      = some ⟨dec (tightStep (packList lm) (packList lb) q1 j nl nh).1,
          dec (tightStep (packList lm) (packList lb) q1 j nl nh).2.1⟩ := by
  have hq : (0 : Int) ≤ q1 := Nat.cast_nonneg _
  rw [hrad, rad_mul_spec _ _ _ _ hq (by positivity)]
  rw [jetL_get _ _ _ hj, jetL_get _ _ _ hj, ivL_pack hlm, ivL_pack hlb]
  have fm1 := fld_le hlm (0 + 2 * j)
  have fm2 := fld_le hlm (0 + 2 * j + 1)
  have fb1 := fld_le hlb (0 + 2 * j)
  have fb2 := fld_le hlb (0 + 2 * j + 1)
  simp only [Nat.zero_add] at fm1 fm2 fb1 fb2 ⊢
  have ha := absB_cast hnl
  have hb := absB_cast hnh
  have hmax : (((nmax (absB nl) (absB nh) : Nat)) : Int) = max |dec nl| |dec nh| := by
    rw [nmax_cast, ha, hb]
  generalize hmm : nmax (absB nl) (absB nh) = mm at hmax
  unfold tightStep at hok ⊢
  simp only [] at hok ⊢
  rw [hmm] at hok ⊢
  have hsh : ∀ n : Nat, Nat.shiftRight n 110 = n / S110 := by
    intro n
    have : n >>> 110 = n / 2 ^ 110 := Nat.shiftRight_eq_div_pow n 110
    rw [S110_eq]
    exact this
  generalize hc : Nat.shiftRight (Nat.add (Nat.mul (Nat.mul (Nat.add j 1) q1) mm) S110m1) 110 = c
  have hcc : (c : Int) = (q1 * ((j : Int) + 1) * max |dec nl| |dec nh| + (S110m1 : Int)) / S110 := by
    rw [← hc, hsh, Int.natCast_div]
    simp only [Nat.add_eq, Nat.mul_eq]
    push_cast
    rw [hmax]; ring_nf
  rw [← hcc]
  simp only [Nat.sub_eq, Nat.add_eq] at hok hc ⊢
  rw [hc] at hok
  generalize fld (packList lb) (2 * j) = bl at *
  generalize fld (packList lb) (2 * j + 1) = bh at *
  generalize fld (packList lm) (2 * j) = ml at *
  generalize fld (packList lm) (2 * j + 1) = mh at *
  have e1 := nmax_cast bl (ml - c)
  have e2 := nmin_cast bh (mh + c)
  have hle := ble_iff.1 hok
  generalize nmax bl (ml - c) = lo at *
  generalize nmin bh (mh + c) = hi at *
  have hle' : (lo : Int) ≤ hi := by exact_mod_cast hle
  refine ⟨by push_cast at e1; omega, by push_cast at e2; omega, ?_⟩
  unfold Iv.meet? Iv.mk? Iv.add dec
  push_cast at e1 e2
  rw [if_pos (by simp only []; omega)]
  simp only [Option.some.injEq, Iv.mk.injEq]
  constructor <;> omega

/-- The chain of tightening steps: `tTk k` is the tightened entry `6 - k` (entry `6` is the box
entry itself, `k = 0`). -/
def tTk (mid box q1 : Nat) : Nat → Nat × Nat × Bool
  | 0 => (fld box 12, fld box 13, true)
  | k + 1 =>
    let r := tTk mid box q1 k
    tightStep mid box q1 (5 - k) r.1 r.2.1

/-- The fourteen fields of the tightened box. -/
def tightFields (mid box q1 : Nat) : List Nat :=
  [(tTk mid box q1 6).1, (tTk mid box q1 6).2.1, (tTk mid box q1 5).1, (tTk mid box q1 5).2.1,
    (tTk mid box q1 4).1, (tTk mid box q1 4).2.1, (tTk mid box q1 3).1, (tTk mid box q1 3).2.1,
    (tTk mid box q1 2).1, (tTk mid box q1 2).2.1, (tTk mid box q1 1).1, (tTk mid box q1 1).2.1,
    (tTk mid box q1 0).1, (tTk mid box q1 0).2.1]

def tightOk (mid box q1 : Nat) : Bool :=
  (tTk mid box q1 6).2.2 && (tTk mid box q1 5).2.2 && (tTk mid box q1 4).2.2 &&
    (tTk mid box q1 3).2.2 && (tTk mid box q1 2).2.2 && (tTk mid box q1 1).2.2

/-- The six tightening steps (indices `5, …, 0`) and the repacking of the box. -/
def tightF (mid box q1 : Nat) : Nat × Bool :=
  (packList (tightFields mid box q1), tightOk mid box q1)

theorem tightF_fst (mid box q1 : Nat) :
    (tightF mid box q1).1 = packList (tightFields mid box q1) := by
  simp only [tightF]

theorem tightF_snd (mid box q1 : Nat) : (tightF mid box q1).2 = tightOk mid box q1 := by
  simp only [tightF]

theorem tightF_spec {lm lb : List Nat} (hlm : ∀ x ∈ lm, x ≤ TWOB) (hlb : ∀ x ∈ lb, x ≤ TWOB)
    {x : Ctx} {q1 : Nat} (hrad : x.rad = ⟨-(q1 : Int), q1⟩)
    (hok : (tightF (packList lm) (packList lb) q1).2 = true) :
    HalfL (tightF (packList lm) (packList lb) q1).1 (tightFields (packList lm) (packList lb) q1) ∧
      CJet.tight x (jetL lm 0) (jetL lb 0)
        = some (jetL (tightFields (packList lm) (packList lb) q1) 0) := by
  have n6l : fld (packList lb) 12 ≤ TWOB := fld_le hlb 12
  have n6h : fld (packList lb) 13 ≤ TWOB := fld_le hlb 13
  have hok' : tightOk (packList lm) (packList lb) q1 = true := by rw [← tightF_snd]; exact hok
  unfold tightOk at hok'
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨⟨⟨⟨o0, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩ := hok'
  have e1 : tTk (packList lm) (packList lb) q1 1 = tightStep (packList lm) (packList lb) q1 5
      (fld (packList lb) 12) (fld (packList lb) 13) := rfl
  have e2 : tTk (packList lm) (packList lb) q1 2 = tightStep (packList lm) (packList lb) q1 4
      (tTk (packList lm) (packList lb) q1 1).1 (tTk (packList lm) (packList lb) q1 1).2.1 := rfl
  have e3 : tTk (packList lm) (packList lb) q1 3 = tightStep (packList lm) (packList lb) q1 3
      (tTk (packList lm) (packList lb) q1 2).1 (tTk (packList lm) (packList lb) q1 2).2.1 := rfl
  have e4 : tTk (packList lm) (packList lb) q1 4 = tightStep (packList lm) (packList lb) q1 2
      (tTk (packList lm) (packList lb) q1 3).1 (tTk (packList lm) (packList lb) q1 3).2.1 := rfl
  have e5 : tTk (packList lm) (packList lb) q1 5 = tightStep (packList lm) (packList lb) q1 1
      (tTk (packList lm) (packList lb) q1 4).1 (tTk (packList lm) (packList lb) q1 4).2.1 := rfl
  have e6 : tTk (packList lm) (packList lb) q1 6 = tightStep (packList lm) (packList lb) q1 0
      (tTk (packList lm) (packList lb) q1 5).1 (tTk (packList lm) (packList lb) q1 5).2.1 := rfl
  rw [e1] at o5
  obtain ⟨b1l, b1h, m1⟩ := tightStep_spec hlm hlb hrad (j := 5) (by norm_num) n6l n6h o5
  rw [← e1] at b1l b1h m1
  rw [e2] at o4
  obtain ⟨b2l, b2h, m2⟩ := tightStep_spec hlm hlb hrad (j := 4) (by norm_num) b1l b1h o4
  rw [← e2] at b2l b2h m2
  rw [e3] at o3
  obtain ⟨b3l, b3h, m3⟩ := tightStep_spec hlm hlb hrad (j := 3) (by norm_num) b2l b2h o3
  rw [← e3] at b3l b3h m3
  rw [e4] at o2
  obtain ⟨b4l, b4h, m4⟩ := tightStep_spec hlm hlb hrad (j := 2) (by norm_num) b3l b3h o2
  rw [← e4] at b4l b4h m4
  rw [e5] at o1
  obtain ⟨b5l, b5h, m5⟩ := tightStep_spec hlm hlb hrad (j := 1) (by norm_num) b4l b4h o1
  rw [← e5] at b5l b5h m5
  rw [e6] at o0
  obtain ⟨b6l, b6h, m6⟩ := tightStep_spec hlm hlb hrad (j := 0) (by norm_num) b5l b5h o0
  rw [← e6] at b6l b6h m6
  have h6 : (jetL lb 0).get 6 = ⟨dec (fld (packList lb) 12), dec (fld (packList lb) 13)⟩ := by
    rw [jetL_get _ _ _ (by norm_num), ivL_pack hlb]
  refine ⟨⟨by simp [tightFields], ?_, tightF_fst _ _ _⟩, ?_⟩
  · simp only [tightFields, List.forall_mem_cons, List.forall_mem_nil]
    exact ⟨b6l, b6h, b5l, b5h, b4l, b4h, b3l, b3h, b2l, b2h, b1l, b1h, n6l, n6h, fun _ h => absurd h (List.not_mem_nil)⟩
  · unfold CJet.tight
    simp only [CJet.tightGo, h6, List.headD_cons]
    rw [m1]
    simp only [Option.bind_some, List.headD_cons]
    rw [m2]
    simp only [Option.bind_some, List.headD_cons]
    rw [m3]
    simp only [Option.bind_some, List.headD_cons]
    rw [m4]
    simp only [Option.bind_some, List.headD_cons]
    rw [m5]
    simp only [Option.bind_some, List.headD_cons]
    rw [m6]
    simp only [Option.bind_some, List.headD_cons]
    congr 1

end BecknerOnofri.V2.IntervalKernel
