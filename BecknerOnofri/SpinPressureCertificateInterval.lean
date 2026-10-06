module

public import BecknerOnofri.SpinPressureCertificateCore
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Soundness of the fixed-point interval operations

Lemma 5.20 (lem:section5-scalar-pressure). Every operation of
`SpinPressureCertificateCore` on intervals `[lo/2¹⁰⁰, hi/2¹⁰⁰]` encloses the exact real
result; this includes the verified exponential (Taylor series with the remainder of
`Real.exp_bound` and repeated squaring) and the verified logarithm (checked against the
exponential enclosure).
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Real

theorem scale_pos_int : (0 : ℤ) < scale := by decide

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos_int

theorem fdiv_le (m b : ℤ) (hb : 0 < b) : ((fdiv m b : ℤ) : ℝ) ≤ (m : ℝ) / b := by
  have h := Int.ediv_mul_le m (ne_of_gt hb)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast h

theorem le_cdiv (m b : ℤ) (hb : 0 < b) : (m : ℝ) / b ≤ ((cdiv m b : ℤ) : ℝ) := by
  have h := fdiv_le (-m) b hb
  simp only [fdiv] at h
  simp only [cdiv, Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

/-- Real membership in a fixed-point interval. -/
def Iv.Mem (a : Iv) (x : ℝ) : Prop := (a.lo : ℝ) / scale ≤ x ∧ x ≤ (a.hi : ℝ) / scale

namespace Iv

theorem mem_zero : zero.Mem 0 := by simp [Mem, zero]

theorem mem_one : one.Mem 1 := by
  simp [Mem, one, div_self (ne_of_gt scale_pos)]

theorem mem_point (m : ℤ) : (⟨m, m⟩ : Iv).Mem ((m : ℝ) / scale) := ⟨le_rfl, le_rfl⟩

theorem mem_add {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  simp only [Mem, add, Int.cast_add, add_div] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {a : Iv} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  simp only [Mem, neg, Int.cast_neg, neg_div] at *
  constructor <;> linarith [hx.1, hx.2]

theorem mem_of_le {lo hi : ℤ} {x : ℝ} (h1 : (lo : ℝ) / scale ≤ x) (h2 : x ≤ (hi : ℝ) / scale) :
    (⟨lo, hi⟩ : Iv).Mem x := ⟨h1, h2⟩

theorem mem_symm {B : ℤ} {x : ℝ} (h : |x| ≤ (B : ℝ) / scale) : (⟨-B, B⟩ : Iv).Mem x := by
  refine ⟨?_, (le_abs_self x).trans h⟩
  rw [Int.cast_neg, neg_div]
  linarith [neg_abs_le x]

/-- Endpoint bounds for a product of two reals in intervals. -/
theorem prod_bounds {al ah bl bh X Y : ℝ} (hX : al ≤ X ∧ X ≤ ah) (hY : bl ≤ Y ∧ Y ≤ bh) :
    min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh)) ≤ X * Y ∧
      X * Y ≤ max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)) := by
  have hXY : min (al * Y) (ah * Y) ≤ X * Y ∧ X * Y ≤ max (al * Y) (ah * Y) := by
    rcases le_total 0 Y with hy | hy
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hX.1 hy),
        (mul_le_mul_of_nonneg_right hX.2 hy).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hX.2 hy),
        (mul_le_mul_of_nonpos_right hX.1 hy).trans (le_max_left _ _)⟩
  have hl : min (al * bl) (al * bh) ≤ al * Y ∧ al * Y ≤ max (al * bl) (al * bh) := by
    rcases le_total 0 al with ha | ha
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hY.1 ha),
        (mul_le_mul_of_nonneg_left hY.2 ha).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hY.2 ha),
        (mul_le_mul_of_nonpos_left hY.1 ha).trans (le_max_left _ _)⟩
  have hu : min (ah * bl) (ah * bh) ≤ ah * Y ∧ ah * Y ≤ max (ah * bl) (ah * bh) := by
    rcases le_total 0 ah with ha | ha
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hY.1 ha),
        (mul_le_mul_of_nonneg_left hY.2 ha).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hY.2 ha),
        (mul_le_mul_of_nonpos_left hY.1 ha).trans (le_max_left _ _)⟩
  constructor
  · calc min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh))
        ≤ min (al * Y) (ah * Y) := min_le_min hl.1 hu.1
      _ ≤ X * Y := hXY.1
  · calc X * Y ≤ max (al * Y) (ah * Y) := hXY.2
      _ ≤ max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)) := max_le_max hl.2 hu.2

theorem mem_iff_scaled {a : Iv} {x : ℝ} :
    a.Mem x ↔ (a.lo : ℝ) ≤ x * scale ∧ x * scale ≤ (a.hi : ℝ) := by
  simp only [Mem, div_le_iff₀ scale_pos, le_div_iff₀ scale_pos]

theorem mem_mul {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.mul b).Mem (x * y) := by
  rw [mem_iff_scaled] at hx hy
  have h := prod_bounds hx hy
  have hS := scale_pos
  simp only [mul, Mem]
  constructor
  · have h1 := fdiv_le (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)))
      scale scale_pos_int
    push_cast at h1
    rw [div_le_iff₀ hS]
    calc _ ≤ _ := h1
      _ ≤ x * scale * (y * scale) / scale := by gcongr; exact h.1
      _ = x * y * scale := by field_simp
  · have h1 := le_cdiv (max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)))
      scale scale_pos_int
    push_cast at h1
    rw [le_div_iff₀ hS]
    calc x * y * scale = x * scale * (y * scale) / scale := by field_simp
      _ ≤ _ := by gcongr; exact h.2
      _ ≤ _ := h1

theorem mem_ofRat (n d : ℤ) (hd : 0 < d) : (ofRat n d).Mem ((n : ℝ) / d) := by
  have hS := scale_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [ofRat, Mem]
  constructor
  · have h := fdiv_le (n * scale) d hd
    push_cast at h
    rw [div_le_iff₀ hS]
    calc _ ≤ _ := h
      _ = _ := by field_simp
  · have h := le_cdiv (n * scale) d hd
    push_cast at h
    rw [le_div_iff₀ hS]
    calc _ = _ := by field_simp
      _ ≤ _ := h

theorem mem_ofInt (k : ℤ) : (ofInt k).Mem (k : ℝ) := by
  have hS := scale_pos
  simp only [ofInt, Mem, Int.cast_mul]
  rw [mul_div_assoc, div_self (ne_of_gt hS), mul_one]
  exact ⟨le_rfl, le_rfl⟩

theorem lo_pos_of_mem {a : Iv} {x : ℝ} (hx : a.Mem x) (h : 0 < a.lo) : 0 < x :=
  lt_of_lt_of_le (div_pos (by exact_mod_cast h) scale_pos) hx.1

theorem mem_inv {a : Iv} {x : ℝ} (hx : a.Mem x) (h : 0 < a.lo) : a.inv.Mem x⁻¹ := by
  have hS := scale_pos
  have hl : (0 : ℝ) < a.lo := by exact_mod_cast h
  have hxpos := lo_pos_of_mem hx h
  have hhi : (0 : ℝ) < a.hi := by
    have := hx.1.trans hx.2
    have : (0 : ℝ) < a.hi / scale := lt_of_lt_of_le (div_pos hl hS) this
    exact (div_pos_iff_of_pos_right hS).mp this
  have hhi' : 0 < a.hi := by exact_mod_cast hhi
  simp only [inv, Mem]
  constructor
  · have h1 := fdiv_le (scale * scale) a.hi hhi'
    push_cast at h1
    calc _ ≤ (scale : ℝ) * scale / a.hi / scale := by gcongr
      _ = ((a.hi : ℝ) / scale)⁻¹ := by field_simp
      _ ≤ x⁻¹ := by
        rw [inv_le_inv₀ (div_pos hhi hS) hxpos]
        exact hx.2
  · have h1 := le_cdiv (scale * scale) a.lo h
    push_cast at h1
    calc x⁻¹ ≤ ((a.lo : ℝ) / scale)⁻¹ := by
          rw [inv_le_inv₀ hxpos (div_pos hl hS)]
          exact hx.1
      _ = (scale : ℝ) * scale / a.lo / scale := by field_simp
      _ ≤ _ := by gcongr

theorem mem_divNat {a : Iv} {x : ℝ} (hx : a.Mem x) {n : ℕ} (hn : 0 < n) :
    (a.divNat n).Mem (x / n) := by
  have hS := scale_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  simp only [divNat, Mem]
  constructor
  · have h1 := fdiv_le a.lo n hnz
    push_cast at h1
    calc _ ≤ (a.lo : ℝ) / n / scale := by gcongr
      _ = (a.lo / scale) / n := by ring
      _ ≤ x / n := by gcongr; exact hx.1
  · have h1 := le_cdiv a.hi n hnz
    push_cast at h1
    calc x / n ≤ (a.hi / scale) / n := by gcongr; exact hx.2
      _ = (a.hi : ℝ) / n / scale := by ring
      _ ≤ _ := by gcongr

theorem mag_eq (a : Iv) : (a.mag : ℝ) = max |(a.lo : ℝ)| |(a.hi : ℝ)| := by
  simp [mag, Int.cast_max, Int.cast_abs]

theorem abs_le_mag {a : Iv} {x : ℝ} (hx : a.Mem x) : |x| ≤ (a.mag : ℝ) / scale := by
  have hS := scale_pos
  rw [mag_eq, abs_le]
  constructor
  · have : -((max |(a.lo : ℝ)| |(a.hi : ℝ)|) / scale) ≤ (a.lo : ℝ) / scale := by
      rw [← neg_div]
      gcongr
      linarith [neg_abs_le (a.lo : ℝ), le_max_left |(a.lo : ℝ)| |(a.hi : ℝ)|]
    linarith [hx.1]
  · calc x ≤ (a.hi : ℝ) / scale := hx.2
      _ ≤ _ := by gcongr; exact (le_abs_self _).trans (le_max_right _ _)

theorem mag_nonneg (a : Iv) : (0 : ℝ) ≤ a.mag := by
  rw [mag_eq]; exact (abs_nonneg _).trans (le_max_left _ _)

theorem mem_sq {a : Iv} {x : ℝ} (hx : a.Mem x) : a.sq.Mem (x ^ 2) := by
  have hS := scale_pos
  have hm := abs_le_mag hx
  simp only [sq, Mem, Int.cast_zero, zero_div]
  refine ⟨by positivity, ?_⟩
  have h1 := le_cdiv (a.mag * a.mag) scale scale_pos_int
  push_cast at h1
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ ((a.mag : ℝ) / scale) ^ 2 := by gcongr
    _ = (a.mag : ℝ) * a.mag / scale / scale := by ring
    _ ≤ _ := by gcongr

theorem mem_sqPos {a : Iv} {v : ℝ} (hv : a.Mem v) (hpos : 0 < v) : a.sqPos.Mem (v ^ 2) := by
  have hS := scale_pos
  simp only [sqPos, Mem]
  constructor
  · have h1 := fdiv_le (max a.lo 0 * max a.lo 0) scale scale_pos_int
    push_cast at h1
    have hm : max (a.lo : ℝ) 0 / scale ≤ v := by
      rcases le_total (a.lo : ℝ) 0 with h | h
      · rw [max_eq_right h, zero_div]; exact hpos.le
      · rw [max_eq_left h]; exact hv.1
    calc ((fdiv (max a.lo 0 * max a.lo 0) scale : ℤ) : ℝ) / scale
        ≤ max (a.lo : ℝ) 0 * max (a.lo : ℝ) 0 / scale / scale :=
          div_le_div_of_nonneg_right h1 hS.le
      _ = (max (a.lo : ℝ) 0 / scale) ^ 2 := by ring
      _ ≤ v ^ 2 := by gcongr
  · have h1 := le_cdiv (a.hi * a.hi) scale scale_pos_int
    push_cast at h1
    calc v ^ 2 ≤ ((a.hi : ℝ) / scale) ^ 2 := by gcongr; exact hv.2
      _ = (a.hi : ℝ) * a.hi / scale / scale := by ring
      _ ≤ _ := by gcongr

theorem mem_sqIter {a : Iv} {v : ℝ} (hv : a.Mem v) (hpos : 0 < v) (k : ℕ) :
    (a.sqIter k).Mem (v ^ (2 ^ k)) := by
  induction k with
  | zero => simpa [sqIter] using hv
  | succ k ih =>
    rw [sqIter, pow_succ, pow_mul]
    exact mem_sqPos ih (by positivity)

end Iv

/-! ### The exponential -/

/-- Real Horner sum `1 + y/j (1 + y/(j+1) (⋯))`. -/
noncomputable def expHornerR (y : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | r + 1, j => 1 + y * expHornerR y r (j + 1) / j

theorem mem_expHorner {Y : Iv} {y : ℝ} (hy : Y.Mem y) (r j : ℕ) (hj : 0 < j) :
    (expHorner Y r j).Mem (expHornerR y r j) := by
  induction r generalizing j with
  | zero => exact Iv.mem_one
  | succ r ih =>
    simp only [expHorner, expHornerR]
    exact Iv.mem_add Iv.mem_one (Iv.mem_divNat (Iv.mem_mul hy (ih (j + 1) (by omega))) hj)

theorem expHornerR_eq (y : ℝ) :
    expHornerR y 13 1 = ∑ m ∈ Finset.range 14, y ^ m / (m.factorial : ℝ) := by
  simp only [expHornerR, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring

theorem powUp_ge {m : ℤ} (hm : 0 ≤ m) (n : ℕ) :
    ((m : ℝ) / scale) ^ n ≤ (powUp m n : ℝ) / scale := by
  have hS := scale_pos
  induction n with
  | zero => simp [powUp, div_self (ne_of_gt hS)]
  | succ n ih =>
    have h1 := le_cdiv (powUp m n * m) scale scale_pos_int
    push_cast at h1
    have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [powUp]
    calc ((m : ℝ) / scale) ^ (n + 1) = ((m : ℝ) / scale) ^ n * (m / scale) := pow_succ _ _
      _ ≤ (powUp m n : ℝ) / scale * (m / scale) := by gcongr
      _ = (powUp m n : ℝ) * m / scale / scale := by ring
      _ ≤ _ := by gcongr

theorem expTail_ge {m : ℤ} (hm : 0 ≤ m) {y : ℝ} (hy : |y| ≤ (m : ℝ) / scale) :
    |y| ^ 14 * ((Nat.succ 14 : ℕ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ)) : ℝ) ≤
      (expTail m : ℝ) / scale := by
  have hS := scale_pos
  have h1 := le_cdiv (powUp m 14 * 15) 1220496076800 (by norm_num)
  push_cast at h1
  have h2 := powUp_ge hm 14
  have hf : ((Nat.factorial 14 : ℕ) : ℝ) * (14 : ℕ) = 1220496076800 := by
    norm_num [Nat.factorial]
  rw [hf]
  simp only [expTail]
  calc |y| ^ 14 * ((Nat.succ 14 : ℕ) / 1220496076800 : ℝ)
      ≤ ((m : ℝ) / scale) ^ 14 * (15 / 1220496076800) := by
        push_cast
        gcongr
    _ ≤ (powUp m 14 : ℝ) / scale * (15 / 1220496076800) := by gcongr
    _ = (powUp m 14 : ℝ) * 15 / 1220496076800 / scale := by ring
    _ ≤ _ := by gcongr

theorem mem_expPoint (m : ℤ) (h : (expPoint m).2 = true) :
    (expPoint m).1.Mem (Real.exp ((m : ℝ) / scale)) := by
  have hS := scale_pos
  simp only [expPoint, decide_eq_true_eq] at h ⊢
  generalize halvings m 64 = k at h ⊢
  set Y : Iv := ⟨fdiv m (2 ^ k), cdiv m (2 ^ k)⟩ with hY
  have h2k : (0 : ℤ) < 2 ^ k := by positivity
  have h2k' : (0 : ℝ) < 2 ^ k := by positivity
  set y : ℝ := (m : ℝ) / 2 ^ k / scale with hydef
  have hy : Y.Mem y := by
    constructor
    · have := fdiv_le m (2 ^ k) h2k
      push_cast at this
      exact div_le_div_of_nonneg_right this hS.le
    · have := le_cdiv m (2 ^ k) h2k
      push_cast at this
      exact div_le_div_of_nonneg_right this hS.le
  have habs := Iv.abs_le_mag hy
  have hy1 : |y| ≤ 1 := by
    calc |y| ≤ (Y.mag : ℝ) / scale := habs
      _ ≤ (scale : ℝ) / scale := by gcongr
      _ = 1 := div_self (ne_of_gt hS)
  have hb := Real.exp_bound hy1 (n := 14) (by norm_num)
  rw [← expHornerR_eq] at hb
  have hH := mem_expHorner hy 13 1 (by norm_num)
  have hT := expTail_ge (m := Y.mag) (by exact_mod_cast Y.mag_nonneg) habs
  have hmem : (⟨(expHorner Y 13 1).lo - expTail Y.mag, (expHorner Y 13 1).hi + expTail Y.mag⟩ :
      Iv).Mem (Real.exp y) := by
    rw [abs_le] at hb
    constructor
    · push_cast; rw [sub_div]; linarith [hH.1]
    · push_cast; rw [add_div]; linarith [hH.2]
  have hk := Iv.mem_sqIter hmem (Real.exp_pos y) k
  rw [← Real.exp_nat_mul] at hk
  have : ((2 ^ k : ℕ) : ℝ) * y = (m : ℝ) / scale := by
    rw [hydef]; push_cast; field_simp
  rwa [this] at hk

theorem exp_le_inv_one_sub {w : ℝ} (hw : w < 1) : Real.exp w ≤ (1 - w)⁻¹ := by
  have h := Real.add_one_le_exp (-w)
  rw [Real.exp_neg] at h
  have h1 : 0 < 1 - w := by linarith
  rw [le_inv_comm₀ (Real.exp_pos w) h1]
  linarith

theorem mem_expIv {a : Iv} {x : ℝ} (hx : a.Mem x) (h : (expIv a).2 = true) :
    (expIv a).1.Mem (Real.exp x) := by
  have hS := scale_pos
  simp only [expIv, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hok, hw0⟩, hw1⟩ := h
  have he := mem_expPoint a.lo hok
  constructor
  · exact he.1.trans (Real.exp_le_exp.mpr hx.1)
  · have hwS : (0 : ℝ) < (scale : ℝ) - (a.hi - a.lo) := by
      have : ((a.hi - a.lo : ℤ) : ℝ) < scale := by exact_mod_cast hw1
      push_cast at this; linarith
    have hwS' : (0 : ℤ) < scale - (a.hi - a.lo) := by linarith
    have h1 := le_cdiv ((expPoint a.lo).1.hi * scale) (scale - (a.hi - a.lo)) hwS'
    push_cast at h1
    have hw : ((a.hi : ℝ) - a.lo) / scale < 1 := by
      rw [div_lt_one hS]; linarith
    have hexp := exp_le_inv_one_sub hw
    have hpos : 0 ≤ ((expPoint a.lo).1.hi : ℝ) / scale :=
      (Real.exp_pos _).le.trans he.2
    calc Real.exp x ≤ Real.exp ((a.hi : ℝ) / scale) := Real.exp_le_exp.mpr hx.2
      _ = Real.exp ((a.lo : ℝ) / scale) * Real.exp (((a.hi : ℝ) - a.lo) / scale) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ ((expPoint a.lo).1.hi : ℝ) / scale * (1 - ((a.hi : ℝ) - a.lo) / scale)⁻¹ := by
        gcongr
        · exact he.2
      _ = ((expPoint a.lo).1.hi : ℝ) * scale / ((scale : ℝ) - (a.hi - a.lo)) / scale := by
        field_simp
      _ ≤ _ := by gcongr

/-! ### The logarithm -/

theorem mem_logIv {a : Iv} {x : ℝ} (hx : a.Mem x) (h : (logIv a).2 = true) :
    (logIv a).1.Mem (Real.log x) := by
  have hS := scale_pos
  simp only [logIv, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨hok, hlo⟩, hc1⟩, hc2⟩, hle⟩ := h
  set L := approxLog a.lo
  set e := expPoint L
  have he := mem_expPoint L hok
  have hlo' : (0 : ℝ) < a.lo := by exact_mod_cast hlo
  have hl : 0 < (a.lo : ℝ) / scale := div_pos hlo' hS
  have hxpos : 0 < x := lt_of_lt_of_le hl hx.1
  have hδ : (0 : ℝ) < (logSlack : ℝ) / scale := div_pos (by norm_num [logSlack]) hS
  have hδexp : 1 + (logSlack : ℝ) / scale ≤ Real.exp ((logSlack : ℝ) / scale) := by
    linarith [Real.add_one_le_exp ((logSlack : ℝ) / scale)]
  have hc1' : (e.1.hi : ℝ) * scale ≤ a.lo * (scale + logSlack) := by exact_mod_cast hc1
  have hc2' : (a.lo : ℝ) * scale ≤ e.1.lo * (scale + logSlack) := by exact_mod_cast hc2
  constructor
  · -- lower bound: exp (L - δ) ≤ a.lo
    have hkey : Real.exp ((L : ℝ) / scale) ≤ (a.lo : ℝ) / scale * (1 + (logSlack : ℝ) / scale) := by
      calc Real.exp ((L : ℝ) / scale) ≤ (e.1.hi : ℝ) / scale := he.2
        _ ≤ _ := by
          rw [div_le_iff₀ hS]
          calc (e.1.hi : ℝ) ≤ a.lo * (scale + logSlack) / scale := by
                rw [le_div_iff₀ hS]; exact hc1'
            _ = _ := by field_simp
    have h2 : Real.exp (((L - logSlack : ℤ) : ℝ) / scale) ≤ (a.lo : ℝ) / scale := by
      push_cast
      rw [sub_div, Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]
      calc Real.exp ((L : ℝ) / scale) ≤ _ := hkey
        _ ≤ _ := by gcongr
    calc (((L - logSlack : ℤ) : ℝ) / scale) ≤ Real.log ((a.lo : ℝ) / scale) := by
          rw [Real.le_log_iff_exp_le hl]; exact h2
      _ ≤ Real.log x := Real.log_le_log hl hx.1
  · -- upper bound
    have hkey : (a.lo : ℝ) / scale ≤ Real.exp (((L + logSlack : ℤ) : ℝ) / scale) := by
      push_cast
      rw [add_div, Real.exp_add]
      calc (a.lo : ℝ) / scale ≤ (e.1.lo : ℝ) / scale * (1 + (logSlack : ℝ) / scale) := by
            rw [div_le_iff₀ hS]
            calc (a.lo : ℝ) ≤ e.1.lo * (scale + logSlack) / scale := by
                  rw [le_div_iff₀ hS]; exact hc2'
              _ = _ := by field_simp
        _ ≤ _ := mul_le_mul he.1 hδexp (by positivity) (Real.exp_pos _).le
    have h1 : Real.log ((a.lo : ℝ) / scale) ≤ ((L + logSlack : ℤ) : ℝ) / scale := by
      rw [Real.log_le_iff_le_exp hl]; exact hkey
    have hle' : (a.lo : ℝ) ≤ a.hi := by exact_mod_cast hle
    have h2 : Real.log x - Real.log ((a.lo : ℝ) / scale) ≤ ((a.hi : ℝ) - a.lo) / a.lo := by
      rw [← Real.log_div hxpos.ne' hl.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hxpos hl)
      refine this.trans ?_
      rw [sub_le_iff_le_add, div_le_iff₀ hl]
      calc x ≤ (a.hi : ℝ) / scale := hx.2
        _ = (((a.hi : ℝ) - a.lo) / a.lo + 1) * ((a.lo : ℝ) / scale) := by field_simp; ring
    have h3 := le_cdiv ((a.hi - a.lo) * scale) a.lo hlo
    push_cast at h3 ⊢
    have h4 : ((a.hi : ℝ) - a.lo) / a.lo = ((a.hi : ℝ) - a.lo) * scale / a.lo / scale := by
      field_simp
    rw [add_div]
    push_cast at h1
    rw [h4] at h2
    have h5 : ((a.hi : ℝ) - a.lo) * scale / a.lo / scale ≤
        ((cdiv ((a.hi - a.lo) * scale) a.lo : ℤ) : ℝ) / scale := by gcongr
    linarith

end BecknerOnofri.HighDim.Spin.PressureCertificate
