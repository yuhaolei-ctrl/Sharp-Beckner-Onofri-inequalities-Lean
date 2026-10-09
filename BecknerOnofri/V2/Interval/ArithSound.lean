module

public import BecknerOnofri.V2.Interval.Arith
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Soundness of the dyadic interval arithmetic (Arith.lean)

`Iv.Mem a x` : `a.lo/2^110 ≤ x ≤ a.hi/2^110`.  Every operation that succeeds encloses the exact
real result; every failure case is `none`.
-/

namespace BecknerOnofri.V2.Interval

open Real

theorem scale_pos_int : (0 : ℤ) < scale := by unfold scale; positivity

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_pos_int

/-- Rounding down: `⌊m/b⌋ ≤ m/b`. -/
theorem fdiv_le (m b : ℤ) (hb : 0 < b) : ((fdiv m b : ℤ) : ℝ) ≤ (m : ℝ) / b := by
  have h := Int.ediv_mul_le m (ne_of_gt hb)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  exact_mod_cast h

/-- Rounding up: `m/b ≤ ⌈m/b⌉`. -/
theorem le_cdiv (m b : ℤ) (hb : 0 < b) : (m : ℝ) / b ≤ ((cdiv m b : ℤ) : ℝ) := by
  have h := fdiv_le (-m) b hb
  simp only [fdiv] at h
  simp only [cdiv, Int.cast_neg]
  push_cast at h
  rw [neg_div] at h
  linarith

/-- Real membership. -/
def Iv.Mem (a : Iv) (x : ℝ) : Prop := (a.lo : ℝ) / scale ≤ x ∧ x ≤ (a.hi : ℝ) / scale

namespace Iv

theorem mem_iff_scaled {a : Iv} {x : ℝ} :
    a.Mem x ↔ (a.lo : ℝ) ≤ x * scale ∧ x * scale ≤ (a.hi : ℝ) := by
  simp only [Mem, div_le_iff₀ scale_pos, le_div_iff₀ scale_pos]

theorem mem_zero : zero.Mem 0 := by simp [Mem, zero]

theorem mem_add {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  simp only [Mem, add, Int.cast_add, add_div] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {a : Iv} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  simp only [Mem, neg, Int.cast_neg, neg_div] at *
  constructor <;> linarith [hx.1, hx.2]

/-- Endpoint bounds for a product (all four products). -/
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

theorem mem_ofRat (n : ℤ) (d : ℕ) (hd : 0 < d) : (ofRat n d).Mem ((n : ℝ) / d) := by
  have hS := scale_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdz : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  simp only [ofRat, Mem]
  constructor
  · have h := fdiv_le (n * scale) d hdz
    push_cast at h
    rw [div_le_iff₀ hS]
    calc _ ≤ _ := h
      _ = _ := by field_simp
  · have h := le_cdiv (n * scale) d hdz
    push_cast at h
    rw [le_div_iff₀ hS]
    calc _ = _ := by field_simp
      _ ≤ _ := h

/-- `ofRat2` encloses every real between its two rational endpoints. -/
theorem mem_ofRat2 {n₁ n₂ : ℤ} {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) {x : ℝ}
    (hx₁ : (n₁ : ℝ) / d₁ ≤ x) (hx₂ : x ≤ (n₂ : ℝ) / d₂) : (ofRat2 n₁ d₁ n₂ d₂).Mem x := by
  have hlo := (mem_ofRat n₁ d₁ h₁).1
  have hhi := (mem_ofRat n₂ d₂ h₂).2
  simp only [ofRat2, Mem] at *
  constructor
  · exact hlo.trans hx₁
  · exact hx₂.trans hhi

theorem mem_ofInt (k : ℤ) : (ofInt k).Mem (k : ℝ) := by
  have hS := scale_pos
  simp only [ofInt, Mem, Int.cast_mul]
  rw [mul_div_assoc, div_self (ne_of_gt hS), mul_one]
  exact ⟨le_rfl, le_rfl⟩

theorem mem_recipPos {a : Iv} {x : ℝ} (hx : a.Mem x) (h : 0 < a.lo) :
    x ≠ 0 ∧ (recipPos a).Mem x⁻¹ := by
  have hS := scale_pos
  have hl : (0 : ℝ) < a.lo := by exact_mod_cast h
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hl hS) hx.1
  have hhi : (0 : ℝ) < a.hi := by
    have h2 : (0 : ℝ) < a.hi / scale := lt_of_lt_of_le (div_pos hl hS) (hx.1.trans hx.2)
    exact (div_pos_iff_of_pos_right hS).mp h2
  have hhi' : 0 < a.hi := by exact_mod_cast hhi
  refine ⟨hxpos.ne', ?_⟩
  simp only [recipPos, Mem]
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

/-- Reciprocal: success implies the interval avoids zero, and encloses `x⁻¹`. -/
theorem mem_recip {a b : Iv} {x : ℝ} (hx : a.Mem x) (hb : a.recip = some b) :
    x ≠ 0 ∧ b.Mem x⁻¹ := by
  unfold recip at hb
  split_ifs at hb with h1 h2
  · obtain rfl := Option.some.inj hb
    exact mem_recipPos hx h1
  · obtain rfl := Option.some.inj hb
    have hneg : 0 < a.neg.lo := by simp only [neg]; omega
    obtain ⟨hx0, hm⟩ := mem_recipPos (mem_neg hx) hneg
    refine ⟨fun h => hx0 (by simp [h]), ?_⟩
    simpa [inv_neg] using mem_neg hm

theorem mk?_mem {lo hi : ℤ} {b : Iv} (h : mk? lo hi = some b) :
    b = ⟨lo, hi⟩ := by
  unfold mk? at h
  split_ifs at h
  exact (Option.some.inj h).symm

theorem mem_meet {a b c : Iv} {x : ℝ} (ha : a.Mem x) (hb : b.Mem x) (h : a.meet? b = some c) :
    c.Mem x := by
  unfold meet? at h
  obtain rfl := mk?_mem h
  rw [mem_iff_scaled] at ha hb ⊢
  simp only [Int.cast_max, Int.cast_min]
  exact ⟨max_le ha.1 hb.1, le_min ha.2 hb.2⟩

end Iv

/-! ### Logarithm -/

theorem oddLcm42 : oddLcm 42 = 126187983663182839765532348501593275 := by decide +kernel
theorem log2Num_eq : log2Num =
    3141594392672391489236013350733961244277294726293717599776485561365283312568 := by
  decide +kernel

theorem log2_sum_eq :
    (∑ r ∈ Finset.range 42, 2 * (((1 : ℝ) / 3) ^ (2 * r + 1) / (2 * r + 1))) =
      (log2Num : ℝ) / ((3 ^ 85 * oddLcm 42 : ℕ) : ℝ) := by
  rw [oddLcm42, log2Num_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- The positive atanh series (eq:logbounds): for `0 ≤ z < 1`,
`2 Σ_{r<42} z^{2r+1}/(2r+1) ≤ log((1+z)/(1-z)) ≤ that + 2 z^85 / (85 (1 - z²))`. -/
theorem log_series_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) :
    (∑ r ∈ Finset.range 42, 2 * (z ^ (2 * r + 1) / (2 * r + 1))) ≤ log ((1 + z) / (1 - z)) ∧
    log ((1 + z) / (1 - z)) ≤
      (∑ r ∈ Finset.range 42, 2 * (z ^ (2 * r + 1) / (2 * r + 1))) +
        2 * z ^ 85 / (85 * (1 - z ^ 2)) := by
  have habs : |z| < 1 := by rwa [abs_of_nonneg h0]
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hlog : log (1 + z) - log (1 - z) = log ((1 + z) / (1 - z)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hlog] at hS
  have hnn : ∀ r : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * r + 1)) * z ^ (2 * r + 1) := fun r => by positivity
  have hterm : ∀ r : ℕ, (2 : ℝ) * (1 / (2 * r + 1)) * z ^ (2 * r + 1) =
      2 * (z ^ (2 * r + 1) / (2 * r + 1)) := fun r => by ring
  constructor
  · have := sum_le_hasSum (Finset.range 42) (fun r _ => hnn r) hS
    simpa only [hterm] using this
  · -- tail bound
    have hT := (hasSum_nat_add_iff' 42).mpr hS
    have hg : HasSum (fun r : ℕ => 2 * z ^ 85 / 85 * (z ^ 2) ^ r)
        (2 * z ^ 85 / 85 * (1 - z ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
    have hle : ∀ r : ℕ, (2 : ℝ) * (1 / (2 * ((r + 42 : ℕ) : ℝ) + 1)) * z ^ (2 * (r + 42) + 1) ≤
        2 * z ^ 85 / 85 * (z ^ 2) ^ r := by
      intro r
      have hz : z ^ (2 * (r + 42) + 1) = z ^ 85 * (z ^ 2) ^ r := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [hz]
      have : (1 : ℝ) / (2 * ((r + 42 : ℕ) : ℝ) + 1) ≤ 1 / 85 := by
        apply one_div_le_one_div_of_le (by norm_num)
        push_cast; linarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
      have hp : 0 ≤ z ^ 85 * (z ^ 2) ^ r :=
        mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sq_nonneg z) r)
      calc (2 : ℝ) * (1 / (2 * ((r + 42 : ℕ) : ℝ) + 1)) * (z ^ 85 * (z ^ 2) ^ r)
          ≤ 2 * (1 / 85) * (z ^ 85 * (z ^ 2) ^ r) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hp
        _ = 2 * z ^ 85 / 85 * (z ^ 2) ^ r := by ring
    have := hasSum_le hle hT hg
    rw [sub_le_iff_le_add] at this
    have e : 2 * z ^ 85 / 85 * (1 - z ^ 2)⁻¹ = 2 * z ^ 85 / (85 * (1 - z ^ 2)) := by
      field_simp
    simp only [hterm] at *
    linarith [this, e]

/-- Series partial sums are tracked by `seriesFold`. -/
theorem seriesFold_mem {z z2 : Iv} {y : ℝ} (hz : z.Mem y) (hz2 : z2.Mem (y * y)) (n : ℕ) :
    (seriesFold z z2 n).1.Mem (∑ r ∈ Finset.range n, 2 * (y ^ (2 * r + 1) / (2 * r + 1))) ∧
      (seriesFold z z2 n).2.Mem (y ^ (2 * n + 1)) := by
  induction n with
  | zero => simpa [seriesFold] using ⟨Iv.mem_zero, hz⟩
  | succ n ih =>
    have e : seriesFold z z2 (n + 1) = seriesStep z2 (seriesFold z z2 n) n := by
      simp [seriesFold, List.range_succ, List.foldl_append]
    rw [e]
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_range_succ]
      refine Iv.mem_add h1 ?_
      have := Iv.mem_mul h2 (Iv.mem_ofRat 2 (2 * n + 1) (by omega))
      convert this using 1
      push_cast; ring
    · have := Iv.mem_mul h2 hz2
      have e3 : y ^ (2 * (n + 1) + 1) = y ^ (2 * n + 1) * (y * y) := by ring
      rw [e3]; exact this

theorem Iv.mem_one : (Iv.ofInt 1).Mem 1 := by simpa using Iv.mem_ofInt 1

/-- Enclosure of `log 2`. -/
theorem log2Iv_mem : log2Iv.Mem (Real.log 2) := by
  have hb := log_series_bounds (z := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  have e2 : (1 + (1 : ℝ) / 3) / (1 - 1 / 3) = 2 := by norm_num
  rw [e2] at hb
  obtain ⟨hlo, hhi⟩ := hb
  rw [log2_sum_eq] at hlo hhi
  have htail : (2 : ℝ) * (1 / 3) ^ 85 / (85 * (1 - (1 / 3) ^ 2)) = 9 / (340 * 3 ^ 85) := by
    norm_num
  rw [htail] at hhi
  have hL : (0 : ℝ) < (oddLcm 42 : ℝ) := by rw [oddLcm42]; norm_num
  have key : log2Iv = Iv.ofRat2 (log2Num : ℤ) (3 ^ 85 * oddLcm 42)
      ((340 * log2Num + 9 * oddLcm 42 : ℕ) : ℤ) (340 * (3 ^ 85 * oddLcm 42)) := by
    unfold log2Iv Iv.ofRat2
    push_cast
    rfl
  rw [key]
  refine Iv.mem_ofRat2 (by rw [oddLcm42]; norm_num) (by rw [oddLcm42]; norm_num) ?_ ?_
  · simpa only [Int.cast_natCast] using hlo
  · refine hhi.trans (le_of_eq ?_)
    push_cast
    have : (oddLcm 42 : ℝ) ≠ 0 := hL.ne'
    field_simp
    ring


/-- `zOf` encloses `(v-1)/(v+1)`; success forces `v + 1 ≠ 0`. -/
theorem zOf_mem {x z : Iv} {v : ℝ} (hx : x.Mem v) (h : zOf x = some z) :
    v + 1 ≠ 0 ∧ z.Mem ((v - 1) / (v + 1)) := by
  unfold zOf at h
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 : (x.add (Iv.ofInt 1)).Mem (v + 1) := Iv.mem_add hx Iv.mem_one
  obtain ⟨hne, hm⟩ := Iv.mem_recip h1 hw
  refine ⟨hne, ?_⟩
  have h2 : (x.add (Iv.ofInt 1).neg).Mem (v + -1) := Iv.mem_add hx (Iv.mem_neg Iv.mem_one)
  have := Iv.mem_mul h2 hm
  rw [div_eq_mul_inv]
  convert this using 2

/-- `remOf` encloses `2 t / (85 (1 - y²))` whenever `z2 ∋ y²` and `term ∋ t`. -/
theorem remOf_mem {z2 term rem : Iv} {w t : ℝ} (hz2 : z2.Mem w) (ht : term.Mem t)
    (h : remOf z2 term = some rem) :
    1 - w ≠ 0 ∧ rem.Mem (2 * t / (85 * (1 - w))) := by
  unfold remOf at h
  obtain ⟨den, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 : (((Iv.ofInt 1).add z2.neg).mul (Iv.ofInt 85)).Mem ((1 + -w) * 85) :=
    Iv.mem_mul (Iv.mem_add Iv.mem_one (Iv.mem_neg hz2)) (by simpa using Iv.mem_ofInt 85)
  obtain ⟨hne, hm⟩ := Iv.mem_recip h1 hd
  refine ⟨?_, ?_⟩
  · intro h0
    apply hne
    have : 1 + -w = 0 := by linarith
    rw [this]; ring
  · have := Iv.mem_mul (Iv.mem_mul ht (by simpa using Iv.mem_ofInt 2)) hm
    convert this using 1
    field_simp
    ring

theorem logCore_mem {x r : Iv} {v : ℝ} (hv1 : 1 ≤ v) (hx : x.Mem v)
    (h : logCore x = some r) : r.Mem (Real.log v) := by
  unfold logCore at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hne, hzm⟩ := zOf_mem hx hz
  set y : ℝ := (v - 1) / (v + 1) with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hz2 : (z.mul z).Mem (y * y) := Iv.mem_mul hzm hzm
  obtain ⟨rem, hrem, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hne2, hremm⟩ := remOf_mem hz2 (seriesFold_mem hzm hz2 42).2 hrem
  have hser := seriesFold_mem hzm hz2 42
  obtain rfl := Iv.mk?_mem h
  have hb := log_series_bounds hy0 hy1
  have hlogv : (1 + y) / (1 - y) = v := by
    rw [hy]; field_simp; ring
  rw [hlogv] at hb
  have hy2 : y * y = y ^ 2 := by ring
  have e85 : y ^ (2 * 42 + 1) = y ^ 85 := by norm_num
  rw [e85, hy2] at hremm
  have hsum := hser.1
  rw [Iv.mem_iff_scaled] at hsum hremm
  rw [Iv.mem_iff_scaled]
  have hS := scale_pos
  push_cast
  constructor
  · nlinarith [hb.1, hsum.1]
  · nlinarith [hb.2, hsum.2, hremm.2]


theorem scale_eq : (scale : ℝ) = 2 ^ 110 := by
  simp only [scale, Int.cast_pow, Int.cast_ofNat]

/-- Reduction to a mantissa: for a positive integer `a`, with `m = ⌊log₂ a⌋`, the real
`v = a / 2^m` lies in `[1, 2)`. -/
theorem mantissa_bounds {a : ℤ} (ha : 0 < a) :
    1 ≤ (a : ℝ) / 2 ^ Nat.log2 a.toNat ∧ (a : ℝ) / 2 ^ Nat.log2 a.toNat < 2 := by
  have hn : a.toNat ≠ 0 := by omega
  have h1 := Nat.log2_self_le hn
  have h2 := Nat.lt_log2_self (n := a.toNat)
  have hac : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
    have : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    exact_mod_cast this
  have h1' : (2 : ℝ) ^ Nat.log2 a.toNat ≤ (a : ℝ) := by
    rw [← hac]; exact_mod_cast h1
  have h2' : (a : ℝ) < 2 ^ (Nat.log2 a.toNat + 1) := by
    rw [← hac]; exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ Nat.log2 a.toNat := by positivity
  constructor
  · rw [le_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; rw [pow_succ] at h2'; linarith

theorem logPoint_mem {a : ℤ} (ha : 0 < a) {r : Iv} (h : logPoint a = some r) :
    r.Mem (Real.log ((a : ℝ) / scale)) := by
  unfold logPoint at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  set m : ℕ := Nat.log2 a.toNat with hm
  obtain ⟨hv1, hv2⟩ := mantissa_bounds ha
  rw [← hm] at hv1 hv2
  set v : ℝ := (a : ℝ) / 2 ^ m with hv
  have hx : (Iv.ofRat (a * 2 ^ (-((m : ℤ) - 110)).toNat) (2 ^ 110 * 2 ^ ((m : ℤ) - 110).toNat)).Mem v := by
    have := Iv.mem_ofRat (a * 2 ^ (-((m : ℤ) - 110)).toNat) (2 ^ 110 * 2 ^ ((m : ℤ) - 110).toNat)
      (by positivity)
    convert this using 1
    rcases le_total 110 m with hm110 | hm110
    · have e1 : (-((m : ℤ) - 110)).toNat = 0 := by omega
      have e2 : ((m : ℤ) - 110).toNat = m - 110 := by omega
      rw [e1, e2, hv]
      have : (2 : ℝ) ^ m = 2 ^ 110 * 2 ^ (m - 110) := by
        rw [← pow_add]; congr 1; omega
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_zero, mul_one]
      rw [this]
    · have e1 : (-((m : ℤ) - 110)).toNat = 110 - m := by omega
      have e2 : ((m : ℤ) - 110).toNat = 0 := by omega
      rw [e1, e2, hv]
      have : (2 : ℝ) ^ 110 = 2 ^ m * 2 ^ (110 - m) := by
        rw [← pow_add]; congr 1; omega
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow,
        Nat.cast_ofNat, pow_zero, mul_one]
      rw [this]
      have : (0 : ℝ) < 2 ^ (110 - m) := by positivity
      have : (0 : ℝ) < 2 ^ m := by positivity
      field_simp
  have hcm := logCore_mem hv1 hx hc
  have hk := Iv.mem_ofInt ((m : ℤ) - 110)
  have h2 := Iv.mem_mul log2Iv_mem hk
  have := Iv.mem_add hcm h2
  convert this using 1
  have hpos : (0 : ℝ) < a := by exact_mod_cast ha
  have hvpos : 0 < v := by positivity
  have e : (a : ℝ) / scale = v * 2 ^ ((m : ℤ) - 110) := by
    rw [scale_eq, hv]
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_natCast]
    field_simp
  rw [e, Real.log_mul hvpos.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  push_cast
  ring

theorem Iv.log_mem {a r : Iv} {x : ℝ} (hx : a.Mem x) (h : a.log = some r) :
    0 < x ∧ r.Mem (Real.log x) := by
  unfold Iv.log at h
  split_ifs at h with hlo
  obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Iv.mk?_mem h
  have hS := scale_pos
  have hlo' : (0 : ℝ) < a.lo := by exact_mod_cast hlo
  have hxpos : 0 < x := lt_of_lt_of_le (div_pos hlo' hS) hx.1
  refine ⟨hxpos, ?_⟩
  have hhi : (0 : ℤ) < a.hi := by
    have : (0 : ℝ) < a.hi := by
      have h2 : (0 : ℝ) < a.hi / scale := lt_of_lt_of_le (div_pos hlo' hS) (hx.1.trans hx.2)
      exact (div_pos_iff_of_pos_right hS).mp h2
    exact_mod_cast this
  have hL := (logPoint_mem hlo hl).1
  have hU := (logPoint_mem hhi hu).2
  constructor
  · exact hL.trans (Real.log_le_log (div_pos hlo' hS) hx.1)
  · refine (Real.log_le_log hxpos hx.2).trans hU

end BecknerOnofri.V2.Interval
