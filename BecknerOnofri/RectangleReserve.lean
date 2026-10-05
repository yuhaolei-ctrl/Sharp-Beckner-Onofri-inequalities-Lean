module

public import BecknerOnofri.Arithmetic
public import BecknerOnofri.RectangleCombinatorics
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-!
The positive two-coordinate reserve dominates the large-support tail in
every dimension at least thirteen.  Real powers retain the half-integer
exponents in odd dimensions.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace BecknerOnofri.RectangleReserve

def ratio (d : ℕ) : ℝ :=
  (17 / 15 : ℝ) * (27 / (d : ℝ)) ^ ((d : ℝ) / 2) /
    ((d : ℝ) * ((d : ℝ) - 1))

theorem ratio_square (d : ℕ) :
    ratio d ^ 2 = (17 / 15 : ℝ) ^ 2 * (27 / (d : ℝ)) ^ d /
      ((d : ℝ) * ((d : ℝ) - 1)) ^ 2 := by
  have hp : ((27 / (d : ℝ)) ^ ((d : ℝ) / 2)) ^ 2 =
      (27 / (d : ℝ)) ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  unfold ratio
  rw [div_pow, mul_pow, hp]

/-- Exact rational checks cover the interval before the exponential base
falls below one; no floating-point or untrusted native evaluation is used. -/
theorem ratio_lt_one (d : ℕ) (hd : 13 ≤ d) : ratio d < 1 := by
  by_cases hlarge : 27 ≤ d
  · have hd' : (27 : ℝ) ≤ d := by exact_mod_cast hlarge
    have hd0 : (0 : ℝ) < d := by linarith
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    have hb : 27 / (d : ℝ) ≤ 1 := (div_le_one (by linarith)).2 hd'
    have hp := Real.rpow_le_one (show (0 : ℝ) ≤ 27 / d by positivity) hb
      (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
    have hden : 0 < (d : ℝ) * ((d : ℝ) - 1) := by positivity
    unfold ratio
    apply (div_lt_one hden).2
    have hs : 0 ≤ ((d : ℝ) - 27) ^ 2 := sq_nonneg _
    nlinarith
  · have hsmall : d ≤ 26 := by omega
    have hs : ratio d ^ 2 < 1 := by
      rw [ratio_square]
      interval_cases d <;> norm_num
    nlinarith [sq_nonneg (ratio d - 1)]

def pairReserve (d : ℕ) : ℝ :=
  4 * (d.choose 2 : ℝ) * (2 : ℝ) ^ (-((d : ℝ) / 2)) *
    ((((d : ℝ) - 2) / ((d : ℝ) - 1)) * Real.sqrt 2 - 1)

def tailMass (d : ℕ) : ℝ :=
  ∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
    (2 : ℝ) ^ j * (d.choose j : ℝ) * (j : ℝ) ^ (-((d : ℝ) / 2))

theorem pairReserve_lower_bound (d : ℕ) (hd : 13 ≤ d) :
    (10 / 17 : ℝ) * (d : ℝ) * ((d : ℝ) - 1) *
      (2 : ℝ) ^ (-((d : ℝ) / 2)) < pairReserve d := by
  have hd' : (13 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hr := Arithmetic.projected_dimension_ratio hd'
  have hs := Arithmetic.sqrt_two_gt_twenty_four_seventeenths
  have hratio : 0 < ((d : ℝ) - 2) / ((d : ℝ) - 1) := by positivity
  have hm := mul_lt_mul_of_pos_left hs hratio
  have hreserve : (5 / 17 : ℝ) <
      (((d : ℝ) - 2) / ((d : ℝ) - 1)) * Real.sqrt 2 - 1 := by nlinarith
  unfold pairReserve
  rw [Nat.cast_choose_two]
  calc
    _ = (4 * ((d : ℝ) * ((d : ℝ) - 1) / 2) *
      (2 : ℝ) ^ (-((d : ℝ) / 2))) * (5 / 17) := by ring
    _ < _ := mul_lt_mul_of_pos_left hreserve (by positivity)

theorem tail_scale_identity (d : ℕ) :
    (3 : ℝ) ^ d * (2 * (d : ℝ) / 3) ^ (-((d : ℝ) / 2)) =
      (27 / (d : ℝ)) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-((d : ℝ) / 2)) := by
  have h3 : (3 : ℝ) ^ d = (9 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    convert (Real.rpow_natCast (3 : ℝ) d).symm using 1
    congr 1
    ring
  rw [h3, Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num)]
  change (9 : ℝ) ^ ((d : ℝ) / 2) / (2 * (d : ℝ) / 3) ^ ((d : ℝ) / 2) =
    (27 / (d : ℝ)) ^ ((d : ℝ) / 2) / (2 : ℝ) ^ ((d : ℝ) / 2)
  rw [← Real.div_rpow (by norm_num) (by positivity),
    ← Real.div_rpow (by positivity) (by norm_num)]
  congr 1
  ring

theorem tailMass_upper_bound (d : ℕ) (hd : 13 ≤ d) :
    tailMass d ≤ (2 / 3 : ℝ) * (27 / (d : ℝ)) ^ ((d : ℝ) / 2) *
      (2 : ℝ) ^ (-((d : ℝ) / 2)) := by
  have hd' : (13 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hbase : 0 < 2 * (d : ℝ) / 3 := by positivity
  have hbound (j : ℕ) (hj : j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j)) :
      (j : ℝ) ^ (-((d : ℝ) / 2)) ≤
        (2 * (d : ℝ) / 3) ^ (-((d : ℝ) / 2)) := by
    have hj' : 2 * (d : ℝ) < 3 * (j : ℝ) := by exact_mod_cast (mem_filter.mp hj).2
    exact Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
  unfold tailMass
  calc
    _ ≤ ∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
      ((2 : ℝ) ^ j * (d.choose j : ℝ)) *
        (2 * (d : ℝ) / 3) ^ (-((d : ℝ) / 2)) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hbound j hj) (by positivity)
    _ = (∑ j ∈ (range (d + 1)).filter (fun j => 2 * d < 3 * j),
      (2 : ℝ) ^ j * (d.choose j : ℝ)) *
        (2 * (d : ℝ) / 3) ^ (-((d : ℝ) / 2)) := (sum_mul ..).symm
    _ ≤ ((2 / 3 : ℝ) * 3 ^ d) *
        (2 * (d : ℝ) / 3) ^ (-((d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (RectangleCombinatorics.three_symbol_count d) (by positivity)
    _ = _ := by rw [mul_assoc, tail_scale_identity]; ring

theorem tailMass_lt_pairReserve (d : ℕ) (hd : 13 ≤ d) : tailMass d < pairReserve d := by
  have hd' : (13 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hr := ratio_lt_one d hd
  have hden : 0 < (d : ℝ) * ((d : ℝ) - 1) := by positivity
  rw [ratio, div_lt_one hden] at hr
  have hcoeff : (2 / 3 : ℝ) * (27 / (d : ℝ)) ^ ((d : ℝ) / 2) <
      (10 / 17 : ℝ) * (d : ℝ) * ((d : ℝ) - 1) := by nlinarith
  calc
    tailMass d ≤ _ := tailMass_upper_bound d hd
    _ < _ := mul_lt_mul_of_pos_right hcoeff (by positivity)
    _ < pairReserve d := pairReserve_lower_bound d hd

/-- The small-support cube factor is nonnegative.  The cubic identity below
is the chord inequality for `j * (d-j)^2`, proved directly as a polynomial. -/
theorem cube_factor_nonneg {d j : ℝ} (hd : 13 ≤ d) (hj : 2 ≤ j)
    (hjupper : 3 * j ≤ 2 * d) :
    0 ≤ ((d - j) / (d - 1)) * Real.sqrt j - 1 := by
  let L : ℝ := 2 * d / 3
  let g : ℝ → ℝ := fun x => x * (d - x) ^ 2 - (d - 1) ^ 2
  have hL : 0 < L - 2 := by dsimp [L]; linarith
  have hleft : 0 ≤ L - j := by dsimp [L]; linarith
  have hright : 0 ≤ j - 2 := by linarith
  have hlast : 0 ≤ 4 * d / 3 - j - 2 := by linarith
  have h2 : 0 ≤ g 2 := by
    simpa [g] using (Arithmetic.pair_polynomial_pos hd).le
  have hLvalue : 0 ≤ g L := by
    have hp := Arithmetic.endpoint_polynomial_pos hd
    dsimp [g, L]
    nlinarith
  have hidentity :
      (L - 2) * g j = (L - j) * g 2 + (j - 2) * g L +
        (L - 2) * (j - 2) * (L - j) * (4 * d / 3 - j - 2) := by
    dsimp [g, L]
    ring
  have hg : 0 ≤ g j := by
    apply nonneg_of_mul_nonneg_right (a := L - 2) ?_ hL
    rw [hidentity]
    positivity
  have hj0 : 0 ≤ j := by linarith
  have hs : ((d - j) * Real.sqrt j) ^ 2 = j * (d - j) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hj0]
    ring
  have hprod : 0 ≤ (d - j) * Real.sqrt j := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hmajor : d - 1 ≤ (d - j) * Real.sqrt j := by
    dsimp [g] at hg
    nlinarith
  have hden : 0 < d - 1 := by linarith
  have hdiv : 1 ≤ ((d - j) * Real.sqrt j) / (d - 1) := (le_div_iff₀ hden).2 (by linarith)
  have he : ((d - j) / (d - 1)) * Real.sqrt j =
      ((d - j) * Real.sqrt j) / (d - 1) := by ring
  rw [he]
  linarith

def cubeWeight (d r j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (r.choose j : ℝ) * (j : ℝ) ^ (-((d : ℝ) / 2))

def cubeFactor (d j : ℕ) : ℝ :=
  (((d : ℝ) - (j : ℝ)) / ((d : ℝ) - 1)) * Real.sqrt (j : ℝ) - 1

/-- The gap for a zero-one rectangle with r active coordinates.  For r≤d,
the extra indices r<j≤d vanish because their binomial coefficient is zero. -/
def cubeGap (d r : ℕ) : ℝ :=
  ∑ j ∈ range (d + 1), if 2 ≤ j then cubeWeight d r j * cubeFactor d j else 0

def pairScale (d r : ℕ) : ℝ := (r.choose 2 : ℝ) / (d.choose 2 : ℝ)

theorem cubeWeight_nonneg (d r j : ℕ) : 0 ≤ cubeWeight d r j := by
  unfold cubeWeight
  positivity

theorem pairScale_pos {d r : ℕ} (hr : 2 ≤ r) (hrd : r ≤ d) : 0 < pairScale d r := by
  unfold pairScale
  apply div_pos
  · exact_mod_cast Nat.choose_pos hr
  · exact_mod_cast Nat.choose_pos (hr.trans hrd)

theorem cubeWeight_le_scaled {d r j : ℕ} (hr : 2 ≤ r) (hrd : r ≤ d) (hj : 2 ≤ j) :
    cubeWeight d r j ≤ pairScale d r * cubeWeight d d j := by
  have hbin : (r.choose j : ℝ) ≤ pairScale d r * (d.choose j : ℝ) := by
    by_cases hjr : j ≤ r
    · have h := RectangleCombinatorics.binomial_ratio_mono hj hjr hrd
      have hr0 : (0 : ℝ) < r.choose 2 := by exact_mod_cast Nat.choose_pos hr
      have hh := (div_le_iff₀ hr0).mp h
      unfold pairScale
      calc
        (r.choose j : ℝ) ≤ ((d.choose j : ℝ) / (d.choose 2 : ℝ)) * (r.choose 2 : ℝ) := hh
        _ = _ := by ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : r < j)]
      have hs := (pairScale_pos hr hrd).le
      norm_num only [Nat.cast_zero]
      exact mul_nonneg hs (Nat.cast_nonneg _)
  unfold cubeWeight
  calc
    (2 : ℝ) ^ j * (r.choose j : ℝ) * (j : ℝ) ^ (-((d : ℝ) / 2)) ≤
        (2 : ℝ) ^ j * (pairScale d r * (d.choose j : ℝ)) *
          (j : ℝ) ^ (-((d : ℝ) / 2)) := by gcongr
    _ = _ := by ring

theorem cubeFactor_ge_neg_one {d j : ℕ} (hd : 13 ≤ d) (hj : j ≤ d) :
    -1 ≤ cubeFactor d j := by
  have hd' : (13 : ℝ) ≤ d := by exact_mod_cast hd
  have hj' : (j : ℝ) ≤ d := by exact_mod_cast hj
  have hden : 0 < (d : ℝ) - 1 := by linarith
  have hquot : 0 ≤ ((d : ℝ) - (j : ℝ)) / ((d : ℝ) - 1) := by positivity
  have hm := mul_nonneg hquot (Real.sqrt_nonneg (j : ℝ))
  unfold cubeFactor
  linarith

theorem pair_term_eq {d r : ℕ} (hd : 13 ≤ d) :
    cubeWeight d r 2 * cubeFactor d 2 = pairScale d r * pairReserve d := by
  have hd0 : (d.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ d by omega)).ne'
  unfold cubeWeight cubeFactor pairScale pairReserve
  norm_num only [Nat.cast_ofNat, pow_two]
  field_simp

/-- Every cube term plus its allotted tail compensation is nonnegative;
the two-coordinate term supplies the whole positive reserve. -/
theorem cube_term_compensation {d r j : ℕ} (hd : 13 ≤ d) (hr : 2 ≤ r)
    (hrd : r ≤ d) (hjd : j ≤ d) :
    (if 2 ≤ j then cubeWeight d r j * cubeFactor d j else 0) +
      pairScale d r * (if 2 * d < 3 * j then cubeWeight d d j else 0) ≥
        (if j = 2 then pairScale d r * pairReserve d else 0) := by
  by_cases hj2 : j = 2
  · subst j
    have ht : ¬ 2 * d < 3 * 2 := by omega
    simp only [le_refl, if_true, ht, if_false, mul_zero, add_zero, pair_term_eq hd]
  · by_cases hj : 2 ≤ j
    · simp only [hj, hj2, if_true, if_false]
      by_cases ht : 2 * d < 3 * j
      · simp only [ht, if_true]
        have hfac := cubeFactor_ge_neg_one hd hjd
        have hw := cubeWeight_nonneg d r j
        have hscaled := cubeWeight_le_scaled hr hrd hj
        have hmul := mul_le_mul_of_nonneg_left hfac hw
        nlinarith
      · simp only [ht, if_false, mul_zero, add_zero]
        apply mul_nonneg (cubeWeight_nonneg d r j)
        exact cube_factor_nonneg
          (by exact_mod_cast hd) (by exact_mod_cast hj)
          (by exact_mod_cast (show 3 * j ≤ 2 * d by omega))
    · have ht : ¬ 2 * d < 3 * j := by omega
      simp [hj, hj2, ht]

theorem cubeGap_reserve_lower_bound {d r : ℕ} (hd : 13 ≤ d) (hr : 2 ≤ r)
    (hrd : r ≤ d) :
    pairScale d r * (pairReserve d - tailMass d) ≤ cubeGap d r := by
  have hsum := sum_le_sum (s := range (d + 1)) (fun j hj =>
    cube_term_compensation (j := j) hd hr hrd (by have := mem_range.mp hj; omega))
  have h2mem : 2 ∈ range (d + 1) := mem_range.mpr (by omega)
  have htail : (∑ j ∈ range (d + 1),
      if 2 * d < 3 * j then cubeWeight d d j else 0) = tailMass d := by
    rw [← sum_filter]
    rfl
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [htail] at hsum
  have hsingle : (∑ j ∈ range (d + 1), if j = 2 then pairScale d r * pairReserve d else 0) =
      pairScale d r * pairReserve d := by simp [h2mem]
  rw [hsingle] at hsum
  change pairScale d r * pairReserve d ≤ cubeGap d r + pairScale d r * tailMass d at hsum
  nlinarith

theorem cubeGap_pos {d r : ℕ} (hd : 13 ≤ d) (hr : 2 ≤ r) (hrd : r ≤ d) :
    0 < cubeGap d r := by
  have hp := tailMass_lt_pairReserve d hd
  have hs := pairScale_pos hr hrd
  exact (mul_pos hs (sub_pos.mpr hp)).trans_le (cubeGap_reserve_lower_bound hd hr hrd)

theorem cubeGap_nonneg {d r : ℕ} (hd : 13 ≤ d) (hrd : r ≤ d) : 0 ≤ cubeGap d r := by
  by_cases hr : 2 ≤ r
  · exact (cubeGap_pos hd hr hrd).le
  · have he : cubeGap d r = 0 := by
      unfold cubeGap
      apply sum_eq_zero
      intro j hj
      split_ifs with h2
      · have hchoose : r.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [cubeWeight, hchoose]
      · rfl
    rw [he]

end BecknerOnofri.RectangleReserve
